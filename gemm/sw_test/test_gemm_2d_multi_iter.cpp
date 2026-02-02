// 2D Multi-Row GEMM Multi-Iteration Test
//
// Purpose: Validate batched command execution with configurable B/C/V
//
// Supported configurations (via command line):
//   - B8_C8_V16: B=8, C=32 (4 blocks x 8), V=256 (16x16 rows)
//   - B1_C64_V2: B=1, C=64, V=32 (2x16 rows) - single weight dispatch
//
// Memory layout (GDDR6 line addresses):
//   - Left (activations): line 0
//   - Right (weights): line 0x400000 (byte 0x8000000)
//
// Command sequence (per run; one round = one batch of NUM_RUNS runs):
//   - FETCH + DISPATCH for weights (1 or more blocks)
//   - FETCH + DISPATCH for activations
//   - MATMUL + READOUT + WAIT_MATMUL
// Total: NUM_ROUNDS rounds, each round has NUM_RUNS runs in one batch.

#include <iostream>
#include <iomanip>
#include <fstream>
#include <sstream>
#include <string>
#include <cstring>
#include <cstdlib>
#include <chrono>
#include <cmath>
#include <vector>
#include <array>
#include <unistd.h>
#include "vp815_gemm_device.hpp"

using namespace std;
using namespace achronix;

// ============================================================================
// Constants
// ============================================================================
constexpr uint32_t BYTES_PER_LINE = 32;
constexpr uint32_t BLOCK_SIZE = LINES_PER_BLOCK * BYTES_PER_LINE;

// Memory layout
constexpr uint32_t LINE_ADDR_LEFT = 0;                    // Activations @ line 0
constexpr uint32_t LINE_ADDR_RIGHT_BASE = 0x400000;       // Weights @ line 0x400000 (byte 0x8000000)

// Configuration selection (compile-time or runtime)
// Config 0: B8_C8_V16 (B=8, C=32 via 4x8, V=256)
// Config 1: B1_C64_V2 (B=1, C=64, V=32)

// #if TEST_CONFIG == 0
// // B8_C8_V16 configuration
// constexpr int TEST_B = 8;
// constexpr int TEST_C_PER_BLOCK = 8;
// constexpr int NUM_WEIGHT_BLOCKS = 4;
// constexpr int TEST_C_TOTAL = TEST_C_PER_BLOCK * NUM_WEIGHT_BLOCKS;  // 32
// constexpr int TEST_V_PER_ROW = 16;
// constexpr int TEST_V_TOTAL = TEST_V_PER_ROW * NUM_ROWS;  // 256
// constexpr const char* HEX_DIR = "../../hex/B8_C8_V16";
// constexpr const char* CONFIG_NAME = "B8_C8_V16";
// #else
// constexpr int TEST_B = 4;
// constexpr int TEST_C_PER_BLOCK = 4;
// constexpr int TEST_V_PER_ROW = 4;
constexpr int TEST_B = 1;
constexpr int TEST_C_PER_BLOCK = 64;
constexpr int TEST_V_PER_ROW = 2;   
// constexpr int TEST_B = 1;
// constexpr int TEST_C_PER_BLOCK = 64;
// constexpr int TEST_V_PER_ROW = 2;
// Built from TEST_B, TEST_C_PER_BLOCK, TEST_V_PER_ROW (not constexpr: to_string is runtime)
const std::string HEX_DIR = "../../hex/B" + std::to_string(TEST_B) + "_C" + std::to_string(TEST_C_PER_BLOCK) + "_V" + std::to_string(TEST_V_PER_ROW);
const std::string CONFIG_NAME = "B" + std::to_string(TEST_B) + "_C" + std::to_string(TEST_C_PER_BLOCK) + "_V" + std::to_string(TEST_V_PER_ROW);

constexpr int NUM_WEIGHT_BLOCKS = 4; 
// assert(NUM_WEIGHT_BLOCKS <= 4);
constexpr int TEST_C_TOTAL = TEST_C_PER_BLOCK * NUM_WEIGHT_BLOCKS;
constexpr int TEST_V_TOTAL = TEST_V_PER_ROW * NUM_ROWS;  // 2
// #endif

// One round = one command batch containing NUM_RUNS runs (each run = one GEMM).
// We run NUM_ROUNDS rounds total. Total GEMM runs = NUM_ROUNDS * NUM_RUNS.
const int NUM_RUNS = 2;   // runs per round (per command batch)
const int NUM_ROUNDS = 100; // number of rounds

// Result BRAM address (from NAP placement)
static uint64_t BRAM_RESULT_BASE = 0;

// ============================================================================
// Helper Functions
// ============================================================================

float fp16ToFloat(uint16_t fp16_val) {
    uint16_t sign = (fp16_val >> 15) & 1;
    uint16_t exp = (fp16_val >> 10) & 0x1F;
    uint16_t frac = fp16_val & 0x3FF;

    if (exp == 0) {
        if (frac == 0) return sign ? -0.0f : 0.0f;
        return (sign ? -1.0f : 1.0f) * (frac / 1024.0f) * powf(2.0f, -14.0f);
    } else if (exp == 31) {
        return (frac == 0) ? (sign ? -INFINITY : INFINITY) : NAN;
    } else {
        return (sign ? -1.0f : 1.0f) * (1.0f + frac / 1024.0f) * powf(2.0f, (int)exp - 15);
    }
}

uint16_t floatToFP16(float val) {
    uint32_t bits;
    memcpy(&bits, &val, sizeof(float));
    uint32_t sign = (bits >> 31) & 0x1;
    uint32_t exp = (bits >> 23) & 0xFF;
    uint32_t mant = bits & 0x7FFFFF;

    if (exp == 0) return (sign << 15);
    if (exp == 0xFF) return (sign << 15) | 0x7C00;

    int32_t new_exp = (int32_t)exp - 127 + 15;
    if (new_exp <= 0) {
        int shift = 1 - new_exp;
        if (shift >= 24) return (sign << 15);
        uint32_t full_mant = (1 << 23) | mant;
        uint32_t new_mant = (full_mant + (1 << (shift + 12))) >> (shift + 13);
        if (new_mant > 0x3FF) return (sign << 15) | (1 << 10);
        return (sign << 15) | (new_mant & 0x3FF);
    }
    if (new_exp >= 31) return (sign << 15) | 0x7C00;

    uint32_t new_mant = (mant + 0x1000) >> 13;
    if (new_mant > 0x3FF) {
        new_exp++;
        new_mant = 0;
        if (new_exp >= 31) return (sign << 15) | 0x7C00;
    }
    return (sign << 15) | (new_exp << 10) | (new_mant & 0x3FF);
}

// Load hex file into byte vector (528 lines x 32 bytes)
bool loadHexFile(const string& filename, vector<uint8_t>& data) {
    ifstream file(filename);
    if (!file.is_open()) {
        cerr << "ERROR: Cannot open hex file: " << filename << endl;
        return false;
    }

    data.clear();
    data.reserve(BLOCK_SIZE);

    string line;
    int line_num = 0;

    while (getline(file, line)) {
        if (line.empty()) continue;

        istringstream iss(line);
        string hex_val;
        int byte_count = 0;

        while (iss >> hex_val) {
            if (byte_count >= 32) {
                cerr << "ERROR: Line " << line_num << " has more than 32 bytes" << endl;
                return false;
            }
            uint8_t val = (uint8_t)strtoul(hex_val.c_str(), NULL, 16);
            data.push_back(val);
            byte_count++;
        }

        if (byte_count != 32) {
            cerr << "ERROR: Line " << line_num << " has " << byte_count << " bytes, expected 32" << endl;
            return false;
        }
        line_num++;
    }

    if (line_num != (int)LINES_PER_BLOCK) {
        cerr << "ERROR: Expected " << LINES_PER_BLOCK << " lines, got " << line_num << endl;
        return false;
    }

    return true;
}

// Load golden FP16 hex file (one hex value per line)
bool loadGoldenHex(const string& filename, vector<uint16_t>& golden) {
    ifstream file(filename);
    if (!file.is_open()) {
        cerr << "ERROR: Cannot open golden file: " << filename << endl;
        return false;
    }

    golden.clear();
    string line;
    while (getline(file, line)) {
        if (line.empty() || line[0] == '#') continue;
        uint16_t val = (uint16_t)strtoul(line.c_str(), NULL, 16);
        golden.push_back(val);
    }
    return true;
}

// ============================================================================
// Main
// ============================================================================
int main(int argc, char* argv[]) {
    cout << "========================================" << endl;
    cout << "2D Multi-Row GEMM Multi-Iteration Test" << endl;
    cout << "========================================" << endl;
    cout << "Configuration: " << CONFIG_NAME << endl;
    cout << "Architecture: " << NUM_ROWS << " rows x " << NUM_COLS << " columns" << endl;
    cout << "Weight blocks: " << NUM_WEIGHT_BLOCKS << endl;

    // Parse command line
    int device_id = 0;
    bool verbose = false;
    string hex_dir = HEX_DIR;  // Use compile-time config default

    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "-d") == 0 && i + 1 < argc) {
            device_id = stoi(argv[++i]);
        } else if (strcmp(argv[i], "-v") == 0) {
            verbose = true;
        } else if (strcmp(argv[i], "-x") == 0 && i + 1 < argc) {
            hex_dir = argv[++i];
        } else if (strcmp(argv[i], "-h") == 0 || strcmp(argv[i], "--help") == 0) {
            cout << "\nUsage: test_gemm_2d_multi_iter [options]\n";
            cout << "Options:\n";
            cout << "  -d N    Use device N (default: 0)\n";
            cout << "  -v      Verbose output\n";
            cout << "  -x DIR  Hex file directory (default: " << HEX_DIR << ")\n";
            cout << "  -h      Show this help\n";
            cout << "\nBuilt for config: " << CONFIG_NAME << endl;
            return 0;
        }
    }

    // Fixed test configuration
    const int B = TEST_B;
    const int C_per_block = TEST_C_PER_BLOCK;
    const int C_total = TEST_C_TOTAL;
    const int V_per_row = TEST_V_PER_ROW;
    const int V_TOTAL = TEST_V_TOTAL;
    const int expected_results = B * C_total;

    cout << "\nTest Configuration: " << CONFIG_NAME << endl;
    cout << "  B = " << B << " (batches)" << endl;
    cout << "  C = " << C_total << " (" << NUM_WEIGHT_BLOCKS << " blocks x " << C_per_block << " columns)" << endl;
    cout << "  V = " << V_TOTAL << " (" << V_per_row << " per row x " << NUM_ROWS << " rows)" << endl;
    cout << "  Expected results: " << expected_results << " FP16 values" << endl;
    cout << "  Hex directory: " << hex_dir << endl;

    try {
        // Initialize device
        cout << "\nInitializing VP815 device " << device_id << "..." << endl;
        VP815 device(device_id);
        VP815GemmDevice gemm_device(device);

        // Read bitstream ID
        uint32_t bitstream_id = gemm_device.mmio_read32(0, 0x214);
        cout << "Bitstream ID: 0x" << hex << bitstream_id << dec
             << " (Build: " << ((bitstream_id >> 24) & 0xFF) << "/"
             << ((bitstream_id >> 16) & 0xFF) << " "
             << ((bitstream_id >> 8) & 0xFF) << ":"
             << (bitstream_id & 0xFF) << ")" << endl;

        // Set result BRAM base address
        BRAM_RESULT_BASE = acx_util_nap_absolute_addr(ACX_PART_AC7t1500,
                                                       DATA_OUT_BRAM_NAP_COL, DATA_OUT_BRAM_NAP_ROW);
        cout << "Result BRAM: NAP[" << DATA_OUT_BRAM_NAP_COL << "][" << DATA_OUT_BRAM_NAP_ROW
             << "] = 0x" << hex << BRAM_RESULT_BASE << dec << endl;

        // =====================================================================
        // PHASE 1: DMA data to GDDR6
        //   - Left (activations) @ line 0
        //   - Right (weights) @ lines 0x8000000, +528, +1056, +1584
        // =====================================================================
        cout << "\n========================================" << endl;
        cout << "PHASE 1: DMA data to GDDR6" << endl;
        cout << "========================================" << endl;
        cout << "Memory layout (line addresses):" << endl;
        cout << "  Left (activations): line 0" << endl;
        for (int blk = 0; blk < NUM_WEIGHT_BLOCKS; blk++) {
            cout << "  Right block " << blk << ":     line 0x" << hex 
                 << (LINE_ADDR_RIGHT_BASE + blk * LINES_PER_BLOCK) << dec << endl;
        }

        auto dma_start = chrono::high_resolution_clock::now();

        // Load hex files and DMA to GDDR6 for all 16 rows
        for (int r = 0; r < NUM_ROWS; r++) {
            stringstream left_path;
            left_path << hex_dir << "/left_" << r << ".hex";

            vector<uint8_t> left_data;

            // Load left (activations)
            if (!loadHexFile(left_path.str(), left_data)) {
                cerr << "ERROR: Failed to load left_" << r << ".hex" << endl;
                return 1;
            }

            // DMA left to line 0
            uint64_t left_byte_offset = static_cast<uint64_t>(LINE_ADDR_LEFT) * BYTES_PER_LINE;
            uint64_t left_addr = gddr6_dma_addr(r, left_byte_offset);
            if (!gemm_device.dma_write(left_addr, left_data.data(), left_data.size())) {
                cerr << "ERROR: DMA write failed for left, row " << r << endl;
                return 1;
            }

            // Load and DMA 4 different right (weight) blocks per row
            for (int blk = 0; blk < NUM_WEIGHT_BLOCKS; blk++) {
                stringstream right_path;
                right_path << hex_dir << "/right_" << r << "_" << blk << ".hex";

                vector<uint8_t> right_data;
                if (!loadHexFile(right_path.str(), right_data)) {
                    cerr << "ERROR: Failed to load right_" << r << "_" << blk << ".hex" << endl;
                    return 1;
                }

                uint32_t line_addr = LINE_ADDR_RIGHT_BASE + blk * LINES_PER_BLOCK;
                // Cast to uint64_t to prevent overflow in byte offset calculation
                uint64_t byte_offset = static_cast<uint64_t>(line_addr) * BYTES_PER_LINE;
                uint64_t right_addr = gddr6_dma_addr(r, byte_offset);
                if (!gemm_device.dma_write(right_addr, right_data.data(), right_data.size())) {
                    cerr << "ERROR: DMA write failed for right block " << blk << ", row " << r << endl;
                    return 1;
                }

                if (verbose && r == 0) {
                    cout << "  Row 0: right[" << blk << "] @ 0x" << hex << right_addr
                         << " (line 0x" << line_addr << ") from right_0_" << blk << ".hex" << dec << endl;
                }
            }

            if (verbose && r == 0) {
                cout << "  Row 0: left @ 0x" << hex << left_addr
                     << " (line " << LINE_ADDR_LEFT << ")" << dec << endl;
            }
        }

        auto dma_end = chrono::high_resolution_clock::now();
        double dma_ms = chrono::duration<double, milli>(dma_end - dma_start).count();
        cout << "DMA complete: " << fixed << setprecision(2) << dma_ms << " ms" << endl;

        // =====================================================================
        // PHASE 2: Initial soft reset and pointer reset
        // =====================================================================
        cout << "\n========================================" << endl;
        cout << "PHASE 2: Initial soft reset" << endl;
        cout << "========================================" << endl;

        gemm_device.soft_reset();
        // gemm_device.reset_cmd_id();
        usleep(100000);  // 100ms settle
        
        // Reset both rd_ptr and wr_ptr to 0
        gemm_device.mmio_write32(0, 0x230, 0);  // Reset rd_ptr to 0
        // Note: wr_ptr (0x234) is read-only from hardware, can't write it directly
        
        uint32_t initial_rd_ptr = gemm_device.mmio_read32(0, 0x230);
        uint32_t initial_wr_ptr = gemm_device.mmio_read32(0, 0x234);
        cout << "Soft reset complete" << endl;
        cout << "Initial pointers: rd_ptr=" << initial_rd_ptr << ", wr_ptr=" << initial_wr_ptr << endl;

        // Calculate tile_addr offsets for weight accumulation
        const int NV_LINES = 4;  // 4 mantissa lines per NV
        const int vecs_per_col_per_dispatch = C_per_block / NUM_COLS;  // 8/4 = 2
        const int tile_addr_increment = vecs_per_col_per_dispatch * V_per_row * NV_LINES;  // 2*16*4 = 128

        const int results_per_round = expected_results * NUM_RUNS;
        const int TOTAL_RESULTS = results_per_round * NUM_ROUNDS;
        const int TOTAL_LINES = (TOTAL_RESULTS + 15) / 16;  // Round up to full lines
        const int lines_per_run = (expected_results + 15) / 16;
        const int lines_per_round = lines_per_run * NUM_RUNS;
        const int bytes_per_round = lines_per_round * 32;
        const int expected_cmds_per_run = (NUM_WEIGHT_BLOCKS + 2) * 3;  // weight dispatches + activation + matmul
        const int expected_cmds_per_round = expected_cmds_per_run * NUM_RUNS;

        // =====================================================================
        // PHASE 3/4/5: For each round: build one batch (NUM_RUNS runs), submit, wait, read results
        // =====================================================================
        cout << "\n========================================" << endl;
        cout << "PHASE 3-5: " << NUM_ROUNDS << " rounds, " << NUM_RUNS << " runs per round" << endl;
        cout << "========================================" << endl;

        vector<uint8_t> all_result_data(static_cast<size_t>(TOTAL_LINES) * 32);
        double total_cmd_ms = 0.0;

        // Track rd_ptr for reading (software manages this)
        uint32_t current_rd_ptr = 0;

        for (int round = 1; round <= NUM_ROUNDS; round++) {
            cout << "\n--- Round " << round << " of " << NUM_ROUNDS << " (" << NUM_RUNS << " runs in batch) ---" << endl;
            // Option B: No soft_reset - software tracks rd_ptr, hardware tracks wr_ptr
            // RTL handles cmd_id wrap-around with signed comparison

            // Build one command batch with NUM_RUNS runs
            gemm_device.begin_command_batch();
            for (int run = 1; run <= NUM_RUNS; run++) {
                if (verbose) {
                    cout << "  Building run " << run << " of " << NUM_RUNS << "..." << endl;
                }

                // Weight dispatches (NUM_WEIGHT_BLOCKS iterations)
                for (int blk = 0; blk < NUM_WEIGHT_BLOCKS; blk++) {
                    uint32_t fetch_addr = LINE_ADDR_RIGHT_BASE + blk * LINES_PER_BLOCK;
                    uint16_t tile_addr = blk * tile_addr_increment;

                    if (verbose) {
                        cout << "    FETCH(right):  addr=0x" << hex << fetch_addr << dec
                            << ", ugd_len=" << V_TOTAL << ", lines=" << LINES_PER_BLOCK
                            << ", is_right=1" << endl;
                    }
                    gemm_device.fetch(fetch_addr, V_TOTAL, LINES_PER_BLOCK, true);

                    if (verbose) {
                        cout << "    DISPATCH(right): nv_cnt=" << C_per_block
                            << ", ugd_len=" << V_TOTAL << ", tile_addr=" << tile_addr
                            << ", col_start=0, is_right=1, acc=0" << endl;
                    }
                    uint8_t disp_id = gemm_device.dispatch(C_per_block, V_TOTAL, tile_addr, 0, true, false);

                    if (verbose) {
                        cout << "    WAIT_DISPATCH: id=" << (int)disp_id << endl;
                    }
                    gemm_device.waitDispatch(disp_id);
                }

                // Activation dispatch
                if (verbose) {
                    cout << "    FETCH(left):   addr=0x" << hex << LINE_ADDR_LEFT << dec
                        << ", ugd_len=" << V_TOTAL << ", lines=" << LINES_PER_BLOCK
                        << ", is_right=0" << endl;
                }
                gemm_device.fetch(LINE_ADDR_LEFT, V_TOTAL, LINES_PER_BLOCK, false);

                if (verbose) {
                    cout << "    DISPATCH(left):  nv_cnt=" << B
                        << ", ugd_len=" << V_TOTAL << ", tile_addr=0" << endl;
                }
                uint8_t disp_left_id = gemm_device.dispatch(B, V_TOTAL, 0, 0, false, false);

                if (verbose) {
                    cout << "    WAIT_DISPATCH: id=" << (int)disp_left_id << endl;
                }
                gemm_device.waitDispatch(disp_left_id);

                // MATMUL + READOUT + WAIT
                if (verbose) {
                    cout << "    MATMUL:        row_start=0, col_start=0, B=" << B
                        << ", C=" << C_total << ", V=" << V_TOTAL << endl;
                }
                uint8_t matmul_id = gemm_device.matmul(0, 0, B, C_total, V_TOTAL, false, false, false);

                if (verbose) {
                    cout << "    READOUT:       B=" << B << ", C=" << C_total
                        << ", V=" << V_TOTAL << endl;
                }
                (void)gemm_device.readout(B, C_total, V_TOTAL);

                if (verbose) {
                    cout << "    WAIT_MATMUL:   id=" << (int)matmul_id << endl;
                }
                gemm_device.waitMatmul(matmul_id);
            }

            int total_commands = gemm_device.get_command_count();
            if (round == 1) {
                cout << "Commands this round: " << total_commands << " (expected " << expected_cmds_per_round << ")" << endl;
            }

            // Submit this round's batch
            auto cmd_start = chrono::high_resolution_clock::now();

            if (!gemm_device.submit_commands(verbose, verbose)) {
                cerr << "ERROR: Failed to submit commands (round " << round << ")" << endl;
                return 1;
            }

            // Wait for engine to become idle
            int wait_iter = 0;
            while (wait_iter < 100) {
                uint32_t status = gemm_device.mmio_read32(0, 0x50);
                if ((status & 0x1) == 0) break;
                usleep(100000);
                wait_iter++;
            }

            auto cmd_end = chrono::high_resolution_clock::now();
            double cmd_ms = chrono::duration<double, milli>(cmd_end - cmd_start).count();
            total_cmd_ms += cmd_ms;

            if (wait_iter >= 10) {
                cerr << "ERROR: Timeout waiting for engine (round " << round << ")" << endl;
                uint32_t status = gemm_device.mmio_read32(0, 0x50);
                cout << "Engine Status (0x50):  0x" << hex << setw(8) << setfill('0')
                    << status << dec << endl;
                uint32_t debug = gemm_device.mmio_read32(0, 0x58);
                cout << "Engine Debug (0x58):   0x" << hex << setw(8) << setfill('0')
                    << debug << dec << endl;

                // Decode ENGINE_DEBUG fields
                bool bridge_busy       = (debug >> 27) & 0x1;
                bool dc_fifo_afull     = (debug >> 26) & 0x1;
                bool ce_fifo_afull     = (debug >> 25) & 0x1;
                bool rc_fifo_afull     = (debug >> 24) & 0x1;
                bool ce_read_empty     = (debug >> 21) & 0x1;
                bool ce_results_rdy    = (debug >> 20) & 0x1;
                uint32_t mc_state      = (debug >> 16) & 0xF;
                uint32_t fifo_count    = debug & 0x1FFF;

                cout << "  Decoded:" << endl;
                cout << "    Bridge busy:         " << (bridge_busy ? "YES" : "no") << endl;
                cout << "    DC FIFO almost-full: " << (dc_fifo_afull ? "YES" : "no") << endl;
                cout << "    CE FIFO almost-full: " << (ce_fifo_afull ? "YES" : "no") << endl;
                cout << "    RC FIFO almost-full: " << (rc_fifo_afull ? "YES" : "no") << endl;
                cout << "    CE read-empty sticky:" << (ce_read_empty ? "YES" : "no") << endl;
                cout << "    CE results ready:    " << (ce_results_rdy ? "YES" : "no") << endl;
                cout << "    MC state:            " << mc_state << endl;
                cout << "    CMD FIFO count:      " << fifo_count << endl;
                return 1;
            }

            cout << "  Round " << round << " complete: " << fixed << setprecision(2) << cmd_ms << " ms" << endl;

            // Read this round's results from current rd_ptr
            // Software manages rd_ptr, hardware manages wr_ptr
            uint64_t read_addr = BRAM_RESULT_BASE + (static_cast<uint64_t>(current_rd_ptr) * 32);
            size_t offset = static_cast<size_t>(round - 1) * bytes_per_round;
            if (!gemm_device.dma_read(read_addr, all_result_data.data() + offset, bytes_per_round)) {
                cerr << "ERROR: Failed to read results (round " << round << ")" << endl;
                return 1;
            }

            // Advance rd_ptr for next read (with wrap-around at 512 lines)
            current_rd_ptr = (current_rd_ptr + lines_per_round) % 512;
            // Update hardware rd_ptr register
            gemm_device.mmio_write32(0, 0x230, current_rd_ptr);

            if (verbose) {
                cout << "    Read from rd_ptr, advanced to " << current_rd_ptr << endl;
            }
        }

        cout << "\nAll " << NUM_ROUNDS << " rounds complete: " << fixed << setprecision(2) << total_cmd_ms << " ms total" << endl;

        // Pointer summary
        uint32_t final_rd_ptr = gemm_device.mmio_read32(0, 0x230);
        uint32_t final_wr_ptr = gemm_device.mmio_read32(0, 0x234);
        uint32_t final_used = gemm_device.mmio_read32(0, 0x238);
        uint32_t final_empty = gemm_device.mmio_read32(0, 0x23C);

        cout << "\n========================================" << endl;
        cout << "POINTER SUMMARY" << endl;
        cout << "========================================" << endl;
        cout << "Initial: rd_ptr=" << initial_rd_ptr << ", wr_ptr=" << initial_wr_ptr << endl;
        cout << "Final:   rd_ptr=" << final_rd_ptr << ", wr_ptr=" << final_wr_ptr << endl;
        cout << "Total wr_ptr delta: " << (final_wr_ptr - initial_wr_ptr) << " lines" << endl;
        cout << "Expected: " << NUM_ROUNDS << " rounds x " << lines_per_round << " lines = " << TOTAL_LINES << " lines" << endl;
        cout << "used_entries: " << final_used << ", empty: " << final_empty << endl;

        // BRAM dump (all rounds)
        cout << "\nBRAM Dump (all " << TOTAL_LINES << " lines):" << endl;
        for (int line = 0; line < TOTAL_LINES; line++) {
            cout << "  Line " << setw(2) << line << ": ";
            for (int i = 0; i < 16; i++) {
                uint16_t val = *(uint16_t*)(all_result_data.data() + line * 32 + i * 2);
                cout << hex << setw(4) << setfill('0') << val << " ";
            }
            cout << dec << setfill(' ') << endl;
            cout << "         FP16: ";
            for (int i = 0; i < 16; i++) {
                uint16_t val = *(uint16_t*)(all_result_data.data() + line * 32 + i * 2);
                cout << fixed << setprecision(1) << setw(7) << fp16ToFloat(val) << " ";
            }
            cout << endl;
        }

            // =====================================================================
            // PHASE 6: Validate all results
            // =====================================================================
            cout << "\n========================================" << endl;
            cout << "PHASE 6: Validate all " << TOTAL_RESULTS << " results" << endl;
            cout << "========================================" << endl;

            // Extract FP16 results from already-read data
            vector<uint16_t> hw_results(TOTAL_RESULTS);
            for (int i = 0; i < TOTAL_RESULTS; i++) {
                hw_results[i] = *(uint16_t*)(all_result_data.data() + i * 2);
            }

            cout << "Extracted " << TOTAL_RESULTS << " results" << endl;

            // Show first 8 of round 1, first 8 of round 2, and last 8
            cout << "\nResults sample:" << endl;
            cout << "Round 1 first 8 (indices 0-7):" << endl;
            for (int i = 0; i < 8; i++) {
                cout << "  [" << i << "] 0x" << hex << setw(4) << setfill('0') << hw_results[i]
                    << " = " << fixed << setprecision(4) << fp16ToFloat(hw_results[i]) << dec << endl;
            }
            int round2_start = results_per_round;  // Round 2 starts at index results_per_round
            cout << "Round 2 first 8 (indices " << round2_start << "-" << (round2_start + 7) << "):" << endl;
            for (int i = round2_start; i < round2_start + 8; i++) {
                cout << "  [" << i << "] 0x" << hex << setw(4) << setfill('0') << hw_results[i]
                    << " = " << fixed << setprecision(4) << fp16ToFloat(hw_results[i]) << dec << endl;
            }
            cout << "Last 8 (indices " << (TOTAL_RESULTS - 8) << "-" << (TOTAL_RESULTS - 1) << "):" << endl;
            for (int i = TOTAL_RESULTS - 8; i < TOTAL_RESULTS; i++) {
                cout << "  [" << i << "] 0x" << hex << setw(4) << setfill('0') << hw_results[i]
                    << " = " << fixed << setprecision(4) << fp16ToFloat(hw_results[i]) << dec << endl;
            }

            // Load golden reference and compute expected result
            cout << "\nLoading golden reference..." << endl;

            // Golden files are named: golden_B{B}_C{C_per_block}_V{V_per_row}_{row}_{block}.hex
            // Each row has NUM_WEIGHT_BLOCKS golden files, each with C_per_block values
            // Sum across all 16 rows, concatenate blocks to form full C_total columns
            vector<float> golden_one_run(expected_results, 0.0f);

            for (int r = 0; r < NUM_ROWS; r++) {
                // Load 4 golden files for this row (one per weight block)
                for (int blk = 0; blk < NUM_WEIGHT_BLOCKS; blk++) {
                    stringstream golden_path;
                    golden_path << hex_dir << "/golden_B" << B << "_C" << C_per_block
                                << "_V" << V_per_row << "_" << r << "_" << blk << ".hex";

                    vector<uint16_t> block_golden;
                    if (!loadGoldenHex(golden_path.str(), block_golden)) {
                        cerr << "WARNING: Could not load golden for row " << r << " block " << blk
                            << " from " << golden_path.str() << ", skipping validation" << endl;

                        // Just report results without golden comparison
                        cout << "\n========================================" << endl;
                        cout << "TEST SUMMARY (No Golden Reference)" << endl;
                        cout << "========================================" << endl;
                        cout << "Configuration: " << CONFIG_NAME << endl;
                        cout << "  B=" << B << ", C=" << C_total << ", V=" << V_TOTAL << endl;
                        cout << "Rounds: " << NUM_ROUNDS << endl;
                        cout << "Results read: " << TOTAL_RESULTS << endl;
                        cout << "Golden files not found - manual verification required" << endl;
                        cout << "========================================" << endl;
                        return 0;
                    }

                    // Sum this block's contribution at the correct column offset
                    // For B=1: block 0 -> columns 0-63, block 1 -> columns 64-127, etc.
                    int col_offset = blk * C_per_block;
                    for (int b = 0; b < B; b++) {
                        for (int c = 0; c < C_per_block && c < (int)block_golden.size(); c++) {
                            int result_idx = b * C_total + col_offset + c;
                            golden_one_run[result_idx] += fp16ToFloat(block_golden[b * C_per_block + c]);
                        }
                    }
                }
            }

            // Build full golden for all runs (NUM_ROUNDS * NUM_RUNS runs total)
            vector<float> golden_full(TOTAL_RESULTS, 0.0f);
            for (int run_idx = 0; run_idx < NUM_ROUNDS * NUM_RUNS; run_idx++) {
                for (int i = 0; i < expected_results; i++) {
                    golden_full[run_idx * expected_results + i] = golden_one_run[i];
                }
            }

            // Validate results
            cout << "\nValidating " << TOTAL_RESULTS << " results against golden..." << endl;
            constexpr int LSB_TOLERANCE = 16;
            constexpr float PCT_TOLERANCE = 0.05f;
            int exact_match = 0;
            int close_match = 0;
            int mismatch = 0;

            for (int i = 0; i < TOTAL_RESULTS; i++) {
                uint16_t hw_val = hw_results[i];
                uint16_t gd_val = floatToFP16(golden_full[i]);
                uint16_t lsb_diff = (hw_val > gd_val) ? (hw_val - gd_val) : (gd_val - hw_val);

                float hw_f = fp16ToFloat(hw_val);
                float gd_f = golden_full[i];
                float pct_diff = (fabs(gd_f) > 0.001f) ? fabs((hw_f - gd_f) / gd_f) : fabs(hw_f - gd_f);

                if (hw_val == gd_val) {
                    exact_match++;
                } else if (lsb_diff <= LSB_TOLERANCE || pct_diff <= PCT_TOLERANCE) {
                    close_match++;
                } else {
                    mismatch++;
                    if (mismatch <= 10) {
                        int run_idx = i / expected_results;
                        int round_num = run_idx / NUM_RUNS + 1;
                        int run_num = run_idx % NUM_RUNS + 1;
                        int idx_in_run = i % expected_results;
                        cout << "  MISMATCH [" << i << "] (round " << round_num << " run " << run_num << " idx " << idx_in_run << "): hw=0x" << hex << hw_val
                            << " (" << fixed << setprecision(4) << hw_f << ")"
                            << ", golden=0x" << gd_val
                            << " (" << golden_full[i] << ")" << dec << endl;
                    }
                }
            }

            float match_rate = 100.0f * (exact_match + close_match) / TOTAL_RESULTS;

            // =====================================================================
            // Summary
            // =====================================================================
            cout << "\n========================================" << endl;
            cout << "TEST SUMMARY" << endl;
            cout << "========================================" << endl;
            cout << "Configuration: B=" << B << ", C=" << C_total << ", V=" << V_TOTAL << endl;
            cout << "Weight blocks: " << NUM_WEIGHT_BLOCKS << " (different data per block)" << endl;
            cout << "Total rounds: " << NUM_ROUNDS << endl;
            cout << "Runs per round: " << NUM_RUNS << endl;
            cout << "Total runs: " << (NUM_ROUNDS * NUM_RUNS) << endl;
            cout << "Commands per round: " << expected_cmds_per_round << endl;
            cout << "Results per run: " << expected_results << endl;
            cout << "Total results: " << TOTAL_RESULTS << endl;
            uint32_t ce_fifo_full = gemm_device.mmio_read32(0, 0x54);
            cout << "CE FIFO Full (0x54): 0x" << std::hex << std::setw(8) << std::setfill('0')
                << ce_fifo_full << std::dec << std::endl;

            // ENGINE_DEBUG (0x58) bit layout from RTL:
            //   [27]    cmd_bram_bridge_busy - Bridge busy
            //   [26]    dbg_dc_fifo_afull    - Dispatcher FIFO almost-full
            //   [25]    dbg_ce_fifo_afull    - CE result FIFO almost-full
            //   [24]    dbg_rc_fifo_afull    - RC output FIFO almost-full
            //   [23:22] Reserved (2'b0)
            //   [21]    dbg_ce_read_empty_sticky - CE read-while-empty sticky (OR'd all rows/cols)
            //   [20]    ce_results_ready     - Any CE has results ready for draining
            //   [19:16] mc_state_2d          - MC state (4 bits)
            //   [15:13] Reserved (3'b0)
            //   [12:0]  cmd_fifo_count       - Command FIFO count
            uint32_t engine_debug = gemm_device.mmio_read32(0, 0x58);
            cout << "ENGINE DEBUG (0x58): 0x" << std::hex << std::setw(8) << std::setfill('0')
                << engine_debug << std::dec << std::endl;

            // Decode ENGINE_DEBUG fields
            bool bridge_busy       = (engine_debug >> 27) & 0x1;
            bool dc_fifo_afull     = (engine_debug >> 26) & 0x1;
            bool ce_fifo_afull     = (engine_debug >> 25) & 0x1;
            bool rc_fifo_afull     = (engine_debug >> 24) & 0x1;
            bool ce_read_empty     = (engine_debug >> 21) & 0x1;
            bool ce_results_rdy    = (engine_debug >> 20) & 0x1;
            uint32_t mc_state      = (engine_debug >> 16) & 0xF;
            uint32_t fifo_count    = engine_debug & 0x1FFF;

            cout << "  Decoded:" << endl;
            cout << "    Bridge busy:         " << (bridge_busy ? "YES" : "no") << endl;
            cout << "    DC FIFO almost-full: " << (dc_fifo_afull ? "YES" : "no") << endl;
            cout << "    CE FIFO almost-full: " << (ce_fifo_afull ? "YES" : "no") << endl;
            cout << "    RC FIFO almost-full: " << (rc_fifo_afull ? "YES" : "no") << endl;
            cout << "    CE read-empty sticky:" << (ce_read_empty ? "YES" : "no") << endl;
            cout << "    CE results ready:    " << (ce_results_rdy ? "YES" : "no") << endl;
            cout << "    MC state:            " << mc_state << endl;
            cout << "    CMD FIFO count:      " << fifo_count << endl;
                
            cout << "\nValidation:" << endl;
            cout << "  Exact match: " << exact_match << endl;
            cout << "  Close match: " << close_match << " (<= " << LSB_TOLERANCE << " LSB or " 
                << (int)(PCT_TOLERANCE * 100) << "%)" << endl;
            cout << "  Mismatch:    " << mismatch << endl;
            cout << "  Match rate:  " << fixed << setprecision(1) << match_rate << "%" << endl;

            bool passed = (match_rate >= 95.0f);

            if (passed) {
                cout << "\nSTATUS: [PASS]" << endl;
            } else {
                cout << "\nSTATUS: [FAIL]" << endl;
            }
            cout << "========================================" << endl;
            
        return passed ? 0 : 1;

    } catch (const exception& e) {
        cerr << "ERROR: " << e.what() << endl;
        return 1;
    }
}
