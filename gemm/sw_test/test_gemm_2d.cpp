// 2D Multi-Row GEMM Engine Test
//
// Tests the 2D GEMM architecture with:
// - 16 parallel rows (each with its own GDDR6 channel)
// - V dimension partitioned across rows by Master Control
// - Result reduction across all rows via result_collector_2d
//
// Test data format:
// - Per-row hex files: left_{r}.hex, right_{r}.hex (r = 0..15)
// - Per-row golden: golden_B{B}_C{C}_V{V}_{r}.hex
// - Final result = sum of all row partials
//
// Command sequence (from tb_gemm2d.sv):
// 1. FETCH RIGHT + WAIT_DISP
// 2. DISPATCH RIGHT + WAIT_DISP
// 3. FETCH LEFT + WAIT_DISP
// 4. DISPATCH LEFT + WAIT_DISP
// 5. MATMUL + READOUT + WAIT_MATMUL
// 6. Read B*C reduced FP16 results

#include <iostream>
#include <iomanip>
#include <fstream>
#include <sstream>
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
// GDDR6 Channel Configuration (from engine_top_2d.sv GDDR6_CTRL_ID)
// ============================================================================
// 16 rows mapped to 16 GDDR6 page IDs (controller channels)
// West controllers (0-3): Ch0=lower ID, Ch1=higher ID
// East controllers (4-7): Ch0=higher ID, Ch1=lower ID (reversed)
constexpr uint16_t GDDR6_CTRL_ID[16] = {
    0x00C, 0x00D,   // Controller 0: Ch0, Ch1 (West)
    0x004, 0x005,   // Controller 1: Ch0, Ch1 (West)
    0x000, 0x001,   // Controller 2: Ch0, Ch1 (West)
    0x008, 0x009,   // Controller 3: Ch0, Ch1 (West)
    0x00F, 0x00E,   // Controller 4: Ch0, Ch1 (East, reversed)
    0x007, 0x006,   // Controller 5: Ch0, Ch1 (East, reversed)
    0x003, 0x002,   // Controller 6: Ch0, Ch1 (East, reversed)
    0x00B, 0x00A    // Controller 7: Ch0, Ch1 (East, reversed)
};

// Calculate DMA base address for a given row/channel
// Format: (page_id << 33) | offset
inline uint64_t gddr6_dma_addr(int row, uint64_t offset = 0) {
    return (static_cast<uint64_t>(GDDR6_CTRL_ID[row] & 0x1FF) << 33) | offset;
}

// ============================================================================
// Constants (use those from vp815_gemm_device.hpp where possible)
// ============================================================================
// NUM_ROWS, NUM_COLS, LINES_PER_BLOCK are defined in vp815_gemm_device.hpp
constexpr uint32_t BYTES_PER_LINE = 32;
constexpr uint32_t BLOCK_SIZE = LINES_PER_BLOCK * BYTES_PER_LINE;

// Line addresses for left/right blocks in each row's GDDR6
constexpr uint32_t LINE_ADDR_LEFT = 0;          // Lines 0-527
constexpr uint32_t LINE_ADDR_RIGHT = 528;       // Lines 528-1055

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
// Test Configuration
// ============================================================================
struct TestConfig {
    int B;              // Batch dimension
    int C;              // Column dimension
    int V;              // V per row (total V = V * 16)
    string hex_dir;     // Directory containing hex files
    string name;        // Test name
};

// ============================================================================
// Run 2D GEMM Test
// ============================================================================
bool run_2d_gemm_test(VP815GemmDevice& gemm_device, const TestConfig& config, bool verbose) {
    const int B = config.B;
    const int C = config.C;
    const int V_per_row = config.V;
    const int V_TOTAL = V_per_row * NUM_ROWS;
    const int expected_results = B * C;

    cout << "\n========================================" << endl;
    cout << "2D GEMM Test: " << config.name << endl;
    cout << "B=" << B << ", C=" << C << ", V/row=" << V_per_row << ", V_TOTAL=" << V_TOTAL << endl;
    cout << "Expected results: " << expected_results << " FP16 values" << endl;
    cout << "========================================" << endl;

    auto test_start = chrono::high_resolution_clock::now();

    // =========================================================================
    // Step 1: Load per-row hex files
    // =========================================================================
    cout << "\n[1/6] Loading per-row hex files..." << endl;

    array<vector<uint8_t>, NUM_ROWS> left_data;
    array<vector<uint8_t>, NUM_ROWS> right_data;

    for (int r = 0; r < NUM_ROWS; r++) {
        stringstream left_path, right_path;
        left_path << config.hex_dir << "/left_" << r << ".hex";
        right_path << config.hex_dir << "/right_" << r << ".hex";

        if (!loadHexFile(left_path.str(), left_data[r])) {
            cerr << "ERROR: Failed to load left_" << r << ".hex" << endl;
            return false;
        }
        if (!loadHexFile(right_path.str(), right_data[r])) {
            cerr << "ERROR: Failed to load right_" << r << ".hex" << endl;
            return false;
        }
    }
    cout << "  Loaded " << NUM_ROWS << " pairs of hex files (" << BLOCK_SIZE << " bytes each)" << endl;

    // =========================================================================
    // Step 2: DMA write to all 16 GDDR6 channels
    // =========================================================================
    cout << "\n[2/6] DMA write to 16 GDDR6 channels..." << endl;

    auto dma_start = chrono::high_resolution_clock::now();

    for (int r = 0; r < NUM_ROWS; r++) {
        // Left block at offset 0 (lines 0-527)
        uint64_t left_addr = gddr6_dma_addr(r, 0);
        if (!gemm_device.dma_write(left_addr, left_data[r].data(), left_data[r].size())) {
            cerr << "ERROR: DMA write failed for row " << r << " left" << endl;
            return false;
        }

        // Right block at offset 528*32 bytes (lines 528-1055)
        uint64_t right_addr = gddr6_dma_addr(r, LINE_ADDR_RIGHT * BYTES_PER_LINE);
        if (!gemm_device.dma_write(right_addr, right_data[r].data(), right_data[r].size())) {
            cerr << "ERROR: DMA write failed for row " << r << " right" << endl;
            return false;
        }

        if (verbose) {
            cout << "  Row " << setw(2) << r << ": left @ 0x" << hex << left_addr
                 << ", right @ 0x" << right_addr << dec << endl;
        }
    }

    auto dma_end = chrono::high_resolution_clock::now();
    double dma_ms = chrono::duration<double, milli>(dma_end - dma_start).count();
    cout << "  DMA complete: " << fixed << setprecision(2) << dma_ms << " ms" << endl;

    // =========================================================================
    // Step 3: Soft reset and initialize engine
    // =========================================================================
    cout << "\n[3/6] Initializing engine..." << endl;

    gemm_device.soft_reset();
    gemm_device.reset_cmd_id();

    // =========================================================================
    // Step 4: Issue 2D GEMM command sequence via DMA-BRAM interface
    // =========================================================================
    cout << "\n[4/6] Issuing 2D GEMM command sequence (DMA-BRAM batch)..." << endl;

    auto cmd_start = chrono::high_resolution_clock::now();

    // Start new command batch
    gemm_device.begin_command_batch();

    // --- FETCH RIGHT (weights) ---
    // Line address 528, full block, ugd_len=V_TOTAL
    uint8_t fetch_right_id = gemm_device.fetch(LINE_ADDR_RIGHT, V_TOTAL, LINES_PER_BLOCK, true);
    if (verbose) cout << "  FETCH RIGHT: id=" << (int)fetch_right_id << ", line=" << LINE_ADDR_RIGHT << endl;

    // WAIT for FETCH to complete
    uint8_t wait_fetch_right_id = gemm_device.waitDispatch(fetch_right_id);
    if (verbose) cout << "  WAIT_DISP: id=" << (int)wait_fetch_right_id << ", wait_for=" << (int)fetch_right_id << endl;

    // --- DISPATCH RIGHT (weights -> mlp_bram) ---
    // nv_cnt=C (number of columns), ugd_len=V_TOTAL
    uint8_t disp_right_id = gemm_device.dispatch(C, V_TOTAL, 0, 0, true, false);
    if (verbose) cout << "  DISPATCH RIGHT: id=" << (int)disp_right_id << ", nv_cnt=" << C << endl;

    // WAIT for DISPATCH to complete
    uint8_t wait_disp_right_id = gemm_device.waitDispatch(disp_right_id);
    if (verbose) cout << "  WAIT_DISP: id=" << (int)wait_disp_right_id << ", wait_for=" << (int)disp_right_id << endl;

    // --- FETCH LEFT (activations) ---
    // Line address 0, full block, ugd_len=V_TOTAL
    uint8_t fetch_left_id = gemm_device.fetch(LINE_ADDR_LEFT, V_TOTAL, LINES_PER_BLOCK, false);
    if (verbose) cout << "  FETCH LEFT: id=" << (int)fetch_left_id << ", line=" << LINE_ADDR_LEFT << endl;

    // WAIT for FETCH to complete
    uint8_t wait_fetch_left_id = gemm_device.waitDispatch(fetch_left_id);
    if (verbose) cout << "  WAIT_DISP: id=" << (int)wait_fetch_left_id << ", wait_for=" << (int)fetch_left_id << endl;

    // --- DISPATCH LEFT (activations -> row_bram) ---
    // nv_cnt=B (number of batches), ugd_len=V_TOTAL
    uint8_t disp_left_id = gemm_device.dispatch(B, V_TOTAL, 0, 0, false, false);
    if (verbose) cout << "  DISPATCH LEFT: id=" << (int)disp_left_id << ", nv_cnt=" << B << endl;

    // WAIT for DISPATCH to complete
    uint8_t wait_disp_left_id = gemm_device.waitDispatch(disp_left_id);
    if (verbose) cout << "  WAIT_DISP: id=" << (int)wait_disp_left_id << ", wait_for=" << (int)disp_left_id << endl;

    // --- MATMUL ---
    // left_addr=0, right_addr=0, B, C, V_TOTAL
    uint8_t matmul_id = gemm_device.matmul(0, 0, B, C, V_TOTAL, false, false, false);
    if (verbose) cout << "  MATMUL: id=" << (int)matmul_id << ", B=" << B << ", C=" << C << ", V=" << V_TOTAL << endl;

    // --- READOUT ---
    // Issue readout to trigger result collection
    uint8_t readout_id = gemm_device.readout(B, C, V_TOTAL);
    if (verbose) cout << "  READOUT: id=" << (int)readout_id << endl;

    // --- WAIT for MATMUL to complete ---
    uint8_t wait_matmul_id = gemm_device.waitMatmul(matmul_id);
    if (verbose) cout << "  WAIT_MATMUL: id=" << (int)wait_matmul_id << ", wait_for=" << (int)matmul_id << endl;

    // Submit all commands to hardware via DMA-BRAM interface
    cout << "  Submitting " << gemm_device.get_command_count() << " commands to FPGA..." << endl;
    if (!gemm_device.submit_commands(verbose)) {
        cerr << "ERROR: Failed to submit command batch" << endl;
        return false;
    }

    // Wait for engine to become idle with extended timeout and debug
    cout << "  Waiting for engine..." << endl;
    auto wait_start = chrono::high_resolution_clock::now();
    int wait_iter = 0;
    while (wait_iter < 50) {  // 50 * 100ms = 5 seconds total
        uint32_t status = gemm_device.mmio_read32(0, 0x50);
        if ((status & 0x1) == 0) {
            break;  // Engine idle
        }
        
        if (verbose && (wait_iter % 10 == 0)) {
            uint32_t mc = (status >> 8) & 0xF;
            uint32_t rc = (status >> 4) & 0xF;
            cout << "  Status: 0x" << hex << status << dec 
                 << " (MC=" << mc << ", RC=" << rc << ", busy=" << (status & 1) << ")" << endl;
        }
        
        usleep(100000);  // 100ms
        wait_iter++;
    }

    if (wait_iter >= 50) {
        uint32_t status = gemm_device.mmio_read32(0, 0x50);
        cerr << "ERROR: Engine timeout after 5s, STATUS=0x" << hex << status << dec << endl;
        return false;
    }

    auto cmd_end = chrono::high_resolution_clock::now();
    double cmd_ms = chrono::duration<double, milli>(cmd_end - cmd_start).count();
    cout << "  Commands complete: " << fixed << setprecision(2) << cmd_ms << " ms" << endl;

    // =========================================================================
    // Step 5: Read results from BRAM
    // =========================================================================
    cout << "\n[5/6] Reading results from BRAM..." << endl;

    // Results are packed 16 FP16 per 256-bit line
    // Total lines needed = ceil(expected_results / 16)
    int lines_to_read = (expected_results + 15) / 16;
    int bytes_to_read = lines_to_read * 32;

    vector<uint8_t> result_data(bytes_to_read);
    if (!gemm_device.dma_read(BRAM_RESULT_BASE, result_data.data(), bytes_to_read)) {
        cerr << "ERROR: Failed to read results from BRAM" << endl;
        return false;
    }

    // Extract FP16 results
    vector<uint16_t> hw_results(expected_results);
    for (int i = 0; i < expected_results; i++) {
        hw_results[i] = *(uint16_t*)(result_data.data() + i * 2);
    }

    if (verbose) {
        cout << "  First 4 results: ";
        for (int i = 0; i < min(4, expected_results); i++) {
            cout << "0x" << hex << setw(4) << setfill('0') << hw_results[i] << " ";
        }
        cout << dec << endl;
    }

    // =========================================================================
    // Step 6: Load golden and validate
    // =========================================================================
    cout << "\n[6/6] Validating against golden reference..." << endl;

    // Load per-row golden files and compute expected sum
    vector<float> golden_sum(expected_results, 0.0f);

    for (int r = 0; r < NUM_ROWS; r++) {
        stringstream golden_path;
        golden_path << config.hex_dir << "/golden_B" << B << "_C" << C << "_V" << V_per_row << "_" << r << ".hex";

        vector<uint16_t> row_golden;
        if (!loadGoldenHex(golden_path.str(), row_golden)) {
            cerr << "ERROR: Failed to load golden for row " << r << endl;
            return false;
        }

        if ((int)row_golden.size() != expected_results) {
            cerr << "ERROR: Row " << r << " golden has " << row_golden.size()
                 << " values, expected " << expected_results << endl;
            return false;
        }

        // Sum partial results
        for (int i = 0; i < expected_results; i++) {
            golden_sum[i] += fp16ToFloat(row_golden[i]);
        }
    }

    // Convert golden sum back to FP16 for comparison
    vector<uint16_t> golden_fp16(expected_results);
    for (int i = 0; i < expected_results; i++) {
        golden_fp16[i] = floatToFP16(golden_sum[i]);
    }

    // Compare results
    int exact_matches = 0;
    int close_matches = 0;
    int mismatches = 0;

    for (int i = 0; i < expected_results; i++) {
        uint16_t diff = (hw_results[i] > golden_fp16[i])
                            ? (hw_results[i] - golden_fp16[i])
                            : (golden_fp16[i] - hw_results[i]);

        if (hw_results[i] == golden_fp16[i]) {
            exact_matches++;
        } else if (diff <= 4) {
            close_matches++;
        } else {
            mismatches++;
            if (verbose && mismatches <= 10) {
                float hw_f = fp16ToFloat(hw_results[i]);
                float golden_f = golden_sum[i];
                cout << "  MISMATCH [" << i << "]: hw=0x" << hex << hw_results[i]
                     << " (" << fixed << setprecision(4) << hw_f << ")"
                     << ", golden=0x" << golden_fp16[i]
                     << " (" << golden_f << ")"
                     << ", diff=" << dec << diff << " LSB" << endl;
            }
        }
    }

    auto test_end = chrono::high_resolution_clock::now();
    double total_ms = chrono::duration<double, milli>(test_end - test_start).count();

    // Report results
    double match_rate = (double)(exact_matches + close_matches) / expected_results * 100.0;
    cout << "\n  Results: " << exact_matches << " exact, " << close_matches << " close (<= 4 LSB), "
         << mismatches << " mismatches" << endl;
    cout << "  Match rate: " << fixed << setprecision(1) << match_rate << "%" << endl;
    cout << "  Total time: " << setprecision(2) << total_ms << " ms" << endl;

    // Pass criteria: >= 95% within tolerance
    bool passed = (match_rate >= 95.0);
    cout << "\n  " << (passed ? "[PASS]" : "[FAIL]") << " " << config.name << endl;

    return passed;
}

// ============================================================================
// Main
// ============================================================================
int main(int argc, char* argv[]) {
    cout << "========================================" << endl;
    cout << "2D Multi-Row GEMM Engine Test" << endl;
    cout << "========================================" << endl;
    cout << "Architecture: " << NUM_ROWS << " rows x " << NUM_COLS << " columns" << endl;
    cout << "Each row has its own GDDR6 channel" << endl;

    // Parse command line
    int device_id = 0;
    bool verbose = false;
    string test_name = "";

    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "-d") == 0 && i + 1 < argc) {
            device_id = stoi(argv[++i]);
        } else if (strcmp(argv[i], "-v") == 0) {
            verbose = true;
        } else if (strcmp(argv[i], "-t") == 0 && i + 1 < argc) {
            test_name = argv[++i];
        } else if (strcmp(argv[i], "-h") == 0 || strcmp(argv[i], "--help") == 0) {
            cout << "\nUsage: test_gemm_2d [options]\n";
            cout << "Options:\n";
            cout << "  -d N    Use device N (default: 0)\n";
            cout << "  -v      Verbose output\n";
            cout << "  -t NAME Run specific test (B4_C4_V32 or B4_C13_V9)\n";
            cout << "  -h      Show this help\n";
            return 0;
        }
    }

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
        BRAM_RESULT_BASE = acx_util_nap_absolute_addr(ACX_PART_AC7t1500, 3, 5);
        cout << "Result BRAM: 0x" << hex << BRAM_RESULT_BASE << dec << endl;

        // Define test configurations
        // RTL now supports 16-bit B, C, V parameters per MULTI_ROW_REFERENCE.md
        vector<TestConfig> tests = {
            {4, 13, 9, "../../hex/B4_C13_V9", "B4_C13_V9"},
            {4, 4, 32, "../../hex/B4_C4_V32", "B4_C4_V32"}  // V_TOTAL=512
        };

        // Run tests
        int passed = 0;
        int failed = 0;

        for (const auto& config : tests) {
            // Skip if specific test requested and this isn't it
            if (!test_name.empty() && config.name != test_name) {
                continue;
            }

            gemm_device.soft_reset();

            if (run_2d_gemm_test(gemm_device, config, verbose)) {
                passed++;
            } else {
                failed++;
            }
        }

        // Summary
        cout << "\n========================================" << endl;
        cout << "TEST SUMMARY" << endl;
        cout << "========================================" << endl;
        cout << "Passed: " << passed << endl;
        cout << "Failed: " << failed << endl;
        cout << "========================================" << endl;

        if (failed == 0 && passed > 0) {
            cout << "STATUS: ALL TESTS PASSED" << endl;
        } else if (failed > 0) {
            cout << "STATUS: SOME TESTS FAILED" << endl;
        }

        return (failed == 0) ? 0 : 1;

    } catch (const exception& e) {
        cerr << "ERROR: " << e.what() << endl;
        return 1;
    }
}
