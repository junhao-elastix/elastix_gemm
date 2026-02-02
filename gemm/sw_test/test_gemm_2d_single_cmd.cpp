// 2D Multi-Row GEMM Engine Test - Single Command Mode
//
// Submits commands in three groups (not truly one-at-a-time) to observe
// engine status after each group. Useful for debugging command sequencing.
//
// Group 1: FETCH RIGHT + DISPATCH RIGHT + WAIT_DISP (submit, wait for idle)
// Group 2: FETCH LEFT  + DISPATCH LEFT  + WAIT_DISP (submit, wait for idle)
// Group 3: MATMUL + READOUT + WAIT_MATMUL          (submit, wait for idle)

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
constexpr uint32_t LINE_ADDR_LEFT = 0;
constexpr uint32_t LINE_ADDR_RIGHT = 528;

// Ring buffer register offsets (per RESULT_BUFFER_REFERENCE.md)
constexpr uint32_t REG_RD_PTR        = 0x230;  // Host-controlled read pointer (9-bit line addr)
constexpr uint32_t REG_WR_PTR        = 0x234;  // Hardware write pointer (9-bit line addr)
constexpr uint32_t REG_USED_ENTRIES  = 0x238;  // Valid lines count (10-bit)
constexpr uint32_t REG_RESULT_EMPTY  = 0x23C;  // Buffer empty flag

// Ring buffer constants
constexpr uint32_t BRAM_LINE_DEPTH   = 512;    // 512 lines total
constexpr uint32_t BRAM_LINE_MASK    = 0x1FF;  // 9-bit mask for line pointer wrap
constexpr uint32_t FP16_PER_LINE     = 16;     // 16 FP16 values per 256-bit line
constexpr uint32_t BYTES_PER_BRAM_LINE = 32;   // 256 bits = 32 bytes

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

// Load golden FP16 hex file
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
// Print Engine Status (detailed)
// ============================================================================
void print_engine_status(VP815GemmDevice& dev, const char* label) {
    uint32_t status = dev.mmio_read32(0, 0x50);
    uint32_t result_cnt = dev.mmio_read32(0, 0x54);
    uint32_t cmd_valid = dev.mmio_read32(0, 0x40);
    uint32_t cmd_rd_addr = dev.mmio_read32(0, 0x44);
    
    // Read debug registers for more insight
    uint32_t debug_0x5C = dev.mmio_read32(0, 0x5C);  // Often has additional state info
    uint32_t debug_0x60 = dev.mmio_read32(0, 0x60);  // Row 0 CE debug
    
    uint32_t busy = status & 0x1;
    uint32_t rc_state = (status >> 4) & 0xF;
    uint32_t mc_state = (status >> 8) & 0xF;
    uint32_t dc_state = (status >> 12) & 0xF;
    uint32_t ce_state = (status >> 16) & 0xF;
    
    cout << "  [STATUS after " << label << "]" << endl;
    cout << "    STATUS=0x" << hex << setw(8) << setfill('0') << status << dec << endl;
    cout << "    busy=" << busy 
         << ", MC=" << mc_state 
         << ", DC=" << dc_state 
         << ", CE=" << ce_state 
         << ", RC=" << rc_state << endl;
    cout << "    result_cnt=" << result_cnt 
         << ", cmd_valid=" << cmd_valid 
         << ", cmd_rd_addr=" << cmd_rd_addr << endl;
    cout << "    debug_0x5C=0x" << hex << debug_0x5C 
         << ", debug_0x60=0x" << debug_0x60 << dec << endl;
}

// ============================================================================
// Submit Command Group - with optional wait for completion
// ============================================================================
bool submit_group(VP815GemmDevice& dev, const char* cmd_name, bool wait_for_idle, bool verbose = true) {
    if (verbose) {
        cout << "\n  Submitting: " << cmd_name << (wait_for_idle ? " (will wait)" : " (no wait)") << endl;
    }
    
    if (!dev.submit_commands(verbose, true /* verify */)) {
        cerr << "ERROR: Failed to submit " << cmd_name << endl;
        return false;
    }
    
    if (!wait_for_idle) {
        // Just check status once and continue
        usleep(1000);  // 1ms settle
        if (verbose) {
            print_engine_status(dev, cmd_name);
        }
        return true;
    }
    
    // Wait for engine to become idle (busy=0)
    int wait_count = 0;
    const int MAX_WAIT = 30;  // 30 * 100ms = 3 seconds max
    
    while (wait_count < MAX_WAIT) {
        uint32_t status = dev.mmio_read32(0, 0x50);
        if ((status & 0x1) == 0) {
            // Engine idle - group completed
            if (verbose) {
                cout << "  -> Engine idle after " << wait_count << " polls" << endl;
                print_engine_status(dev, cmd_name);
            }
            return true;
        }
        
        // Print progress every 5 polls to see what's happening
        if (verbose && (wait_count % 5 == 0)) {
            uint32_t mc_state = (status >> 8) & 0xF;
            uint32_t ce_state = (status >> 16) & 0xF;
            uint32_t rc_state = (status >> 4) & 0xF;
            cout << "  [POLL " << wait_count << "] busy=1, MC=" << mc_state 
                 << ", CE=" << ce_state << ", RC=" << rc_state << endl;
        }
        
        usleep(100000);  // 100ms between polls
        wait_count++;
    }
    
    // Timeout - print detailed status
    cerr << "  TIMEOUT: Engine still busy after " << MAX_WAIT << " polls (" << (MAX_WAIT/10) << "s)" << endl;
    print_engine_status(dev, "TIMEOUT");
    return false;  // Return false to indicate failure
}

// Wrapper for backward compatibility
bool submit_and_wait(VP815GemmDevice& dev, const char* cmd_name, bool verbose = true) {
    return submit_group(dev, cmd_name, true /* wait */, verbose);
}

// ============================================================================
// Main Test
// ============================================================================
int main(int argc, char* argv[]) {
    cout << "========================================" << endl;
    cout << "2D GEMM Test - Single Command Mode" << endl;
    cout << "========================================" << endl;

    // Parse command line
    int device_id = 0;
    int B = 8, C = 8, V_per_row = 16;
    string hex_dir = "../../hex/B8_C8_V16";

    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "-d") == 0 && i + 1 < argc) {
            device_id = stoi(argv[++i]);
        } else if (strcmp(argv[i], "-B") == 0 && i + 1 < argc) {
            B = stoi(argv[++i]);
        } else if (strcmp(argv[i], "-C") == 0 && i + 1 < argc) {
            C = stoi(argv[++i]);
        } else if (strcmp(argv[i], "-V") == 0 && i + 1 < argc) {
            V_per_row = stoi(argv[++i]);
        } else if (strcmp(argv[i], "--hex") == 0 && i + 1 < argc) {
            hex_dir = argv[++i];
        } else if (strcmp(argv[i], "-h") == 0 || strcmp(argv[i], "--help") == 0) {
            cout << "\nUsage: test_gemm_2d_single_cmd [options]\n";
            cout << "Options:\n";
            cout << "  -d N      Use device N (default: 0)\n";
            cout << "  -B N      Batch dimension (default: 4)\n";
            cout << "  -C N      Column dimension (default: 13)\n";
            cout << "  -V N      V per row (default: 9)\n";
            cout << "  --hex DIR Hex file directory (default: ../../hex/B4_C13_V9)\n";
            cout << "  -h        Show this help\n";
            return 0;
        }
    }

    const int V_TOTAL = V_per_row * NUM_ROWS;
    const int expected_results = B * C;

    cout << "Configuration: B=" << B << ", C=" << C << ", V/row=" << V_per_row 
         << ", V_TOTAL=" << V_TOTAL << endl;
    cout << "Expected results: " << expected_results << endl;
    cout << "Hex directory: " << hex_dir << endl;

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
        cout << "Result BRAM: 0x" << hex << BRAM_RESULT_BASE << dec << endl;

        // Print initial status
        cout << "\n--- Initial Status ---" << endl;
        print_engine_status(gemm_device, "INIT");

        // =====================================================================
        // Step 1: Load test data to GDDR6
        // =====================================================================
        cout << "\n========================================" << endl;
        cout << "Step 1: Loading test data to GDDR6" << endl;
        cout << "========================================" << endl;

        array<vector<uint8_t>, NUM_ROWS> left_data;
        array<vector<uint8_t>, NUM_ROWS> right_data;

        for (int r = 0; r < NUM_ROWS; r++) {
            stringstream left_path;
            left_path << hex_dir << "/left_" << r << ".hex";

            if (!loadHexFile(left_path.str(), left_data[r])) {
                cerr << "ERROR: Failed to load left_" << r << ".hex" << endl;
                return 1;
            }
            // Try multi-block layout first (right_{r}_0.hex), then legacy (right_{r}.hex)
            string right_multi = hex_dir + "/right_" + to_string(r) + "_0.hex";
            string right_legacy = hex_dir + "/right_" + to_string(r) + ".hex";
            if (!loadHexFile(right_multi, right_data[r]) && !loadHexFile(right_legacy, right_data[r])) {
                cerr << "ERROR: Failed to load right_" << r << "_0.hex or right_" << r << ".hex" << endl;
                return 1;
            }
        }

        // DMA write to all 16 GDDR6 channels
        for (int r = 0; r < NUM_ROWS; r++) {
            uint64_t left_addr = gddr6_dma_addr(r, LINE_ADDR_LEFT * BYTES_PER_LINE);
            uint64_t right_addr = gddr6_dma_addr(r, LINE_ADDR_RIGHT * BYTES_PER_LINE);

            if (!gemm_device.dma_write(left_addr, left_data[r].data(), left_data[r].size())) {
                cerr << "ERROR: DMA write failed for row " << r << " left" << endl;
                return 1;
            }
            if (!gemm_device.dma_write(right_addr, right_data[r].data(), right_data[r].size())) {
                cerr << "ERROR: DMA write failed for row " << r << " right" << endl;
                return 1;
            }
        }
        cout << "DMA complete for all 16 rows" << endl;

        // =====================================================================
        // Step 2: Soft reset
        // =====================================================================
        cout << "\n========================================" << endl;
        cout << "Step 2: Soft reset" << endl;
        cout << "========================================" << endl;

        gemm_device.soft_reset();
        gemm_device.reset_cmd_id();

        // Reset ring buffer read pointer to 0
        gemm_device.mmio_write32(0, REG_RD_PTR, 0);

        usleep(100000);  // 100ms settle

        // Verify ring buffer state after reset
        uint32_t init_rd_ptr = gemm_device.mmio_read32(0, REG_RD_PTR) & BRAM_LINE_MASK;
        uint32_t init_wr_ptr = gemm_device.mmio_read32(0, REG_WR_PTR) & BRAM_LINE_MASK;
        cout << "Soft reset complete" << endl;
        cout << "Ring buffer: rd_ptr=" << init_rd_ptr << ", wr_ptr=" << init_wr_ptr << endl;
        print_engine_status(gemm_device, "RESET");

        // =====================================================================
        // Step 3: Submit commands in three groups (fetch+dispatch together, matmul+readout together)
        // =====================================================================
        cout << "\n========================================" << endl;
        cout << "Step 3: Submitting commands in groups" << endl;
        cout << "========================================" << endl;

        // --- GROUP 1: FETCH + DISPATCH RIGHT + WAIT (submit, then wait for idle) ---
        cout << "\n[GROUP 1] FETCH + DISPATCH RIGHT + WAIT_DISP" << endl;
        gemm_device.begin_command_batch();
        uint8_t fetch_right_id = gemm_device.fetch(LINE_ADDR_RIGHT, V_TOTAL, LINES_PER_BLOCK, true);
        uint8_t disp_right_id = gemm_device.dispatch(C, V_TOTAL, 0, 0, true, false);
        gemm_device.waitDispatch(disp_right_id);
        cout << "  FETCH RIGHT, DISPATCH RIGHT, WAIT_DISP (id=" << (int)disp_right_id << ")" << endl;
        if (!submit_group(gemm_device, "FETCH+DISPATCH RIGHT", true)) return 1;

        // --- GROUP 2: FETCH + DISPATCH LEFT + WAIT (submit, then wait for idle) ---
        cout << "\n[GROUP 2] FETCH + DISPATCH LEFT + WAIT_DISP" << endl;
        gemm_device.begin_command_batch();
        uint8_t fetch_left_id = gemm_device.fetch(LINE_ADDR_LEFT, V_TOTAL, LINES_PER_BLOCK, false);
        uint8_t disp_left_id = gemm_device.dispatch(B, V_TOTAL, 0, 0, false, false);
        gemm_device.waitDispatch(disp_left_id);
        cout << "  FETCH LEFT, DISPATCH LEFT, WAIT_DISP (id=" << (int)disp_left_id << ")" << endl;
        if (!submit_group(gemm_device, "FETCH+DISPATCH LEFT", true)) return 1;

        // --- GROUP 3: MATMUL + READOUT + WAIT_MATMUL (submit, then wait for idle) ---
        cout << "\n[GROUP 3] MATMUL + READOUT + WAIT_MATMUL" << endl;
        gemm_device.begin_command_batch();
        uint8_t matmul_id = gemm_device.matmul(0, 0, B, C, V_TOTAL, false, false, false);
        uint8_t readout_id = gemm_device.readout(B, C, V_TOTAL);
        gemm_device.waitMatmul(readout_id);
        cout << "  MATMUL, READOUT, WAIT_MATMUL (readout_id=" << (int)readout_id << ")" << endl;
        if (!submit_group(gemm_device, "MATMUL+READOUT", true)) return 1;

        (void)fetch_right_id;
        (void)fetch_left_id;
        (void)matmul_id;

        print_engine_status(gemm_device, "COMPLETE");

        // =====================================================================
        // Step 5: Read results from BRAM (using wr_ptr directly)
        // =====================================================================
        cout << "\n========================================" << endl;
        cout << "Step 5: Reading results from BRAM" << endl;
        cout << "========================================" << endl;

        // Calculate lines needed (16 FP16 per line)
        uint32_t lines_needed = (expected_results + FP16_PER_LINE - 1) / FP16_PER_LINE;

        // Get pointers from registers
        uint32_t rd_ptr = gemm_device.mmio_read32(0, REG_RD_PTR) & BRAM_LINE_MASK;
        uint32_t wr_ptr = gemm_device.mmio_read32(0, REG_WR_PTR) & BRAM_LINE_MASK;
        uint32_t used_entries = gemm_device.mmio_read32(0, REG_USED_ENTRIES) & 0x3FF;

        // Calculate available lines from wr_ptr (bypass broken used_entries register)
        uint32_t lines_available = (wr_ptr >= rd_ptr) ? (wr_ptr - rd_ptr) : (512 - rd_ptr + wr_ptr);

        cout << "  rd_ptr=" << rd_ptr << ", wr_ptr=" << wr_ptr << endl;
        cout << "  used_entries (reg)=" << used_entries << ", lines_available (calc)=" << lines_available << endl;
        cout << "  lines_needed=" << lines_needed << endl;

        if (lines_available < lines_needed) {
            cerr << "WARNING: wr_ptr says " << lines_available << " lines, need " << lines_needed << endl;
            cerr << "         Reading " << lines_needed << " lines anyway (wr_ptr may be next-write position)" << endl;
            // Don't reduce lines_needed - try reading all expected lines
        }

        // Read data from BRAM, handling wrap-around
        uint32_t bytes_to_read = lines_needed * BYTES_PER_BRAM_LINE;
        vector<uint8_t> result_data(bytes_to_read);

        if (rd_ptr + lines_needed > BRAM_LINE_DEPTH) {
            // Wrap-around case: split into two DMA reads
            uint32_t first_chunk_lines = BRAM_LINE_DEPTH - rd_ptr;
            uint32_t second_chunk_lines = lines_needed - first_chunk_lines;
            uint32_t first_bytes = first_chunk_lines * BYTES_PER_BRAM_LINE;
            uint32_t second_bytes = second_chunk_lines * BYTES_PER_BRAM_LINE;

            uint64_t first_addr = BRAM_RESULT_BASE + (rd_ptr * BYTES_PER_BRAM_LINE);
            uint64_t second_addr = BRAM_RESULT_BASE;  // Wrap to start

            cout << "  Wrap-around read: " << first_chunk_lines << " lines @ " << rd_ptr
                 << " + " << second_chunk_lines << " lines @ 0" << endl;

            if (!gemm_device.dma_read(first_addr, result_data.data(), first_bytes) ||
                !gemm_device.dma_read(second_addr, result_data.data() + first_bytes, second_bytes)) {
                cerr << "ERROR: DMA read failed (wrap-around)" << endl;
                return 1;
            }

            // Update read pointer (wrapped)
            rd_ptr = second_chunk_lines;
        } else {
            // Normal case: single DMA read
            uint64_t byte_addr = BRAM_RESULT_BASE + (rd_ptr * BYTES_PER_BRAM_LINE);

            if (!gemm_device.dma_read(byte_addr, result_data.data(), bytes_to_read)) {
                cerr << "ERROR: DMA read failed" << endl;
                return 1;
            }

            // Update read pointer
            rd_ptr = (rd_ptr + lines_needed) & BRAM_LINE_MASK;
        }

        // Dump raw BRAM contents (first 8 lines regardless of wr_ptr)
        cout << "\n  === Raw BRAM Dump (first 8 lines) ===" << endl;
        vector<uint8_t> bram_dump(8 * BYTES_PER_BRAM_LINE);
        if (gemm_device.dma_read(BRAM_RESULT_BASE, bram_dump.data(), bram_dump.size())) {
            for (int line = 0; line < 8; line++) {
                cout << "  Line " << setw(2) << line << ": ";
                for (int i = 0; i < 16; i++) {
                    uint16_t val = *(uint16_t*)(bram_dump.data() + line * 32 + i * 2);
                    cout << hex << setw(4) << setfill('0') << val << " ";
                }
                cout << dec << setfill(' ') << endl;
            }
        }

        // Update hardware read pointer register (allows engine to reuse buffer space)
        gemm_device.mmio_write32(0, REG_RD_PTR, rd_ptr);
        cout << "\n  Updated rd_ptr to " << rd_ptr << endl;

        // Extract FP16 results
        vector<uint16_t> hw_results(expected_results);
        for (int i = 0; i < expected_results; i++) {
            hw_results[i] = *(uint16_t*)(result_data.data() + i * 2);
        }

        cout << "\nFirst 16 results (as FP16):" << endl;
        for (int i = 0; i < min(16, expected_results); i++) {
            float val = fp16ToFloat(hw_results[i]);
            cout << "  [" << setw(2) << i << "] 0x" << hex << setw(4) << setfill('0')
                 << hw_results[i] << dec << setfill(' ') << " = " << fixed << setprecision(4) << setw(10) << val << endl;
        }

        // =====================================================================
        // Step 6: Validate
        // =====================================================================
        cout << "\n========================================" << endl;
        cout << "Step 6: Validation" << endl;
        cout << "========================================" << endl;

        // Load per-row golden files and compute expected sum
        vector<float> golden_sum(expected_results, 0.0f);

        for (int r = 0; r < NUM_ROWS; r++) {
            // Try multi-block layout first (golden_{r}_0.hex), then legacy (golden_{r}.hex)
            string golden_multi = hex_dir + "/golden_B" + to_string(B) + "_C" + to_string(C) + "_V" + to_string(V_per_row) + "_" + to_string(r) + "_0.hex";
            string golden_legacy = hex_dir + "/golden_B" + to_string(B) + "_C" + to_string(C) + "_V" + to_string(V_per_row) + "_" + to_string(r) + ".hex";

            vector<uint16_t> row_golden;
            if (!loadGoldenHex(golden_multi, row_golden) && !loadGoldenHex(golden_legacy, row_golden)) {
                cerr << "WARNING: Failed to load golden for row " << r << endl;
                continue;
            }

            if ((int)row_golden.size() != expected_results) {
                cerr << "WARNING: Row " << r << " golden size mismatch" << endl;
                continue;
            }

            for (int i = 0; i < expected_results; i++) {
                golden_sum[i] += fp16ToFloat(row_golden[i]);
            }
        }

        // Compare
        int matches = 0;
        int mismatches = 0;
        for (int i = 0; i < expected_results; i++) {
            float hw_f = fp16ToFloat(hw_results[i]);
            float golden_f = golden_sum[i];
            float diff = fabs(hw_f - golden_f);
            float pct = (fabs(golden_f) > 0.001f) ? diff / fabs(golden_f) : diff;

            if (pct <= 0.05f || diff < 0.01f) {
                matches++;
            } else {
                mismatches++;
                if (mismatches <= 5) {
                    cout << "MISMATCH [" << i << "]: hw=" << hw_f 
                         << ", golden=" << golden_f << ", diff=" << diff << endl;
                }
            }
        }

        double match_rate = (double)matches / expected_results * 100.0;
        cout << "\nResults: " << matches << "/" << expected_results 
             << " (" << fixed << setprecision(1) << match_rate << "%)" << endl;

        bool passed = (match_rate >= 95.0);
        cout << "\n" << (passed ? "[PASS]" : "[FAIL]") << " Single Command Test" << endl;

        return passed ? 0 : 1;

    } catch (const exception& e) {
        cerr << "ERROR: " << e.what() << endl;
        return 1;
    }
}
