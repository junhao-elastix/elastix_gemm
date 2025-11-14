// MS2.0 GEMM Engine Test
//
// Test suite using VP815GemmDevice class with:
// - Encapsulated command interface
// - Default multi-config test suite (10 configurations)
// - CLI override support for single tests

#include <iostream>
#include <iomanip>
#include <fstream>
#include <sstream>
#include <cstring>
#include <cstdlib>
#include <chrono>
#include <cmath>
#include <vector>
#include <unistd.h>  // for usleep
#include "vp815_gemm_device.hpp"

using namespace std;
using namespace achronix;

// Test Configuration
static uint64_t BRAM_RESULT_BASE = 0;

// Timing helper struct
struct TimingStats {
    double dma_write_ms = 0;
    double fetch_left_ms = 0;
    double fetch_right_ms = 0;
    double dispatch_left_ms = 0;
    double dispatch_right_ms = 0;
    double tile_ms = 0;
    double readout_ms = 0;
    double total_ms = 0;
};

// Helper Functions

float fp16ToFloat(uint16_t fp16_val) {
    uint16_t sign = (fp16_val >> 15) & 1;
    uint16_t exp = (fp16_val >> 10) & 0x1F;
    uint16_t frac = fp16_val & 0x3FF;

    if (exp == 0) {
        if (frac == 0) {
            return sign ? -0.0f : 0.0f;
        }
        // Subnormal
        return (sign ? -1.0f : 1.0f) * (frac / 1024.0f) * powf(2.0f, -14.0f);
    } else if (exp == 31) {
        return (frac == 0) ? (sign ? -INFINITY : INFINITY) : NAN;
    } else {
        // Normal
        return (sign ? -1.0f : 1.0f) * (1.0f + frac / 1024.0f) * powf(2.0f, (int)exp - 15);
    }
}

bool loadGoldenReferenceHex(const string& filename, vector<float>& golden, int expected_count) {
    ifstream file(filename);
    if (!file.is_open()) {
        cerr << "ERROR: Cannot open golden reference file: " << filename << endl;
        return false;
    }

    golden.clear();
    golden.reserve(expected_count);

    string line;
    while (getline(file, line)) {
        if (line.empty() || line[0] == '#') continue;
        uint16_t fp16_val = stoi(line, nullptr, 16);
        golden.push_back(fp16ToFloat(fp16_val));
    }

    if ((int)golden.size() != expected_count) {
        cerr << "ERROR: Expected " << expected_count << " values, got " << golden.size() << endl;
        return false;
    }

    return true;
}

uint16_t floatToFP16(float val) {
    uint32_t bits;
    memcpy(&bits, &val, sizeof(float));

    uint32_t sign = (bits >> 31) & 0x1;
    uint32_t exp = (bits >> 23) & 0xFF;
    uint32_t mant = bits & 0x7FFFFF;

    // Handle special cases
    if (exp == 0) return (sign << 15);
    if (exp == 0xFF) return (sign << 15) | 0x7C00;

    // Rebias exponent
    int32_t new_exp = (int32_t)exp - 127 + 15;
    
    // Handle subnormal FP16 output
    if (new_exp <= 0) {
        int shift = 1 - new_exp;
        if (shift >= 24) return (sign << 15);
        
        uint32_t full_mant = (1 << 23) | mant;
        uint32_t new_mant = (full_mant + (1 << (shift + 12))) >> (shift + 13);
        
        if (new_mant > 0x3FF) {
            return (sign << 15) | (1 << 10);
        }
        return (sign << 15) | (new_mant & 0x3FF);
    }
    
    if (new_exp >= 31) return (sign << 15) | 0x7C00;

    // Round mantissa
    uint32_t new_mant = (mant + 0x1000) >> 13;
    
    if (new_mant > 0x3FF) {
        new_exp++;
        new_mant = 0;
        if (new_exp >= 31) return (sign << 15) | 0x7C00;
    }

    return (sign << 15) | (new_exp << 10) | (new_mant & 0x3FF);
}

// Test Configuration Structure
struct TestConfig {
    int B;
    int C;
    int V;
    const char* name;
};

// Function Declarations
bool run_single_test(VP815GemmDevice& gemm_device, int B, int C, int V, bool verbose, bool timing, uint32_t col_en = 0x0001);
bool run_single_test_with_collection(VP815GemmDevice& gemm_device, int B, int C, int V, bool verbose, bool timing,
                                     uint32_t& host_rd_ptr, bool reset_rd_ptr, vector<uint16_t>& collected_results);

// Main
int main(int argc, char* argv[]) {
    cout << "========================================" << endl;
    cout << "MS2.0 GEMM Engine (Refactored)" << endl;
    cout << "========================================" << endl;

    // Parse command line arguments
    int device_id = 0;
    bool verbose = false;
    bool timing = false;
    int test_B = -1, test_C = -1, test_V = -1;
    int num_tiles = 1;  // Default: single tile (column 0 only)
    uint32_t col_en = 0x0001;  // Default: single tile (column 0 only)
    
    for (int i = 1; i < argc; ++i) {
        if (strcmp(argv[i], "-d") == 0 && i+1 < argc) {
            device_id = stoi(argv[++i]);
        } else if (strcmp(argv[i], "-v") == 0) {
            verbose = true;
            timing = true;
        } else if (strcmp(argv[i], "-t") == 0) {
            timing = true;
        } else if (strcmp(argv[i], "-B") == 0 && i+1 < argc) {
            test_B = stoi(argv[++i]);
        } else if (strcmp(argv[i], "-C") == 0 && i+1 < argc) {
            test_C = stoi(argv[++i]);
        } else if (strcmp(argv[i], "-V") == 0 && i+1 < argc) {
            test_V = stoi(argv[++i]);
        } else if (strcmp(argv[i], "-n") == 0 && i+1 < argc) {
            num_tiles = stoul(argv[++i]);  // Parse as hex if starts with 0x
        } else if (strcmp(argv[i], "-h") == 0 || strcmp(argv[i], "--help") == 0) {
            cout << "Usage: test_gemm [options]\n";
            cout << "Options:\n";
            cout << "  -d N                Use device N (default: 0)\n";
            cout << "  -v                  Verbose output (results and debug info)\n";
            cout << "  -t                  Print timing information for each method\n";
            cout << "  -B N, -C N, -V N    Run single test with specified B, C, V parameters\n";
            cout << "  -n N                Number of tiles (1,2,4,8) - sets col_en mask (default: 1)\n";
            cout << "  -h, --help          Show this help\n";
            cout << "\nDefault: Runs 10-config test suite if B/C/V not specified.\n";
            return 0;
        }
    }

    try {
        cout << "\n[Initialization] Opening VP815 device " << device_id << "..." << endl;
        VP815 device(device_id);
        VP815GemmDevice gemm_device(device);
        gemm_device.soft_reset();

        uint32_t bitstream_id = gemm_device.mmio_read32(0, 0x214);
        cout << "  Bitstream ID: 0x" << hex << bitstream_id << dec
             << " (Build: " << ((bitstream_id >> 24) & 0xFF) << "/"
             << ((bitstream_id >> 16) & 0xFF) << " "
             << ((bitstream_id >> 8) & 0xFF) << ":"
             << (bitstream_id & 0xFF) << ")" << endl;

        BRAM_RESULT_BASE = acx_util_nap_absolute_addr(ACX_PART_AC7t1500, 3, 5);
        if (num_tiles == 2) {
            col_en = 0x0003;
        } else if (num_tiles == 4) {
            col_en = 0x000F;
        } else if (num_tiles == 8) {
            col_en = 0x00FF;
        }
        else {
            col_en = 0x0001;
        }

        // Check if single test mode (all three parameters specified)
        bool single_test_mode = (test_B >= 0 && test_C >= 0 && test_V >= 0);

        if (single_test_mode) {
            // Single test mode
            cout << "\n========================================" << endl;
            cout << "Single Test: B=" << test_B << ", C=" << test_C << ", V=" << test_V << endl;
            cout << "Column Enable: 0x" << hex << setfill('0') << setw(6) << col_en << dec 
                 << " (" << num_tiles << " tile" << (num_tiles != 1 ? "s" : "") << " enabled)" << endl;
            cout << "========================================" << endl;
            
            bool result = run_single_test(gemm_device, test_B, test_C, test_V, verbose, timing, col_en);
            
            cout << "\n========================================" << endl;
            cout << "TEST " << (result ? "PASSED" : "FAILED") << endl;
            cout << "========================================" << endl;
            
            return result ? 0 : 1;
        }

        // Default multi-config test suite - THREE-STAGE MODE
        const TestConfig test_suite[] = {
            {1, 1, 1, "B1_C1_V1"},
            {2, 2, 2, "B2_C2_V2"},
            {4, 4, 4, "B4_C4_V4"},
            {2, 2, 64, "B2_C2_V64"},
            {4, 4, 32, "B4_C4_V32"},
            {8, 8, 16, "B8_C8_V16"},
            {16, 16, 8, "B16_C16_V8"},
            {1, 128, 1, "B1_C128_V1"},
            {128, 1, 1, "B128_C1_V1"},
            {1, 1, 128, "B1_C1_V128"}
        };
        const int num_tests = sizeof(test_suite) / sizeof(test_suite[0]);

        cout << "\n========================================" << endl;
        cout << "THREE-STAGE CIRCULAR BUFFER VALIDATION" << endl;
        cout << "========================================\n" << endl;

        // ===================================================================
        // STAGE 1: Individual Tests with Reset (Baseline)
        // ===================================================================
        cout << "================================================================" << endl;
        cout << "STAGE 1: Individual Tests (Baseline with Reset)" << endl;
        cout << "================================================================\n" << endl;

        vector<uint16_t> results_stage1;
        int stage1_passed = 0;

        for (int i = 0; i < num_tests; ++i) {
            const auto& config = test_suite[i];

            cout << "----------------------------------------" << endl;
            cout << "Test " << (i+1) << "/" << num_tests << ": " << config.name << endl;
            cout << "  B=" << config.B << ", C=" << config.C << ", V=" << config.V << endl;
            cout << "----------------------------------------" << endl;

            // STAGE 1: Soft reset before first test only
            if (i == 0) {
                gemm_device.soft_reset();  // Reset engine + circular buffer
                cout << "  [Stage 1] Initial soft reset complete" << endl;
            }

            bool result = run_single_test(gemm_device, config.B, config.C, config.V, verbose, timing, col_en);

            if (result) {
                stage1_passed++;

                // Collect results into stage1 array
                // Read results again to collect (already validated in run_single_test)
                size_t result_count = config.B * config.C;

                // Byte-addressed read from rd_ptr=0 (reset before each test)
                uint32_t rd_ptr = 0;
                uint32_t byte_offset = rd_ptr * 2;
                uint32_t byte_count = result_count * 2;
                uint32_t offset_in_first_line = byte_offset % 32;
                uint32_t total_bytes = offset_in_first_line + byte_count;
                uint32_t dma_bytes = ((total_bytes + 31) / 32) * 32;
                uint32_t dma_start = (byte_offset / 32) * 32;

                cout << "  [Stage 1 DMA] rd_ptr=" << rd_ptr
                     << ", byte_offset=" << byte_offset
                     << ", offset_in_line=" << offset_in_first_line
                     << ", dma_start=" << dma_start
                     << ", dma_bytes=" << dma_bytes << endl;

                vector<uint8_t> bram_data(dma_bytes);
                if (gemm_device.dma_read(BRAM_RESULT_BASE + dma_start, bram_data.data(), dma_bytes)) {
                    for (size_t j = 0; j < result_count; j++) {
                        size_t byte_pos = offset_in_first_line + j * 2;
                        uint16_t fp16_val = *(uint16_t*)(bram_data.data() + byte_pos);
                        results_stage1.push_back(fp16_val);
                    }
                }

                // Soft reset AFTER collecting results, ready for next test
                gemm_device.soft_reset();  // Reset engine + circular buffer (wr_ptr, rd_ptr)  
                if (verbose) {
                    cout << "  [Stage 1] Post-test reset: rd_ptr=0, wr_ptr=0" << endl;
                }
            }

            cout << endl;
        }

        cout << "[Stage 1 Complete] Tests: " << stage1_passed << "/" << num_tests << " passed" << endl;
        cout << "[Stage 1 Complete] Collected: " << results_stage1.size() << " FP16 results\n" << endl;
    return stage1_passed == num_tests;

    } catch (const exception& e) {
        cerr << "ERROR: " << e.what() << endl;
        return 1;
    }
}

// Run Single Test Configuration
bool run_single_test(VP815GemmDevice& gemm_device, int B, int C, int V, bool verbose, bool timing, uint32_t col_en) {
    TimingStats timing_stats;
    auto test_start = chrono::high_resolution_clock::now();
    
    try {
        // Load matrices from hex files
        string left_hex = "../../hex/left.hex";
        string right_hex = "../../hex/right.hex";
        vector<uint8_t> left_data, right_data;
        
        if (!gemm_device.loadHexMatrix(left_hex, left_data)) {
            cerr << "ERROR: Failed to load left matrix" << endl;
            return false;
        }
        
        if (!gemm_device.loadHexMatrix(right_hex, right_data)) {
            cerr << "ERROR: Failed to load right matrix" << endl;
            return false;
        }
        
        if (verbose) {
            cout << "  Loaded matrices: " << left_data.size() << " + " << right_data.size() << " bytes" << endl;
        }
        
        // Software reset
        gemm_device.soft_reset();
        gemm_device.reset_cmd_id();

        uint32_t status_after_reset = gemm_device.mmio_read32(0, MS2_STATUS);
        if ((status_after_reset & 0x1) != 0) {
            cerr << "  WARNING: Engine still busy after reset" << endl;
        }

        // Reset circular buffer read pointer for this test
        // Register 0x230 (140) - REG_RD_PTR: Host read/write pointer
        uint32_t host_rd_ptr = 0;  // Initialize to 0 at start of each test
        gemm_device.mmio_write32(0, 0x230, host_rd_ptr);

        int num_tiles = __builtin_popcount(col_en & 0xFF);
        if (C < num_tiles) {
            if (C == 1) {
                col_en = 0x0001;
            } else if (C == 2) {
                col_en = 0x0003;
            } else if (C == 4) {
                col_en = 0x000F;
            }
        }

        if (verbose) {
            cout << "  [Circular Buffer] Reset rd_ptr to 0" << endl;
        }

        // DMA matrices to GDDR6
        auto dma_start = chrono::high_resolution_clock::now();
        if (!gemm_device.dma_write(GDDR6_BASE_LEFT, left_data.data(), left_data.size())) {
            cerr << "ERROR: Failed to DMA write left matrix" << endl;
            return false;
        }

        if (!gemm_device.dma_write(GDDR6_BASE_RIGHT, right_data.data(), right_data.size())) {
            cerr << "ERROR: Failed to DMA write right matrix" << endl;
            return false;
        }
        auto dma_end = chrono::high_resolution_clock::now();
        timing_stats.dma_write_ms = chrono::duration<double, milli>(dma_end - dma_start).count();

        // ===================================================================
        // Command Flow: Batched submission matching testbench tb_engine_top.sv
        // Strategy: Submit command batches, wait only after DISPATCH stages
        // ===================================================================
        uint32_t left_lines = (left_data.size() + 31) / 32;
        uint32_t right_lines = (right_data.size() + 31) / 32;
        size_t result_count_expected = B * C;
        
        // ========== BATCH 1: FETCH LEFT + DISPATCH LEFT + WAIT_DISPATCH ==========
        // Hardware needs wait after FETCH (GDDR6→BRAM transfer) before DISPATCH
        auto fetch_left_start = chrono::high_resolution_clock::now();
        gemm_device.fetch(GDDR6_BASE_LEFT, left_lines, false);
        auto fetch_left_end = chrono::high_resolution_clock::now();
        timing_stats.fetch_left_ms = chrono::duration<double, milli>(fetch_left_end - fetch_left_start).count();
        
        auto dispatch_left_start = chrono::high_resolution_clock::now();
        uint8_t disp_left_id = gemm_device.dispatch(B * V, V, 0, false, col_en, 0, true, false);
        gemm_device.waitDispatch(disp_left_id);
        auto dispatch_left_end = chrono::high_resolution_clock::now();
        timing_stats.dispatch_left_ms = chrono::duration<double, milli>(dispatch_left_end - dispatch_left_start).count();
        
        // ========== BATCH 2: FETCH RIGHT + DISPATCH RIGHT + WAIT_DISPATCH ==========
        auto fetch_right_start = chrono::high_resolution_clock::now();
        gemm_device.fetch(GDDR6_BASE_RIGHT, right_lines, true);
        auto fetch_right_end = chrono::high_resolution_clock::now();
        timing_stats.fetch_right_ms = chrono::duration<double, milli>(fetch_right_end - fetch_right_start).count();
        
        auto dispatch_right_start = chrono::high_resolution_clock::now();
        uint8_t disp_right_id = gemm_device.dispatch(C * V, V, 0, true, col_en, 0, false, false);
        gemm_device.waitDispatch(disp_right_id);
        auto dispatch_right_end = chrono::high_resolution_clock::now();
        timing_stats.dispatch_right_ms = chrono::duration<double, milli>(dispatch_right_end - dispatch_right_start).count();

        
        // ========== BATCH 3: TILE + WAIT_TILE + READOUT ==========
        auto tile_start = chrono::high_resolution_clock::now();
        uint8_t tile_id = gemm_device.tile(0, 0, B, C, V, false, false, false, col_en);
        gemm_device.waitTile(tile_id);
        auto tile_end = chrono::high_resolution_clock::now();
        timing_stats.tile_ms = chrono::duration<double, milli>(tile_end - tile_start).count();
        
        auto readout_start = chrono::high_resolution_clock::now();
        gemm_device.readout(0, result_count_expected);
        if (!gemm_device.wait_idle(1000)) {
            cerr << "ERROR: READOUT timeout" << endl;
            return false;
        }
        auto readout_end = chrono::high_resolution_clock::now();
        timing_stats.readout_ms = chrono::duration<double, milli>(readout_end - readout_start).count();


        // Read results using packed BRAM format with two-pointer circular buffer
        // New optimization: 16 FP16 values per 256-bit (32-byte) BRAM line
        // Hardware maintains wr_ptr, host maintains rd_ptr

        // Step 1: Read circular buffer pointers
        // Register 0x230 (140) - REG_RD_PTR: Host read/write pointer
        // Register 0x234 (141) - REG_WR_PTR: Hardware write pointer (read-only)
        // Register 0x238 (142) - REG_USED_ENTRIES: Used entries (read-only)

        // host_rd_ptr was already declared and reset at the start of this test

        uint32_t wr_ptr_raw = gemm_device.mmio_read32(0, 0x234);  // Read hardware write pointer
        uint32_t wr_ptr = wr_ptr_raw & 0x1FFF;  // 13-bit counter (0-8191)

        uint32_t used_entries_raw = gemm_device.mmio_read32(0, 0x238);  // Read used entries
        uint32_t used_entries = used_entries_raw & 0x3FFF;  // 14-bit counter (0-8192)

        if (verbose) {
            cout << "  [Circular Buffer] wr_ptr = " << wr_ptr
                 << ", rd_ptr = " << host_rd_ptr
                 << ", used_entries = " << used_entries << endl;
        }

        // Step 2: Calculate available results (already calculated above)
        // size_t result_count_expected = B * C;

        // Verify we have enough results
        if (used_entries < result_count_expected) {
            cerr << "WARNING: Not enough results yet (expected " << result_count_expected
                 << ", available " << used_entries << ")" << endl;

            // Re-read pointers
            wr_ptr_raw = gemm_device.mmio_read32(0, 0x234);
            wr_ptr = wr_ptr_raw & 0x1FFF;
            used_entries_raw = gemm_device.mmio_read32(0, 0x238);
            used_entries = used_entries_raw & 0x3FFF;

            if (verbose) {
                cout << "  [Circular Buffer] After wait: wr_ptr = " << wr_ptr
                     << ", used_entries = " << used_entries << endl;
            }
        }

        // Step 3: Handle partial buffers - flush if needed
        // If result count is not a multiple of 16, we have a partial line that needs flushing
        if ((result_count_expected % 16) != 0) {
            if (verbose) {
                cout << "  [DMA Read] Forcing flush (partial line: " << result_count_expected
                     << " results, not multiple of 16)" << endl;
            }

            // Trigger flush by writing 0 to write_top_reset (register 0x22C)
                gemm_device.mmio_write32(0, 0x22C, 0x00000000);
        }

        // Step 4: Calculate byte-aligned DMA read
        // Convert FP16 index to byte address (2 bytes per FP16)
        uint32_t byte_offset = host_rd_ptr * 2;
        uint32_t byte_count = result_count_expected * 2;

        // Calculate how many complete 32-byte lines we need to read
        // Account for starting offset within first line
        uint32_t offset_in_first_line = byte_offset % 32;
        uint32_t total_bytes_needed = offset_in_first_line + byte_count;
        uint32_t lines_to_read = (total_bytes_needed + 31) / 32;
        uint32_t dma_read_bytes = lines_to_read * 32;

        // DMA read starting from rd_ptr (byte-addressed!)
        uint32_t dma_start_addr = (byte_offset / 32) * 32;  // Round down to line boundary
        vector<uint8_t> bram_data(dma_read_bytes);

        if (verbose) {
            cout << "  [DMA Read] rd_ptr=" << host_rd_ptr
                 << ", byte_offset=" << byte_offset
                 << ", reading " << dma_read_bytes << " bytes from offset " << dma_start_addr << endl;
        }

        if (!gemm_device.dma_read(BRAM_RESULT_BASE + dma_start_addr, bram_data.data(), dma_read_bytes)) {
            cerr << "ERROR: Failed to DMA read results" << endl;
            return false;
        }

        // Step 5: Extract FP16 results with automatic offset handling
        vector<uint16_t> result_fp16(result_count_expected);

        for (size_t i = 0; i < result_count_expected; i++) {
            // Calculate byte position in the DMA buffer
            size_t byte_pos = offset_in_first_line + i * 2;
            result_fp16[i] = *(uint16_t*)(bram_data.data() + byte_pos);
        }

        if (verbose) {
            cout << "  [DMA Read] Unpacked " << result_count_expected << " FP16 results" << endl;
            cout << "  First 4 results: 0x" << hex << setfill('0')
                 << setw(4) << result_fp16[0] << " 0x"
                 << setw(4) << result_fp16[1] << " 0x"
                 << setw(4) << result_fp16[2] << " 0x"
                 << setw(4) << result_fp16[3] << dec << endl;
        }

        // Load and validate golden reference
        stringstream golden_ss;
        golden_ss << "../../hex/golden_B" << B << "_C" << C << "_V" << V << ".hex";
        string golden_file = golden_ss.str();
        
        vector<float> golden_results;
        if (!loadGoldenReferenceHex(golden_file, golden_results, result_count_expected)) {
            cerr << "ERROR: Failed to load golden reference: " << golden_file << endl;
            return false;
        }
        
        // Convert FP16 results to float for comparison
        vector<float> result_float(result_fp16.size());
        for (size_t i = 0; i < result_fp16.size(); i++) {
            result_float[i] = fp16ToFloat(result_fp16[i]);
        }
        
        if (verbose) {
            cout << "\n  Hardware Results vs Golden Reference:" << endl;
            cout << "  Index | Hardware (Hex) | Hardware (Float) | Golden (Hex) | Golden (Float) | Match" << endl;
            cout << "  ------|----------------|------------------|--------------|----------------|------" << endl;
        }
        
        int matches = 0;
        for (size_t i = 0; i < result_fp16.size() && i < golden_results.size(); i++) {
            uint16_t golden_fp16 = floatToFP16(golden_results[i]);
            float diff = fabs(result_float[i] - golden_results[i]);
            float rel_err = (golden_results[i] != 0.0f) ? diff / fabs(golden_results[i]) : diff;
            bool match = (rel_err <= 0.4f);
            
            if (match) matches++;
            
            if (verbose) {
                cout << "  " << setw(5) << i << " | 0x" << hex << setw(4) << setfill('0') << result_fp16[i] << dec 
                     << "         | " << setw(15) << setprecision(6) << result_float[i]
                     << " | 0x" << hex << setw(4) << setfill('0') << golden_fp16 << dec
                        << "        | " << setw(15) << setprecision(6) << golden_results[i]
                        << " | " << (match ? "Y" : "N") << endl;
            }
        }
        
        bool validation_passed = (matches == (int)result_fp16.size());
        
        // Always report match count
        cout << "  Validation: " << matches << "/" << result_fp16.size() << " matches" << endl;
        
        if (validation_passed) {
            cout << "  [PASS] B" << B << "_C" << C << "_V" << V << endl;
        } else {
            cout << "  [FAIL] B" << B << "_C" << C << "_V" << V << " - Validation failed" << endl;
        }

        // Update host read pointer after consuming results
        // Advance rd_ptr by the number of results we just read
        host_rd_ptr = (host_rd_ptr + result_count_expected) & 0x1FFF;  // Wrap at 8192

        // Write updated rd_ptr back to hardware (register 0x230)
        gemm_device.mmio_write32(0, 0x230, host_rd_ptr);

        if (verbose) {
            cout << "  [Circular Buffer] Updated rd_ptr to " << host_rd_ptr << endl;

            // Verify updated state
            uint32_t new_used_entries = gemm_device.mmio_read32(0, 0x238) & 0x3FFF;
            cout << "  [Circular Buffer] After read: used_entries = " << new_used_entries << endl;
        }

        // Note: We do NOT reset wr_ptr - circular buffer is persistent
        // The buffer will wrap around automatically at 8192 results

        // Calculate total time
        auto test_end = chrono::high_resolution_clock::now();
        timing_stats.total_ms = chrono::duration<double, milli>(test_end - test_start).count();

        // Print timing information if requested
        if (timing) {
            int num_tiles = __builtin_popcount(col_en & 0xFF);
            cout << "\n  ====================================================================" << endl;
            cout << "  TIMING BREAKDOWN (B=" << B << ", C=" << C << ", V=" << V 
                 << ", " << num_tiles << " tile" << (num_tiles != 1 ? "s" : "") << ")" << endl;
            cout << "  ====================================================================" << endl;
            cout << "  DMA Write:       " << fixed << setprecision(3) << timing_stats.dma_write_ms << " ms" << endl;
            cout << "  FETCH Left:      " << timing_stats.fetch_left_ms << " ms" << endl;
            cout << "  FETCH Right:     " << timing_stats.fetch_right_ms << " ms" << endl;
            cout << "  DISPATCH Left:   " << timing_stats.dispatch_left_ms << " ms" << endl;
            cout << "  DISPATCH Right:  " << timing_stats.dispatch_right_ms << " ms" << endl;
            cout << "  TILE:            " << timing_stats.tile_ms << " ms" << endl;
            cout << "  READOUT:         " << timing_stats.readout_ms << " ms" << endl;
            cout << "  ------------------------------------------------" << endl;
            cout << "  TOTAL:           " << timing_stats.total_ms << " ms" << endl;
            
            // Calculate throughput (GOPS)
            double total_ops = (double)B * C * V * 128 * 2;  // B×C×V×128 dot products, each has 128 multiply-adds
            double gops = total_ops / (timing_stats.tile_ms * 1e6);  // GOPS
            cout << "\n  Performance:" << endl;
            cout << "  Compute ops:     " << scientific << setprecision(2) << total_ops << " ops" << endl;
            cout << "  Throughput:      " << fixed << setprecision(3) << gops << " GOPS" << endl;
            cout << "  ====================================================================" << endl;
        }

        // Soft reset after test
        gemm_device.soft_reset();

        return validation_passed;

    } catch (const exception& e) {
        cerr << "ERROR: " << e.what() << endl;
        return false;
    }
}
