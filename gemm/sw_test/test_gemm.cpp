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
#include "vp815_gemm_device.hpp"

using namespace std;
using namespace achronix;

// Test Configuration
static uint64_t BRAM_RESULT_BASE = 0;

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
bool run_single_test(VP815GemmDevice& gemm_device, int B, int C, int V, bool verbose, bool timing);

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
        } else if (strcmp(argv[i], "-h") == 0 || strcmp(argv[i], "--help") == 0) {
            cout << "Usage: test_gemm [options]\n";
            cout << "Options:\n";
            cout << "  -d N                Use device N (default: 0)\n";
            cout << "  -v                  Verbose output (results and debug info)\n";
            cout << "  -t                  Print timing information for each method\n";
            cout << "  -B N, -C N, -V N    Run single test with specified B, C, V parameters\n";
            cout << "  -h, --help          Show this help\n";
            cout << "\nDefault: Runs 10-config test suite if B/C/V not specified.\n";
            return 0;
        }
    }

    try {
        cout << "\n[Initialization] Opening VP815 device " << device_id << "..." << endl;
        VP815 device(device_id);
        VP815GemmDevice gemm_device(device);

        uint32_t bitstream_id = gemm_device.mmio_read32(0, 0x214);
        cout << "  Bitstream ID: 0x" << hex << bitstream_id << dec
             << " (Build: " << ((bitstream_id >> 24) & 0xFF) << "/"
             << ((bitstream_id >> 16) & 0xFF) << " "
             << ((bitstream_id >> 8) & 0xFF) << ":"
             << (bitstream_id & 0xFF) << ")" << endl;

        BRAM_RESULT_BASE = acx_util_nap_absolute_addr(ACX_PART_AC7t1500, 3, 5);

        // Check if single test mode (all three parameters specified)
        bool single_test_mode = (test_B >= 0 && test_C >= 0 && test_V >= 0);

        if (single_test_mode) {
            // Single test mode
            cout << "\n========================================" << endl;
            cout << "Single Test: B=" << test_B << ", C=" << test_C << ", V=" << test_V << endl;
            cout << "========================================" << endl;
            
            bool result = run_single_test(gemm_device, test_B, test_C, test_V, verbose, timing);
            
            cout << "\n========================================" << endl;
            cout << "TEST " << (result ? "PASSED" : "FAILED") << endl;
            cout << "========================================" << endl;
            
            return result ? 0 : 1;
        }

        // Default multi-config test suite
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
        cout << "Running " << num_tests << " Test Configurations" << endl;
        cout << "========================================\n" << endl;

        int passed = 0;
        int failed = 0;

        for (int i = 0; i < num_tests; ++i) {
            const auto& config = test_suite[i];
            
            cout << "----------------------------------------" << endl;
            cout << "Test " << (i+1) << "/" << num_tests << ": " << config.name << endl;
            cout << "  B=" << config.B << ", C=" << config.C << ", V=" << config.V << endl;
            cout << "----------------------------------------" << endl;
            
            bool result = run_single_test(gemm_device, config.B, config.C, config.V, verbose, timing);
            
            if (result) {
                passed++;
            } else {
                failed++;
            }
            
            cout << endl;
        }

        // Print summary
        cout << "========================================" << endl;
        cout << "TEST SUITE SUMMARY" << endl;
        cout << "========================================" << endl;
        cout << "Total tests: " << num_tests << endl;
        cout << "Passed: " << passed << " (" << (passed*100/num_tests) << "%)" << endl;
        cout << "Failed: " << failed << " (" << (failed*100/num_tests) << "%)" << endl;
        cout << "========================================" << endl;

        return (failed == 0) ? 0 : 1;

    } catch (const exception& e) {
        cerr << "ERROR: " << e.what() << endl;
        return 1;
    }
}

// Run Single Test Configuration
bool run_single_test(VP815GemmDevice& gemm_device, int B, int C, int V, bool verbose, bool timing) {
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

        // DMA matrices to GDDR6
        if (!gemm_device.dma_write(GDDR6_BASE_LEFT, left_data.data(), left_data.size())) {
            cerr << "ERROR: Failed to DMA write left matrix" << endl;
            return false;
        }

        if (!gemm_device.dma_write(GDDR6_BASE_RIGHT, right_data.data(), right_data.size())) {
            cerr << "ERROR: Failed to DMA write right matrix" << endl;
            return false;
        }

        // FETCH commands (using class methods)
        uint32_t left_lines = (left_data.size() + 31) / 32;
        uint32_t right_lines = (right_data.size() + 31) / 32;
        
        // Time the FETCH operations
        auto fetch_left_start = chrono::high_resolution_clock::now();
        gemm_device.fetch(GDDR6_BASE_LEFT, left_lines, false);  // Left matrix
        if (!gemm_device.wait_idle(10)) {
            cerr << "ERROR: FETCH LEFT timeout" << endl;
            return false;
        }
        auto fetch_left_end = chrono::high_resolution_clock::now();
        chrono::duration<double, std::milli> fetch_left_duration = fetch_left_end - fetch_left_start;
        if (timing) {
            cout << "  FETCH LEFT commands took " << fetch_left_duration.count() << " ms" << endl;
        }
        auto fetch_right_start = chrono::high_resolution_clock::now();
        gemm_device.fetch(GDDR6_BASE_RIGHT, right_lines, true); // Right matrix (fetch_right=true)
        if (!gemm_device.wait_idle(10)) {
            cerr << "ERROR: FETCH RIGHT timeout" << endl;
            return false;
        }
        auto fetch_right_end = chrono::high_resolution_clock::now();
        chrono::duration<double, std::milli> fetch_right_duration = fetch_right_end - fetch_right_start;
        if (timing) {
            cout << "  FETCH RIGHT commands took " << fetch_right_duration.count() << " ms" << endl;
        }

        // DISPATCH LEFT command (disp_right=false for left matrix)
        // man_nv_cnt = B×V (total NVs in left matrix)
        // LEFT matrix uses BROADCAST mode (same data replicated to all enabled tiles)
        auto dispatch_left_start = chrono::high_resolution_clock::now();
        if (verbose) {
            cout << "  DEBUG: Sending DISPATCH LEFT with man_nv_cnt=" << (B*V) << ", ugd_vec_size=" << V << endl;
        }
        uint8_t disp_left_id = gemm_device.dispatch(
            B * V,  // man_nv_cnt: Total Native Vectors = B × V
            V,      // ugd_vec_size: NVs per UGD vector (matches test V parameter)
            0,      // tile_addr: Start at tile_bram[0]
            false,  // disp_right: LEFT matrix (disp_right=0)
            0x0001, // col_en: Enable tile 0 only
            0,      // col_start: Start from tile 0
            true,   // broadcast: BROADCAST mode for left (activations replicated)
            false   // man_4b: 8-bit mantissas
        );
        gemm_device.waitDispatch(disp_left_id);
        auto dispatch_left_end = chrono::high_resolution_clock::now();
        chrono::duration<double, std::milli> dispatch_left_duration = dispatch_left_end - dispatch_left_start;
        if (timing) {
            cout << "  DISPATCH LEFT commands took " << dispatch_left_duration.count() << " ms" << endl;
        }

        // DISPATCH RIGHT command (disp_right=true for right matrix)
        // man_nv_cnt = C×V (total NVs in right matrix)
        // RIGHT matrix uses DISTRIBUTE mode (different data per tile)
        auto dispatch_right_start = chrono::high_resolution_clock::now();
        if (verbose) {
            cout << "  DEBUG: Sending DISPATCH RIGHT with man_nv_cnt=" << (C*V) << ", ugd_vec_size=" << V << endl;
        }
        uint8_t disp_right_id = gemm_device.dispatch(
            C * V,  // man_nv_cnt: Total Native Vectors = C × V
            V,      // ugd_vec_size: NVs per UGD vector (matches test V parameter)
            0,      // tile_addr: Start at tile_bram[0]
            true,   // disp_right: RIGHT matrix (disp_right=1)
            0x0001, // col_en: Enable tile 0 only
            0,      // col_start: Start from tile 0
            false,  // broadcast: DISTRIBUTE mode for right (weights sharded)
            false   // man_4b: 8-bit mantissas
        );
        gemm_device.waitDispatch(disp_right_id);
        auto dispatch_right_end = chrono::high_resolution_clock::now();
        chrono::duration<double, std::milli> dispatch_right_duration = dispatch_right_end - dispatch_right_start;
        if (timing) {
            cout << "  DISPATCH RIGHT commands took " << dispatch_right_duration.count() << " ms" << endl;
        }

        // MATMUL command - AMD-compatible signature
        // Pass B, C, V directly as leftUgdLen, rightUgdLen, vecLen
        auto tile_start = chrono::high_resolution_clock::now();
        if (verbose) {
            cout << "  DEBUG: Sending TILE with B=" << B << ", C=" << C << ", V=" << V << endl;
        }
        uint8_t tile_id = gemm_device.tile(
            0,    // left_addr
            0,    // right_addr
            B,    // leftUgdLen (used as both ugd_len and dimB)
            C,    // rightUgdLen (used as both ugd_len and dimC)
            V,    // vecLen (used as both vec_len and dimV)
            false, // leftMan4b
            false, // rightMan4b
            true   // mainLoopOverLeft
        );
        gemm_device.waitTile(tile_id);
        auto tile_end = chrono::high_resolution_clock::now();
        chrono::duration<double, std::milli> tile_duration = tile_end - tile_start;
        if (timing) {
            cout << "  MATMUL commands took " << tile_duration.count() << " ms" << endl;
        }

        auto wait_idle_start = chrono::high_resolution_clock::now();
        if (!gemm_device.wait_idle()) {
            cerr << "ERROR: Engine timeout" << endl;
            return false;
        }
        auto wait_idle_end = chrono::high_resolution_clock::now();
        chrono::duration<double, std::milli> wait_idle_duration = wait_idle_end - wait_idle_start;
        if (timing) {
            cout << "  WAIT IDLE commands took " << wait_idle_duration.count() << " ms" << endl;
        }

        // Read results
        size_t result_count_expected = B * C;
        size_t bram_bytes_per_result = 32;
        size_t result_bytes = result_count_expected * bram_bytes_per_result;
        vector<uint8_t> bram_data(result_bytes);

        if (!gemm_device.dma_read(BRAM_RESULT_BASE, bram_data.data(), result_bytes)) {
            cerr << "ERROR: Failed to DMA read results" << endl;
            return false;
        }

        vector<uint16_t> result_fp16(result_count_expected);
        for (size_t i = 0; i < result_count_expected; i++) {
            uint8_t* line_ptr = bram_data.data() + (i * 32);
            result_fp16[i] = *(uint16_t*)line_ptr;
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

        auto wait_idle_start_2 = chrono::high_resolution_clock::now();
        if (!gemm_device.wait_idle()) {
            cerr << "ERROR: Engine timeout" << endl;
            return false;
        }
        auto wait_idle_end_2 = chrono::high_resolution_clock::now();
        chrono::duration<double, std::milli> wait_idle_duration_2 = wait_idle_end_2 - wait_idle_start_2;
        if (timing) {
            cout << "  WAIT IDLE commands took " << wait_idle_duration_2.count() << " ms" << endl;
        }
        // Soft reset after test
        gemm_device.soft_reset();

        return validation_passed;

    } catch (const exception& e) {
        cerr << "ERROR: " << e.what() << endl;
        return false;
    }
}
