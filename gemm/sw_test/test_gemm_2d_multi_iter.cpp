// 2D Multi-Row GEMM Multi-Iteration Test
//
// Purpose: Validate weight persistence across multiple MATMUL operations
//   - Weights loaded ONCE at init (persist in MLP BRAM)
//   - Activations fetched from GDDR6 each iteration
//   - All iterations should produce identical results
//
// This mirrors real LLM inference patterns where model weights are
// loaded once and reused for many inference operations.
//
// Memory layout:
//   Lines 0-527:    Weights (right_*.hex) - fetched and dispatched once
//   Lines 528-1055: Activations (left_*.hex) - fetched each iteration
//
// Command sequence per iteration (after initial weight load):
//   1. FETCH LEFT        - load activations from GDDR6
//   2. DISPATCH LEFT     - move to row_bram
//   3. WAIT_DISP         - wait for dispatch complete
//   4. MATMUL            - compute B*C outputs
//   5. READOUT           - trigger result collection
//   6. WAIT_MATMUL       - wait for completion
//   7. Read results from BRAM

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
// Constants
// ============================================================================
constexpr uint32_t BYTES_PER_LINE = 32;
constexpr uint32_t BLOCK_SIZE = LINES_PER_BLOCK * BYTES_PER_LINE;

// Memory layout: weights @ 0-527, activations @ 528-1055
constexpr uint32_t LINE_ADDR_WEIGHTS = 0;         // Lines 0-527
constexpr uint32_t LINE_ADDR_ACTIVATIONS = 528;   // Lines 528-1055

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
// Run single iteration (activations only - weights already in MLP BRAM)
// Returns results in hw_results vector
// ============================================================================
bool run_iteration(VP815GemmDevice& gemm_device, const TestConfig& config,
                   int iter_num, vector<uint16_t>& hw_results, bool verbose) {
    const int B = config.B;
    const int C = config.C;
    const int V_per_row = config.V;
    const int V_TOTAL = V_per_row * NUM_ROWS;
    const int expected_results = B * C;

    if (verbose) {
        cout << "  Iteration " << iter_num << ": issuing commands..." << endl;
    }

    // Start new command batch
    gemm_device.begin_command_batch();

    // --- FETCH LEFT (activations from GDDR6) ---
    uint8_t fetch_left_id = gemm_device.fetch(LINE_ADDR_ACTIVATIONS, V_TOTAL, LINES_PER_BLOCK, false);
    if (verbose) {
        cout << "    [" << (int)fetch_left_id << "] FETCH LEFT: addr=" << LINE_ADDR_ACTIVATIONS
             << ", ugd=" << V_TOTAL << ", len=" << LINES_PER_BLOCK << endl;
    }

    // --- DISPATCH LEFT (activations -> row_bram) ---
    uint8_t disp_left_id = gemm_device.dispatch(B, V_TOTAL, 0, 0, false, false);
    if (verbose) {
        cout << "    [" << (int)disp_left_id << "] DISPATCH LEFT: nv=" << B
             << ", ugd=" << V_TOTAL << endl;
    }

    // WAIT for DISPATCH to complete
    uint8_t wait_disp_id = gemm_device.waitDispatch(disp_left_id);
    if (verbose) {
        cout << "    [" << (int)wait_disp_id << "] WAIT_DISP: wait_id=" << (int)disp_left_id << endl;
    }

    // --- MATMUL ---
    uint8_t matmul_id = gemm_device.matmul(0, 0, B, C, V_TOTAL, false, false, false);
    if (verbose) {
        cout << "    [" << (int)matmul_id << "] MATMUL: B=" << B << ", C=" << C
             << ", V=" << V_TOTAL << endl;
    }

    // --- READOUT ---
    uint8_t readout_id = gemm_device.readout(B, C, V_TOTAL);
    if (verbose) {
        cout << "    [" << (int)readout_id << "] READOUT: B=" << B << ", C=" << C << endl;
    }

    // --- WAIT for MATMUL to complete ---
    uint8_t wait_matmul_id = gemm_device.waitMatmul(matmul_id);
    if (verbose) {
        cout << "    [" << (int)wait_matmul_id << "] WAIT_MATMUL: wait_id=" << (int)matmul_id << endl;
    }

    // Submit commands
    if (!gemm_device.submit_commands(false)) {
        cerr << "ERROR: Iteration " << iter_num << " - failed to submit commands" << endl;
        return false;
    }

    // Wait for engine to become idle
    int wait_iter = 0;
    while (wait_iter < 50) {  // 5 seconds max
        uint32_t status = gemm_device.mmio_read32(0, 0x50);
        if ((status & 0x1) == 0) {
            break;  // Engine idle
        }
        usleep(100000);  // 100ms
        wait_iter++;
    }

    if (wait_iter >= 50) {
        uint32_t status = gemm_device.mmio_read32(0, 0x50);
        cerr << "ERROR: Iteration " << iter_num << " - timeout, STATUS=0x"
             << hex << status << dec << endl;
        return false;
    }

    // Read results from BRAM
    int lines_to_read = (expected_results + 15) / 16;
    int bytes_to_read = lines_to_read * 32;

    vector<uint8_t> result_data(bytes_to_read);
    if (!gemm_device.dma_read(BRAM_RESULT_BASE, result_data.data(), bytes_to_read)) {
        cerr << "ERROR: Iteration " << iter_num << " - failed to read results" << endl;
        return false;
    }

    // Extract FP16 results
    hw_results.resize(expected_results);
    for (int i = 0; i < expected_results; i++) {
        hw_results[i] = *(uint16_t*)(result_data.data() + i * 2);
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
    cout << "Purpose: Validate weight persistence across iterations" << endl;
    cout << "Architecture: " << NUM_ROWS << " rows x " << NUM_COLS << " columns" << endl;

    // Parse command line
    int device_id = 0;
    bool verbose = false;
    int num_iterations = 10;
    string test_name = "B4_C4_V32";  // Default test

    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "-d") == 0 && i + 1 < argc) {
            device_id = stoi(argv[++i]);
        } else if (strcmp(argv[i], "-v") == 0) {
            verbose = true;
        } else if (strcmp(argv[i], "-n") == 0 && i + 1 < argc) {
            num_iterations = stoi(argv[++i]);
        } else if (strcmp(argv[i], "-t") == 0 && i + 1 < argc) {
            test_name = argv[++i];
        } else if (strcmp(argv[i], "-h") == 0 || strcmp(argv[i], "--help") == 0) {
            cout << "\nUsage: test_gemm_2d_multi_iter [options]\n";
            cout << "Options:\n";
            cout << "  -d N    Use device N (default: 0)\n";
            cout << "  -v      Verbose output\n";
            cout << "  -n N    Number of iterations (default: 10)\n";
            cout << "  -t NAME Test configuration (default: B4_C4_V32)\n";
            cout << "          Options: B4_C4_V32, B4_C13_V9, etc.\n";
            cout << "  -h      Show this help\n";
            return 0;
        }
    }

    // Define test configuration based on name
    TestConfig config;
    if (test_name == "B4_C4_V32") {
        config = {4, 4, 32, "../../hex/B4_C4_V32", "B4_C4_V32"};
    } else if (test_name == "B4_C13_V9") {
        config = {4, 13, 9, "../../hex/B4_C13_V9", "B4_C13_V9"};
    } else if (test_name == "B4_C16_V8") {
        config = {4, 16, 8, "../../hex/B4_C16_V8", "B4_C16_V8"};
    } else if (test_name == "B1_C1_V1") {
        config = {1, 1, 1, "../../hex/B1_C1_V1", "B1_C1_V1"};
    } else if (test_name == "B2_C2_V2") {
        config = {2, 2, 2, "../../hex/B2_C2_V2", "B2_C2_V2"};
    } else {
        cerr << "ERROR: Unknown test configuration: " << test_name << endl;
        return 1;
    }

    const int B = config.B;
    const int C = config.C;
    const int V_per_row = config.V;
    const int V_TOTAL = V_per_row * NUM_ROWS;
    const int expected_results = B * C;

    cout << "\nConfiguration:" << endl;
    cout << "  Test: " << config.name << endl;
    cout << "  B=" << B << ", C=" << C << ", V/row=" << V_per_row << endl;
    cout << "  V_TOTAL=" << V_TOTAL << " (across " << NUM_ROWS << " rows)" << endl;
    cout << "  Iterations: " << num_iterations << endl;
    cout << "  Results per iteration: " << expected_results << endl;

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
        // PHASE 1: Load data to GDDR6
        //   - Weights @ lines 0-527
        //   - Activations @ lines 528-1055
        // =====================================================================
        cout << "\n========================================" << endl;
        cout << "PHASE 1: Loading data to GDDR6" << endl;
        cout << "========================================" << endl;
        cout << "Memory layout:" << endl;
        cout << "  Weights (right):     lines 0-" << (LINES_PER_BLOCK-1) << endl;
        cout << "  Activations (left):  lines " << LINE_ADDR_ACTIVATIONS
             << "-" << (LINE_ADDR_ACTIVATIONS + LINES_PER_BLOCK - 1) << endl;

        auto dma_start = chrono::high_resolution_clock::now();

        // Load and DMA both weights and activations
        for (int r = 0; r < NUM_ROWS; r++) {
            stringstream left_path, right_path;
            left_path << config.hex_dir << "/left_" << r << ".hex";
            right_path << config.hex_dir << "/right_" << r << ".hex";

            vector<uint8_t> left_data, right_data;

            if (!loadHexFile(right_path.str(), right_data)) {
                cerr << "ERROR: Failed to load right_" << r << ".hex" << endl;
                return 1;
            }
            if (!loadHexFile(left_path.str(), left_data)) {
                cerr << "ERROR: Failed to load left_" << r << ".hex" << endl;
                return 1;
            }

            // DMA weights to line 0
            uint64_t weight_addr = gddr6_dma_addr(r, LINE_ADDR_WEIGHTS * BYTES_PER_LINE);
            if (!gemm_device.dma_write(weight_addr, right_data.data(), right_data.size())) {
                cerr << "ERROR: DMA write failed for weights, row " << r << endl;
                return 1;
            }

            // DMA activations to line 528
            uint64_t act_addr = gddr6_dma_addr(r, LINE_ADDR_ACTIVATIONS * BYTES_PER_LINE);
            if (!gemm_device.dma_write(act_addr, left_data.data(), left_data.size())) {
                cerr << "ERROR: DMA write failed for activations, row " << r << endl;
                return 1;
            }

            if (verbose && r == 0) {
                cout << "  Row 0: weights @ 0x" << hex << weight_addr
                     << ", activations @ 0x" << act_addr << dec << endl;
            }
        }

        auto dma_end = chrono::high_resolution_clock::now();
        double dma_ms = chrono::duration<double, milli>(dma_end - dma_start).count();
        cout << "DMA complete: " << fixed << setprecision(2) << dma_ms << " ms" << endl;

        // =====================================================================
        // PHASE 2: Soft reset and load weights to MLP BRAM (once)
        // =====================================================================
        cout << "\n========================================" << endl;
        cout << "PHASE 2: Loading weights to MLP BRAM (once)" << endl;
        cout << "========================================" << endl;

        gemm_device.soft_reset();
        gemm_device.reset_cmd_id();
        usleep(100000);  // 100ms settle

        // Issue commands to fetch and dispatch weights
        gemm_device.begin_command_batch();

        // FETCH weights from GDDR6
        uint8_t fetch_right_id = gemm_device.fetch(LINE_ADDR_WEIGHTS, V_TOTAL, LINES_PER_BLOCK, true);
        cout << "  FETCH weights: id=" << (int)fetch_right_id
             << ", addr=" << LINE_ADDR_WEIGHTS << ", len=" << LINES_PER_BLOCK << endl;

        // DISPATCH weights to MLP BRAM
        uint8_t disp_right_id = gemm_device.dispatch(C, V_TOTAL, 0, 0, true, false);
        cout << "  DISPATCH weights: id=" << (int)disp_right_id
             << ", nv=" << C << ", ugd=" << V_TOTAL << endl;

        // WAIT for dispatch complete
        uint8_t wait_disp_id = gemm_device.waitDispatch(disp_right_id);
        cout << "  WAIT_DISP: id=" << (int)wait_disp_id << ", wait_id=" << (int)disp_right_id << endl;

        // Submit weight loading commands
        if (!gemm_device.submit_commands(verbose)) {
            cerr << "ERROR: Failed to submit weight loading commands" << endl;
            return 1;
        }

        // Wait for weight loading to complete
        int wait_iter = 0;
        while (wait_iter < 50) {
            uint32_t status = gemm_device.mmio_read32(0, 0x50);
            if ((status & 0x1) == 0) break;
            usleep(100000);
            wait_iter++;
        }

        if (wait_iter >= 50) {
            cerr << "ERROR: Timeout waiting for weight loading" << endl;
            return 1;
        }

        cout << "Weights loaded to MLP BRAM (will persist across iterations)" << endl;

        // =====================================================================
        // PHASE 3: Run N iterations (activations only)
        // =====================================================================
        cout << "\n========================================" << endl;
        cout << "PHASE 3: Running " << num_iterations << " iterations" << endl;
        cout << "========================================" << endl;

        // Store results from each iteration
        vector<vector<uint16_t>> all_results(num_iterations);

        auto iter_start = chrono::high_resolution_clock::now();

        for (int iter = 0; iter < num_iterations; iter++) {
            cout << "\n--- Iteration " << iter << " ---" << endl;

            if (!run_iteration(gemm_device, config, iter, all_results[iter], verbose)) {
                cerr << "ERROR: Iteration " << iter << " failed" << endl;
                return 1;
            }

            // Show first few results
            if (all_results[iter].size() >= 4) {
                cout << "  Results[0:3]: ";
                for (int i = 0; i < 4; i++) {
                    cout << "0x" << hex << setw(4) << setfill('0') << all_results[iter][i] << " ";
                }
                cout << dec << setfill(' ') << endl;
            }
        }

        auto iter_end = chrono::high_resolution_clock::now();
        double iter_ms = chrono::duration<double, milli>(iter_end - iter_start).count();
        cout << "\nAll iterations complete: " << fixed << setprecision(2) << iter_ms << " ms"
             << " (" << (iter_ms / num_iterations) << " ms/iter)" << endl;

        // =====================================================================
        // PHASE 4: Verify results
        // =====================================================================
        cout << "\n========================================" << endl;
        cout << "PHASE 4: Verifying results" << endl;
        cout << "========================================" << endl;

        // Load golden reference (sum across all rows)
        vector<float> golden_sum(expected_results, 0.0f);

        for (int r = 0; r < NUM_ROWS; r++) {
            stringstream golden_path;
            golden_path << config.hex_dir << "/golden_B" << B << "_C" << C << "_V" << V_per_row << "_" << r << ".hex";

            vector<uint16_t> row_golden;
            if (!loadGoldenHex(golden_path.str(), row_golden)) {
                cerr << "ERROR: Failed to load golden for row " << r << endl;
                return 1;
            }

            for (int i = 0; i < expected_results && i < (int)row_golden.size(); i++) {
                golden_sum[i] += fp16ToFloat(row_golden[i]);
            }
        }

        // Convert golden to FP16
        vector<uint16_t> golden_fp16(expected_results);
        for (int i = 0; i < expected_results; i++) {
            golden_fp16[i] = floatToFP16(golden_sum[i]);
        }

        // Check iteration 0 against golden
        cout << "\nVerifying iteration 0 against golden..." << endl;

        constexpr int LSB_TOLERANCE = 16;
        constexpr float PCT_TOLERANCE = 0.05f;
        int golden_errors = 0;

        for (int i = 0; i < expected_results; i++) {
            uint16_t hw_val = all_results[0][i];
            uint16_t gd_val = golden_fp16[i];
            uint16_t lsb_diff = (hw_val > gd_val) ? (hw_val - gd_val) : (gd_val - hw_val);

            float hw_f = fp16ToFloat(hw_val);
            float gd_f = golden_sum[i];
            float pct_diff = (fabs(gd_f) > 0.001f) ? fabs((hw_f - gd_f) / gd_f) : fabs(hw_f - gd_f) / 0.1f;

            bool is_close = (lsb_diff <= LSB_TOLERANCE) || (pct_diff <= PCT_TOLERANCE);

            if (!is_close) {
                golden_errors++;
                if (golden_errors <= 5) {
                    cout << "  MISMATCH [" << i << "]: hw=0x" << hex << hw_val
                         << " (" << fixed << setprecision(4) << hw_f << ")"
                         << ", golden=0x" << gd_val
                         << " (" << golden_sum[i] << ")" << dec << endl;
                }
            }
        }

        cout << "Golden comparison: " << (expected_results - golden_errors) << "/" << expected_results
             << " within tolerance" << endl;

        // Check all iterations match iteration 0 (weight persistence test)
        cout << "\nVerifying iteration consistency (weight persistence)..." << endl;

        int consistency_errors = 0;
        for (int iter = 1; iter < num_iterations; iter++) {
            int iter_mismatches = 0;

            for (int i = 0; i < expected_results; i++) {
                if (all_results[iter][i] != all_results[0][i]) {
                    iter_mismatches++;
                    consistency_errors++;
                    if (iter_mismatches <= 3) {
                        cout << "  MISMATCH: iter[" << iter << "][" << i << "]=0x" << hex
                             << all_results[iter][i] << " != iter[0][" << i << "]=0x"
                             << all_results[0][i] << dec << endl;
                    }
                }
            }

            if (iter_mismatches == 0) {
                cout << "  Iteration " << iter << ": MATCH (identical to iter 0)" << endl;
            } else {
                cout << "  Iteration " << iter << ": MISMATCH (" << iter_mismatches
                     << " differences)" << endl;
            }
        }

        // =====================================================================
        // Summary
        // =====================================================================
        cout << "\n========================================" << endl;
        cout << "TEST SUMMARY" << endl;
        cout << "========================================" << endl;
        cout << "Configuration: " << config.name << endl;
        cout << "Iterations:    " << num_iterations << endl;
        cout << "Results/iter:  " << expected_results << endl;
        cout << "Golden errors: " << golden_errors << endl;
        cout << "Consistency errors: " << consistency_errors << endl;

        bool passed = (golden_errors == 0) && (consistency_errors == 0);

        if (passed) {
            cout << "\nSTATUS: [PASS] - All iterations identical, golden match" << endl;
        } else if (consistency_errors == 0) {
            cout << "\nSTATUS: [PARTIAL] - Iterations consistent but golden mismatch" << endl;
        } else {
            cout << "\nSTATUS: [FAIL] - Weight persistence failure detected" << endl;
        }
        cout << "========================================" << endl;

        return passed ? 0 : 1;

    } catch (const exception& e) {
        cerr << "ERROR: " << e.what() << endl;
        return 1;
    }
}
