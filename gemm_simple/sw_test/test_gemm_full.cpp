// MS2.0 GEMM Engine Full Integration Test
//
// Tests complete GEMM workflow with MS2.0 engine using 5 microcode commands:
//   1. FETCH (0xF0) - Fetch matrices from GDDR6 to local buffers
//   2. DISPATCH (0xF1) - Dispatch vectors to tile buffers
//   3. WAIT_DISPATCH (0xF3) - Wait for dispatch completion
//   4. MATMUL (0xF2) - Perform matrix multiplication
//   5. WAIT_MATMUL (0xF4) - Wait for matmul completion
//
// Test Flow:
//   1. Generate test matrices (left, right) and golden reference
//   2. DMA write matrices to GDDR6
//   3. Issue FETCH command to load from GDDR6 to engine buffers
//   4. Issue DISPATCH command to distribute vectors to tiles
//   5. Poll for dispatch completion
//   6. Issue MATMUL command to compute result
//   7. Poll for matmul completion
//   8. DMA read results from BRAM
//   9. Validate against golden reference
//
// Author: Reconstructed from project memory
// Date: Tue Oct 8 2025

#include <iostream>
#include <iomanip>
#include <fstream>
#include <sstream>
#include <cstring>
#include <cstdlib>
#include <chrono>
#include <thread>
#include <cmath>
#include <vector>
#include <algorithm>
#include <limits>
#include "../../../eus/shell/devices/acx/vp815/api/vp815.hpp"
#include "Achronix_device.h"
#include "Achronix_util.h"

using namespace std;
using namespace achronix;

// MS2.0 GEMM Engine Register Map (BAR0)
#define ENGINE_CMD_WORD0        0x3C    // Command word 0 (opcode) - shifted +3 for MC payload debug regs
#define ENGINE_CMD_WORD1        0x40    // Command word 1 - shifted +3 for MC payload debug regs
#define ENGINE_CMD_WORD2        0x44    // Command word 2 - shifted +3 for MC payload debug regs
#define ENGINE_CMD_WORD3        0x48    // Command word 3 - shifted +3 for MC payload debug regs
#define ENGINE_CMD_SUBMIT       0x4C    // Submit trigger (write 1) - shifted +3 for MC payload debug regs
#define ENGINE_STATUS           0x50    // {CE[3:0], DC[3:0], MC[3:0], busy} - shifted +3 for MC payload debug regs
#define ENGINE_RESULT_COUNT     0x54    // FP16 result count - shifted +3 for MC payload debug regs
#define ENGINE_DEBUG            0x58    // Debug register - shifted +3 for MC payload debug regs

// New MC payload debug registers (Oct 10, 2025 - for dimension corruption debug)
#define MC_PAYLOAD_WORD1        0x2C    // Master control raw payload word 1
#define MC_PAYLOAD_WORD2        0x30    // Master control raw payload word 2
#define MC_PAYLOAD_WORD3        0x34    // Master control raw payload word 3

// MS2.0 Microcode Opcodes
#define OPCODE_FETCH            0xF0    // Fetch memory block from GDDR6
#define OPCODE_DISPATCH         0xF1    // Dispatch vectors to tiles
#define OPCODE_MATMUL           0xF2    // Matrix multiplication (TILE)
#define OPCODE_WAIT_DISPATCH    0xF3    // Wait for dispatch done
#define OPCODE_WAIT_MATMUL      0xF4    // Wait for matmul done

// Test Configuration
// Configurable test parameters (can be set via command-line)
// Default values (will be overridden by command-line args if provided)
static int MATRIX_ROWS = 4;       // B parameter (result rows)
static int MATRIX_COLS = 4;       // C parameter (result cols)
static int VLOOP_SIZE = 32;       // V parameter (vectors per row/col)
#define NATIVE_VEC_SIZE         128     // Native vector size (from Plan_C.md)
#define GFP_GROUP_SIZE          32      // GFP group size
#define MEMORY_BLOCK_SIZE       128     // Memory block size in native vectors

// Matrix dimensions derived from B, C, V:
// Matrix A: B rows × (128×V) columns = 4 × (128×32) = 4 × 4096
// Matrix B: (128×V) rows × C columns = (128×32) × 4 = 4096 × 4
// Result: B × C = 4 × 4

// GDDR6 addressing
#define GDDR6_BASE_LEFT         0x0             // Left matrix base address
#define GDDR6_BASE_RIGHT        0x4200          // Right matrix base address (528×32B = 16,896 = 0x4200)

// BRAM addressing for results
// Result BRAM at NAP[3][5] per placement constraint (NOC[3][5] in ace_placements.pdc)
// Result BRAM base address - calculated in main() using acx_util_nap_absolute_addr(ACX_PART_AC7t1500, 3, 5)
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

// Wait for engine to become idle (ENGINE_STATUS bit 0)
bool waitEngineIdle(VP815& device, uint32_t timeout_ms = 10000) {
    auto start = chrono::steady_clock::now();

    while (true) {
        uint32_t status = device.mmioRead32(0, ENGINE_STATUS);
        if ((status & 0x1) == 0) {  // Busy bit clear
            return true;
        }

        auto elapsed = chrono::duration_cast<chrono::milliseconds>(
            chrono::steady_clock::now() - start).count();
        if (elapsed > timeout_ms) {
            cerr << "ERROR: Engine timeout after " << timeout_ms << "ms" << endl;
            cerr << "ENGINE_STATUS: 0x" << hex << status << dec << endl;
            return false;
        }

    }
}

// Issue command to MS2.0 engine
void issueCommand(VP815& device, uint32_t word0, uint32_t word1,
                  uint32_t word2, uint32_t word3) {
    device.mmioWrite32(0, ENGINE_CMD_WORD0, word0);
    device.mmioWrite32(0, ENGINE_CMD_WORD1, word1);
    device.mmioWrite32(0, ENGINE_CMD_WORD2, word2);
    device.mmioWrite32(0, ENGINE_CMD_WORD3, word3);
    device.mmioWrite32(0, ENGINE_CMD_SUBMIT, 0x1);  // Trigger execution
}

// Load GFP8 matrix from hex file (left.hex or right.hex format)
// Format: 528 lines total, each line is exactly 256 bits (32 bytes)
//   Lines 0-15: Exponents (32 bytes per line, space-separated hex)
//   Lines 16-527: Mantissas (32 bytes per line, space-separated hex)
// This matches GDDR6 memory organization exactly.
bool loadHexMatrix(const string& filename, vector<uint8_t>& data) {
    ifstream file(filename);
    if (!file.is_open()) {
        cerr << "ERROR: Cannot open hex file: " << filename << endl;
        return false;
    }

    data.clear();
    data.reserve(528 * 32);  // 528 lines × 32 bytes = 16896 bytes

    string line;
    int line_num = 0;

    while (getline(file, line)) {
        if (line.empty()) continue;

        istringstream iss(line);
        string hex_val;
        int byte_count = 0;

        // Each line should have exactly 32 hex bytes (256 bits)
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
            cerr << "ERROR: Line " << line_num << " has " << byte_count
                 << " bytes, expected 32 (256 bits)" << endl;
            return false;
        }

        line_num++;
    }

    if (line_num != 528) {
        cerr << "ERROR: Expected 528 lines in hex file, got " << line_num << endl;
        return false;
    }

    return true;
}

// Forward declaration
uint16_t floatToFP16(float val);

// Load golden reference from file
// Load golden reference from .hex file (FP16 hex values, one per line)
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

    cout << "  Loaded golden reference: " << filename << " (" << golden.size() << " values)" << endl;
    return true;
}

// Convert float to FP16 (simple conversion for testing)
uint16_t floatToFP16(float val) {
    // Simplified FP16 conversion (can be replaced with proper conversion)
    uint32_t bits;
    memcpy(&bits, &val, sizeof(float));

    uint32_t sign = (bits >> 31) & 0x1;
    uint32_t exp = (bits >> 23) & 0xFF;
    uint32_t mant = bits & 0x7FFFFF;

    // Handle special cases
    if (exp == 0) return (sign << 15);  // Zero (float subnormals become FP16 zero)
    if (exp == 0xFF) return (sign << 15) | 0x7C00;  // Inf/NaN

    // Rebias exponent
    int32_t new_exp = (int32_t)exp - 127 + 15;
    
    // Handle subnormal FP16 output
    if (new_exp <= 0) {
        // Shift mantissa to create subnormal
        // FP16 subnormal: value = mantissa * 2^(-14) / 1024
        // We need to shift the mantissa right by (1 - new_exp) positions
        int shift = 1 - new_exp;
        if (shift >= 24) return (sign << 15);  // Too small, underflow to zero
        
        // Add implicit 1 to mantissa for normal float
        uint32_t full_mant = (1 << 23) | mant;
        // Shift to FP16 position and account for subnormal exponent
        uint32_t new_mant = (full_mant + (1 << (shift + 12))) >> (shift + 13);
        
        if (new_mant > 0x3FF) {
            // Rounding caused overflow to normal number
            return (sign << 15) | (1 << 10);
        }
        return (sign << 15) | (new_mant & 0x3FF);
    }
    
    if (new_exp >= 31) return (sign << 15) | 0x7C00;  // Overflow

    // Round mantissa
    uint32_t new_mant = (mant + 0x1000) >> 13;
    
    // Check for mantissa overflow after rounding
    if (new_mant > 0x3FF) {
        new_exp++;
        new_mant = 0;
        if (new_exp >= 31) return (sign << 15) | 0x7C00;  // Overflow
    }

    return (sign << 15) | (new_exp << 10) | (new_mant & 0x3FF);
}

// Compare results with tolerance (also accepts result_fp16 for hex display)
bool compareResults(const vector<float>& result, const vector<float>& golden,
                   const vector<uint16_t>& result_fp16, float tolerance = 0.01f) {
    if (result.size() != golden.size()) {
        cerr << "ERROR: Size mismatch - result: " << result.size()
             << ", golden: " << golden.size() << endl;
        return false;
    }

    int mismatches = 0;
    for (size_t i = 0; i < result.size(); i++) {
        float diff = fabs(result[i] - golden[i]);
        float rel_err = (golden[i] != 0.0f) ? diff / fabs(golden[i]) : diff;

        if (rel_err > tolerance) {
            if (mismatches < 10) {  // Print first 10 mismatches
                // Convert golden to FP16 for hex display
                uint16_t golden_fp16 = floatToFP16(golden[i]);
                cerr << "  Mismatch [" << i << "]: HW=0x" << hex << setw(4) << setfill('0') 
                     << result_fp16[i] << " (" << dec << result[i] 
                     << "), Golden=0x" << hex << setw(4) << setfill('0')
                     << golden_fp16 << " (" << dec << golden[i] << "), rel_err=" << rel_err << endl;
            }
            mismatches++;
        }
    }

    if (mismatches > 0) {
        cerr << "ERROR: " << mismatches << " / " << result.size()
             << " mismatches (tolerance=" << tolerance << ")" << endl;
        return false;
    }

    return true;
}

// Test Configuration Structure
struct TestConfig {
    int B;
    int C;
    int V;
    const char* name;
};

// All 9 test configurations from simulation
const TestConfig test_configs[] = {
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
const int num_tests = sizeof(test_configs) / sizeof(test_configs[0]);

// Run a single test configuration
bool run_single_test(VP815& device, const TestConfig& config, int stress_factor, bool verbose, 
                     const vector<uint8_t>& left_data, const vector<uint8_t>& right_data, vector<uint16_t>& result_fp16, bool print_time);

// Run multi-tile test (single FETCH, multiple DISPATCH/TILE)
bool run_multitile_test(VP815& device, int B, int C, int V, bool verbose);

// Main Test
int main(int argc, char* argv[]) {
    cout << "========================================" << endl;
    cout << "MS2.0 GEMM Engine" << endl;
    cout << "========================================" << endl;

    // Parse command line arguments
    int device_id = 0;
    int num_runs = 1;
    bool run_infinite = false;
    int stress_factor = 1;
    bool verbose = false;
    bool print_time = false;
    bool run_multitile = false;
    int multitile_B = 2, multitile_C = 2, multitile_V = 32;  // Default: B2_C2_V32
    
    // Simple CLI parsing
    for (int i = 1; i < argc; ++i) {
        if (std::strcmp(argv[i], "-d") == 0 || (std::strcmp(argv[i], "--device") == 0 && i+1 < argc)) {
            device_id = std::stoi(argv[++i]);
        } else if (std::strcmp(argv[i], "-n") == 0 || (std::strcmp(argv[i], "--num_runs") == 0 && i+1 < argc)) {
            num_runs = std::stoi(argv[++i]);
            if (num_runs < 1) {
                std::cerr << "Warning: -n must be >= 1. Using 1.\n";
                num_runs = 1;
            }
        } else if (std::strcmp(argv[i], "-i") == 0 || (std::strcmp(argv[i], "--run_infinite") == 0 && i+1 < argc)) {
            run_infinite = true;
        } else if (std::strcmp(argv[i], "-s") == 0 || (std::strcmp(argv[i], "--stress") == 0 && i+1 < argc)) {
            stress_factor = std::stoi(argv[++i]);
            if (stress_factor < 1) {
                std::cerr << "Warning: -s must be >= 1. Using 1.\n";
                stress_factor = 1;
            }
        } else if (std::strcmp(argv[i], "-t") == 0 || (std::strcmp(argv[i], "--print_time") == 0 && i+1 < argc)) {
            print_time = true;
        } else if (std::strcmp(argv[i], "-v") == 0 || (std::strcmp(argv[i], "--verbose") == 0 && i+1 < argc)) {
            verbose = true;
        } else if (std::strcmp(argv[i], "-m") == 0 || (std::strcmp(argv[i], "--multitile") == 0 && i+1 < argc)) {
            run_multitile = true;
        } else if (std::strcmp(argv[i], "-B") == 0 && i+1 < argc) {
            multitile_B = std::stoi(argv[++i]);
        } else if (std::strcmp(argv[i], "-C") == 0 && i+1 < argc) {
            multitile_C = std::stoi(argv[++i]);
        } else if (std::strcmp(argv[i], "-V") == 0 && i+1 < argc) {
            multitile_V = std::stoi(argv[++i]);
        } else if (std::strcmp(argv[i], "-h") == 0 || (std::strcmp(argv[i], "--help") == 0 && i+1 < argc)) {
            std::cout << "Usage: test_ms2_gemm_full [options]\n";
            std::cout << "Options:\n";
            std::cout << "  -d N                Use device N (default: 0)\n";
            std::cout << "  -n N                Run tests N times (default: 1)\n";
            std::cout << "  -i                  Run tests infinitely\n";
            std::cout << "  -s N                Repeat dispatch/matmul N times per test (default: 1)\n";
            std::cout << "  -t                  Print time\n";
            std::cout << "  -v                  Verbose output\n";
            std::cout << "  --multitile         Run multi-tile test instead of normal tests\n";
            std::cout << "  --singletile N      Run single tile test for tile N only\n";
            std::cout << "  --B N               Set B parameter for multi-tile test (default: 2)\n";
            std::cout << "  --C N               Set C parameter for multi-tile test (default: 2)\n";
            std::cout << "  --V N               Set V parameter for multi-tile test (default: 32)\n";
            std::cout << "  -h, --help          Show this help\n";
            return 0;
        } else {
            // Positional argument (device_id)
            try {
                device_id = std::stoi(argv[i]);
            } catch (const std::exception& e) {
                std::cerr << "Warning: Invalid device ID '" << argv[i] << "'. Using 0.\n";
                device_id = 0;
            }
        }
    }

    try {
        // Initialize device once
        cout << "\n[Initialization] Opening VP815 device " << device_id << "..." << endl;
        VP815 device(device_id);

        uint32_t bitstream_id = device.mmioRead32(0, 0x214);
        cout << "  Bitstream ID: 0x" << hex << bitstream_id << dec
             << " (Build: " << ((bitstream_id >> 24) & 0xFF) << "/"
             << ((bitstream_id >> 16) & 0xFF) << " "
             << ((bitstream_id >> 8) & 0xFF) << ":"
             << (bitstream_id & 0xFF) << ")" << endl;

        // Calculate Result BRAM base address
        BRAM_RESULT_BASE = acx_util_nap_absolute_addr(ACX_PART_AC7t1500, 3, 5);

        // Multi-tile test mode
        if (run_multitile) {
            cout << "\n========================================" << endl;
            cout << "MULTI-TILE TEST MODE" << endl;
            cout << "========================================" << endl;
            
            bool result = run_multitile_test(device, multitile_B, multitile_C, multitile_V, verbose);
            
            cout << "\n========================================" << endl;
            cout << "MULTI-TILE TEST " << (result ? "PASSED" : "FAILED") << endl;
            cout << "========================================" << endl;
            
            return result ? 0 : 1;
        }

        // Run all tests
        int passed = 0;
        int failed = 0;
        if (run_infinite) {
            num_runs = std::numeric_limits<int>::max();
            cout << "Running infinite mode (max " << num_runs << " iterations)" << endl;
        } else {
            cout << "Running " << num_runs << " times" << endl;
        }
        cout << "Stress factor: " << stress_factor << endl;
        cout << "----------------------------------------" << endl;
        
        // ====================================================================
        // Pre-load data once (moved from run_single_test)
        // ====================================================================
        cout << "Loading test data..." << endl;
        
        // Load matrices from hex files (Step 3)
        string left_hex = "../../hex/left.hex";
        string right_hex = "../../hex/right.hex";
        vector<uint8_t> left_data, right_data;
        
        if (!loadHexMatrix(left_hex, left_data)) {
            cerr << "ERROR: Failed to load left matrix" << endl;
            return 1;
        }
        
        if (!loadHexMatrix(right_hex, right_data)) {
            cerr << "ERROR: Failed to load right matrix" << endl;
            return 1;
        }
        
        cout << "  Loaded matrices: " << left_data.size() << " + " << right_data.size() << " bytes" << endl;
        
        // Load golden references for all test configurations
        // Use command-line parameters if provided, otherwise use hardcoded configs
        
        vector<vector<float>> golden_results;
        vector<TestConfig> active_configs;
        
        // Check if command-line parameters were provided
        bool use_cli_params = (multitile_B != 2 || multitile_C != 2 || multitile_V != 32);
        
        if (use_cli_params) {
            // Use command-line parameters
            TestConfig cli_config = {multitile_B, multitile_C, multitile_V, "CLI_CONFIG"};
            active_configs.push_back(cli_config);
            golden_results.resize(1);
            
            // Load golden reference for CLI config
            stringstream golden_ss;
            golden_ss << "../../hex/golden_B" << multitile_B << "_C" << multitile_C << "_V" << multitile_V << ".hex";
            string golden_file = golden_ss.str();
            
            int expected_results = multitile_B * multitile_C;
            if (!loadGoldenReferenceHex(golden_file, golden_results[0], expected_results)) {
                cerr << "ERROR: Failed to load golden reference: " << golden_file << endl;
                return 1;
            }
            
            cout << "Using command-line parameters: B=" << multitile_B << ", C=" << multitile_C << ", V=" << multitile_V << endl;
        } else {
            // Use hardcoded configurations
            active_configs.assign(test_configs, test_configs + num_tests);
            golden_results.resize(num_tests);
            
            for (int i = 0; i < num_tests; i++) {
                stringstream golden_ss;
                golden_ss << "../../hex/golden_" << test_configs[i].name << ".hex";
                string golden_file = golden_ss.str();
                
                int expected_results = test_configs[i].B * test_configs[i].C;
                if (!loadGoldenReferenceHex(golden_file, golden_results[i], expected_results)) {
                    cerr << "ERROR: Failed to load golden reference for " << test_configs[i].name << endl;
                    return 1;
                }
            }
        }
        
        cout << "  Loaded " << active_configs.size() << " golden references" << endl;
        cout << "----------------------------------------" << endl;
        
        static auto get_time = [](){ return std::chrono::high_resolution_clock::now(); };
        static auto to_us = [](auto d){ return std::chrono::duration_cast<std::chrono::microseconds>(d).count(); };
        static std::chrono::high_resolution_clock::time_point all_runs_start;
        static std::chrono::high_resolution_clock::time_point run_end;
        all_runs_start = get_time();
        for (int n = 0; n < num_runs; n++) {

            static std::chrono::high_resolution_clock::time_point run_start;
            run_start = get_time();

            // Collect results from all tests
            vector<vector<uint16_t>> all_results(active_configs.size());
            vector<bool> test_success(active_configs.size(), false);
            
            for (size_t i = 0; i < active_configs.size(); i++) {
                cout << "\n========================================" << endl;
                cout << "Test " << (i+1) << "/" << active_configs.size() << ": " << active_configs[i].name << endl;
                cout << "  B=" << active_configs[i].B << ", C=" << active_configs[i].C 
                     << ", V=" << active_configs[i].V << endl;
                cout << "========================================" << endl;

                if (run_single_test(device, active_configs[i], stress_factor, verbose, left_data, right_data, all_results[i], print_time)) {
                    test_success[i] = true;
                } else {
                    cout << "\n========================================" << endl;
                    cout << "Test " << (i+1) << "/" << active_configs.size() << ": " << active_configs[i].name << endl;
                    cout << "  B=" << active_configs[i].B << ", C=" << active_configs[i].C 
                         << ", V=" << active_configs[i].V << endl;
                    cout << "========================================" << endl;
                    cout << "[FAIL] " << active_configs[i].name << " - Hardware execution failed" << endl;
                    failed++;
                }
            }
            
            // Validate all results (Step 11 moved here)
            for (size_t i = 0; i < active_configs.size(); i++) {
                if (test_success[i]) {
        // Debug: Check if results were collected
        if (verbose) {
            cout << "\nDEBUG: Test " << active_configs[i].name << " collected " << all_results[i].size() << " results" << endl;
        }
                    
                    // Convert FP16 results to float for comparison
                    vector<float> result_float(all_results[i].size());
                    for (size_t j = 0; j < all_results[i].size(); j++) {
                        result_float[j] = fp16ToFloat(all_results[i][j]);
                    }
                    
                    // Display results if verbose
                    if (verbose) {
                        cout << "\nHardware Results vs Golden Reference (2D Matrix View):" << endl;
                        cout << "Matrix dimensions: B=" << active_configs[i].B << " rows × C=" << active_configs[i].C << " cols" << endl;
                        cout << "Format: [B][C] | Hardware (Hex) | Hardware (Float) | Golden (Hex) | Golden (Float) | Match" << endl;
                        cout << "--------|----------------|------------------|--------------|----------------|------" << endl;
                    }

                    int matches = 0;
                    int C = active_configs[i].C;
                    
                    for (size_t j = 0; j < all_results[i].size() && j < golden_results[i].size(); j++) {
                        uint16_t golden_fp16 = floatToFP16(golden_results[i][j]);
                        float diff = fabs(result_float[j] - golden_results[i][j]);
                        float rel_err = (golden_results[i][j] != 0.0f) ? diff / fabs(golden_results[i][j]) : diff;
                        bool match = (rel_err <= 0.4f);  // 40% tolerance
                        
                        if (match) matches++;
                        
                        if (verbose) {
                            // Convert 1D index to 2D coordinates (row-major order)
                            int row = j / C;  // B dimension (row)
                            int col = j % C;  // C dimension (column)
                            
                            if (!match) {
                            cout << "[" << setw(2) << row << "][" << setw(2) << col << "] | 0x" << hex << setw(4) << setfill('0') << all_results[i][j] << dec 
                                 << "         | " << setw(15) << setprecision(6) << result_float[j]
                                 << " | 0x" << hex << setw(4) << setfill('0') << golden_fp16 << dec
                                    << "        | " << setw(15) << setprecision(6) << golden_results[i][j]
                                    << " | " << (match ? "Y" : "N") << endl;
                            }
                        }
                    }
                    
                    bool validation_passed = (matches == (int)all_results[i].size());
                    if (validation_passed) {
                        cout << "[PASS] " << active_configs[i].name << endl;
                        passed++;
                    } else {
                        cout << "\n========================================" << endl;
                        cout << "Test " << (i+1) << "/" << active_configs.size() << ": " << active_configs[i].name << endl;
                        cout << "  B=" << active_configs[i].B << ", C=" << active_configs[i].C 
                             << ", V=" << active_configs[i].V << endl;
                        cout << "========================================" << endl;
                        cout << "[FAIL] " << active_configs[i].name << " - Validation failed (" << matches << "/" << all_results[i].size() << " matches)" << endl;
                        failed++;
                    }
                }
            }
            int print_interval = 100;
            if (num_runs > 1 && n % print_interval == 0) {
                run_end = get_time();
                cout << "Running " << n << " iterations " << endl;
                cout << "Completed " << print_interval << " iterations in " << to_us(run_end - run_start) << " us" << endl;
                cout << "Each test took " << to_us(run_end - run_start) / print_interval / num_tests << " us on average" << endl;
                cout << "----------------------------------------" << endl;
                run_start = get_time();
            }
        }
        run_end = get_time();
        cout << "Total time: " << to_us(run_end - all_runs_start) << " us" << endl;
        cout << "Each test took " << to_us(run_end - all_runs_start) / num_tests / num_runs / stress_factor << " us on average" << endl;
        cout << "----------------------------------------" << endl;
        // Summary
        cout << "\n========================================" << endl;
        cout << "TEST SUITE SUMMARY" << endl;
        cout << "========================================" << endl;
        cout << "Total tests: " << num_tests*num_runs << endl;
        cout << "Passed: " << passed << endl;
        cout << "Failed: " << failed << endl;
        cout << "========================================" << endl;

        return (failed == 0) ? 0 : 1;

    } catch (const exception& e) {
        cerr << "ERROR: " << e.what() << endl;
        return false;
    }
}

// Run Single Test Configuration
bool run_single_test(VP815& device, const TestConfig& config, int stress_factor, bool verbose, 
                     const vector<uint8_t>& left_data, const vector<uint8_t>& right_data, vector<uint16_t>& result_fp16, bool print_time) {
    // Set test parameters
    MATRIX_ROWS = config.B;
    MATRIX_COLS = config.C;
    VLOOP_SIZE = config.V;

    // Timing variables
    static auto get_time = [](){ return std::chrono::high_resolution_clock::now(); };
    static auto to_us = [](auto d){ return std::chrono::duration_cast<std::chrono::microseconds>(d).count(); };
    
    std::chrono::high_resolution_clock::time_point step_start, step_end;
    long long step_times[12] = {0}; // Array to store timing for each step

    try {
        // ====================================================================
        // Step 1: Load golden reference (MOVED TO MAIN FUNCTION)
        // ====================================================================
        // Golden reference and matrices are now pre-loaded in main()

        // ====================================================================
        // Step 2: Software reset of MS2.0 engine
        // ====================================================================
        step_start = get_time();

        // Assert engine soft reset (Control Register bit 1)
        device.mmioWrite32(0, 0x0, 0x2);  // Set bit 1 = soft reset
        device.mmioWrite32(0, 0x0, 0x0);  // Release reset

        // Verify engine is idle
        uint32_t status_after_reset = device.mmioRead32(0, ENGINE_STATUS);
        uint32_t busy_bit = status_after_reset & 0x1;
        if (busy_bit != 0) {
            cerr << "WARNING: Engine still busy after reset" << endl;
        }

        step_end = get_time();
        step_times[0] = to_us(step_end - step_start);  // Step 2 (Reset) -> index 0

        // ====================================================================
        // Step 3: Load test matrices from hex files (MOVED TO MAIN FUNCTION)
        // ====================================================================
        // Matrices are now pre-loaded in main()

        // ====================================================================
        // Step 4: DMA matrices to GDDR6
        // ====================================================================
        step_start = get_time();

        if (!device.dmaWrite(GDDR6_BASE_LEFT, left_data.size(), (char*)left_data.data())) {
            cerr << "ERROR: Failed to DMA write left matrix" << endl;
            return false;
        }

        if (!device.dmaWrite(GDDR6_BASE_RIGHT, right_data.size(), (char*)right_data.data())) {
            cerr << "ERROR: Failed to DMA write right matrix" << endl;
            return false;
        }

        step_end = get_time();
        step_times[1] = to_us(step_end - step_start);  // Step 4 (DMA Write) -> index 1

        // ====================================================================
        // Step 4.5: DMA readback verification (REMOVED for cleaner output)
        // ====================================================================    


        // ====================================================================
        // Step 5: Issue FETCH command
        // ====================================================================
        step_start = get_time();

        // FETCH command format per cmd_fetch_s structure (gemm_pkg.sv):
        //   Word0: Header [31:24]=reserved, [23:16]=len=8, [15:8]=id, [7:0]=opcode(0xF0)
        //   Word1: start_addr[31:0] - Address in units of 32 bytes (256-bit lines)
        //   Word2: len[15:0] + reserved[31:16] - Number of 32-byte lines

        // Calculate number of 32-byte lines (256-bit) needed
        uint32_t left_lines = (left_data.size() + 31) / 32;
        uint32_t right_lines = (right_data.size() + 31) / 32;

        // First FETCH for left matrix (id=0, addr=0, len=528 lines)
        // CRITICAL: cmd_fetch_s structure per gemm_pkg.sv:
        //   Word1[31:0]:  start_addr
        //   Word2[15:0]:  len (LOWER 16 bits, not upper!)
        //   Word2[16]:    fetch_right (0=left, 1=right)
        //   Word2[31:17]: reserved
        uint32_t cmd_fetch_word0 = (0x00 << 24) | (12 << 16) | (0 << 8) | OPCODE_FETCH;
        uint32_t cmd_fetch_word1 = GDDR6_BASE_LEFT / 32;  // Address in 32-byte units
        uint32_t cmd_fetch_word2 = left_lines;  // len in [15:0], fetch_right=0 in bit 16
        uint32_t cmd_fetch_word3 = 0x00000000;

        issueCommand(device, cmd_fetch_word0, cmd_fetch_word1, cmd_fetch_word2, cmd_fetch_word3);

        // Second FETCH for right matrix (id=1, addr=528, len=528 lines)
        cmd_fetch_word0 = (0x00 << 24) | (12 << 16) | (1 << 8) | OPCODE_FETCH;
        cmd_fetch_word1 = GDDR6_BASE_RIGHT / 32;  // Address in 32-byte units
        cmd_fetch_word2 = right_lines | (1 << 16);  // len in [15:0], fetch_right=1 in bit 16
        cmd_fetch_word3 = 0x00000000;

        issueCommand(device, cmd_fetch_word0, cmd_fetch_word1, cmd_fetch_word2, cmd_fetch_word3);

        step_end = get_time();
        step_times[2] = to_us(step_end - step_start);  // Step 5 (FETCH) -> index 2

        // ====================================================================
        // Step 6-9: Stress Test Loop - Repeat DISPATCH and MATMUL operations
        // ====================================================================
        step_start = get_time();
        
        for (int stress_iter = 0; stress_iter < stress_factor; stress_iter++) {
            
            // ====================================================================
            // Step 6: Issue DISPATCH commands (LEFT and RIGHT matrices)
            // ====================================================================

            // DISPATCH command encoding per cmd_disp_s structure:
            // bits [10:0]: tile_addr, [21:11]: len, [22]: man_4b_8b_n, [31:23]: reserved
            uint32_t man_4b_8b_n = 0;         // 8-bit mantissa mode

            // DISPATCH LEFT matrix (id=3, tile_addr=0, len=128)
            uint32_t cmd_disp_left_word0 = (0x00 << 24) | (8 << 16) | (3 << 8) | OPCODE_DISPATCH;
            uint32_t cmd_disp_left_word1 = (man_4b_8b_n << 22) | (128 << 11) | 0;
            issueCommand(device, cmd_disp_left_word0, cmd_disp_left_word1, 0, 0);

            // WAIT_DISPATCH for left (id=3)
            uint32_t cmd_wait_disp_left_word0 = (0x00 << 24) | (3 << 16) | (0 << 8) | OPCODE_WAIT_DISPATCH;
            issueCommand(device, cmd_wait_disp_left_word0, 0, 0, 0);

            // DISPATCH RIGHT matrix (id=5, tile_addr=528, len=128)
            uint32_t cmd_disp_right_word0 = (0x00 << 24) | (8 << 16) | (5 << 8) | OPCODE_DISPATCH;
            uint32_t cmd_disp_right_word1 = (man_4b_8b_n << 22) | (128 << 11) | 528;
            issueCommand(device, cmd_disp_right_word0, cmd_disp_right_word1, 0, 0);

            // ====================================================================
            // Step 7: Issue WAIT_DISPATCH command for right matrix
            // ====================================================================

            uint32_t cmd_wait_disp_right_word0 = (0x00 << 24) | (5 << 16) | (0 << 8) | OPCODE_WAIT_DISPATCH;
            issueCommand(device, cmd_wait_disp_right_word0, 0, 0, 0);

            // ====================================================================
            // Step 8: Issue MATMUL command
            // ====================================================================

            // MATMUL command format (cmd_header_s from gemm_pkg.sv):
            //   Word0: [31:24]=reserved, [23:16]=len, [15:8]=id, [7:0]=opcode
            //   Word1-3: Payload (cmd_tile_s structure)
            //   Word2: [31:24]=Left UGD vecs, [23:16]=Right UGD vecs, [15:8]=UGD vec size, [7:0]=Flags

            // For B=4, C=4, V=32:
            //   left_ugd_vectors = B = 4 (number of output rows)
            //   right_ugd_vectors = C = 4 (number of output cols)
            //   ugd_vector_size = V = 32 (number of native vectors per UGD vector)
            // uint32_t left_ugd_vecs = MATRIX_ROWS;   // B = 4
            // uint32_t right_ugd_vecs = MATRIX_COLS;  // C = 4
            // uint32_t ugd_vec_size = VLOOP_SIZE;     // V = 32

            // MATMUL command encoding matches cmd_tile_s structure (gemm_pkg.sv lines 112-122):
            // Master control reconstructs tile_cmd from: {payload_word3[22:0], payload_word2, payload_word1}
            // 87-bit cmd_tile_s structure:
            //   [86:79] = dim_b (8 bits)
            //   [78:71] = dim_c (8 bits)
            //   [70:63] = dim_v (8 bits)
            //   [62:55] = flags (8 bits)
            //   [54:44] = vec_len (11 bits)
            //   [43:33] = right_ugd_len (11 bits)
            //   [32:22] = left_ugd_len (11 bits)
            //   [21:11] = right_addr (11 bits)
            //   [10:0]  = left_addr (11 bits)

            // For B=4, C=4, V=32, left_addr=0, right_addr=528:
            // Full 87-bit value: 0x0404200020004004210000
            // Word1 (bits [31:0]):  0x04210000 = (528 << 11) | 0
            // Word2 (bits [63:32]): 0x00200040 = (32 << 22) | (4 << 11) | 4
            // Word3 (bits [86:64]): 0x000404   = (4 << 15) | (4 << 7) | 32 (only lower 23 bits used)

            // Build 87-bit cmd_tile_s structure manually with correct bit packing
            // CRITICAL: ugd_len and vec_len are ALWAYS 128 for full 128×128 matrices!
            // B, C, V only control OUTPUT dimensions and V-loop iterations
            uint32_t left_addr_val = 0;
            uint32_t right_addr_val = 0;  // TWO-BRAM architecture: both start at 0
            uint32_t left_ugd_val = 128;   // Total Native Vectors in left matrix (ALWAYS 128)
            uint32_t right_ugd_val = 128;  // Total Native Vectors in right matrix (ALWAYS 128)
            uint32_t vec_len_val = 128;    // Elements per Native Vector (ALWAYS 128)
            uint32_t flags_val = 0;        // No special flags
            uint32_t dim_v_val = VLOOP_SIZE;     // V-loop iterations (controls output accumulation)
            uint32_t dim_c_val = MATRIX_COLS;    // Output columns
            uint32_t dim_b_val = MATRIX_ROWS;    // Output rows

            // Pack into words following cmd_tile_s bit layout:
            // Word1 [31:0]: left_addr[10:0], right_addr[10:0], left_ugd[9:0]
            uint32_t cmd_matmul_word1 = ((left_ugd_val & 0x3FF) << 22) | ((right_addr_val & 0x7FF) << 11) | (left_addr_val & 0x7FF);

            // Word2 [63:32]: left_ugd[10], right_ugd[10:0], vec_len[10:0], flags[7:0], dim_v[0]
            uint32_t cmd_matmul_word2 = ((dim_v_val & 0x1) << 31) | ((flags_val & 0xFF) << 23) |
                                         ((vec_len_val & 0x7FF) << 12) | ((right_ugd_val & 0x7FF) << 1) |
                                         ((left_ugd_val >> 10) & 0x1);

            // Word3 [86:64]: dim_v[7:1], dim_c[7:0], dim_b[7:0] (only 23 bits used)
            uint32_t cmd_matmul_word3 = ((dim_b_val & 0xFF) << 15) | ((dim_c_val & 0xFF) << 7) | ((dim_v_val >> 1) & 0x7F);

            uint32_t cmd_matmul_word0 = (0x00 << 24) | (12 << 16) | (9 << 8) | OPCODE_MATMUL;  // reserved, len=12, id=9, opcode=0xF2

            issueCommand(device, cmd_matmul_word0, cmd_matmul_word1, cmd_matmul_word2, cmd_matmul_word3);

            // ====================================================================
            // Step 9: Issue WAIT_MATMUL command
            // ====================================================================

            uint32_t cmd_wait_matmul_word0 = (0x00 << 24) | (4 << 16) | (1 << 8) | OPCODE_WAIT_MATMUL;  // reserved, len, id=1, opcode
            uint32_t cmd_wait_matmul_word1 = 0x00000000;  // ID=0

            issueCommand(device, cmd_wait_matmul_word0, cmd_wait_matmul_word1, 0, 0);

            if (!waitEngineIdle(device)) {
                cerr << "ERROR: WAIT_MATMUL timeout" << endl;
                return false;
            }

            if (stress_factor > 100 && stress_iter % 100 == 0) {
                cout << "Stress test iteration " << stress_iter << " of " << stress_factor << " completed" << endl;
            }
        } // End of stress test loop
        
        step_end = get_time();
        step_times[3] = to_us(step_end - step_start);  // Step 6-9 (Stress Loop) -> index 3

        // ====================================================================
        // Step 10: Read results from BRAM (after all stress iterations)
        // ====================================================================
        step_start = get_time();

        // Result matrix is B×C = 4×4 = 16 FP16 values
        // With simple adapter: 1 FP16 per 256-bit BRAM line (in LSB 16 bits)
        size_t result_count_expected = MATRIX_ROWS * MATRIX_COLS;
        size_t bram_bytes_per_result = 32;  // 256-bit line per result
        size_t result_bytes = result_count_expected * bram_bytes_per_result;
        vector<uint8_t> bram_data(result_bytes);

        if (!device.dmaRead(BRAM_RESULT_BASE, result_bytes, (char*)bram_data.data())) {
            cerr << "ERROR: Failed to DMA read results" << endl;
            return false;
        }

        // Extract FP16 results from LSB 16 bits of each 256-bit line
        result_fp16.resize(result_count_expected);
        for (size_t i = 0; i < result_count_expected; i++) {
            uint8_t* line_ptr = bram_data.data() + (i * 32);
            result_fp16[i] = *(uint16_t*)line_ptr;  // Result in LSB 16 bits
        }

        step_end = get_time();
        step_times[4] = to_us(step_end - step_start);  // Step 10 (Read Results) -> index 4

        // Convert FP16 results to float for comparison
        vector<float> result_float(MATRIX_ROWS * MATRIX_COLS);
        for (size_t i = 0; i < result_fp16.size(); i++) {
            result_float[i] = fp16ToFloat(result_fp16[i]);
        }

        // ====================================================================
        // Step 12: Soft reset engine before exit
        // ====================================================================
        step_start = get_time();

        // Assert engine soft reset (Control Register bit 1)
        device.mmioWrite32(0, 0x0, 0x2);  // Set bit 1 = soft reset
        device.mmioWrite32(0, 0x0, 0x0);  // Release reset

        step_end = get_time();
        step_times[5] = to_us(step_end - step_start);  // Step 12 (Final Reset) -> index 5

        // Print step timing summary
        if (verbose || print_time) {
            cout << "\nStep Timing Summary (us):" << endl;
            cout << "Step 2  (Reset Engine):    " << setw(8) << step_times[0] << " us" << endl;
            cout << "Step 4  (DMA Write):       " << setw(8) << step_times[1] << " us" << endl;
            cout << "Step 5  (FETCH):           " << setw(8) << step_times[2] << " us" << endl;
            cout << "Step 6-9(Stress Loop):     " << setw(8) << step_times[3] << " us" << endl;
            cout << "Step 10 (Read Results):    " << setw(8) << step_times[4] << " us" << endl;
            cout << "Step 12 (Final Reset):     " << setw(8) << step_times[5] << " us" << endl;
            
            long long total_time = 0;
            for (int i = 0; i < 6; i++) {
                total_time += step_times[i];
            }
            cout << "Total Test Time:           " << setw(8) << total_time << " us" << endl;
            cout << "----------------------------------------" << endl;
        }

        // Return success (validation done in main)
        return true;

    } catch (const exception& e) {
        cerr << "ERROR: " << e.what() << endl;
        return false;
    }
}

bool run_multitile_test(VP815& device, int B, int C, int V, bool verbose) {
    try {
        cout << "\n========================================" << endl;
        cout << "Multi-Tile Test: B=" << B << ", C=" << C << ", V=" << V << endl;
        cout << "========================================" << endl;
        
        // Calculate tile counts
        int num_left_tile = 128 / (B * V);
        int num_right_tile = 128 / (C * V);
        int total_tiles = num_left_tile * num_right_tile;
        int total_results = total_tiles * B * C;
        
        if (verbose) {
            cout << "Configuration:" << endl;
            cout << "  Left tiles: " << num_left_tile << " (each uses " << B*V << " NVs)" << endl;
            cout << "  Right tiles: " << num_right_tile << " (each uses " << C*V << " NVs)" << endl;
            cout << "  Total tiles: " << total_tiles << endl;
            cout << "  Expected results: " << total_results << " (" << total_tiles << " tiles x " << B*C << " results/tile)" << endl;
        }
        
        // Load matrices from hex files
        string left_hex = "../../hex/left.hex";
        string right_hex = "../../hex/right.hex";
        vector<uint8_t> left_data, right_data;
        
        if (!loadHexMatrix(left_hex, left_data)) {
            cerr << "ERROR: Failed to load left matrix" << endl;
            return false;
        }
        
        if (!loadHexMatrix(right_hex, right_data)) {
            cerr << "ERROR: Failed to load right matrix" << endl;
            return false;
        }
        
        if (verbose) {
            cout << "Loaded matrices: " << left_data.size() << " + " << right_data.size() << " bytes" << endl;
        }
        
        // Load golden reference
        stringstream golden_ss;
        golden_ss << "../../hex/golden_B" << B << "_C" << C << "_V" << V << "_multitile.hex";
        string golden_file = golden_ss.str();
        
        vector<float> golden_results;
        if (!loadGoldenReferenceHex(golden_file, golden_results, total_results)) {
            cerr << "ERROR: Failed to load golden reference: " << golden_file << endl;
            return false;
        }
        
        if (verbose) {
            cout << "Loaded golden reference: " << golden_results.size() << " results" << endl;
        }
        
        // Software reset
        if (verbose) {
            cout << "\n[Step 1] Resetting engine..." << endl;
        }
        device.mmioWrite32(0, 0x0, 0x2);
        device.mmioWrite32(0, 0x0, 0x0);
        
        uint32_t status = device.mmioRead32(0, ENGINE_STATUS);
        if ((status & 0x1) != 0) {
            cerr << "WARNING: Engine still busy after reset" << endl;
        }
        
        // DMA write matrices to GDDR6
        if (verbose) {
            cout << "\n[Step 2] Writing matrices to GDDR6..." << endl;
        }
        if (!device.dmaWrite(GDDR6_BASE_LEFT, left_data.size(), (char*)left_data.data())) {
            cerr << "ERROR: Failed to DMA write left matrix" << endl;
            return false;
        }
        
        if (!device.dmaWrite(GDDR6_BASE_RIGHT, right_data.size(), (char*)right_data.data())) {
            cerr << "ERROR: Failed to DMA write right matrix" << endl;
            return false;
        }
        if (verbose) {
            cout << "  DMA write complete" << endl;
        }
        
        // FETCH LEFT (once for all left tiles)
        if (verbose) {
            cout << "\n[Step 3] FETCH left matrix (128 NVs)..." << endl;
        }
        uint32_t left_lines = 528;
        uint32_t cmd_fetch_left_word0 = (0x00 << 24) | (12 << 16) | (0 << 8) | OPCODE_FETCH;
        uint32_t cmd_fetch_left_word1 = GDDR6_BASE_LEFT / 32;
        uint32_t cmd_fetch_left_word2 = left_lines;  // fetch_right=0 (left buffer)
        issueCommand(device, cmd_fetch_left_word0, cmd_fetch_left_word1, cmd_fetch_left_word2, 0);
        
        if (!waitEngineIdle(device)) {
            cerr << "ERROR: Left FETCH timeout" << endl;
            return false;
        }
        if (verbose) {
            cout << "  Left FETCH complete" << endl;
        }
        
        // FETCH RIGHT (once for all right tiles)
        if (verbose) {
            cout << "\n[Step 4] FETCH right matrix (128 NVs)..." << endl;
        }
        uint32_t right_lines = 528;
        uint32_t cmd_fetch_right_word0 = (0x00 << 24) | (12 << 16) | (1 << 8) | OPCODE_FETCH;
        uint32_t cmd_fetch_right_word1 = GDDR6_BASE_RIGHT / 32;
        uint32_t cmd_fetch_right_word2 = right_lines | (1 << 16);  // fetch_right=1 (right buffer)
        issueCommand(device, cmd_fetch_right_word0, cmd_fetch_right_word1, cmd_fetch_right_word2, 0);
        
        if (!waitEngineIdle(device)) {
            cerr << "ERROR: Right FETCH timeout" << endl;
            return false;
        }
        if (verbose) {
            cout << "  Right FETCH complete" << endl;
        }
        
        // Process tiles and read results after each tile to see individual results
        if (verbose) {
            cout << "\n[Step 5] Processing " << total_tiles << " tiles..." << endl;
        }
        vector<uint16_t> all_results;
        all_results.reserve(total_results);
        
        for (int left_tile_idx = 0; left_tile_idx < num_left_tile; left_tile_idx++) {
            for (int right_tile_idx = 0; right_tile_idx < num_right_tile; right_tile_idx++) {
                int tile_num = left_tile_idx * num_right_tile + right_tile_idx;
                
                // Calculate tile addresses (in lines)
                // Each NV uses 4 lines, so addr = nv_idx * 4
                uint32_t left_addr = (left_tile_idx * B * V) * 4;
                uint32_t right_addr = (right_tile_idx * C * V) * 4;
                
                // Print tile addresses only if verbose
                if (verbose) {
                    cout << "  Tile " << tile_num << " addrs: left=" << left_addr 
                         << " (" << (left_addr/4) << " NVs), right=" << right_addr 
                         << " (" << (right_addr/4) << " NVs)" << endl;
                }
                
                // MATMUL command - Use BRAM addresses without offset (TWO-BRAM style)
                // NOTE: Due to 7-bit NV index truncation in BCv controller, we cannot use +528 offset
                //       Both left and right start from 0 in their respective address spaces
                uint32_t left_addr_val = left_addr;
                uint32_t right_addr_val = right_addr;  // NO +528 offset
                uint32_t left_ugd_val = 128;
                uint32_t right_ugd_val = 128;
                uint32_t vec_len_val = 128;
                uint32_t flags_val = 0;
                uint32_t dim_v_val = V;
                uint32_t dim_c_val = C;
                uint32_t dim_b_val = B;
                
                // Use SAME bit layout as single-tile test for consistency:
                // Word1 [31:0]: left_addr[10:0], right_addr[10:0], left_ugd[9:0]
                uint32_t cmd_matmul_word1 = ((left_ugd_val & 0x3FF) << 22) | 
                                             ((right_addr_val & 0x7FF) << 11) | 
                                             (left_addr_val & 0x7FF);
                
                // Word2 [63:32]: left_ugd[10], right_ugd[10:0], vec_len[10:0], flags[7:0], dim_v[0]
                uint32_t cmd_matmul_word2 = ((dim_v_val & 0x1) << 31) | ((flags_val & 0xFF) << 23) |
                                             ((vec_len_val & 0x7FF) << 12) | ((right_ugd_val & 0x7FF) << 1) |
                                             ((left_ugd_val >> 10) & 0x1);
                
                // Word3 [86:64]: dim_v[7:1], dim_c[7:0], dim_b[7:0] (only 23 bits used)
                uint32_t cmd_matmul_word3 = ((dim_b_val & 0xFF) << 15) | ((dim_c_val & 0xFF) << 7) | ((dim_v_val >> 1) & 0x7F);
                
                uint32_t cmd_id = tile_num;
                uint32_t cmd_matmul_word0 = (0x00 << 24) | (12 << 16) | (cmd_id << 8) | OPCODE_MATMUL;
                
                // Debug: Show command encoding only if verbose
                if (verbose) {
                    cout << "    Command: word0=0x" << hex << cmd_matmul_word0 << dec 
                         << " word1=0x" << hex << cmd_matmul_word1 << dec
                         << " (left_addr=" << left_addr_val << ", right_addr=" << right_addr_val << ")" << endl;
                }
                
                issueCommand(device, cmd_matmul_word0, cmd_matmul_word1, cmd_matmul_word2, cmd_matmul_word3);
                
                // Wait for this tile to complete
                if (!waitEngineIdle(device, 5000)) {
                    cerr << "ERROR: Tile " << tile_num << " timeout" << endl;
                    return false;
                }
                
                // Reset engine to clear result BRAM between tiles
                device.mmioWrite32(0, 0x0, 0x2);  // Set bit 1 = soft reset
                device.mmioWrite32(0, 0x0, 0x0);  // Release reset
                
                // Read results for this tile immediately
                size_t tile_results = B * C;
                size_t result_bytes = tile_results * 32;  // 256-bit line per result
                vector<uint8_t> bram_data(result_bytes);
                
                if (!device.dmaRead(BRAM_RESULT_BASE, result_bytes, (char*)bram_data.data())) {
                    cerr << "ERROR: Failed to read tile " << tile_num << " results" << endl;
                    return false;
                }
                
                // Extract FP16 results for this tile
                if (verbose) {
                    cout << "  Tile " << tile_num << " results: ";
                }
                for (size_t i = 0; i < tile_results; i++) {
                    uint8_t* line_ptr = bram_data.data() + (i * 32);
                    uint16_t fp16_val = *(uint16_t*)line_ptr;
                    all_results.push_back(fp16_val);
                    if (verbose) {
                        cout << "0x" << hex << fp16_val << dec << " ";
                    }
                }
                if (verbose) {
                    cout << endl;
                }
            }
        }
        
        if (verbose) {
            cout << "\nAll tiles complete! Collected " << all_results.size() << " results" << endl;
        }
        
        // Validate results
        if (verbose) {
            cout << "\n[Step 7] Validating results..." << endl;
        }
        int matches = 0;
        int mismatches = 0;
        
        for (size_t i = 0; i < all_results.size() && i < golden_results.size(); i++) {
            // Convert FP16 to float
            float result_float = fp16ToFloat(all_results[i]);

            // Compare with tolerance
            float diff = fabs(result_float - golden_results[i]);
            float rel_err = (golden_results[i] != 0.0f) ? diff / fabs(golden_results[i]) : diff;
            bool match = (rel_err <= 0.4f);  // 40% tolerance
            
            if (match) {
                matches++;
            } else {
                mismatches++;
                uint16_t golden_fp16 = floatToFP16(golden_results[i]);
                cerr << "  Mismatch [" << i << "]: HW=0x" << hex << setw(4) << setfill('0')
                     << all_results[i] << " (" << dec << result_float
                     << "), Golden=0x" << hex << setw(4) << setfill('0')
                     << golden_fp16 << " (" << dec << golden_results[i] << "), rel_err=" << rel_err << endl;
            }
        }
        
        cout << "Validation: " << matches << "/" << all_results.size() << " matches" << endl;
        
        if (matches == (int)all_results.size()) {
            cout << "\n[PASS] Multi-tile test passed!" << endl;
            return true;
        } else {
            cout << "\n[FAIL] Multi-tile test failed (" << mismatches << " mismatches)" << endl;
            return false;
        }
        
    } catch (const exception& e) {
        cerr << "ERROR: " << e.what() << endl;
        return false;
    }
}
