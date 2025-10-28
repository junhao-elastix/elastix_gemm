// ============================================================================
// MS2.0 GEMM Engine Clean Integration Test
//
// Clean version of the MS2.0 GEMM engine test with:
// - Removed commented-out code and unused functionality
// - Simplified command-line interface
// - Focused on core single-tile and multi-tile testing
//
// Author: Clean version of test_ms2_gemm_full.cpp
// Date: $(date)
// ============================================================================

#include <iostream>
#include <iomanip>
#include <fstream>
#include <sstream>
#include <cstring>
#include <cstdlib>
#include <chrono>
#include <cmath>
#include <vector>
#include "../../../eus/shell/devices/acx/vp815/api/vp815.hpp"
#include "Achronix_device.h"
#include "Achronix_util.h"

using namespace std;
using namespace achronix;

// ============================================================================
// MS2.0 GEMM Engine Register Map (BAR0)
// ============================================================================
#define ENGINE_CMD_WORD0        0x3C
#define ENGINE_CMD_WORD1        0x40
#define ENGINE_CMD_WORD2        0x44
#define ENGINE_CMD_WORD3        0x48
#define ENGINE_CMD_SUBMIT       0x4C
#define ENGINE_STATUS           0x50
#define ENGINE_RESULT_COUNT     0x54
#define ENGINE_DEBUG            0x58

// ============================================================================
// MS2.0 Microcode Opcodes
// ============================================================================
#define OPCODE_FETCH            0xF0
#define OPCODE_DISPATCH         0xF1
#define OPCODE_MATMUL           0xF2
#define OPCODE_WAIT_DISPATCH    0xF3
#define OPCODE_WAIT_MATMUL      0xF4

// ============================================================================
// Test Configuration
// ============================================================================
static int MATRIX_ROWS = 2;
static int MATRIX_COLS = 2;
static int VLOOP_SIZE = 32;

#define GDDR6_BASE_LEFT         0x0
#define GDDR6_BASE_RIGHT        0x4200
static uint64_t BRAM_RESULT_BASE = 0;

// ============================================================================
// Helper Functions
// ============================================================================

bool waitEngineIdle(VP815& device, uint32_t timeout_ms = 10000) {
    auto start = chrono::steady_clock::now();

    while (true) {
        uint32_t status = device.mmioRead32(0, ENGINE_STATUS);
        if ((status & 0x1) == 0) {
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

void issueCommand(VP815& device, uint32_t word0, uint32_t word1,
                  uint32_t word2, uint32_t word3) {
    device.mmioWrite32(0, ENGINE_CMD_WORD0, word0);
    device.mmioWrite32(0, ENGINE_CMD_WORD1, word1);
    device.mmioWrite32(0, ENGINE_CMD_WORD2, word2);
    device.mmioWrite32(0, ENGINE_CMD_WORD3, word3);
    device.mmioWrite32(0, ENGINE_CMD_SUBMIT, 0x1);
}

bool loadHexMatrix(const string& filename, vector<uint8_t>& data) {
    ifstream file(filename);
    if (!file.is_open()) {
        cerr << "ERROR: Cannot open hex file: " << filename << endl;
        return false;
    }

    data.clear();
    data.reserve(528 * 32);

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
            cerr << "ERROR: Line " << line_num << " has " << byte_count
                 << " bytes, expected 32" << endl;
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
        
        uint16_t sign = (fp16_val >> 15) & 1;
        uint16_t exp = (fp16_val >> 10) & 0x1F;
        uint16_t frac = fp16_val & 0x3FF;
        
        float result;
        if (exp == 0) {
            if (frac == 0) {
                result = sign ? -0.0f : 0.0f;
            } else {
                result = (sign ? -1.0f : 1.0f) * (frac / 1024.0f) * powf(2.0f, -14.0f);
            }
        } else if (exp == 31) {
            if (frac == 0) {
                result = sign ? -INFINITY : INFINITY;
            } else {
                result = NAN;
            }
        } else {
            result = (sign ? -1.0f : 1.0f) * (1.0f + frac / 1024.0f) * powf(2.0f, (int)exp - 15);
        }
        
        golden.push_back(result);
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

    if (exp == 0) return (sign << 15);
    if (exp == 0xFF) return (sign << 15) | 0x7C00;

    int32_t new_exp = (int32_t)exp - 127 + 15;
    if (new_exp <= 0) return (sign << 15);
    if (new_exp >= 31) return (sign << 15) | 0x7C00;

    uint32_t new_mant = (mant + 0x1000) >> 13;

    return (sign << 15) | (new_exp << 10) | (new_mant & 0x3FF);
}

// ============================================================================
// Test Configuration Structure
// ============================================================================
struct TestConfig {
    int B;
    int C;
    int V;
    const char* name;
};

// ============================================================================
// Function Declarations
// ============================================================================
bool run_single_test(VP815& device, int B, int C, int V, bool verbose);
bool run_multitile_test(VP815& device, int B, int C, int V, bool verbose);

// ============================================================================
// Main Test
// ============================================================================
int main(int argc, char* argv[]) {
    cout << "========================================" << endl;
    cout << "MS2.0 GEMM Engine (Clean)" << endl;
    cout << "========================================" << endl;

    // Parse command line arguments
    int device_id = 0;
    bool verbose = false;
    bool run_multitile = false;
    int multitile_B = 2, multitile_C = 2, multitile_V = 32;
    
    for (int i = 1; i < argc; ++i) {
        if (std::strcmp(argv[i], "-d") == 0 || (std::strcmp(argv[i], "--device") == 0 && i+1 < argc)) {
            device_id = std::stoi(argv[++i]);
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
            std::cout << "Usage: test_ms2_gemm_clean [options]\n";
            std::cout << "Options:\n";
            std::cout << "  -d N                Use device N (default: 0)\n";
            std::cout << "  -v                  Verbose output\n";
            std::cout << "  -m                  Run multi-tile test\n";
            std::cout << "  -B N                Set B parameter (default: 2)\n";
            std::cout << "  -C N                Set C parameter (default: 2)\n";
            std::cout << "  -V N                Set V parameter (default: 32)\n";
            std::cout << "  -h, --help          Show this help\n";
            return 0;
        }
    }

    try {
        cout << "\n[Initialization] Opening VP815 device " << device_id << "..." << endl;
        VP815 device(device_id);

        uint32_t bitstream_id = device.mmioRead32(0, 0x214);
        cout << "  Bitstream ID: 0x" << hex << bitstream_id << dec
             << " (Build: " << ((bitstream_id >> 24) & 0xFF) << "/"
             << ((bitstream_id >> 16) & 0xFF) << " "
             << ((bitstream_id >> 8) & 0xFF) << ":"
             << (bitstream_id & 0xFF) << ")" << endl;

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

        // Single-tile test mode
        cout << "\n========================================" << endl;
        cout << "Single-Tile Test: B=" << multitile_B << ", C=" << multitile_C << ", V=" << multitile_V << endl;
        cout << "========================================" << endl;
        
        bool result = run_single_test(device, multitile_B, multitile_C, multitile_V, verbose);
        
        cout << "\n========================================" << endl;
        cout << "SINGLE-TILE TEST " << (result ? "PASSED" : "FAILED") << endl;
        cout << "========================================" << endl;
        
        return result ? 0 : 1;

    } catch (const exception& e) {
        cerr << "ERROR: " << e.what() << endl;
        return 1;
    }
}

// ============================================================================
// Run Single Test Configuration
// ============================================================================
bool run_single_test(VP815& device, int B, int C, int V, bool verbose) {
    MATRIX_ROWS = B;
    MATRIX_COLS = C;
    VLOOP_SIZE = V;

    try {
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
        
        // Software reset
        device.mmioWrite32(0, 0x0, 0x2);
        device.mmioWrite32(0, 0x0, 0x0);

        uint32_t status_after_reset = device.mmioRead32(0, ENGINE_STATUS);
        if ((status_after_reset & 0x1) != 0) {
            cerr << "WARNING: Engine still busy after reset" << endl;
        }

        // DMA matrices to GDDR6
        if (!device.dmaWrite(GDDR6_BASE_LEFT, left_data.size(), (char*)left_data.data())) {
            cerr << "ERROR: Failed to DMA write left matrix" << endl;
            return false;
        }

        if (!device.dmaWrite(GDDR6_BASE_RIGHT, right_data.size(), (char*)right_data.data())) {
            cerr << "ERROR: Failed to DMA write right matrix" << endl;
            return false;
        }

        // FETCH commands
        uint32_t left_lines = (left_data.size() + 31) / 32;
        uint32_t right_lines = (right_data.size() + 31) / 32;

        uint32_t cmd_fetch_word0 = (0x00 << 24) | (12 << 16) | (0 << 8) | OPCODE_FETCH;
        uint32_t cmd_fetch_word1 = GDDR6_BASE_LEFT / 32;
        uint32_t cmd_fetch_word2 = left_lines;
        uint32_t cmd_fetch_word3 = 0x00000000;

        issueCommand(device, cmd_fetch_word0, cmd_fetch_word1, cmd_fetch_word2, cmd_fetch_word3);

        cmd_fetch_word0 = (0x00 << 24) | (12 << 16) | (1 << 8) | OPCODE_FETCH;
        cmd_fetch_word1 = GDDR6_BASE_RIGHT / 32;
        cmd_fetch_word2 = right_lines | (1 << 16);
        cmd_fetch_word3 = 0x00000000;

        issueCommand(device, cmd_fetch_word0, cmd_fetch_word1, cmd_fetch_word2, cmd_fetch_word3);

        // DISPATCH commands
        uint32_t man_4b_8b_n = 0;

        uint32_t cmd_disp_left_word0 = (0x00 << 24) | (8 << 16) | (3 << 8) | OPCODE_DISPATCH;
        uint32_t cmd_disp_left_word1 = (man_4b_8b_n << 22) | (128 << 11) | 0;
        issueCommand(device, cmd_disp_left_word0, cmd_disp_left_word1, 0, 0);

        uint32_t cmd_wait_disp_left_word0 = (0x00 << 24) | (3 << 16) | (0 << 8) | OPCODE_WAIT_DISPATCH;
        issueCommand(device, cmd_wait_disp_left_word0, 0, 0, 0);

        uint32_t cmd_disp_right_word0 = (0x00 << 24) | (8 << 16) | (5 << 8) | OPCODE_DISPATCH;
        uint32_t cmd_disp_right_word1 = (man_4b_8b_n << 22) | (128 << 11) | 528;
        issueCommand(device, cmd_disp_right_word0, cmd_disp_right_word1, 0, 0);

        uint32_t cmd_wait_disp_right_word0 = (0x00 << 24) | (5 << 16) | (0 << 8) | OPCODE_WAIT_DISPATCH;
        issueCommand(device, cmd_wait_disp_right_word0, 0, 0, 0);

        // MATMUL command
        uint32_t left_addr_val = 0;
        uint32_t right_addr_val = 0;
        uint32_t left_ugd_val = 128;
        uint32_t right_ugd_val = 128;
        uint32_t vec_len_val = 128;
        uint32_t flags_val = 0;
        uint32_t dim_v_val = VLOOP_SIZE;
        uint32_t dim_c_val = MATRIX_COLS;
        uint32_t dim_b_val = MATRIX_ROWS;

        uint32_t cmd_matmul_word1 = ((left_ugd_val & 0x3FF) << 22) | ((right_addr_val & 0x7FF) << 11) | (left_addr_val & 0x7FF);
        uint32_t cmd_matmul_word2 = ((dim_v_val & 0x1) << 31) | ((flags_val & 0xFF) << 23) |
                                     ((vec_len_val & 0x7FF) << 12) | ((right_ugd_val & 0x7FF) << 1) |
                                     ((left_ugd_val >> 10) & 0x1);
        uint32_t cmd_matmul_word3 = ((dim_b_val & 0xFF) << 15) | ((dim_c_val & 0xFF) << 7) | ((dim_v_val >> 1) & 0x7F);
        uint32_t cmd_matmul_word0 = (0x00 << 24) | (12 << 16) | (9 << 8) | OPCODE_MATMUL;

        issueCommand(device, cmd_matmul_word0, cmd_matmul_word1, cmd_matmul_word2, cmd_matmul_word3);

        uint32_t cmd_wait_matmul_word0 = (0x00 << 24) | (4 << 16) | (1 << 8) | OPCODE_WAIT_MATMUL;
        uint32_t cmd_wait_matmul_word1 = 0x00000000;

        issueCommand(device, cmd_wait_matmul_word0, cmd_wait_matmul_word1, 0, 0);

        if (!waitEngineIdle(device)) {
            cerr << "ERROR: WAIT_MATMUL timeout" << endl;
            return false;
        }

        // Read results
        size_t result_count_expected = MATRIX_ROWS * MATRIX_COLS;
        size_t bram_bytes_per_result = 32;
        size_t result_bytes = result_count_expected * bram_bytes_per_result;
        vector<uint8_t> bram_data(result_bytes);

        if (!device.dmaRead(BRAM_RESULT_BASE, result_bytes, (char*)bram_data.data())) {
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
            uint16_t fp16 = result_fp16[i];
            uint32_t sign = (fp16 >> 15) & 0x1;
            uint32_t exp = (fp16 >> 10) & 0x1F;
            uint32_t mant = fp16 & 0x3FF;

            if (exp == 0) {
                result_float[i] = 0.0f;
            } else if (exp == 31) {
                result_float[i] = sign ? -INFINITY : INFINITY;
            } else {
                uint32_t float_exp = exp - 15 + 127;
                uint32_t float_mant = mant << 13;
                uint32_t float_bits = (sign << 31) | (float_exp << 23) | float_mant;
                memcpy(&result_float[i], &float_bits, sizeof(float));
            }
        }
        
        if (verbose) {
            cout << "\nHardware Results vs Golden Reference:" << endl;
            cout << "Index | Hardware (Hex) | Hardware (Float) | Golden (Hex) | Golden (Float) | Match" << endl;
            cout << "------|----------------|------------------|--------------|----------------|------" << endl;
        }
        
        int matches = 0;
        for (size_t i = 0; i < result_fp16.size() && i < golden_results.size(); i++) {
            uint16_t golden_fp16 = floatToFP16(golden_results[i]);
            float diff = fabs(result_float[i] - golden_results[i]);
            float rel_err = (golden_results[i] != 0.0f) ? diff / fabs(golden_results[i]) : diff;
            bool match = (rel_err <= 0.4f);
            
            if (match) matches++;
            
            if (verbose) {
                cout << setw(5) << i << " | 0x" << hex << setw(4) << setfill('0') << result_fp16[i] << dec 
                     << "         | " << setw(15) << setprecision(6) << result_float[i]
                     << " | 0x" << hex << setw(4) << setfill('0') << golden_fp16 << dec
                        << "        | " << setw(15) << setprecision(6) << golden_results[i]
                        << " | " << (match ? "Y" : "N") << endl;
            }
        }
        
        bool validation_passed = (matches == (int)result_fp16.size());
        
        // Always report match count
        cout << "Validation: " << matches << "/" << result_fp16.size() << " matches" << endl;
        
        if (validation_passed) {
            cout << "[PASS] B" << B << "_C" << C << "_V" << V << endl;
        } else {
            cout << "[FAIL] B" << B << "_C" << C << "_V" << V << " - Validation failed" << endl;
        }

        // Soft reset
        device.mmioWrite32(0, 0x0, 0x2);
        device.mmioWrite32(0, 0x0, 0x0);

        return validation_passed;

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
        
        int num_left_tile = 128 / (B * V);
        int num_right_tile = 128 / (C * V);
        int total_tiles = num_left_tile * num_right_tile;
        int total_results = total_tiles * B * C;
        
        // Configuration info removed from verbose mode - only show result comparison
        
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
        
        // Matrix loading info removed from verbose mode
        
        stringstream golden_ss;
        golden_ss << "../../hex/golden_B" << B << "_C" << C << "_V" << V << "_multitile.hex";
        string golden_file = golden_ss.str();
        
        vector<float> golden_results;
        if (!loadGoldenReferenceHex(golden_file, golden_results, total_results)) {
            cerr << "ERROR: Failed to load golden reference: " << golden_file << endl;
            return false;
        }
        
        // Golden reference loading info removed from verbose mode
        
        // Software reset
        device.mmioWrite32(0, 0x0, 0x2);
        device.mmioWrite32(0, 0x0, 0x0);
        
        uint32_t status = device.mmioRead32(0, ENGINE_STATUS);
        if ((status & 0x1) != 0) {
            cerr << "WARNING: Engine still busy after reset" << endl;
        }
        
        // DMA write matrices to GDDR6
        if (!device.dmaWrite(GDDR6_BASE_LEFT, left_data.size(), (char*)left_data.data())) {
            cerr << "ERROR: Failed to DMA write left matrix" << endl;
            return false;
        }
        
        if (!device.dmaWrite(GDDR6_BASE_RIGHT, right_data.size(), (char*)right_data.data())) {
            cerr << "ERROR: Failed to DMA write right matrix" << endl;
            return false;
        }
        
        // FETCH LEFT
        uint32_t left_lines = 528;
        uint32_t cmd_fetch_left_word0 = (0x00 << 24) | (12 << 16) | (0 << 8) | OPCODE_FETCH;
        uint32_t cmd_fetch_left_word1 = GDDR6_BASE_LEFT / 32;
        uint32_t cmd_fetch_left_word2 = left_lines;
        issueCommand(device, cmd_fetch_left_word0, cmd_fetch_left_word1, cmd_fetch_left_word2, 0);
        
        if (!waitEngineIdle(device)) {
            cerr << "ERROR: Left FETCH timeout" << endl;
            return false;
        }
        
        // FETCH RIGHT
        uint32_t right_lines = 528;
        uint32_t cmd_fetch_right_word0 = (0x00 << 24) | (12 << 16) | (1 << 8) | OPCODE_FETCH;
        uint32_t cmd_fetch_right_word1 = GDDR6_BASE_RIGHT / 32;
        uint32_t cmd_fetch_right_word2 = right_lines | (1 << 16);
        issueCommand(device, cmd_fetch_right_word0, cmd_fetch_right_word1, cmd_fetch_right_word2, 0);
        
        if (!waitEngineIdle(device)) {
            cerr << "ERROR: Right FETCH timeout" << endl;
            return false;
        }
        
        // Process tiles
        vector<uint16_t> all_results;
        all_results.reserve(total_results);
        
        for (int left_tile_idx = 0; left_tile_idx < num_left_tile; left_tile_idx++) {
            for (int right_tile_idx = 0; right_tile_idx < num_right_tile; right_tile_idx++) {
                int tile_num = left_tile_idx * num_right_tile + right_tile_idx;
                
                uint32_t left_addr = (left_tile_idx * B * V) * 4;
                uint32_t right_addr = (right_tile_idx * C * V) * 4;
                
                // Tile address info removed from verbose mode
                
                uint32_t left_addr_val = left_addr;
                uint32_t right_addr_val = right_addr;
                uint32_t left_ugd_val = 128;
                uint32_t right_ugd_val = 128;
                uint32_t vec_len_val = 128;
                uint32_t flags_val = 0;
                uint32_t dim_v_val = V;
                uint32_t dim_c_val = C;
                uint32_t dim_b_val = B;
                
                uint32_t cmd_matmul_word1 = ((left_ugd_val & 0x3FF) << 22) | 
                                             ((right_addr_val & 0x7FF) << 11) | 
                                             (left_addr_val & 0x7FF);
                
                uint32_t cmd_matmul_word2 = ((dim_v_val & 0x1) << 31) | ((flags_val & 0xFF) << 23) |
                                             ((vec_len_val & 0x7FF) << 12) | ((right_ugd_val & 0x7FF) << 1) |
                                             ((left_ugd_val >> 10) & 0x1);
                
                uint32_t cmd_matmul_word3 = ((dim_b_val & 0xFF) << 15) | ((dim_c_val & 0xFF) << 7) | ((dim_v_val >> 1) & 0x7F);
                
                uint32_t cmd_id = tile_num;
                uint32_t cmd_matmul_word0 = (0x00 << 24) | (12 << 16) | (cmd_id << 8) | OPCODE_MATMUL;
                
                // Command encoding info removed from verbose mode
                
                issueCommand(device, cmd_matmul_word0, cmd_matmul_word1, cmd_matmul_word2, cmd_matmul_word3);
                
                if (!waitEngineIdle(device, 5000)) {
                    cerr << "ERROR: Tile " << tile_num << " timeout" << endl;
                    return false;
                }
                
                // Reset engine to clear result BRAM between tiles
                device.mmioWrite32(0, 0x0, 0x2);
                device.mmioWrite32(0, 0x0, 0x0);
                
                // Read results for this tile
                size_t tile_results = B * C;
                size_t result_bytes = tile_results * 32;
                vector<uint8_t> bram_data(result_bytes);
                
                if (!device.dmaRead(BRAM_RESULT_BASE, result_bytes, (char*)bram_data.data())) {
                    cerr << "ERROR: Failed to read tile " << tile_num << " results" << endl;
                    return false;
                }
                
                // Individual tile results removed from verbose mode
                for (size_t i = 0; i < tile_results; i++) {
                    uint8_t* line_ptr = bram_data.data() + (i * 32);
                    uint16_t fp16_val = *(uint16_t*)line_ptr;
                    all_results.push_back(fp16_val);
                }
            }
        }
        
        // All tiles complete - removed verbose output
        
        // Validate results
        int matches = 0;
        int mismatches = 0;
        
        // Convert FP16 results to float for comparison
        vector<float> result_float(all_results.size());
        for (size_t i = 0; i < all_results.size(); i++) {
            uint16_t fp16 = all_results[i];
            uint32_t sign = (fp16 >> 15) & 0x1;
            uint32_t exp = (fp16 >> 10) & 0x1F;
            uint32_t mant = fp16 & 0x3FF;
            
            if (exp == 0) {
                result_float[i] = 0.0f;
            } else if (exp == 31) {
                result_float[i] = sign ? -INFINITY : INFINITY;
            } else {
                uint32_t float_exp = exp - 15 + 127;
                uint32_t float_mant = mant << 13;
                uint32_t float_bits = (sign << 31) | (float_exp << 23) | float_mant;
                memcpy(&result_float[i], &float_bits, sizeof(float));
            }
        }
        
        if (verbose) {
            cout << "\nHardware Results vs Golden Reference:" << endl;
            cout << "Index | Hardware (Hex) | Hardware (Float) | Golden (Hex) | Golden (Float) | Match" << endl;
            cout << "------|----------------|------------------|--------------|----------------|------" << endl;
        }
        
        for (size_t i = 0; i < all_results.size() && i < golden_results.size(); i++) {
            uint16_t golden_fp16 = floatToFP16(golden_results[i]);
            float diff = fabs(result_float[i] - golden_results[i]);
            float rel_err = (golden_results[i] != 0.0f) ? diff / fabs(golden_results[i]) : diff;
            bool match = (rel_err <= 0.4f);
            
            if (match) {
                matches++;
            } else {
                mismatches++;
            }
            
            if (verbose) {
                cout << setw(5) << i << " | 0x" << hex << setw(4) << setfill('0') << all_results[i] << dec 
                     << "         | " << setw(15) << setprecision(6) << result_float[i]
                     << " | 0x" << hex << setw(4) << setfill('0') << golden_fp16 << dec
                        << "        | " << setw(15) << setprecision(6) << golden_results[i]
                        << " | " << (match ? "Y" : "N") << endl;
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
