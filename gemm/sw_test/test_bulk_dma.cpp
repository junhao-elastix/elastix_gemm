// ============================================================================
// MS2.0 Bulk DMA Address Test
//
// Tests FETCH command address parameter by:
//   1. DMA writing LEFT matrix once to block 0
//   2. DMA writing alternating RIGHT/GARBAGE blocks to GDDR6
//   3. Fetching LEFT once (persists across all GEMMs)
//   4. Fetching RIGHT from different addresses multiple times
//   5. Validating that results match golden reference for RIGHT blocks, differ for GARBAGE blocks
//
// NOTE: This test now relies on hardware auto-reset on FETCH commands to clear
//       stale data, eliminating the need for manual software reset between operations.
//
// Command-line parameters:
//   -d N / --device N: Device ID (default: 0)
//   -B N: Matrix rows (default: 4)
//   -C N: Matrix columns (default: 4)
//   -V N: V-loop size (default: 32)
//   -n N / --num_right N: Number of right fetch iterations (default: 5)
//   -v / --verbose: Verbose output
//   -h / --help: Help message
//
// Author: Bulk DMA Address Test
// Date: Generated for FETCH address parameter validation
// ============================================================================

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

// ============================================================================
// MS2.0 GEMM Engine Register Map (BAR0)
// ============================================================================
#define ENGINE_CMD_WORD0        0x3C    // Command word 0 (opcode)
#define ENGINE_CMD_WORD1        0x40    // Command word 1
#define ENGINE_CMD_WORD2        0x44    // Command word 2
#define ENGINE_CMD_WORD3        0x48    // Command word 3
#define ENGINE_CMD_SUBMIT       0x4C    // Submit trigger (write 1)
#define ENGINE_STATUS           0x50    // {CE[3:0], DC[3:0], MC[3:0], busy}
#define ENGINE_RESULT_COUNT     0x54    // FP16 result count
#define ENGINE_DEBUG            0x58    // Debug register

// ============================================================================
// MS2.0 Microcode Opcodes
// ============================================================================
#define OPCODE_FETCH            0xF0    // Fetch memory block from GDDR6
#define OPCODE_DISPATCH         0xF1    // Dispatch vectors to tiles
#define OPCODE_MATMUL           0xF2    // Matrix multiplication (TILE)
#define OPCODE_WAIT_DISPATCH    0xF3    // Wait for dispatch done
#define OPCODE_WAIT_MATMUL      0xF4    // Wait for matmul done

// ============================================================================
// Test Configuration
// ============================================================================
#define NATIVE_VEC_SIZE         128     // Native vector size
#define GFP_GROUP_SIZE          32      // GFP group size
#define MEMORY_BLOCK_SIZE       128     // Memory block size in native vectors
#define BLOCK_SIZE_BYTES        16896   // 528 lines × 32 bytes = 16896 bytes

// GDDR6 addressing
#define GDDR6_BASE_LEFT         0x0             // Left matrix base address
#define BLOCK_SIZE_LINES        528             // Lines per block

// BRAM addressing for results
static uint64_t BRAM_RESULT_BASE = 0;

// ============================================================================
// Helper Functions
// ============================================================================

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

// Generate garbage data (all bytes set to 0x01)
vector<uint8_t> generate_garbage_data(size_t size) {
    vector<uint8_t> garbage(size);
    for (size_t i = 0; i < size; i++) {
        garbage[i] = 0x01;  // All bytes set to 0x01
    }
    return garbage;
}

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
        // Skip empty lines and comments
        if (line.empty() || line[0] == '#') continue;

        // Parse hex value (4 hex digits for FP16)
        uint16_t fp16_val = stoi(line, nullptr, 16);
        
        // Convert FP16 to float
        uint16_t sign = (fp16_val >> 15) & 1;
        uint16_t exp = (fp16_val >> 10) & 0x1F;
        uint16_t frac = fp16_val & 0x3FF;
        
        float result;
        if (exp == 0) {
            if (frac == 0) {
                result = sign ? -0.0f : 0.0f;
            } else {
                // Subnormal
                result = (sign ? -1.0f : 1.0f) * (frac / 1024.0f) * powf(2.0f, -14.0f);
            }
        } else if (exp == 31) {
            if (frac == 0) {
                result = sign ? -INFINITY : INFINITY;
            } else {
                result = NAN;
            }
        } else {
            // Normal
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

// Convert float to FP16 (simple conversion for testing)
uint16_t floatToFP16(float val) {
    uint32_t bits;
    memcpy(&bits, &val, sizeof(float));

    uint32_t sign = (bits >> 31) & 0x1;
    uint32_t exp = (bits >> 23) & 0xFF;
    uint32_t mant = bits & 0x7FFFFF;

    // Handle special cases
    if (exp == 0) return (sign << 15);  // Zero
    if (exp == 0xFF) return (sign << 15) | 0x7C00;  // Inf/NaN

    // Rebias exponent
    int32_t new_exp = (int32_t)exp - 127 + 15;
    if (new_exp <= 0) return (sign << 15);  // Underflow
    if (new_exp >= 31) return (sign << 15) | 0x7C00;  // Overflow

    // Round mantissa
    uint32_t new_mant = (mant + 0x1000) >> 13;

    return (sign << 15) | (new_exp << 10) | (new_mant & 0x3FF);
}

// Compare results with tolerance
bool compareResults(const vector<float>& result, const vector<float>& golden, float tolerance = 0.01f) {
    if (result.size() != golden.size()) {
        cerr << "ERROR: Size mismatch - result: " << result.size()
             << ", golden: " << golden.size() << endl;
        return false;
    }

    for (size_t i = 0; i < result.size(); i++) {
        float diff = fabs(result[i] - golden[i]);
        float rel_err = (golden[i] != 0.0f) ? diff / fabs(golden[i]) : diff;

        if (rel_err > tolerance) {
            return false;
        }
    }

    return true;
}

// ============================================================================
// Main Test Function
// ============================================================================
bool run_bulk_dma_test(VP815& device, int B, int C, int V, int num_right, bool verbose) {
    try {
        cout << "\n========================================" << endl;
        cout << "MS2.0 Bulk DMA Address Test" << endl;
        cout << "========================================" << endl;
        cout << "Configuration:" << endl;
        cout << "  B=" << B << ", C=" << C << ", V=" << V << endl;
        cout << "  num_right=" << num_right << endl;
        cout << "  Expected results per GEMM: " << (B * C) << " (" << B << "x" << C << ")" << endl;

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

        // Generate garbage data
        vector<uint8_t> garbage_data = generate_garbage_data(BLOCK_SIZE_BYTES);

        if (verbose) {
            cout << "Loaded matrices: " << left_data.size() << " + " << right_data.size() << " bytes" << endl;
            cout << "Generated garbage: " << garbage_data.size() << " bytes (all 0x01)" << endl;
        }

        // Load golden reference
        stringstream golden_ss;
        golden_ss << "../../hex/golden_B" << B << "_C" << C << "_V" << V << ".hex";
        string golden_file = golden_ss.str();
        
        vector<float> golden_results;
        int expected_results = B * C;
        if (!loadGoldenReferenceHex(golden_file, golden_results, expected_results)) {
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
            cout << "\n[DMA Write] Writing " << (num_right + 1) << " blocks to GDDR6..." << endl;
        }

        // Block 0: LEFT matrix
        if (!device.dmaWrite(GDDR6_BASE_LEFT, left_data.size(), (char*)left_data.data())) {
            cerr << "ERROR: Failed to DMA write left matrix" << endl;
            return false;
        }
        cout << "  Block 0 (0x0): LEFT matrix (" << left_data.size() << " bytes)" << endl;

        // Blocks 1 to num_right: alternating RIGHT/GARBAGE
        for (int i = 1; i <= num_right; i++) {
            uint64_t block_addr = i * BLOCK_SIZE_BYTES;
            const vector<uint8_t>* data_to_write;
            const char* block_type;

            if (i % 2 == 1) {
                // Odd blocks: RIGHT matrix
                data_to_write = &right_data;
                block_type = "RIGHT matrix";
            } else {
                // Even blocks: GARBAGE
                data_to_write = &garbage_data;
                block_type = "GARBAGE";
            }

            if (!device.dmaWrite(block_addr, data_to_write->size(), (char*)data_to_write->data())) {
                cerr << "ERROR: Failed to DMA write block " << i << endl;
                return false;
            }

            if (verbose) {
                cout << "  Block " << i << " (0x" << hex << block_addr << dec << "): " << block_type 
                     << " (" << data_to_write->size() << " bytes)" << endl;
            }
        }

        // FETCH LEFT once (addr=0)
        if (verbose) {
            cout << "\n[FETCH] LEFT matrix (addr=0)" << endl;
        }

        uint32_t cmd_fetch_left_word0 = (0x00 << 24) | (12 << 16) | (0 << 8) | OPCODE_FETCH;
        uint32_t cmd_fetch_left_word1 = 0;  // Address in 32-byte units
        uint32_t cmd_fetch_left_word2 = BLOCK_SIZE_LINES;  // len in [15:0], fetch_right=0 in bit 16
        uint32_t cmd_fetch_left_word3 = 0x00000000;

        issueCommand(device, cmd_fetch_left_word0, cmd_fetch_left_word1, cmd_fetch_left_word2, cmd_fetch_left_word3);

        if (!waitEngineIdle(device)) {
            cerr << "ERROR: LEFT FETCH timeout" << endl;
            return false;
        }

        // Execute GEMM sequences for each right block
        vector<vector<float>> all_results(num_right);
        int passed = 0;

        for (int i = 1; i <= num_right; i++) {
            cout << "\n[GEMM #" << i << "] FETCH RIGHT from addr=" << (i * BLOCK_SIZE_LINES) 
                    << " (block " << i << (i % 2 == 1 ? " - RIGHT)" : " - GARBAGE)") << endl;

            // FETCH RIGHT (addr = i * 528)
            uint32_t fetch_addr_lines = i * BLOCK_SIZE_LINES;
            uint32_t cmd_fetch_right_word0 = (0x00 << 24) | (12 << 16) | (i << 8) | OPCODE_FETCH;
            uint32_t cmd_fetch_right_word1 = fetch_addr_lines;  // Address in 32-byte units
            uint32_t cmd_fetch_right_word2 = BLOCK_SIZE_LINES | (1 << 16);  // len in [15:0], fetch_right=1 in bit 16
            uint32_t cmd_fetch_right_word3 = 0x00000000;

            if (verbose) {
                cout << "    DEBUG: FETCH command - word1=0x" << hex << cmd_fetch_right_word1 << dec 
                     << " (addr_lines=" << fetch_addr_lines << ", bytes=0x" << hex << (fetch_addr_lines * 32) << dec << ")" << endl;
            }

            issueCommand(device, cmd_fetch_right_word0, cmd_fetch_right_word1, cmd_fetch_right_word2, cmd_fetch_right_word3);

            if (!waitEngineIdle(device)) {
                cerr << "ERROR: RIGHT FETCH timeout for block " << i << endl;
                return false;
            }

            // WORKING: Manual reset re-enabled - auto-reset approach caused timeouts
            device.mmioWrite32(0, 0x0, 0x2);  // Set bit 1 = soft reset
            device.mmioWrite32(0, 0x0, 0x0);  // Release reset

            // DISPATCH LEFT (id=3)
            uint32_t cmd_disp_left_word0 = (0x00 << 24) | (8 << 16) | (3 << 8) | OPCODE_DISPATCH;
            uint32_t cmd_disp_left_word1 = (0 << 22) | (128 << 11) | 0;  // man_4b=0, len=128, addr=0
            issueCommand(device, cmd_disp_left_word0, cmd_disp_left_word1, 0, 0);

            // WAIT_DISPATCH for left (id=3)
            uint32_t cmd_wait_disp_left_word0 = (0x00 << 24) | (3 << 16) | (0 << 8) | OPCODE_WAIT_DISPATCH;
            issueCommand(device, cmd_wait_disp_left_word0, 0, 0, 0);

            // DISPATCH RIGHT (id=5)
            uint32_t cmd_disp_right_word0 = (0x00 << 24) | (8 << 16) | (5 << 8) | OPCODE_DISPATCH;
            uint32_t cmd_disp_right_word1 = (0 << 22) | (128 << 11) | 0;  // man_4b=0, len=128, addr=0 (TWO-BRAM)
            issueCommand(device, cmd_disp_right_word0, cmd_disp_right_word1, 0, 0);

            // WAIT_DISPATCH for right (id=5)
            uint32_t cmd_wait_disp_right_word0 = (0x00 << 24) | (5 << 16) | (0 << 8) | OPCODE_WAIT_DISPATCH;
            issueCommand(device, cmd_wait_disp_right_word0, 0, 0, 0);

            // MATMUL command
            uint32_t left_addr_val = 0;
            uint32_t right_addr_val = 0;  // TWO-BRAM architecture: both start at 0
            uint32_t left_ugd_val = 128;   // Total Native Vectors in left matrix
            uint32_t right_ugd_val = 128;  // Total Native Vectors in right matrix
            uint32_t vec_len_val = 128;    // Elements per Native Vector
            uint32_t flags_val = 0;        // No special flags
            uint32_t dim_v_val = V;        // V-loop iterations
            uint32_t dim_c_val = C;        // Output columns
            uint32_t dim_b_val = B;        // Output rows

            // Pack into words following cmd_tile_s bit layout
            uint32_t cmd_matmul_word1 = ((left_ugd_val & 0x3FF) << 22) | ((right_addr_val & 0x7FF) << 11) | (left_addr_val & 0x7FF);
            uint32_t cmd_matmul_word2 = ((dim_v_val & 0x1) << 31) | ((flags_val & 0xFF) << 23) |
                                         ((vec_len_val & 0x7FF) << 12) | ((right_ugd_val & 0x7FF) << 1) |
                                         ((left_ugd_val >> 10) & 0x1);
            uint32_t cmd_matmul_word3 = ((dim_b_val & 0xFF) << 15) | ((dim_c_val & 0xFF) << 7) | ((dim_v_val >> 1) & 0x7F);
            uint32_t cmd_matmul_word0 = (0x00 << 24) | (12 << 16) | (9 << 8) | OPCODE_MATMUL;

            issueCommand(device, cmd_matmul_word0, cmd_matmul_word1, cmd_matmul_word2, cmd_matmul_word3);

            // WAIT_MATMUL
            uint32_t cmd_wait_matmul_word0 = (0x00 << 24) | (4 << 16) | (1 << 8) | OPCODE_WAIT_MATMUL;
            issueCommand(device, cmd_wait_matmul_word0, 0, 0, 0);

            if (!waitEngineIdle(device)) {
                cerr << "ERROR: MATMUL timeout for block " << i << endl;
                return false;
            }

            // Read results from BRAM
            size_t result_count_expected = B * C;
            size_t bram_bytes_per_result = 32;  // 256-bit line per result
            size_t result_bytes = result_count_expected * bram_bytes_per_result;
            vector<uint8_t> bram_data(result_bytes);

            if (!device.dmaRead(BRAM_RESULT_BASE, result_bytes, (char*)bram_data.data())) {
                cerr << "ERROR: Failed to DMA read results for block " << i << endl;
                return false;
            }

            // Extract FP16 results from LSB 16 bits of each 256-bit line
            vector<uint16_t> result_fp16(result_count_expected);
            for (size_t j = 0; j < result_count_expected; j++) {
                uint8_t* line_ptr = bram_data.data() + (j * 32);
                result_fp16[j] = *(uint16_t*)line_ptr;  // Result in LSB 16 bits
            }

            // Convert FP16 results to float
            all_results[i-1].resize(result_count_expected);
            for (size_t j = 0; j < result_count_expected; j++) {
                uint16_t fp16 = result_fp16[j];
                uint32_t sign = (fp16 >> 15) & 0x1;
                uint32_t exp = (fp16 >> 10) & 0x1F;
                uint32_t mant = fp16 & 0x3FF;

                if (exp == 0) {
                    all_results[i-1][j] = 0.0f;  // Zero or denormal
                } else if (exp == 31) {
                    all_results[i-1][j] = sign ? -INFINITY : INFINITY;  // Inf/NaN
                } else {
                    uint32_t float_exp = exp - 15 + 127;  // Rebias
                    uint32_t float_mant = mant << 13;  // Shift to float position
                    uint32_t float_bits = (sign << 31) | (float_exp << 23) | float_mant;
                    memcpy(&all_results[i-1][j], &float_bits, sizeof(float));
                }
            }

            // Display detailed results if verbose
            if (verbose) {
                cout << "  Hardware Results:" << endl;
                cout << "    Index | Hex      | Float" << endl;
                cout << "    ------|----------|----------" << endl;
                for (size_t j = 0; j < all_results[i-1].size(); j++) {
                    uint16_t result_fp16 = floatToFP16(all_results[i-1][j]);
                    cout << "    " << setw(5) << j << " | 0x" << hex << setw(4) << setfill('0') 
                         << result_fp16 << dec << setfill(' ') << " | " << setw(8) << setprecision(4) 
                         << all_results[i-1][j] << endl;
                }
                
                cout << "  Golden Reference:" << endl;
                cout << "    Index | Hex      | Float" << endl;
                cout << "    ------|----------|----------" << endl;
                for (size_t j = 0; j < golden_results.size(); j++) {
                    uint16_t golden_fp16 = floatToFP16(golden_results[j]);
                    cout << "    " << setw(5) << j << " | 0x" << hex << setw(4) << setfill('0') 
                         << golden_fp16 << dec << setfill(' ') << " | " << setw(8) << setprecision(4) 
                         << golden_results[j] << endl;
                }
            }

            // Validate results
            bool is_odd_iteration = (i % 2 == 1);
            bool matches_golden = compareResults(all_results[i-1], golden_results, 0.4f);
            
            if (is_odd_iteration) {
                // Odd iterations (1,3,5,...) should match golden
                if (matches_golden) {
                    if (verbose) {
                        cout << "  Result: PASS (matches golden reference)" << endl;
                    }
                    passed++;
                } else {
                    cout << "  Result: FAIL (should match golden reference)" << endl;
                }
            } else {
                // Even iterations (2,4,6,...) should NOT match golden
                if (!matches_golden) {
                    if (verbose) {
                        cout << "  Result: PASS (differs from golden as expected)" << endl;
                    }
                    passed++;
                } else {
                    cout << "  Result: FAIL (should differ from golden reference)" << endl;
                }
            }
        }

        // Summary
        cout << "\n========================================" << endl;
        cout << "TEST SUMMARY" << endl;
        cout << "========================================" << endl;
        cout << "Total GEMMs: " << num_right << endl;
        cout << "Passed: " << passed << "/" << num_right << endl;
        cout << "FETCH address parameter: " << (passed == num_right ? "VALIDATED" : "FAILED") << endl;
        cout << "========================================" << endl;

        return (passed == num_right);

    } catch (const exception& e) {
        cerr << "ERROR: " << e.what() << endl;
        return false;
    }
}

// ============================================================================
// Main Function
// ============================================================================
int main(int argc, char* argv[]) {
    cout << "========================================" << endl;
    cout << "MS2.0 Bulk DMA Address Test" << endl;
    cout << "========================================" << endl;

    // Parse command line arguments
    int device_id = 0;
    int B = 4;
    int C = 4;
    int V = 32;
    int num_right = 5;
    bool verbose = false;
    
    for (int i = 1; i < argc; ++i) {
        if (std::strcmp(argv[i], "-d") == 0 || std::strcmp(argv[i], "--device") == 0) {
            if (i+1 < argc) device_id = std::stoi(argv[++i]);
        } else if (std::strcmp(argv[i], "-B") == 0 && i+1 < argc) {
            B = std::stoi(argv[++i]);
        } else if (std::strcmp(argv[i], "-C") == 0 && i+1 < argc) {
            C = std::stoi(argv[++i]);
        } else if (std::strcmp(argv[i], "-V") == 0 && i+1 < argc) {
            V = std::stoi(argv[++i]);
        } else if (std::strcmp(argv[i], "-n") == 0 || std::strcmp(argv[i], "--num_right") == 0) {
            if (i+1 < argc) num_right = std::stoi(argv[++i]);
        } else if (std::strcmp(argv[i], "-v") == 0 || std::strcmp(argv[i], "--verbose") == 0) {
            verbose = true;
        } else if (std::strcmp(argv[i], "-h") == 0 || std::strcmp(argv[i], "--help") == 0) {
            std::cout << "Usage: test_bulk_dma [options]\n";
            std::cout << "Options:\n";
            std::cout << "  -d N                Use device N (default: 0)\n";
            std::cout << "  -B N                Matrix rows (default: 4)\n";
            std::cout << "  -C N                Matrix columns (default: 4)\n";
            std::cout << "  -V N                V-loop size (default: 32)\n";
            std::cout << "  -n N                Number of right fetch iterations (default: 5)\n";
            std::cout << "  -v                  Verbose output\n";
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
        // Initialize device
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

        // Run the bulk DMA test
        bool result = run_bulk_dma_test(device, B, C, V, num_right, verbose);
        
        return result ? 0 : 1;

    } catch (const exception& e) {
        cerr << "ERROR: " << e.what() << endl;
        return 1;
    }
}
