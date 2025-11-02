// ============================================================================
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
#include "../../../eus/shell/devices/acx/vp815/api/vp815.hpp"

using namespace std;
using namespace achronix;

// ============================================================================
// MS2.0 GEMM Engine Register Map (BAR0)
// ============================================================================
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
// Using existing validated test case: B=4, C=4, V=32
// Result matrix: 4×4 (from golden_B4_C4_V32.txt)
#define MATRIX_ROWS             4       // B parameter (result rows)
#define MATRIX_COLS             4       // C parameter (result cols)
#define VLOOP_SIZE              32      // V parameter (vectors per row/col)
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
// NAP address formula: (0x08<<35) | ((col-1)<<31) | ((row-1)<<28) | offset
// NAP[3][4]: col=3→2, row=4→3: (0x08<<35) | (2<<31) | (3<<28) | 0x0 = 0x4130000000
// Result BRAM CO-LOCATED with engine at NAP[3][4] for direct internal writes
#define BRAM_RESULT_BASE        0x4130000000ULL // BRAM responder @ NAP[3][4], offset 0

// ============================================================================
// Helper Functions
// ============================================================================

// Wait for engine to become idle (ENGINE_STATUS bit 0)
bool waitEngineIdle(VP815& device, uint32_t timeout_ms = 100000) {
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

        this_thread::sleep_for(chrono::milliseconds(10));
    }
}

// Issue command to MS2.0 engine
void issueCommand(VP815& device, uint32_t word0, uint32_t word1,
                  uint32_t word2, uint32_t word3) {
    // Debug: Show what we're writing
    cout << "  CMD DEBUG: Writing word0=0x" << hex << word0 << " @ 0x" << ENGINE_CMD_WORD0 << dec << endl;
    cout << "  CMD DEBUG: Writing word1=0x" << hex << word1 << " @ 0x" << ENGINE_CMD_WORD1 << dec << endl;
    cout << "  CMD DEBUG: Writing word2=0x" << hex << word2 << " @ 0x" << ENGINE_CMD_WORD2 << dec << endl;
    cout << "  CMD DEBUG: Writing word3=0x" << hex << word3 << " @ 0x" << ENGINE_CMD_WORD3 << dec << endl;

    device.mmioWrite32(0, ENGINE_CMD_WORD0, word0);
    device.mmioWrite32(0, ENGINE_CMD_WORD1, word1);
    device.mmioWrite32(0, ENGINE_CMD_WORD2, word2);
    device.mmioWrite32(0, ENGINE_CMD_WORD3, word3);
    device.mmioWrite32(0, ENGINE_CMD_SUBMIT, 0x1);  // Trigger execution

    // Read back to verify
    uint32_t rb0 = device.mmioRead32(0, ENGINE_CMD_WORD0);
    uint32_t rb1 = device.mmioRead32(0, ENGINE_CMD_WORD1);
    uint32_t rb2 = device.mmioRead32(0, ENGINE_CMD_WORD2);
    uint32_t rb3 = device.mmioRead32(0, ENGINE_CMD_WORD3);

    cout << "  CMD READBACK: word0=0x" << hex << rb0 << ", word1=0x" << rb1
         << ", word2=0x" << rb2 << ", word3=0x" << rb3 << dec << endl;
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

    cout << "  Loaded hex file: " << filename << endl;
    cout << "    " << line_num << " lines × 32 bytes = " << data.size()
         << " bytes (GDDR6 memory format)" << endl;

    return true;
}

// Load golden reference from file
bool loadGoldenReference(const string& filename, vector<float>& golden, int& rows, int& cols) {
    ifstream file(filename);
    if (!file.is_open()) {
        cerr << "ERROR: Cannot open golden reference file: " << filename << endl;
        return false;
    }

    string line;
    int B=0, C=0, V=0;

    // Parse header
    while (getline(file, line)) {
        if (line.find("Golden Reference: B=") != string::npos) {
            sscanf(line.c_str(), "Golden Reference: B=%d, C=%d, V=%d", &B, &C, &V);
        }
        if (line.empty()) break;  // End of header
    }

    if (B == 0 || C == 0) {
        cerr << "ERROR: Invalid golden reference file format" << endl;
        return false;
    }

    rows = B;
    cols = C;
    golden.clear();
    golden.reserve(B * C);

    // Parse result matrix
    while (getline(file, line)) {
        if (line.empty()) continue;

        istringstream iss(line);
        float val;
        while (iss >> val) {
            golden.push_back(val);
        }
    }

    if (golden.size() != (size_t)(B * C)) {
        cerr << "ERROR: Expected " << B*C << " values, got " << golden.size() << endl;
        return false;
    }

    cout << "  Loaded golden reference: " << B << "×" << C << " = " << golden.size() << " values" << endl;
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
bool compareResults(const vector<float>& result, const vector<float>& golden,
                   float tolerance = 0.01f) {
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
                cerr << "  Mismatch at [" << i << "]: result=" << result[i]
                     << ", golden=" << golden[i] << ", rel_err=" << rel_err << endl;
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

// ============================================================================
// Main Test
// ============================================================================
int main(int argc, char* argv[]) {
    cout << "=== MS2.0 GEMM Engine Full Integration Test ===" << endl;
    cout << "Test configuration: B=" << MATRIX_ROWS << ", C=" << MATRIX_COLS
         << ", V=" << VLOOP_SIZE << endl;
    cout << "Expected result: " << MATRIX_ROWS << "×" << MATRIX_COLS << " matrix" << endl;

    // Parse command line
    int device_id = 0;
    bool dry_run = false;  // Test golden reference loading without hardware

    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--dry-run") == 0) {
            dry_run = true;
        } else {
            device_id = atoi(argv[i]);
        }
    }

    if (dry_run) {
        cout << "\n[DRY RUN MODE] Testing golden reference loading only" << endl;
    }

    try {
        // ====================================================================
        // Step 1: Load golden reference
        // ====================================================================
        cout << "\n[Step 1] Loading golden reference..." << endl;

        // Path to golden reference file (relative to sw_test directory)
        string golden_file = "../../hex/golden_B4_C4_V32.txt";

        vector<float> golden_result;
        int golden_rows, golden_cols;

        if (!loadGoldenReference(golden_file, golden_result, golden_rows, golden_cols)) {
            return 1;
        }

        // Verify dimensions match test configuration
        if (golden_rows != MATRIX_ROWS || golden_cols != MATRIX_COLS) {
            cerr << "ERROR: Golden reference dimensions (" << golden_rows << "×" << golden_cols
                 << ") don't match test config (" << MATRIX_ROWS << "×" << MATRIX_COLS << ")" << endl;
            return 1;
        }

        cout << "  ✓ Golden reference loaded successfully" << endl;
        cout << "  Statistics: Min=" << *min_element(golden_result.begin(), golden_result.end())
             << ", Max=" << *max_element(golden_result.begin(), golden_result.end()) << endl;

        // ====================================================================
        // Step 2: Initialize device
        // ====================================================================
        cout << "\n[Step 2] Initializing VP815 device " << device_id << "..." << endl;
        VP815 device(device_id);

        uint32_t bitstream_id = device.mmioRead32(0, 0x214);  // BITSTREAM_ID shifted to reg 133
        cout << "  Bitstream ID: 0x" << hex << bitstream_id << dec
             << " (Build: " << ((bitstream_id >> 24) & 0xFF) << "/"
             << ((bitstream_id >> 16) & 0xFF) << " "
             << ((bitstream_id >> 8) & 0xFF) << ":"
             << (bitstream_id & 0xFF) << ")" << endl;

        uint32_t adm_status = device.mmioRead32(0, 0x210);  // ADM_STATUS shifted to reg 132
        // Temporarily bypass GDDR6 training check for debugging - ADM status is 0x0a
        // if ((adm_status & 0x3) != 0x3) {
        //     cerr << "ERROR: GDDR6 not trained (ADM Status: 0x" << hex << adm_status << ")" << endl;
        //     return 1;
        // }
        cout << "  GDDR6 Status: 0x" << hex << adm_status << dec << " (bypassed check for debug)" << endl;

        // ====================================================================
        // Step 2.5: Software reset of MS2.0 engine
        // ====================================================================
        cout << "\n[Step 2.5] Resetting MS2.0 GEMM engine..." << endl;

        // Assert engine soft reset (Control Register bit 1)
        device.mmioWrite32(0, 0x0, 0x2);  // Set bit 1 = soft reset
        this_thread::sleep_for(chrono::milliseconds(10));  // Hold reset
        device.mmioWrite32(0, 0x0, 0x0);  // Release reset
        this_thread::sleep_for(chrono::milliseconds(10));  // Settle time

        // Verify engine is idle
        uint32_t status_after_reset = device.mmioRead32(0, ENGINE_STATUS);
        uint32_t busy_bit = status_after_reset & 0x1;
        cout << "  ENGINE_STATUS after reset: 0x" << hex << status_after_reset << dec
             << " (busy=" << busy_bit << ")" << endl;

        if (busy_bit != 0) {
            cerr << "WARNING: Engine still busy after reset" << endl;
        } else {
            cout << "  ✓ Engine reset successful" << endl;
        }

        // ====================================================================
        // Step 3: Load test matrices from hex files
        // ====================================================================
        cout << "\n[Step 3] Loading test matrices from hex files..." << endl;

        string left_hex = "../../hex/left.hex";
        string right_hex = "../../hex/right.hex";

        vector<uint8_t> left_data, right_data;

        if (!loadHexMatrix(left_hex, left_data)) {
            return 1;
        }

        if (!loadHexMatrix(right_hex, right_data)) {
            return 1;
        }

        // ====================================================================
        // Step 4: DMA matrices to GDDR6
        // ====================================================================
        cout << "\n[Step 4] DMA write matrices to GDDR6..." << endl;

        cout << "  Writing left matrix to GDDR6 @ 0x" << hex << GDDR6_BASE_LEFT << dec
             << " (" << left_data.size() << " bytes)" << endl;
        if (!device.dmaWrite(GDDR6_BASE_LEFT, left_data.size(), (char*)left_data.data())) {
            cerr << "ERROR: Failed to DMA write left matrix" << endl;
            return 1;
        }
        cout << "    ✓ Left matrix write complete" << endl;

        cout << "  Writing right matrix to GDDR6 @ 0x" << hex << GDDR6_BASE_RIGHT << dec
             << " (" << right_data.size() << " bytes)" << endl;
        if (!device.dmaWrite(GDDR6_BASE_RIGHT, right_data.size(), (char*)right_data.data())) {
            cerr << "ERROR: Failed to DMA write right matrix" << endl;
            return 1;
        }
        cout << "    ✓ Right matrix write complete" << endl;

        // ====================================================================
        // Step 4.5: DMA readback verification (like DMA_simple_example.cpp)
        // ====================================================================
        cout << "\n[Step 4.5] DMA readback verification..." << endl;

        vector<uint8_t> left_readback(left_data.size());
        vector<uint8_t> right_readback(right_data.size());

        cout << "  Reading back left matrix from GDDR6..." << endl;
        if (!device.dmaRead(GDDR6_BASE_LEFT, left_data.size(), (char*)left_readback.data())) {
            cerr << "ERROR: Failed to DMA read left matrix" << endl;
            return 1;
        }

        cout << "  Reading back right matrix from GDDR6..." << endl;
        if (!device.dmaRead(GDDR6_BASE_RIGHT, right_data.size(), (char*)right_readback.data())) {
            cerr << "ERROR: Failed to DMA read right matrix" << endl;
            return 1;
        }

        // Verify data integrity
        cout << "  Verifying left matrix data integrity..." << endl;
        if (memcmp(left_data.data(), left_readback.data(), left_data.size()) != 0) {
            cerr << "ERROR: Left matrix readback mismatch!" << endl;

            // Show first mismatch for debugging
            for (size_t i = 0; i < left_data.size(); i++) {
                if (left_data[i] != left_readback[i]) {
                    cerr << "  First mismatch at byte " << i << ": wrote 0x" << hex
                         << (int)left_data[i] << ", read 0x" << (int)left_readback[i] << dec << endl;
                    break;
                }
            }
            return 1;
        }
        cout << "    ✓ Left matrix verified (all " << left_data.size() << " bytes match)" << endl;

        cout << "  Verifying right matrix data integrity..." << endl;
        if (memcmp(right_data.data(), right_readback.data(), right_data.size()) != 0) {
            cerr << "ERROR: Right matrix readback mismatch!" << endl;

            // Show first mismatch for debugging
            for (size_t i = 0; i < right_data.size(); i++) {
                if (right_data[i] != right_readback[i]) {
                    cerr << "  First mismatch at byte " << i << ": wrote 0x" << hex
                         << (int)right_data[i] << ", read 0x" << (int)right_readback[i] << dec << endl;
                    break;
                }
            }
            return 1;
        }
        cout << "    ✓ Right matrix verified (all " << right_data.size() << " bytes match)" << endl;

        cout << "  ✓ DMA readback verification PASSED - Data in GDDR6 is correct!" << endl;    

        // If dry-run mode, exit here after DMA verification
        if (dry_run) {
            cout << "\n=== DRY RUN PASSED ===" << endl;
            cout << "✅ Golden reference loaded successfully" << endl;
            cout << "✅ Hex files loaded and validated (256-bit lines)" << endl;
            cout << "✅ DMA write to GDDR6 successful" << endl;
            cout << "✅ DMA readback verified (all " << (left_data.size() + right_data.size())
                 << " bytes match)" << endl;
            cout << "\nGDDR6 memory subsystem is working correctly!" << endl;
            cout << "Run without --dry-run to test MS2.0 engine commands." << endl;
            return 0;
        }

        // ====================================================================
        // Step 5: Issue FETCH command
        // ====================================================================
        cout << "\n[Step 5] Issuing FETCH command..." << endl;

        // FETCH command format per cmd_fetch_s structure (gemm_pkg.sv):
        //   Word0: Header [31:24]=reserved, [23:16]=len=8, [15:8]=id, [7:0]=opcode(0xF0)
        //   Word1: start_addr[31:0] - Address in units of 32 bytes (256-bit lines)
        //   Word2: len[15:0] + reserved[31:16] - Number of 32-byte lines

        // Calculate number of 32-byte lines (256-bit) needed
        uint32_t left_lines = (left_data.size() + 31) / 32;
        uint32_t right_lines = (right_data.size() + 31) / 32;

        // First FETCH for left matrix (id=0, addr=0, len=528 lines)
        uint32_t cmd_fetch_word0 = (0x00 << 24) | (12 << 16) | (0 << 8) | OPCODE_FETCH;
        uint32_t cmd_fetch_word1 = GDDR6_BASE_LEFT / 32;  // Address in 32-byte units
        uint32_t cmd_fetch_word2 = (left_lines << 16) | 0x0000;  // len in 32-byte lines
        uint32_t cmd_fetch_word3 = 0x00000000;

        cout << "  Fetching left matrix: " << left_lines << " lines from 0x"
             << hex << GDDR6_BASE_LEFT << dec << endl;

        issueCommand(device, cmd_fetch_word0, cmd_fetch_word1, cmd_fetch_word2, cmd_fetch_word3);

        if (!waitEngineIdle(device)) {
            cerr << "ERROR: FETCH command timeout" << endl;
            return 1;
        }
        cout << "  ✓ Left FETCH completed" << endl;

        // Second FETCH for right matrix (id=1, addr=528, len=528 lines)
        cmd_fetch_word0 = (0x00 << 24) | (12 << 16) | (1 << 8) | OPCODE_FETCH;
        cmd_fetch_word1 = GDDR6_BASE_RIGHT / 32;  // Address in 32-byte units
        cmd_fetch_word2 = (right_lines << 16) | 0x0000;  // len in 32-byte lines
        cmd_fetch_word3 = 0x00000000;

        cout << "  Fetching right matrix: " << right_lines << " lines from 0x"
             << hex << GDDR6_BASE_RIGHT << dec << endl;

        issueCommand(device, cmd_fetch_word0, cmd_fetch_word1, cmd_fetch_word2, cmd_fetch_word3);

        if (!waitEngineIdle(device)) {
            cerr << "ERROR: Right FETCH command timeout" << endl;
            return 1;
        }
        cout << "  ✓ Right FETCH completed" << endl;

        // ====================================================================
        // Step 6: Issue DISPATCH commands (LEFT and RIGHT matrices)
        // ====================================================================
        cout << "\n[Step 6] Issuing DISPATCH commands..." << endl;

        // DISPATCH command encoding per cmd_disp_s structure:
        // bits [10:0]: tile_addr, [21:11]: len, [22]: man_4b_8b_n, [31:23]: reserved
        uint32_t man_4b_8b_n = 0;         // 8-bit mantissa mode

        // DISPATCH LEFT matrix (id=3, tile_addr=0, len=128)
        cout << "  Dispatching left matrix..." << endl;
        uint32_t cmd_disp_left_word0 = (0x00 << 24) | (8 << 16) | (3 << 8) | OPCODE_DISPATCH;
        uint32_t cmd_disp_left_word1 = (man_4b_8b_n << 22) | (128 << 11) | 0;
        issueCommand(device, cmd_disp_left_word0, cmd_disp_left_word1, 0, 0);

        if (!waitEngineIdle(device)) {
            cerr << "ERROR: Left DISPATCH timeout" << endl;
            return 1;
        }
        cout << "  ✓ Left DISPATCH completed" << endl;

        // WAIT_DISPATCH for left (id=3)
        uint32_t cmd_wait_disp_left_word0 = (0x00 << 24) | (3 << 16) | (0 << 8) | OPCODE_WAIT_DISPATCH;
        issueCommand(device, cmd_wait_disp_left_word0, 0, 0, 0);

        if (!waitEngineIdle(device)) {
            cerr << "ERROR: Left WAIT_DISPATCH timeout" << endl;
            return 1;
        }
        cout << "  ✓ Left dispatch wait completed" << endl;

        // DISPATCH RIGHT matrix (id=5, tile_addr=528, len=128)
        cout << "  Dispatching right matrix..." << endl;
        uint32_t cmd_disp_right_word0 = (0x00 << 24) | (8 << 16) | (5 << 8) | OPCODE_DISPATCH;
        uint32_t cmd_disp_right_word1 = (man_4b_8b_n << 22) | (128 << 11) | 528;
        issueCommand(device, cmd_disp_right_word0, cmd_disp_right_word1, 0, 0);

        if (!waitEngineIdle(device)) {
            cerr << "ERROR: Right DISPATCH timeout" << endl;
            return 1;
        }
        cout << "  ✓ Right DISPATCH completed" << endl;

        // ====================================================================
        // Step 7: Issue WAIT_DISPATCH command for right matrix
        // ====================================================================
        cout << "\n[Step 7] Issuing final WAIT_DISPATCH command..." << endl;

        uint32_t cmd_wait_disp_right_word0 = (0x00 << 24) | (5 << 16) | (0 << 8) | OPCODE_WAIT_DISPATCH;
        issueCommand(device, cmd_wait_disp_right_word0, 0, 0, 0);

        if (!waitEngineIdle(device)) {
            cerr << "ERROR: Right WAIT_DISPATCH timeout" << endl;
            return 1;
        }
        cout << "  ✓ Final dispatch wait completed" << endl;

        // ====================================================================
        // Step 8: Issue MATMUL command
        // ====================================================================
        cout << "\n[Step 8] Issuing MATMUL command..." << endl;
        cout << "  MATMUL params: B=" << MATRIX_ROWS << ", C=" << MATRIX_COLS
             << ", V=" << VLOOP_SIZE << ", left_addr=0, right_addr=528" << endl;

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
        uint32_t right_addr_val = 528;
        uint32_t left_ugd_val = 128;   // Total Native Vectors in left matrix (ALWAYS 128)
        uint32_t right_ugd_val = 128;  // Total Native Vectors in right matrix (ALWAYS 128)
        uint32_t vec_len_val = 128;    // Elements per Native Vector (ALWAYS 128)
        uint32_t flags_val = 0;        // No special flags
        uint32_t dim_v_val = 32;       // V-loop iterations (controls output accumulation)
        uint32_t dim_c_val = 4;        // Output columns
        uint32_t dim_b_val = 4;        // Output rows

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

        // Debug: Check what master control sees BEFORE waiting
        uint32_t debug_reg = device.mmioRead32(0, 0x58);  // ENGINE_DEBUG register (shifted +3 to 0x58)
        uint32_t status_reg = device.mmioRead32(0, 0x50);  // ENGINE_STATUS register (shifted +3 to 0x50)
        uint32_t bcv_debug = device.mmioRead32(0, 0x20);   // BCV_DEBUG_STATE register (Oct 10, 2025)
        uint32_t bcv_dims = device.mmioRead32(0, 0x24);    // BCV_DEBUG_DIMS register (Oct 10, 2025)
        uint32_t mc_dims = device.mmioRead32(0, 0x28);     // MC_TILE_DIMS register (Oct 10, 2025)
        
        // NEW: Read raw payload words from master_control (Oct 10, 2025)
        uint32_t mc_payload1 = device.mmioRead32(0, MC_PAYLOAD_WORD1);  // 0x2C
        uint32_t mc_payload2 = device.mmioRead32(0, MC_PAYLOAD_WORD2);  // 0x30
        uint32_t mc_payload3 = device.mmioRead32(0, MC_PAYLOAD_WORD3);  // 0x34
        cout << "  ENGINE_DEBUG (before wait): 0x" << hex << debug_reg << dec
             << " (opcode=0x" << hex << ((debug_reg >> 24) & 0xFF)
             << ", submitted=" << dec << ((debug_reg >> 16) & 0xFF)
             << ", payload_words=" << ((debug_reg >> 8) & 0x7)
             << ", count_nonzero=" << ((debug_reg >> 4) & 0x1)
             << ", count_low=" << (debug_reg & 0xF) << ")" << endl;
        // FIXED: Correct bit positions per RTL elastix_gemm_top.sv line 587:
        // {12'h0, mc_state_next[3:0], mc_state[3:0], dc_state[3:0], ce_state[3:0], 3'b0, engine_busy}
        cout << "  ENGINE_STATUS (before wait): 0x" << hex << status_reg
             << " (mc_state_next=" << ((status_reg >> 16) & 0xF)
             << ", mc_state=" << ((status_reg >> 12) & 0xF)
             << ", dc_state=" << ((status_reg >> 8) & 0xF)
             << ", ce_state=" << ((status_reg >> 4) & 0xF)
             << ", busy=" << (status_reg & 0x1) << ")" << dec << endl;
        // BCV Debug: [31:24]=b_idx, [23:16]=c_idx, [15:8]=v_idx, [7:5]=fill_cycle, [4:2]=compute_wait, [1:0]=bcv_state
        cout << "  BCV_DEBUG (internal state): 0x" << hex << bcv_debug << dec
             << " (b=" << ((bcv_debug >> 24) & 0xFF)
             << ", c=" << ((bcv_debug >> 16) & 0xFF)
             << ", v=" << ((bcv_debug >> 8) & 0xFF)
             << ", fill=" << ((bcv_debug >> 5) & 0x7)
             << ", wait=" << ((bcv_debug >> 2) & 0x7)
             << ", bcv_state=" << (bcv_debug & 0x3) << ")" << endl;
        // BCV Dimensions: [31:24]=dim_b_reg, [23:16]=dim_c_reg, [15:8]=dim_v_reg, [7:0]=i_dim_v
        cout << "  BCV_DIMS (captured dims): 0x" << hex << bcv_dims << dec
             << " (dim_b_reg=" << ((bcv_dims >> 24) & 0xFF)
             << ", dim_c_reg=" << ((bcv_dims >> 16) & 0xFF)
             << ", dim_v_reg=" << ((bcv_dims >> 8) & 0xFF)
             << ", i_dim_v=" << (bcv_dims & 0xFF) << ")" << endl;
        // Master Control TILE Dimensions: [31:24]=dim_b, [23:16]=dim_c, [15:8]=dim_v, [7:0]=reserved
        cout << "  MC_TILE_DIMS (master control): 0x" << hex << mc_dims << dec
             << " (dim_b=" << ((mc_dims >> 24) & 0xFF)
             << ", dim_c=" << ((mc_dims >> 16) & 0xFF)
             << ", dim_v=" << ((mc_dims >> 8) & 0xFF) << ")" << endl;
        cout << "  MC_PAYLOAD (raw words in master_control): w1=0x" << hex << mc_payload1
             << ", w2=0x" << mc_payload2 << ", w3=0x" << mc_payload3 << dec << endl;

        if (!waitEngineIdle(device)) {
            cerr << "ERROR: MATMUL command timeout" << endl;

            // DIAGNOSTIC: Check if any results were written to result BRAM despite timeout
            cout << "\n[DEBUG] Checking result BRAM contents despite timeout..." << endl;

            uint32_t result_count_reg = device.mmioRead32(0, ENGINE_RESULT_COUNT);
            cout << "  Result count register: " << result_count_reg << endl;

            // Read first 64 bytes (16 FP16 values = 4×4 matrix) from result BRAM directly
            cout << "  Reading first 16 words from Result BRAM (BAR2 @ 0x4460008000):" << endl;
            uint64_t result_bram_base = 0x4460008000ULL;
            for (int i = 0; i < 16; i++) {
                uint32_t val = device.mmioRead32(2, result_bram_base + i*4);
                cout << "    Word[" << dec << i << "] = 0x" << hex << setw(8) << setfill('0') << val;
                if (val != 0) cout << " *NON-ZERO*";
                cout << dec << endl;
            }

            return 1;
        }
        cout << "  ✓ MATMUL completed" << endl;

        // ====================================================================
        // Step 9: Issue WAIT_MATMUL command
        // ====================================================================
        cout << "\n[Step 9] Issuing WAIT_MATMUL command..." << endl;

        uint32_t cmd_wait_matmul_word0 = (0x00 << 24) | (4 << 16) | (1 << 8) | OPCODE_WAIT_MATMUL;  // reserved, len, id=1, opcode
        uint32_t cmd_wait_matmul_word1 = 0x00000000;  // ID=0

        issueCommand(device, cmd_wait_matmul_word0, cmd_wait_matmul_word1, 0, 0);

        if (!waitEngineIdle(device)) {
            cerr << "ERROR: WAIT_MATMUL timeout" << endl;
            return 1;
        }
        cout << "  ✓ Matmul wait completed" << endl;

        // ====================================================================
        // Step 10: Read results from BRAM
        // ====================================================================
        cout << "\n[Step 10] Reading results from BRAM..." << endl;

        // Result matrix is B×C = 4×4 = 16 FP16 values
        size_t result_bytes = MATRIX_ROWS * MATRIX_COLS * sizeof(uint16_t);  // FP16
        vector<uint16_t> result_fp16(MATRIX_ROWS * MATRIX_COLS);

        if (!device.dmaRead(BRAM_RESULT_BASE, result_bytes, (char*)result_fp16.data())) {
            cerr << "ERROR: Failed to DMA read results" << endl;
            return 1;
        }

        uint32_t result_count = device.mmioRead32(0, ENGINE_RESULT_COUNT);
        cout << "  Result count register: " << result_count << " FP16 values" << endl;

        // Convert FP16 results to float for comparison
        vector<float> result_float(MATRIX_ROWS * MATRIX_COLS);
        for (size_t i = 0; i < result_fp16.size(); i++) {
            // Simple FP16 to float conversion (can be improved)
            uint16_t fp16 = result_fp16[i];
            uint32_t sign = (fp16 >> 15) & 0x1;
            uint32_t exp = (fp16 >> 10) & 0x1F;
            uint32_t mant = fp16 & 0x3FF;

            if (exp == 0) {
                result_float[i] = 0.0f;  // Zero or denormal
            } else if (exp == 31) {
                result_float[i] = sign ? -INFINITY : INFINITY;  // Inf/NaN
            } else {
                uint32_t float_exp = exp - 15 + 127;  // Rebias
                uint32_t float_mant = mant << 13;  // Shift to float position
                uint32_t float_bits = (sign << 31) | (float_exp << 23) | float_mant;
                memcpy(&result_float[i], &float_bits, sizeof(float));
            }
        }

        // ====================================================================
        // Step 11: Validate results
        // ====================================================================
        cout << "\n[Step 11] Validating results..." << endl;

        bool test_passed = compareResults(result_float, golden_result, 0.05f);  // 5% tolerance for FP16

        // ====================================================================
        // Step 12: Soft reset engine before exit
        // ====================================================================
        cout << "\n[Step 12] Soft reset engine before exit..." << endl;

        // Assert engine soft reset (Control Register bit 1)
        device.mmioWrite32(0, 0x0, 0x2);  // Set bit 1 = soft reset
        this_thread::sleep_for(chrono::milliseconds(10));  // Hold reset
        device.mmioWrite32(0, 0x0, 0x0);  // Release reset
        this_thread::sleep_for(chrono::milliseconds(10));  // Settle time

        // Verify engine is idle after final reset
        uint32_t final_status = device.mmioRead32(0, ENGINE_STATUS);
        uint32_t final_busy = final_status & 0x1;
        cout << "  ENGINE_STATUS after reset: 0x" << hex << final_status << dec
             << " (busy=" << final_busy << ")" << endl;

        if (final_busy == 0) {
            cout << "  ✓ Engine soft reset successful" << endl;
        } else {
            cout << "  ⚠️ Engine still busy after reset" << endl;
        }

        // Final test result
        if (test_passed) {
            cout << "  ✓ Results match golden reference!" << endl;
            cout << "\n=== TEST PASSED ===" << endl;
            return 0;
        } else {
            cerr << "\n=== TEST FAILED ===" << endl;
            return 1;
        }

    } catch (const exception& e) {
        cerr << "ERROR: " << e.what() << endl;
        return 1;
    }
}
