// ------------------------------------------------------------------
// Dispatcher BRAM Verification Test
//
// Purpose: Verify FETCH → dispatcher_bram path works correctly
//
// Test Flow:
//   1. Generate known test pattern (incremental values)
//   2. DMA pattern to GDDR6 @ address 0x0
//   3. Issue FETCH command (GDDR6 → dispatcher BRAM)
//   4. Issue MATMUL command with readback stub
//      - Stub reads dispatcher BRAM sequentially
//      - Outputs to result_bram_writer
//   5. DMA results from Result BRAM
//   6. Verify results match expected pattern
//
// Expected: If FETCH works correctly, readback data == original pattern
//
// Author: Temporary test for MS2.0 integration
// Date: Wed Oct 8 2025
// ------------------------------------------------------------------

#include <iostream>
#include <iomanip>
#include <vector>
#include <cstring>
#include <cstdint>
#include <chrono>
#include <thread>
#include "vp815.hpp"

using namespace std;
using namespace achronix;

// ===================================================================
// Register Definitions
// ===================================================================
#define ENGINE_CMD_WORD0    10
#define ENGINE_CMD_WORD1    11
#define ENGINE_CMD_WORD2    12
#define ENGINE_CMD_WORD3    13
#define ENGINE_CMD_SUBMIT   14
#define ENGINE_STATUS       15
#define ENGINE_DEBUG        16

#define MC_STATE_MASK       0x0000000F
#define DC_STATE_MASK       0x000000F0
#define CE_STATE_MASK       0x00000F00

// MS2.0 Opcodes
#define OPCODE_FETCH        0xF0
#define OPCODE_MATMUL       0xF2

// Memory addresses
#define GDDR6_BASE          0x00000000ULL     // GDDR6 test location
#define RESULT_BRAM_BASE    0x4460008000ULL   // Result BRAM base

// Test parameters
#define TEST_LINES          16    // Test with 16 BRAM lines (512 bytes)
#define BYTES_PER_LINE      32    // 256 bits = 32 bytes
#define TOTAL_TEST_BYTES    (TEST_LINES * BYTES_PER_LINE)

// ===================================================================
// Helper Functions
// ===================================================================

void waitForIdle(unique_ptr<VP815>& device) {
    int timeout = 1000;
    uint32_t status;
    while (timeout-- > 0) {
        device->mmioRead32(0, ENGINE_STATUS * 4, status);
        uint32_t mc_state = status & MC_STATE_MASK;
        if (mc_state == 0) {
            return;
        }
        this_thread::sleep_for(chrono::microseconds(100));
    }
    cerr << "ERROR: Timeout waiting for master_control IDLE" << endl;
}

void issueCommand(unique_ptr<VP815>& device, uint32_t w0, uint32_t w1, uint32_t w2, uint32_t w3) {
    // Write command words
    device->mmioWrite32(0, ENGINE_CMD_WORD0 * 4, w0);
    device->mmioWrite32(0, ENGINE_CMD_WORD1 * 4, w1);
    device->mmioWrite32(0, ENGINE_CMD_WORD2 * 4, w2);
    device->mmioWrite32(0, ENGINE_CMD_WORD3 * 4, w3);

    // Submit command
    device->mmioWrite32(0, ENGINE_CMD_SUBMIT * 4, 0x1);
    this_thread::sleep_for(chrono::microseconds(10));  // Hold submit
    device->mmioWrite32(0, ENGINE_CMD_SUBMIT * 4, 0x0);
}

// ===================================================================
// Main Test
// ===================================================================
int main() {
    cout << "===========================================================" << endl;
    cout << "  Dispatcher BRAM Verification Test" << endl;
    cout << "===========================================================" << endl;

    // Step 1: Initialize device
    cout << "\nStep 1: Initialize VP815 device..." << endl;
    unique_ptr<VP815> device;
    try {
        device = make_unique<VP815>(0);
        cout << "  ✅ Device initialized" << endl;
    } catch (const exception& e) {
        cerr << "ERROR: Failed to initialize device: " << e.what() << endl;
        return 1;
    }

    // Wait for idle state
    waitForIdle(device);

    // Step 2: Generate test pattern
    cout << "\nStep 2: Generate test pattern..." << endl;
    vector<uint8_t> test_pattern(TOTAL_TEST_BYTES);

    // Create incremental pattern: byte[i] = i % 256
    for (size_t i = 0; i < TOTAL_TEST_BYTES; i++) {
        test_pattern[i] = (uint8_t)(i % 256);
    }

    cout << "  Generated " << TOTAL_TEST_BYTES << " bytes" << endl;
    cout << "  Pattern: test_pattern[i] = i % 256" << endl;
    cout << "  First 32 bytes: ";
    for (int i = 0; i < 32; i++) {
        cout << hex << setw(2) << setfill('0') << (int)test_pattern[i] << " ";
    }
    cout << dec << endl;

    // Step 3: DMA test pattern to GDDR6
    cout << "\nStep 3: DMA test pattern to GDDR6 @ 0x0..." << endl;
    device->dmaWrite(GDDR6_BASE, test_pattern.size(), (char*)test_pattern.data());
    cout << "  ✅ DMA write complete (" << test_pattern.size() << " bytes)" << endl;

    // Step 4: Issue FETCH command
    cout << "\nStep 4: Issue FETCH command (GDDR6 → dispatcher BRAM)..." << endl;

    uint32_t cmd_fetch_word0 = (OPCODE_FETCH << 0) | (1 << 8) | (12 << 16);
    uint32_t cmd_fetch_word1 = 0x00000000;  // GDDR6 address 0 (in 128B chunks)
    uint32_t cmd_fetch_word2 = TEST_LINES;  // Number of lines to fetch
    uint32_t cmd_fetch_word3 = 0x00000000;

    issueCommand(device, cmd_fetch_word0, cmd_fetch_word1, cmd_fetch_word2, cmd_fetch_word3);

    cout << "  FETCH command issued:" << endl;
    cout << "    GDDR6 address: 0x" << hex << 0 << dec << endl;
    cout << "    Lines to fetch: " << TEST_LINES << endl;

    // Wait for fetch to complete
    cout << "  Waiting for FETCH completion..." << endl;
    this_thread::sleep_for(chrono::milliseconds(10));  // FETCH should complete in ~2µs
    waitForIdle(device);
    cout << "  ✅ FETCH complete" << endl;

    // Step 5: Issue MATMUL command (readback mode)
    cout << "\nStep 5: Issue MATMUL (readback mode)..." << endl;
    cout << "  compute_engine will read BRAM[0-" << (TEST_LINES-1) << "] and output to results" << endl;

    uint32_t cmd_tile_word0 = (OPCODE_MATMUL << 0) | (2 << 8) | (12 << 16);
    uint32_t cmd_tile_word1 = (0 << 21) | (0 << 10) | (0 << 2) | 0;  // left_addr=0, right_addr=0
    uint32_t cmd_tile_word2 = (0 << 21) | (TEST_LINES << 13) | (0 << 5) | 0;  // dim_b=TEST_LINES
    uint32_t cmd_tile_word3 = 0x00000000;

    issueCommand(device, cmd_tile_word0, cmd_tile_word1, cmd_tile_word2, cmd_tile_word3);

    cout << "  MATMUL command issued (readback):" << endl;
    cout << "    BRAM start address: 0" << endl;
    cout << "    Lines to read: " << TEST_LINES << endl;

    // Wait for compute to complete
    cout << "  Waiting for readback completion..." << endl;
    this_thread::sleep_for(chrono::milliseconds(50));  // Readback ~16 lines
    waitForIdle(device);
    cout << "  ✅ Readback complete" << endl;

    // Step 6: DMA results from Result BRAM
    cout << "\nStep 6: DMA results from Result BRAM..." << endl;

    // Result BRAM has FP24 values packed by result_bram_writer
    // 16 FP16 per 256-bit line, but readback outputs 11 FP24 per BRAM line
    // For 16 BRAM lines: 16 × 11 = 176 FP24 values = 176 × 3 = 528 bytes
    size_t result_bytes = TEST_LINES * 11 * 3;  // 11 FP24 per line, 3 bytes per FP24
    vector<uint8_t> results(result_bytes);

    device->dmaRead(RESULT_BRAM_BASE, results.size(), (char*)results.data());
    cout << "  ✅ DMA read complete (" << results.size() << " bytes)" << endl;

    // Step 7: Verify results
    cout << "\nStep 7: Verify results..." << endl;

    int mismatches = 0;
    int first_mismatch = -1;

    // Compare FP24 results with original pattern
    // Each BRAM line (32 bytes) → 11 FP24 values (264 bits, some overlap)
    for (int line = 0; line < TEST_LINES; line++) {
        for (int fp24_idx = 0; fp24_idx < 11; fp24_idx++) {
            int result_offset = (line * 11 + fp24_idx) * 3;
            int pattern_offset = line * BYTES_PER_LINE + fp24_idx * 3;

            if (pattern_offset + 2 >= TOTAL_TEST_BYTES) break;

            // Extract 24 bits from results
            uint32_t result_val = (results[result_offset + 0] << 0) |
                                  (results[result_offset + 1] << 8) |
                                  (results[result_offset + 2] << 16);

            // Extract 24 bits from original pattern
            uint32_t expected_val = (test_pattern[pattern_offset + 0] << 0) |
                                    (test_pattern[pattern_offset + 1] << 8) |
                                    (test_pattern[pattern_offset + 2] << 16);

            if (result_val != expected_val) {
                mismatches++;
                if (first_mismatch < 0) {
                    first_mismatch = line * 11 + fp24_idx;
                    cout << "  ❌ Mismatch at FP24[" << first_mismatch << "]:" << endl;
                    cout << "     Expected: 0x" << hex << setw(6) << setfill('0') << expected_val << endl;
                    cout << "     Got:      0x" << setw(6) << setfill('0') << result_val << dec << endl;
                }
            }
        }
    }

    // Summary
    cout << "\n===========================================================" << endl;
    cout << "  Test Results" << endl;
    cout << "===========================================================" << endl;

    if (mismatches == 0) {
        cout << "  ✅✅✅ TEST PASSED!" << endl;
        cout << "  All " << (TEST_LINES * 11) << " FP24 values match expected pattern" << endl;
        cout << "  Dispatcher BRAM path is working correctly!" << endl;
        return 0;
    } else {
        cout << "  ❌ TEST FAILED!" << endl;
        cout << "  Mismatches: " << mismatches << " / " << (TEST_LINES * 11) << endl;
        cout << "  First mismatch at FP24[" << first_mismatch << "]" << endl;
        return 1;
    }
}
