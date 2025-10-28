// Phase 2: Validate Dispatcher Data Path
// Write known pattern to GDDR6 → FETCH → Read BRAM to verify
#include <iostream>
#include <iomanip>
#include <memory>
#include <vector>
#include <cstring>
#include "vp815.hpp"

#include <unistd.h>
using namespace std;
using namespace achronix;

// Register offsets
#define ENGINE_STATUS      11
#define ENGINE_CMD_WORD0   12
#define ENGINE_CMD_WORD1   13
#define ENGINE_CMD_WORD2   14
#define ENGINE_CMD_SUBMIT  15

// BRAM BAR2 base addresses (from reg_control.sv)
#define BAR2_BRAM_ATU_BASE  0x00000000
#define BAR2_BRAM_DMA_BASE  0x00010000
#define BAR2_BRAM_DL_BASE   0x00020000

// Dispatcher BRAM is accessed via DMA window
#define DISPATCHER_BRAM_BASE BAR2_BRAM_DMA_BASE

int main() {
    cout << "=== Phase 2: Dispatcher Data Path Validation ===" << endl << endl;
    
    unique_ptr<VP815> device;
    try {
        device = make_unique<VP815>(0);
        cout << "✅ Device initialized" << endl << endl;
    } catch (const exception& e) {
        cerr << "ERROR: " << e.what() << endl;
        return 1;
    }

    // Step 1: Create test pattern
    cout << "Step 1: Creating test pattern..." << endl;
    const size_t NUM_LINES = 16;  // Fetch 16 lines
    const size_t BYTES_PER_LINE = 32;
    const size_t TOTAL_BYTES = NUM_LINES * BYTES_PER_LINE;
    
    vector<uint8_t> test_pattern(TOTAL_BYTES);
    
    // Simple pattern: line_num repeated in each byte
    for (size_t line = 0; line < NUM_LINES; line++) {
        for (size_t byte = 0; byte < BYTES_PER_LINE; byte++) {
            test_pattern[line * BYTES_PER_LINE + byte] = (uint8_t)(line + 0xA0);
        }
    }
    
    cout << "  Pattern: Each line filled with (line_num + 0xA0)" << endl;
    cout << "  Line 0: 0xA0A0...A0A0 (32 bytes)" << endl;
    cout << "  Line 1: 0xA1A1...A1A1 (32 bytes)" << endl;
    cout << "  ..." << endl;
    cout << "  Line 15: 0xAFAF...AFAF (32 bytes)" << endl << endl;

    // Step 2: Write to GDDR6
    cout << "Step 2: Writing test pattern to GDDR6..." << endl;
    uint64_t gddr6_addr = 0x0;
    
    if (!device->dmaWrite(gddr6_addr, TOTAL_BYTES, (char*)test_pattern.data(), 5000)) {
        cerr << "❌ DMA write failed" << endl;
        return 1;
    }
    cout << "✅ Wrote " << TOTAL_BYTES << " bytes to GDDR6 @ 0x" << hex << gddr6_addr << dec << endl << endl;

    // Step 3: Issue FETCH command
    cout << "Step 3: Issuing FETCH command..." << endl;
    uint32_t cmd_word0 = (0xF0 << 0) | (1 << 8) | (12 << 16);
    uint32_t cmd_word1 = 0x00000000;  // addr = 0
    uint32_t cmd_word2 = NUM_LINES;
    
    device->mmioWrite32(0, ENGINE_CMD_WORD0 * 4, cmd_word0);
    device->mmioWrite32(0, ENGINE_CMD_WORD1 * 4, cmd_word1);
    device->mmioWrite32(0, ENGINE_CMD_WORD2 * 4, cmd_word2);
    device->mmioWrite32(0, ENGINE_CMD_SUBMIT * 4, 1);
    
    cout << "  Waiting for FETCH completion..." << endl;
    
    // Wait for completion
    bool completed = false;
    for (int i = 0; i < 1000; i++) {
        uint32_t status;
        device->mmioRead32(0, ENGINE_STATUS * 4, status);
        
        uint32_t mc_state = (status >> 12) & 0xF;
        uint32_t dc_state = (status >> 8) & 0xF;
        
        if (mc_state == 0 && dc_state == 0 && i > 5) {
            completed = true;
            cout << "✅ FETCH completed in " << i << " iterations" << endl << endl;
            break;
        }
        
        usleep(100);
    }
    
    if (!completed) {
        cerr << "❌ FETCH timeout" << endl;
        return 1;
    }

    // Step 4: Read back dispatcher BRAM
    cout << "Step 4: Reading dispatcher BRAM contents..." << endl;
    vector<uint8_t> readback(TOTAL_BYTES);
    
    // Read via BAR2 (BRAM window)
    for (size_t i = 0; i < TOTAL_BYTES / 4; i++) {
        uint32_t word;
        device->mmioRead32(2, DISPATCHER_BRAM_BASE + i * 4, word);
        memcpy(&readback[i * 4], &word, 4);
    }
    
    cout << "✅ Read " << TOTAL_BYTES << " bytes from dispatcher BRAM" << endl << endl;

    // Step 5: Verify data
    cout << "Step 5: Verifying data..." << endl;
    int mismatches = 0;
    
    for (size_t line = 0; line < NUM_LINES; line++) {
        bool line_ok = true;
        uint8_t expected = line + 0xA0;
        
        for (size_t byte = 0; byte < BYTES_PER_LINE; byte++) {
            size_t idx = line * BYTES_PER_LINE + byte;
            if (readback[idx] != expected) {
                if (line_ok) {
                    cout << "  ❌ Line " << dec << line << ": Mismatch detected" << endl;
                    line_ok = false;
                }
                mismatches++;
            }
        }
        
        if (line_ok) {
            cout << "  ✅ Line " << dec << line << ": All bytes = 0x" << hex << uppercase 
                 << (int)expected << dec << endl;
        }
    }
    
    cout << endl << "=== TEST SUMMARY ===" << endl;
    if (mismatches == 0) {
        cout << "🎉 SUCCESS: All " << TOTAL_BYTES << " bytes verified correctly!" << endl;
        cout << "   Dispatcher data path is functional (GDDR6 → NAP → Dispatcher → BRAM)" << endl;
        return 0;
    } else {
        cout << "❌ FAILURE: " << mismatches << " byte mismatches detected" << endl;
        cout << "   First few mismatches:" << endl;
        int shown = 0;
        for (size_t i = 0; i < TOTAL_BYTES && shown < 10; i++) {
            if (readback[i] != test_pattern[i]) {
                cout << "     [" << dec << i << "] Expected 0x" << hex << uppercase 
                     << (int)test_pattern[i] << ", Got 0x" << (int)readback[i] << dec << endl;
                shown++;
            }
        }
        return 1;
    }
}
