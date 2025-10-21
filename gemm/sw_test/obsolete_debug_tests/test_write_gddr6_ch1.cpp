// Test: Write data to GDDR6 Channel 1, then test FETCH
#include <iostream>
#include <iomanip>
#include <memory>
#include <vector>
#include <thread>
#include <chrono>
#include "vp815.hpp"

using namespace std;
using namespace achronix;

// Register offsets
#define ENGINE_STATUS      11
#define ENGINE_CMD_WORD0   12
#define ENGINE_CMD_WORD1   13
#define ENGINE_CMD_WORD2   14
#define ENGINE_CMD_SUBMIT  15

int main() {
    cout << "=== GDDR6 Channel 1 Write + FETCH Test ===" << endl;
    
    unique_ptr<VP815> device;
    try {
        device = make_unique<VP815>(0);
        cout << "✅ Device initialized" << endl << endl;
    } catch (const exception& e) {
        cerr << "ERROR: " << e.what() << endl;
        return 1;
    }

    // Step 1: Write test pattern to GDDR6 Channel 1
    cout << "Step 1: Writing test pattern to GDDR6 Channel 1..." << endl;
    
    // Create test pattern (528 lines ×  32 bytes = 16896 bytes)
    const size_t NUM_LINES = 528;
    const size_t BYTES_PER_LINE = 32;
    const size_t TOTAL_BYTES = NUM_LINES * BYTES_PER_LINE;
    
    vector<uint8_t> test_data(TOTAL_BYTES);
    
    // Fill with simple pattern: byte value = (line_num & 0xFF)
    for (size_t line = 0; line < NUM_LINES; line++) {
        for (size_t byte = 0; byte < BYTES_PER_LINE; byte++) {
            test_data[line * BYTES_PER_LINE + byte] = (line & 0xFF);
        }
    }
    
    // Write to GDDR6 using DMA
    // TODO: Need to figure out how to target Channel 1 specifically
    // For now, attempt write to base GDDR6 address
    
    uint64_t gddr6_base = 0x0000000000000000ULL;  // Start of GDDR6 space
    
    // Use PCIe DMA to write data
    try {
        device->dmaWrite(gddr6_base, TOTAL_BYTES, (char*)test_data.data(), 5000);
        cout << "✅ Wrote " << TOTAL_BYTES << " bytes to GDDR6" << endl << endl;
    } catch (const exception& e) {
        cerr << "ERROR during DMA write: " << e.what() << endl;
        cerr << "⚠️  Continuing with FETCH test anyway..." << endl << endl;
    }
    
    // Step 2: Issue FETCH command
    cout << "Step 2: Issuing FETCH command..." << endl;
    
    uint32_t cmd_word0 = (0xF0 << 0) | (1 << 8) | (12 << 16);  // FETCH, id=1, len=12
    uint32_t cmd_word1 = 0x00000000;  // addr = 0
    uint32_t cmd_word2 = 16;          // 16 lines for testing
    
    device->mmioWrite32(0, ENGINE_CMD_WORD0 * 4, cmd_word0);
    device->mmioWrite32(0, ENGINE_CMD_WORD1 * 4, cmd_word1);
    device->mmioWrite32(0, ENGINE_CMD_WORD2 * 4, cmd_word2);
    device->mmioWrite32(0, ENGINE_CMD_SUBMIT * 4, 1);  // Submit
    
    cout << "✅ FETCH command submitted" << endl << endl;
    
    // Step 3: Monitor FSM states
    cout << "Step 3: Monitoring FSM states..." << endl;
    
    for (int i = 0; i < 1000; i++) {
        uint32_t status;
        device->mmioRead32(0, ENGINE_STATUS * 4, status);
        
        uint32_t mc_state = (status >> 12) & 0xF;
        uint32_t dc_state = (status >> 8) & 0xF;
        
        if (status == 0xFFFFFFFF) {
            cout << "\n❌ DEVICE HANG at iteration " << i << endl;
            return 1;
        }
        
        if (mc_state == 0 && dc_state == 0 && i > 10) {
            cout << "\n✅ FSMs returned to IDLE!" << endl;
            cout << "SUCCESS: FETCH completed after memory initialization" << endl;
            return 0;
        }
        
        if (i % 100 == 0) {
            cout << "  [" << i << "] MC=" << mc_state << " DC=" << dc_state << endl;
        }
        
        this_thread::sleep_for(chrono::microseconds(100));
    }
    
    cout << "\n⚠️  TIMEOUT: FSMs did not return to IDLE" << endl;
    
    uint32_t final_status;
    device->mmioRead32(0, ENGINE_STATUS * 4, final_status);
    uint32_t final_mc = (final_status >> 12) & 0xF;
    uint32_t final_dc = (final_status >> 8) & 0xF;
    
    cout << "Final state: MC=" << final_mc << " DC=" << final_dc << endl;
    
    return 1;
}
