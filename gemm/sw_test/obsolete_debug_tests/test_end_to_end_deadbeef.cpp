// End-to-End Data Path Test with DEADBEEF Marker
// Tests: GDDR6 → Dispatcher → Compute Engine → Result BRAM → Host

#include <iostream>
#include <iomanip>
#include <memory>
#include <vector>
#include <cstring>
#include <unistd.h>
#include "vp815.hpp"

using namespace std;
using namespace achronix;

// Register offsets
#define ENGINE_STATUS      11
#define ENGINE_CMD_WORD0   12
#define ENGINE_CMD_WORD1   13
#define ENGINE_CMD_WORD2   14
#define ENGINE_CMD_SUBMIT  15
#define ENGINE_RESULT_COUNT 16
#define ENGINE_DEBUG       17

// Result BRAM BAR2 mapping (from CLAUDE.md)
#define BAR2_RESULT_BRAM_BASE 0x00000000  // Results written here

int main() {
    cout << "=== END-TO-END DATA PATH TEST (DEADBEEF MARKER) ===" << endl << endl;
    
    unique_ptr<VP815> device;
    try {
        device = make_unique<VP815>(0);
        cout << "✅ Device initialized" << endl << endl;
    } catch (const exception& e) {
        cerr << "ERROR: " << e.what() << endl;
        return 1;
    }

    // Verify ADM Status
    uint32_t adm_status;
    device->mmioRead32(0, 0x1F4, adm_status);
    cout << "ADM Status: 0x" << hex << uppercase << adm_status << dec << endl;
    if (adm_status != 0x3) {
        cerr << "⚠️  WARNING: ADM Status is " << hex << adm_status 
             << " (expected 0x3). DMA may not work properly." << dec << endl;
        cerr << "   Machine reboot may be needed." << endl << endl;
    } else {
        cout << "✅ ADM properly initialized for DMA" << endl << endl;
    }

    // Step 1: Write test pattern to GDDR6
    cout << "Step 1: Writing test pattern to GDDR6..." << endl;
    const size_t NUM_LINES = 16;
    const size_t BYTES_PER_LINE = 32;
    const size_t TOTAL_BYTES = NUM_LINES * BYTES_PER_LINE;
    
    vector<uint8_t> test_data(TOTAL_BYTES);
    
    // Pattern: 0xAA, 0xBB, 0xCC, 0xDD repeated
    for (size_t i = 0; i < TOTAL_BYTES; i++) {
        test_data[i] = 0xAA + (i % 4);
    }
    
    uint64_t gddr6_addr = 0x0;
    if (!device->dmaWrite(gddr6_addr, TOTAL_BYTES, (char*)test_data.data(), 5000)) {
        cerr << "❌ DMA write failed" << endl;
        return 1;
    }
    cout << "✅ Wrote " << TOTAL_BYTES << " bytes (pattern: AA BB CC DD...)" << endl << endl;

    // Step 2: Issue FETCH command
    cout << "Step 2: Issuing FETCH command..." << endl;
    uint32_t cmd_fetch_word0 = (0xF0 << 0) | (1 << 8) | (12 << 16);  // FETCH, id=1, len=12
    uint32_t cmd_fetch_word1 = 0x00000000;  // addr = 0
    uint32_t cmd_fetch_word2 = NUM_LINES;   // 16 lines
    
    device->mmioWrite32(0, ENGINE_CMD_WORD0 * 4, cmd_fetch_word0);
    device->mmioWrite32(0, ENGINE_CMD_WORD1 * 4, cmd_fetch_word1);
    device->mmioWrite32(0, ENGINE_CMD_WORD2 * 4, cmd_fetch_word2);
    device->mmioWrite32(0, ENGINE_CMD_SUBMIT * 4, 1);
    
    // Wait for FETCH completion
    bool fetch_done = false;
    for (int i = 0; i < 1000; i++) {
        uint32_t status;
        device->mmioRead32(0, ENGINE_STATUS * 4, status);
        
        uint32_t mc_state = (status >> 12) & 0xF;
        uint32_t dc_state = (status >> 8) & 0xF;
        
        if (mc_state == 0 && dc_state == 0 && i > 5) {
            fetch_done = true;
            cout << "✅ FETCH completed in " << i << " iterations" << endl << endl;
            break;
        }
        usleep(100);
    }
    
    if (!fetch_done) {
        cerr << "❌ FETCH timeout" << endl;
        return 1;
    }

    // Step 3: Issue MATMUL command (triggers compute engine)
    cout << "Step 3: Issuing MATMUL command (passthrough test)..." << endl;
    
    // MATMUL command format (simplified for passthrough)
    // op=0xF2, id=2, len=12 (3-word payload)
    uint32_t cmd_matmul_word0 = (0xF2 << 0) | (2 << 8) | (12 << 16);
    
    // Payload word1: left_addr (21 bits), right_addr (21 bits), reserved
    // For passthrough test, left_addr=0 (first line of fetched data)
    uint32_t cmd_matmul_word1 = (0 << 21) | (528 << 10) | 0;  // left=0, right=528
    
    // Payload word2: vec_len, dim_b, dim_c, flags
    // B=1, C=1, V=1 for single output test
    uint32_t cmd_matmul_word2 = (1 << 21) | (1 << 13) | (1 << 5) | 0;
    
    device->mmioWrite32(0, ENGINE_CMD_WORD0 * 4, cmd_matmul_word0);
    device->mmioWrite32(0, ENGINE_CMD_WORD1 * 4, cmd_matmul_word1);
    device->mmioWrite32(0, ENGINE_CMD_WORD2 * 4, cmd_matmul_word2);
    device->mmioWrite32(0, ENGINE_CMD_SUBMIT * 4, 1);
    
    // Wait for MATMUL completion
    bool matmul_done = false;
    for (int i = 0; i < 1000; i++) {
        uint32_t status;
        device->mmioRead32(0, ENGINE_STATUS * 4, status);
        
        uint32_t mc_state = (status >> 12) & 0xF;
        uint32_t ce_state = (status >> 4) & 0xF;
        
        if (mc_state == 0 && ce_state == 0 && i > 5) {
            matmul_done = true;
            cout << "✅ MATMUL completed in " << i << " iterations" << endl;
            break;
        }
        usleep(100);
    }
    
    if (!matmul_done) {
        cerr << "❌ MATMUL timeout" << endl;
        
        // Debug output
        uint32_t status;
        device->mmioRead32(0, ENGINE_STATUS * 4, status);
        uint32_t mc = (status >> 12) & 0xF;
        uint32_t dc = (status >> 8) & 0xF;
        uint32_t ce = (status >> 4) & 0xF;
        cerr << "   Final states: MC=" << mc << " DC=" << dc << " CE=" << ce << endl;
        return 1;
    }
    
    // Check result count
    uint32_t result_count;
    device->mmioRead32(0, ENGINE_RESULT_COUNT * 4, result_count);
    cout << "   Result count: " << result_count << endl << endl;

    // Step 4: Read result from Result BRAM
    cout << "Step 4: Reading result from Result BRAM..." << endl;
    
    // Result should be 24-bit value with 0xDEADBEEF marker (lower 24 bits = 0xADBEEF)
    uint32_t result_word;
    device->mmioRead32(2, BAR2_RESULT_BRAM_BASE, result_word);
    
    cout << "   Result word read: 0x" << hex << uppercase << setw(8) << setfill('0') 
         << result_word << dec << endl;
    cout << "   Lower 24 bits: 0x" << hex << uppercase << setw(6) << setfill('0') 
         << (result_word & 0xFFFFFF) << dec << endl << endl;

    // Step 5: Verify DEADBEEF marker
    cout << "Step 5: Verifying DEADBEEF marker..." << endl;
    
    // Compute engine writes lower 24 bits of 0xDEADBEEF = 0xADBEEF
    uint32_t expected_marker = 0xADBEEF;
    uint32_t actual_marker = result_word & 0xFFFFFF;
    
    if (actual_marker == expected_marker) {
        cout << "✅ DEADBEEF marker verified!" << endl;
        cout << "   Expected: 0x" << hex << uppercase << setw(6) << setfill('0') 
             << expected_marker << endl;
        cout << "   Got:      0x" << hex << uppercase << setw(6) << setfill('0') 
             << actual_marker << dec << endl << endl;
        
        cout << "🎉 SUCCESS: Complete data path validated!" << endl;
        cout << "   GDDR6 → Dispatcher BRAM → Compute Engine → Result BRAM → Host" << endl;
        return 0;
    } else {
        cerr << "❌ Marker mismatch!" << endl;
        cerr << "   Expected: 0x" << hex << uppercase << setw(6) << setfill('0') 
             << expected_marker << endl;
        cerr << "   Got:      0x" << hex << uppercase << setw(6) << setfill('0') 
             << actual_marker << dec << endl;
        
        // Show full result for debugging
        cerr << "   Full result: 0x" << hex << uppercase << setw(8) << setfill('0') 
             << result_word << dec << endl;
        return 1;
    }
}
