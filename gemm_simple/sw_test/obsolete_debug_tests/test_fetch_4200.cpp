// Test: FETCH directly from 0x4200 (not as second FETCH)
#include <iostream>
#include <unistd.h>
#include "vp815.hpp"

using namespace std;
using namespace achronix;

int main() {
    cout << "=== FETCH @ 0x4200 Test ===" << endl;
    
    auto device = make_unique<achronix::VP815>(0);
    
    // DMA write data to 0x4200 first
    cout << "Writing test data to GDDR6 @ 0x4200..." << endl;
    char test_data[16896];  // 528 lines × 32 bytes
    for (int i = 0; i < 16896; i++) {
        test_data[i] = i & 0xFF;
    }
    device->dmaWrite(0x4200, 16896, test_data);
    cout << "  ✓ Write complete" << endl;
    
    // Reset FPGA (reboot simulation)
    cout << "\nNOTE: You need to reboot system before this test!" << endl;
    cout << "Press Enter after reboot to continue...";
    cin.get();
    
    // Issue FETCH: 528 lines from 0x4200 (as FIRST FETCH, not second)
    uint32_t word0 = (0 << 24) | (12 << 16) | (0 << 8) | 0xF0;  // FETCH opcode
    uint32_t word1 = 0x4200 / 32;  // Address in 32-byte units = 0x210
    uint32_t word2 = (528 << 16);   // 528 lines
    uint32_t word3 = 0;
    
    cout << "Issuing FETCH command:" << endl;
    cout << "  word1 = 0x" << hex << word1 << " (addr 0x4200)" << dec << endl;
    cout << "  word2 = 0x" << hex << word2 << " (528 lines)" << dec << endl;
    
    device->mmioWrite32(0, 0x28, word0);
    device->mmioWrite32(0, 0x2C, word1);
    device->mmioWrite32(0, 0x30, word2);
    device->mmioWrite32(0, 0x34, word3);
    device->mmioWrite32(0, 0x38, 1);  // Submit
    
    cout << "\nWaiting for FETCH to complete (or timeout)..." << endl;
    sleep(2);
    
    // Read debug registers
    uint32_t wr_addr, dc_status;
    device->mmioRead32(0, 0x18, wr_addr);
    device->mmioRead32(0, 0x1C, dc_status);
    
    int lines_written = (wr_addr & 0x7FF) + 1;
    bool fetch_done = (dc_status >> 7) & 1;
    
    cout << "\n=== Results ===" << endl;
    cout << "Lines written: " << lines_written << endl;
    cout << "fetch_done: " << fetch_done << endl;
    cout << "dc_state: " << (dc_status & 0xF) << endl;
    
    if (lines_written == 528 && fetch_done) {
        cout << "\n✅ SUCCESS! FETCH @ 0x4200 works as FIRST command!" << endl;
        cout << "   → Problem is 'sequential FETCH', not address 0x4200" << endl;
    } else if (lines_written == 16) {
        cout << "\n❌ FAILED! Only 16 lines written (same as before)" << endl;
        cout << "   → Problem IS address 0x4200 itself" << endl;
    } else {
        cout << "\n⚠️  Unexpected result: " << lines_written << " lines" << endl;
    }
    
    return 0;
}
