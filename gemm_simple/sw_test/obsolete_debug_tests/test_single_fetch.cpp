// Quick test: Single FETCH command to verify dispatcher can handle 528 lines
#include <iostream>
#include <unistd.h>
#include "vp815.hpp"

using namespace std;
using namespace achronix;

int main() {
    cout << "=== Single FETCH Test ===" << endl;
    
    auto device = make_unique<achronix::VP815>(0);
    
    // Issue single FETCH: 528 lines from address 0
    uint32_t word0 = (0 << 24) | (12 << 16) | (0 << 8) | 0xF0;  // FETCH opcode
    uint32_t word1 = 0x0;                                        // Address 0
    uint32_t word2 = (528 << 16);                                // 528 lines
    uint32_t word3 = 0;
    
    device->mmioWrite32(0, 0x28, word0);
    device->mmioWrite32(0, 0x2C, word1);
    device->mmioWrite32(0, 0x30, word2);
    device->mmioWrite32(0, 0x34, word3);
    device->mmioWrite32(0, 0x38, 1);  // Submit
    
    cout << "Submitted FETCH command, waiting..." << endl;
    
    sleep(2);  // Wait for FETCH to complete
    
    // Read debug registers
    uint32_t wr_addr, dc_status;
    device->mmioRead32(0, 0x18, wr_addr);
    device->mmioRead32(0, 0x1C, dc_status);
    
    cout << "wr_addr: " << (wr_addr & 0x7FF) << endl;
    cout << "fetch_done: " << ((dc_status >> 7) & 1) << endl;
    cout << "dc_state: " << (dc_status & 0xF) << endl;
    
    if ((wr_addr & 0x7FF) == 527) {
        cout << "✅ Single FETCH wrote 528 lines successfully!" << endl;
    } else {
        cout << "❌ Expected 528 lines, got " << ((wr_addr & 0x7FF) + 1) << endl;
    }
    
    return 0;
}
