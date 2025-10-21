#include "vp815.hpp"
#include <iostream>
#include <iomanip>
#include <unistd.h>
using namespace std;
using namespace achronix;

int main() {
    VP815 device(0);
    if (!device.isReady()) return 1;
    
    cout << "Testing single FETCH command submission..." << endl;
    
    // Check initial state
    uint32_t debug_before = device.mmioRead32(0, 0x58);
    cout << "\nBefore command:" << endl;
    cout << "  cmd_fifo_count: " << (debug_before & 0x1FFF) << endl;
    cout << "  last_opcode: 0x" << hex << ((debug_before >> 4) & 0xFF) << dec << endl;
    
    // Issue FETCH command (4 words)
    cout << "\nIssuing FETCH command..." << endl;
    uint32_t w0 = 0x000c00F0;  // opcode=0xF0, id=0, len=12
    uint32_t w1 = 0x00000000;  // start_addr=0
    uint32_t w2 = 0x00100000;  // len=16 lines in upper 16 bits
    uint32_t w3 = 0x00000000;
    
    cout << "  word0: 0x" << hex << setw(8) << setfill('0') << w0 << dec << endl;
    cout << "  word1: 0x" << hex << setw(8) << setfill('0') << w1 << dec << endl;
    cout << "  word2: 0x" << hex << setw(8) << setfill('0') << w2 << dec << endl;
    cout << "  word3: 0x" << hex << setw(8) << setfill('0') << w3 << dec << endl;
    
    device.mmioWrite32(0, 0x3C, w0);
    device.mmioWrite32(0, 0x40, w1);
    device.mmioWrite32(0, 0x44, w2);
    device.mmioWrite32(0, 0x48, w3);
    device.mmioWrite32(0, 0x4C, 1);  // Submit
    
    usleep(50000);  // Wait 50ms for processing
    
    // Check after
    uint32_t debug_after = device.mmioRead32(0, 0x58);
    uint32_t status_after = device.mmioRead32(0, 0x50);
    
    cout << "\nAfter command:" << endl;
    cout << "  cmd_fifo_count: " << (debug_after & 0x1FFF) << endl;
    cout << "  last_opcode: 0x" << hex << ((debug_after >> 4) & 0xFF) << dec << endl;
    cout << "  mc_state: 0x" << hex << ((status_after >> 12) & 0xF) << dec << endl;
    cout << "  busy: " << (status_after & 1) << endl;
    
    int fifo_delta = (int)(debug_after & 0x1FFF) - (int)(debug_before & 0x1FFF);
    cout << "\nFIFO count change: " << fifo_delta << " entries" << endl;
    if (fifo_delta == 4) {
        cout << "[PASS] Command pushed to FIFO (4 words)" << endl;
    } else if (fifo_delta < 0) {
        cout << "[GOOD] Command was processed! (" << -fifo_delta << " words consumed)" << endl;
    } else {
        cout << "[ERROR] Unexpected FIFO behavior" << endl;
    }
    
    return 0;
}
