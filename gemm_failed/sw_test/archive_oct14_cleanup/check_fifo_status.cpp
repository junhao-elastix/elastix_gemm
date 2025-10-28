#include "vp815.hpp"
#include <iostream>
#include <iomanip>
#include <unistd.h>
using namespace std;
using namespace achronix;

int main() {
    VP815 device(0);
    if (!device.isReady()) return 1;
    
    cout << "Detailed FIFO status check..." << endl;
    
    // Reset first
    device.mmioWrite32(0, 0x0, 0x10);
    usleep(100000);
    device.mmioWrite32(0, 0x0, 0x0);
    usleep(100000);
    
    uint32_t debug = device.mmioRead32(0, 0x58);
    cout << "\nAfter reset:" << endl;
    cout << "  ENGINE_DEBUG: 0x" << hex << setw(8) << setfill('0') << debug << dec << endl;
    cout << "  cmd_fifo_count: " << (debug & 0x1FFF) << endl;
    
    // Now issue ONE simple command (WAIT_DISP with id=0)
    cout << "\nIssuing single WAIT_DISP command..." << endl;
    device.mmioWrite32(0, 0x3C, 0x000300F3);  // word0: WAIT_DISP opcode
    device.mmioWrite32(0, 0x40, 0x00000000);  // word1
    device.mmioWrite32(0, 0x44, 0x00000000);  // word2
    device.mmioWrite32(0, 0x48, 0x00000000);  // word3
    device.mmioWrite32(0, 0x4C, 0x00000001);  // Submit
    usleep(10000);
    
    debug = device.mmioRead32(0, 0x58);
    cout << "\nAfter single command:" << endl;
    cout << "  ENGINE_DEBUG: 0x" << hex << setw(8) << setfill('0') << debug << dec << endl;
    cout << "  cmd_fifo_count: " << (debug & 0x1FFF) << endl;
    cout << "  fifo_empty bit: " << ((debug >> 14) & 1) << endl;
    
    uint32_t status = device.mmioRead32(0, 0x50);
    cout << "  ENGINE_STATUS: 0x" << hex << setw(8) << setfill('0') << status << dec << endl;
    cout << "  mc_state: 0x" << hex << ((status >> 4) & 0xF) << dec << endl;
    cout << "  busy: " << (status & 1) << endl;
    
    return 0;
}
