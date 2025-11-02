#include "vp815.hpp"
#include <iostream>
#include <iomanip>
#include <unistd.h>
using namespace std;
using namespace achronix;

int main() {
    VP815 device(0);
    if (!device.isReady()) return 1;
    
    cout << "Checking reset and clock status..." << endl;
    
    // Read control register
    uint32_t ctrl = device.mmioRead32(0, 0x0);
    cout << "  CONTROL (0x00): 0x" << hex << setw(8) << setfill('0') << ctrl << dec << endl;
    cout << "    bit[4] (engine_reset): " << ((ctrl >> 4) & 1) << endl;
    
    // Read engine status
    uint32_t status = device.mmioRead32(0, 0x50);
    cout << "  ENGINE_STATUS (0x50): 0x" << hex << setw(8) << setfill('0') << status << dec << endl;
    cout << "    bit[0] (busy): " << (status & 1) << endl;
    cout << "    mc_state: 0x" << hex << ((status >> 4) & 0xF) << dec << endl;
    
    // Read ENGINE_DEBUG
    uint32_t debug = device.mmioRead32(0, 0x58);
    cout << "  ENGINE_DEBUG (0x58): 0x" << hex << setw(8) << setfill('0') << debug << dec << endl;
    cout << "    cmd_fifo_count: " << (debug & 0x1FFF) << endl;
    cout << "    bridge_busy: " << ((debug >> 13) & 1) << endl;
    
    // Try toggling reset
    cout << "\nToggling engine reset..." << endl;
    device.mmioWrite32(0, 0x0, 0x10);  // Assert reset
    usleep(10000);
    uint32_t debug_after_reset = device.mmioRead32(0, 0x58);
    cout << "  After reset assert - cmd_fifo_count: " << (debug_after_reset & 0x1FFF) << endl;
    
    device.mmioWrite32(0, 0x0, 0x0);   // Deassert reset
    usleep(10000);
    uint32_t debug_after_clear = device.mmioRead32(0, 0x58);
    cout << "  After reset clear - cmd_fifo_count: " << (debug_after_clear & 0x1FFF) << endl;
    
    return 0;
}
