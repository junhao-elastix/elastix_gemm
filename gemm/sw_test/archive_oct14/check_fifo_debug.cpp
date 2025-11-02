#include "vp815.hpp"
#include <iostream>
#include <iomanip>
using namespace std;
using namespace achronix;

int main() {
    VP815 device(0);
    if (!device.isReady()) return 1;
    
    cout << "Reading ENGINE_DEBUG (contains cmd_fifo_count)..." << endl;
    uint32_t engine_debug = device.mmioRead32(0, 0x58);
    
    cout << "  ENGINE_DEBUG: 0x" << hex << setw(8) << setfill('0') << engine_debug << dec << endl;
    
    uint32_t fifo_count = engine_debug & 0x1FFF;  // Lower 13 bits
    uint32_t bridge_busy = (engine_debug >> 13) & 0x1;
    uint32_t fifo_empty = (engine_debug >> 14) & 0x1;
    
    cout << "  cmd_fifo_count: " << fifo_count << endl;
    cout << "  bridge_busy: " << bridge_busy << endl;
    cout << "  fifo_empty: " << fifo_empty << endl;
    
    return 0;
}
