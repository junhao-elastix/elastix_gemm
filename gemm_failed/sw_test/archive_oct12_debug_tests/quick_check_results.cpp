#include <iostream>
#include <iomanip>
#include "../../../eus/shell/devices/acx/vp815/api/vp815.hpp"

using namespace std;
using namespace achronix;

int main() {
    VP815 device(0);
    
    // Check result count register
    uint32_t result_count = device.mmioRead32(0, 0x54);  // ENGINE_RESULT_COUNT
    cout << "Result count register: " << dec << result_count << " (0x" << hex << result_count << ")" << dec << endl;
    
    // Check result FIFO count from engine_top
    uint32_t status = device.mmioRead32(0, 0x50);  // ENGINE_STATUS
    cout << "ENGINE_STATUS: 0x" << hex << status << dec << endl;
    cout << "  mc_state: " << ((status >> 12) & 0xF) << endl;
    cout << "  dc_state: " << ((status >> 8) & 0xF) << endl;
    cout << "  ce_state: " << ((status >> 4) & 0xF) << endl;
    cout << "  busy: " << (status & 0x1) << endl;
    
    // Try reading first few words from BRAM (BAR2 offset 0)
    cout << "\nReading first 16 FP16 values from Result BRAM (BAR2):" << endl;
    for (int i = 0; i < 16; i++) {
        uint16_t val = device.mmioRead16(2, i*2);
        cout << "  [" << dec << i << "] = 0x" << hex << setw(4) << setfill('0') << val << dec << endl;
    }
    
    return 0;
}
