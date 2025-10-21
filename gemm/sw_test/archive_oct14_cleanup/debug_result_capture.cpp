#include <iostream>
#include <iomanip>
#include "../../../eus/shell/devices/acx/vp815/api/vp815.hpp"

using namespace std;
using namespace achronix;

int main() {
    VP815 device(0);
    
    cout << "=== Result Capture Debug ===" << endl;
    
    // Check result FIFO status
    uint32_t result_count = device.mmioRead32(0, 0x54);  // ENGINE_RESULT_COUNT
    uint32_t ce_state = device.mmioRead32(0, 0x50) & 0xF0;  // CE state in STATUS reg
    
    cout << "Result count register: " << result_count << " FP16 values" << endl;
    cout << "CE state: 0x" << hex << (ce_state >> 4) << dec << endl;
    
    // Read first 4 result registers
    cout << "\nFirst 4 results from registers:" << endl;
    for (int i = 0; i < 4; i++) {
        uint32_t val = device.mmioRead32(0, 0x21C + i*4);
        cout << "  Result[" << i << "] = 0x" << hex << setw(4) << setfill('0') 
             << (val & 0xFFFF) << dec << endl;
    }
    
    return 0;
}
