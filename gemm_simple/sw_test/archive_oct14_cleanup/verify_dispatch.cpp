#include <iostream>
#include "../../../eus/shell/devices/acx/vp815/api/vp815.hpp"
using namespace std;
using namespace achronix;

int main() {
    VP815 device(0);
    
    cout << "=== Checking Dispatcher Status ===" << endl;
    
    // ENGINE_STATUS: {12'h0, mc_state_next[3:0], mc_state[3:0], dc_state[3:0], ce_state[3:0], 3'b0, engine_busy}
    uint32_t status = device.mmioRead32(0, 0x50);
    uint32_t dc_state = (status >> 8) & 0xF;
    uint32_t ce_state = (status >> 4) & 0xF;
    uint32_t mc_state = (status >> 12) & 0xF;
    
    cout << "DC state: " << dc_state << " (0=idle, should be 0 after FETCH)" << endl;
    cout << "CE state: " << ce_state << " (0=idle)" << endl;
    cout << "MC state: " << mc_state << " (0=idle)" << endl;
    
    // Check if there are any debug registers showing BRAM write count
    uint32_t result_count = device.mmioRead32(0, 0x54);
    cout << "Result count: " << result_count << endl;
    
    return 0;
}
