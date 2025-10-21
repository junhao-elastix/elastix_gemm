#include <iostream>
#include <iomanip>
#include "../../../eus/shell/devices/acx/vp815/api/vp815.hpp"

using namespace std;

int main() {
    VP815 device(0);
    
    uint32_t status = device.mmioRead32(0, 0x24);  // ENGINE_STATUS
    
    cout << "ENGINE_STATUS: 0x" << hex << status << dec << endl;
    
    uint32_t mc_state_next = (status >> 20) & 0xF;
    uint32_t mc_state = (status >> 16) & 0xF;
    uint32_t dc_state = (status >> 8) & 0xF;
    uint32_t ce_state = (status >> 4) & 0xF;
    uint32_t busy = status & 0x1;
    
    cout << "  mc_state_next: " << mc_state_next << endl;
    cout << "  mc_state: " << mc_state << endl;
    cout << "  dc_state: " << dc_state << endl;
    cout << "  ce_state: " << ce_state << endl;
    cout << "  busy: " << busy << endl;
    
    return 0;
}
