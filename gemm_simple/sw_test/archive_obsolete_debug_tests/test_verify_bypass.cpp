#include <iostream>
#include <iomanip>
#include <memory>
#include "vp815.hpp"

using namespace std;
using namespace achronix;

#define REG_ENGINE_BYPASS   0x24
#define REG_ENGINE_STATUS   0x08

int main() {
    cout << "\n=== Bypass Mode Verification ===" << endl;

    unique_ptr<VP815> device = make_unique<VP815>(0);
    
    // Read bypass mode
    uint32_t bypass_val;
    device->mmioRead32(0, REG_ENGINE_BYPASS, bypass_val);
    cout << "ENGINE_BYPASS_CTRL (0x24): 0x" << hex << bypass_val << dec << endl;
    cout << "  bypass_mode = " << (bypass_val & 0x3) << endl;
    
    // Read engine status
    uint32_t status;
    device->mmioRead32(0, REG_ENGINE_STATUS, status);
    cout << "\nENGINE_STATUS (0x08): 0x" << hex << status << dec << endl;
    cout << "  mc_state = " << ((status >> 16) & 0xF) << endl;
    cout << "  dc_state = " << ((status >> 8) & 0xF) << endl;
    cout << "  ce_state = " << (status & 0xF) << endl;
    
    // Try writing different values to bypass register
    cout << "\n=== Testing Bypass Register Write ===" << endl;
    
    for (int i = 0; i < 3; i++) {
        device->mmioWrite32(0, REG_ENGINE_BYPASS, i);
        device->mmioRead32(0, REG_ENGINE_BYPASS, bypass_val);
        cout << "  Wrote " << i << ", read back: " << (bypass_val & 0x3) << endl;
    }
    
    // Set back to mode 2
    device->mmioWrite32(0, REG_ENGINE_BYPASS, 2);
    device->mmioRead32(0, REG_ENGINE_BYPASS, bypass_val);
    cout << "\nFinal bypass_mode: " << (bypass_val & 0x3) << endl;
    
    return 0;
}
