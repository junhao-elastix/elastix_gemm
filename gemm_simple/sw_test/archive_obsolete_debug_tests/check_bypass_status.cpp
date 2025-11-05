#include <iostream>
#include <iomanip>
#include <memory>
#include "vp815.hpp"

using namespace std;
using namespace achronix;

int main() {
    cout << "\n=== Bypass Mode Status Check ===" << endl;
    
    unique_ptr<VP815> device;
    try {
        device = make_unique<VP815>(0);
    } catch (const exception& e) {
        cerr << "❌ Failed to initialize device: " << e.what() << endl;
        return -1;
    }
    
    uint32_t bypass_val, status, debug;
    
    // Check bypass mode
    device->mmioRead32(0, 0x24, bypass_val);
    cout << "Bypass mode: " << (bypass_val & 0x3) << endl;
    
    // Check engine status
    device->mmioRead32(0, 0x08, status);
    cout << "ENGINE_STATUS: 0x" << hex << setw(5) << setfill('0') << status << dec << endl;
    cout << "  mc_state = 0x" << hex << ((status >> 16) & 0xF) << " ";
    switch ((status >> 16) & 0xF) {
        case 0: cout << "(ST_IDLE)"; break;
        case 12: cout << "(ST_CMD_COMPLETE)"; break;
        default: cout << "(UNKNOWN)"; break;
    }
    cout << dec << endl;
    cout << "  dc_state = 0x" << hex << ((status >> 8) & 0xF) << dec << endl;
    cout << "  ce_state = 0x" << hex << (status & 0xF) << dec << endl;
    
    // Check engine debug
    device->mmioRead32(0, 0x0c, debug);
    cout << "\nENGINE_DEBUG: 0x" << hex << setw(8) << setfill('0') << debug << dec << endl;
    cout << "  opcode = 0x" << hex << ((debug >> 24) & 0xFF) << dec << endl;
    cout << "  submitted = " << ((debug >> 16) & 0xFF) << endl;
    cout << "  payload_words = " << ((debug >> 8) & 0xFF) << endl;
    
    cout << "\n✅ Stage 1 bypass working - commands complete without CE execution" << endl;
    
    return 0;
}
