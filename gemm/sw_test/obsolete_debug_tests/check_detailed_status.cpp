#include <iostream>
#include <iomanip>
#include "../../../eus/shell/devices/acx/vp815/api/vp815.hpp"

using namespace std;
using namespace achronix;

int main() {
    auto device = VP815Device::getInstance(0);
    if (!device) return 1;
    
    uint32_t engine_debug, engine_status, result_count;
    device->mmioRead32(0, 0x38, engine_debug);
    device->mmioRead32(0, 0x3C, engine_status);
    device->mmioRead32(0, 0x40, result_count);
    
    cout << hex << uppercase;
    cout << "ENGINE_STATUS (0x3C): 0x" << engine_status << endl;
    cout << "  mc_state_next: " << dec << ((engine_status >> 20) & 0xF) << " (0x" << hex << ((engine_status >> 20) & 0xF) << ")" << endl;
    cout << "  mc_state: " << dec << ((engine_status >> 16) & 0xF) << " (0x" << hex << ((engine_status >> 16) & 0xF) << ")" << endl;
    cout << "  dc_state: " << dec << ((engine_status >> 8) & 0xF) << " (0x" << hex << ((engine_status >> 8) & 0xF) << ")" << endl;
    cout << "  ce_state: " << dec << (engine_status & 0xF) << " (0x" << hex << (engine_status & 0xF) << ")" << endl;
    
    cout << "\nRESULT_COUNT (0x40): " << dec << result_count << endl;
    
    // Read debug registers
    uint32_t ce_control;
    device->mmioRead32(0, 0x14, ce_control);
    
    cout << "\nCE_CONTROL (0x14): 0x" << hex << ce_control << endl;
    cout << "  rd_en: " << ((ce_control >> 12) & 0x1) << endl;
    cout << "  load_count: " << dec << ((ce_control >> 11) & 0x1) << endl;
    cout << "  ce_state: " << dec << (ce_control & 0xF) << " = ";
    
    switch (ce_control & 0xF) {
        case 0: cout << "IDLE"; break;
        case 1: cout << "LOAD_LEFT_EXP"; break;
        case 2: cout << "LOAD_RIGHT_EXP"; break;
        case 3: cout << "LOAD_LEFT_MAN"; break;
        case 4: cout << "LOAD_RIGHT_MAN"; break;
        case 5: cout << "COMPUTE"; break;
        case 6: cout << "CONVERT"; break;
        case 7: cout << "OUTPUT"; break;
        case 8: cout << "NEXT_DOT"; break;
        case 9: cout << "DONE"; break;
        case 10: cout << "BYPASS_FORWARD"; break;
        default: cout << "UNKNOWN";
    }
    cout << endl;
    
    return 0;
}
