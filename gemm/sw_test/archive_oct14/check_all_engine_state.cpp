#include "vp815.hpp"
#include <iostream>
#include <iomanip>
using namespace std;
using namespace achronix;

int main() {
    VP815 device(0);
    if (!device.isReady()) return 1;
    
    cout << "Complete Engine State After Test:" << endl;
    
    uint32_t status = device.mmioRead32(0, 0x50);
    uint32_t result_count = device.mmioRead32(0, 0x54);
    uint32_t debug = device.mmioRead32(0, 0x58);
    uint32_t bcv_debug = device.mmioRead32(0, 0x20);
    uint32_t bcv_dims = device.mmioRead32(0, 0x24);
    uint32_t mc_dims = device.mmioRead32(0, 0x28);
    
    cout << "\n  ENGINE_STATUS (0x50): 0x" << hex << setw(8) << setfill('0') << status << dec << endl;
    cout << "    busy: " << (status & 1) << endl;
    cout << "    ce_state: 0x" << hex << ((status >> 4) & 0xF) << dec << endl;
    cout << "    dc_state: 0x" << hex << ((status >> 8) & 0xF) << dec << endl;
    cout << "    mc_state: 0x" << hex << ((status >> 12) & 0xF) << dec << endl;
    cout << "    mc_state_next: 0x" << hex << ((status >> 16) & 0xF) << dec << endl;
    
    cout << "\n  ENGINE_RESULT_COUNT (0x54): " << (result_count & 0xFFFF) << " FP16 values" << endl;
    
    cout << "\n  ENGINE_DEBUG (0x58): 0x" << hex << setw(8) << setfill('0') << debug << dec << endl;
    cout << "    cmd_fifo_count: " << (debug & 0x1FFF) << endl;
    cout << "    last_opcode: 0x" << hex << ((debug >> 4) & 0xFF) << dec;
    if (((debug >> 4) & 0xFF) >= 0xF0 && ((debug >> 4) & 0xFF) <= 0xF4) {
        const char* names[] = {"FETCH", "DISPATCH", "MATMUL", "WAIT_DISPATCH", "WAIT_MATMUL"};
        cout << " (" << names[((debug >> 4) & 0xFF) - 0xF0] << ")";
    }
    cout << endl;
    
    cout << "\n  BCV_DEBUG (0x20): 0x" << hex << bcv_debug << dec << endl;
    cout << "  BCV_DIMS (0x24): 0x" << hex << bcv_dims << dec;
    cout << " (B=" << ((bcv_dims >> 24) & 0xFF);
    cout << ", C=" << ((bcv_dims >> 16) & 0xFF);
    cout << ", V=" << ((bcv_dims >> 8) & 0xFF) << ")" << endl;
    
    cout << "  MC_DIMS (0x28): 0x" << hex << mc_dims << dec;
    cout << " (dim_b=" << ((mc_dims >> 16) & 0xFF);
    cout << ", dim_c=" << ((mc_dims >> 8) & 0xFF);
    cout << ", dim_v=" << (mc_dims & 0xFF) << ")" << endl;
    
    return 0;
}
