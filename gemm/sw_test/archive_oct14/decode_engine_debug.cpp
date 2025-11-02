#include "vp815.hpp"
#include <iostream>
#include <iomanip>
using namespace std;
using namespace achronix;

int main() {
    VP815 device(0);
    if (!device.isReady()) return 1;
    
    cout << "Decoding ENGINE_DEBUG register..." << endl;
    
    uint32_t debug = device.mmioRead32(0, 0x58);
    cout << "\n  ENGINE_DEBUG (0x58): 0x" << hex << setw(8) << setfill('0') << debug << dec << endl;
    
    // Based on elastix_gemm_top.sv line 648:
    // assign engine_debug = {24'd0, last_opcode, mc_state};
    // But looking at the actual assignment, it might be different
    
    uint32_t mc_state = debug & 0xF;
    uint32_t last_opcode = (debug >> 4) & 0xFF;
    
    cout << "\n  Decoded:" << endl;
    cout << "    mc_state: 0x" << hex << mc_state << dec << " (" << mc_state << ")" << endl;
    cout << "    last_opcode: 0x" << hex << (int)last_opcode << dec << " (" << (int)last_opcode << ")" << endl;
    
    cout << "\n  Known opcodes:" << endl;
    cout << "    0xF0 = FETCH" << endl;
    cout << "    0xF1 = DISPATCH" << endl;
    cout << "    0xF2 = MATMUL (TILE)" << endl;
    cout << "    0xF3 = WAIT_DISPATCH" << endl;
    cout << "    0xF4 = WAIT_MATMUL" << endl;
    
    if (last_opcode >= 0xF0 && last_opcode <= 0xF4) {
        const char* names[] = {"FETCH", "DISPATCH", "MATMUL", "WAIT_DISPATCH", "WAIT_MATMUL"};
        cout << "\n  [INFO] Last opcode: " << names[last_opcode - 0xF0] << endl;
    } else if (last_opcode == 0) {
        cout << "\n  [INFO] No commands processed yet (last_opcode=0)" << endl;
    } else {
        cout << "\n  [WARNING] Unknown opcode 0x" << hex << (int)last_opcode << dec << endl;
    }
    
    return 0;
}
