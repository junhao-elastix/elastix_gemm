// Quick test with V=1 to isolate V-loop issue
#include <iostream>
#include "../../../eus/shell/devices/acx/vp815/api/vp815.hpp"

using namespace std;
using namespace achronix;

#define OPCODE_MATMUL 0xF2

int main() {
    cout << "=== V=1 Quick Test ===" << endl;
    
    auto device = VP815Device::getInstance(0);
    if (!device) {
        cerr << "Failed to init device" << endl;
        return 1;
    }
    
    // Build MATMUL command with V=1 (all other params same)
    uint32_t dim_b = 4, dim_c = 4, dim_v = 1;  // ← V=1!
    uint32_t left_addr = 0, right_addr = 528;
    uint32_t left_ugd = 128, right_ugd = 128, vec_len = 128, flags = 0;
    
    uint32_t word1 = ((left_ugd & 0x3FF) << 22) | ((right_addr & 0x7FF) << 11) | (left_addr & 0x7FF);
    uint32_t word2 = ((dim_v & 0x1) << 31) | ((flags & 0xFF) << 23) |
                      ((vec_len & 0x7FF) << 12) | ((right_ugd & 0x7FF) << 1) | ((left_ugd >> 10) & 0x1);
    uint32_t word3 = ((dim_b & 0xFF) << 15) | ((dim_c & 0xFF) << 7) | ((dim_v >> 1) & 0x7F);
    uint32_t word0 = (12 << 16) | (9 << 8) | OPCODE_MATMUL;
    
    cout << "Issuing MATMUL with V=1..." << endl;
    cout << "  word0=0x" << hex << word0 << ", word1=0x" << word1 
         << ", word2=0x" << word2 << ", word3=0x" << word3 << dec << endl;
    
    device->mmioWrite32(0, 0x28, word0);
    device->mmioWrite32(0, 0x2C, word1);
    device->mmioWrite32(0, 0x30, word2);
    device->mmioWrite32(0, 0x34, word3);
    
    // Wait and check status
    sleep(1);
    
    uint32_t status;
    device->mmioRead32(0, 0x3C, status);
    cout << "ENGINE_STATUS after 1s: 0x" << hex << status << dec << endl;
    cout << "  ce_state: " << (status & 0xF) << endl;
    
    // Check debug registers
    uint32_t ce_control;
    device->mmioRead32(0, 0x14, ce_control);
    cout << "CE_CONTROL: 0x" << hex << ce_control << dec << endl;
    cout << "  ce_state: " << (ce_control & 0xF) << " (should be 0=IDLE or 9=DONE if successful)" << endl;
    
    return 0;
}
