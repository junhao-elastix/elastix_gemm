#include <iostream>
#include <iomanip>
#include <memory>
#include <unistd.h>
#include "vp815.hpp"

using namespace std;
using namespace achronix;

#define ENGINE_STATUS      0x3C
#define ENGINE_RESULT_COUNT 0x40
#define ENGINE_CMD_WORD0   0x28
#define ENGINE_CMD_SUBMIT  0x38
#define OPCODE_MATMUL      0xF2

int main() {
    unique_ptr<VP815> device = make_unique<VP815>(0);
    
    uint32_t count_before = device->mmioRead32(0, ENGINE_RESULT_COUNT);
    cout << "Result count BEFORE: " << dec << count_before << endl;
    
    // Issue MATMUL
    device->mmioWrite32(0, ENGINE_CMD_WORD0, (OPCODE_MATMUL << 0) | (1 << 8) | (12 << 16));
    device->mmioWrite32(0, ENGINE_CMD_WORD0+4, 0);
    device->mmioWrite32(0, ENGINE_CMD_WORD0+8, (4 << 13) | (4 << 5));
    device->mmioWrite32(0, ENGINE_CMD_WORD0+12, (32 << 8));
    device->mmioWrite32(0, ENGINE_CMD_SUBMIT, 0x1);
    
    usleep(10000);  // 10ms
    
    uint32_t count_after = device->mmioRead32(0, ENGINE_RESULT_COUNT);
    uint32_t status = device->mmioRead32(0, ENGINE_STATUS);
    
    cout << "Result count AFTER: " << dec << count_after << endl;
    cout << "ENGINE_STATUS: 0x" << hex << status << endl;
    cout << "  MC=" << dec << ((status >> 16) & 0xF);
    cout << " DC=" << ((status >> 8) & 0xF);
    cout << " CE=" << (status & 0xF) << endl;
    
    if (count_after > count_before) {
        cout << "\n✅ Command executed! Count increased by " << (count_after - count_before) << endl;
    } else {
        cout << "\n❌ Command did NOT execute (count unchanged)" << endl;
    }
    
    return 0;
}
