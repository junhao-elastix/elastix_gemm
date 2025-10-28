#include <iostream>
#include <iomanip>
#include <memory>
#include <unistd.h>
#include "vp815.hpp"

using namespace std;
using namespace achronix;

#define ENGINE_STATUS    0x3C
#define ENGINE_DEBUG     0x44
#define ENGINE_CMD_WORD0 0x28
#define ENGINE_CMD_SUBMIT 0x38

int main() {
    cout << "\n=== Testing Single MATMUL (no FETCH) ===" << endl;
    unique_ptr<VP815> device = make_unique<VP815>(0);

    auto check_status = [&](const char* label) {
        uint32_t status = device->mmioRead32(0, ENGINE_STATUS);
        uint32_t debug = device->mmioRead32(0, ENGINE_DEBUG);
        
        uint8_t mc = (status >> 16) & 0xF;
        uint8_t dc = (status >> 8) & 0xF;
        uint8_t ce = status & 0xF;
        uint8_t sub = (debug >> 16) & 0xFF;
        uint8_t rd = (debug >> 8) & 0xFF;
        uint8_t cmp = debug & 0xFF;
        
        cout << label << " MC=" << (int)mc << " DC=" << (int)dc << " CE=" << (int)ce;
        cout << " | sub=" << (int)sub << " rd=" << (int)rd << " cmp=" << (int)cmp << endl;
        
        return make_tuple(mc, dc, ce, sub, rd, cmp);
    };

    check_status("Initial:");

    // Issue MATMUL (CE will be stuck waiting for data)
    cout << "\nIssuing MATMUL (CE expects FETCH data)..." << endl;
    device->mmioWrite32(0, ENGINE_CMD_WORD0, (0xF2 << 0) | (1 << 8) | (12 << 16));
    device->mmioWrite32(0, ENGINE_CMD_WORD0+4, 0);
    device->mmioWrite32(0, ENGINE_CMD_WORD0+8, (4 << 13) | (4 << 5));
    device->mmioWrite32(0, ENGINE_CMD_WORD0+12, (32 << 8));
    device->mmioWrite32(0, ENGINE_CMD_SUBMIT, 0x1);
    
    usleep(10000);  // 10ms
    auto [mc, dc, ce, sub, rd, cmp] = check_status("\nAfter 10ms:");
    
    usleep(90000);  // 90ms more
    check_status("After 100ms:");
    
    cout << "\n=== Analysis ===" << endl;
    if (mc == 11 && ce == 1) {
        cout << "❌ MC stuck in WAIT_DONE (11), CE stuck in LOAD_LEFT_EXP (1)" << endl;
        cout << "   Root cause: CE expects data in dispatcher BRAM (from FETCH)" << endl;
        cout << "   But dispatcher BRAM is empty - no FETCH was issued" << endl;
        cout << "\nThis confirms the command queue bug is FIXED (cmd was read)," << endl;
        cout << "but reveals CE hangs when BRAM is empty." << endl;
    } else if (cmp > 0) {
        cout << "✅ Command completed!" << endl;
    }

    return 0;
}
