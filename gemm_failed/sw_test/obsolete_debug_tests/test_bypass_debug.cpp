#include <iostream>
#include <iomanip>
#include <memory>
#include <unistd.h>
#include "vp815.hpp"

using namespace std;
using namespace achronix;

#define ENGINE_STATUS    0x3C
#define ENGINE_BYPASS    0x24
#define ENGINE_CMD_WORD0 0x28
#define ENGINE_CMD_SUBMIT 0x38
#define OPCODE_MATMUL    0xF2

int main() {
    cout << "\n=== Bypass Debug - Check Engine State ===" << endl;

    unique_ptr<VP815> device = make_unique<VP815>(0);
    
    // Set bypass mode 2
    device->mmioWrite32(0, ENGINE_BYPASS, 0x2);
    uint32_t bypass = device->mmioRead32(0, ENGINE_BYPASS);
    cout << "Bypass mode: " << (bypass & 0x3) << "\n" << endl;

    // Issue simple MATMUL command
    cout << "Issuing MATMUL command..." << endl;
    uint32_t cmd = (OPCODE_MATMUL << 0) | (1 << 8) | (12 << 16);
    device->mmioWrite32(0, ENGINE_CMD_WORD0, cmd);
    device->mmioWrite32(0, ENGINE_CMD_WORD0+4, 0);  // word1
    device->mmioWrite32(0, ENGINE_CMD_WORD0+8, (4 << 13) | (4 << 5));  // B=4, C=4
    device->mmioWrite32(0, ENGINE_CMD_WORD0+12, (32 << 8));  // V=32
    device->mmioWrite32(0, ENGINE_CMD_SUBMIT, 0x1);

    // Poll engine status
    cout << "\nEngine status during execution:" << endl;
    for (int i = 0; i < 20; i++) {
        uint32_t status = device->mmioRead32(0, ENGINE_STATUS);
        uint32_t mc_state = (status >> 16) & 0xF;
        uint32_t dc_state = (status >> 8) & 0xF;
        uint32_t ce_state = status & 0xF;
        uint32_t busy = status & 0x1;

        cout << "  [" << setw(2) << i << "] STATUS=0x" << hex << setw(8) << setfill('0') << status;
        cout << " MC=" << dec << mc_state << " DC=" << dc_state << " CE=" << ce_state;
        cout << " busy=" << busy << endl;

        if (!busy && i > 0) {
            cout << "\n✅ Engine went idle after " << i << " polls" << endl;
            break;
        }

        usleep(1000);  // 1ms delay
    }

    return 0;
}
