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
#define OPCODE_MATMUL    0xF2

int main() {
    cout << "\n=== FIFO Signal Debug ===" << endl;

    unique_ptr<VP815> device = make_unique<VP815>(0);

    // Before command
    uint32_t status_before = device->mmioRead32(0, ENGINE_STATUS);
    cout << "Before command - ENGINE_STATUS: 0x" << hex << setw(8) << setfill('0') << status_before << dec << endl;
    cout << "  MC state:    " << ((status_before >> 16) & 0xF) << endl;
    cout << "  DC state:    " << ((status_before >> 8) & 0xF) << endl;
    cout << "  CE state:    " << ((status_before >> 0) & 0xF) << endl;
    cout << "  MC busy:     " << ((status_before >> 24) & 0x1) << endl;

    // Issue command
    cout << "\nIssuing MATMUL command..." << endl;
    device->mmioWrite32(0, ENGINE_CMD_WORD0, (OPCODE_MATMUL << 0) | (1 << 8) | (12 << 16));
    device->mmioWrite32(0, ENGINE_CMD_WORD0+4, 0);
    device->mmioWrite32(0, ENGINE_CMD_WORD0+8, (4 << 13) | (4 << 5));
    device->mmioWrite32(0, ENGINE_CMD_WORD0+12, (32 << 8));
    device->mmioWrite32(0, ENGINE_CMD_SUBMIT, 0x1);

    usleep(10000);  // 10ms

    // After command
    uint32_t status_after = device->mmioRead32(0, ENGINE_STATUS);
    uint32_t debug_after = device->mmioRead32(0, ENGINE_DEBUG);

    cout << "\nAfter command - ENGINE_STATUS: 0x" << hex << setw(8) << setfill('0') << status_after << dec << endl;
    cout << "  MC state:    " << ((status_after >> 16) & 0xF) << endl;
    cout << "  DC state:    " << ((status_after >> 8) & 0xF) << endl;
    cout << "  CE state:    " << ((status_after >> 0) & 0xF) << endl;
    cout << "  MC busy:     " << ((status_after >> 24) & 0x1) << endl;

    cout << "\nCommand Queue (ENGINE_DEBUG): 0x" << hex << setw(8) << setfill('0') << debug_after << dec << endl;
    cout << "  Opcode:    0x" << hex << ((debug_after >> 24) & 0xFF) << dec << endl;
    cout << "  Submitted: " << ((debug_after >> 16) & 0xFF) << endl;
    cout << "  Read:      " << ((debug_after >> 8) & 0xFF) << endl;
    cout << "  Completed: " << (debug_after & 0xFF) << endl;

    return 0;
}
