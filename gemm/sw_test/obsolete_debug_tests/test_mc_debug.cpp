#include <iostream>
#include <iomanip>
#include <memory>
#include <unistd.h>
#include "vp815.hpp"

using namespace std;
using namespace achronix;

#define ENGINE_STATUS    0x08  
#define ENGINE_DEBUG     0x44
#define ENGINE_CMD_WORD0 0x28
#define ENGINE_CMD_SUBMIT 0x38
#define OPCODE_MATMUL    0xF2

int main() {
    cout << "\n=== Master Control Debug ===" << endl;

    unique_ptr<VP815> device = make_unique<VP815>(0);

    cout << "Issuing MATMUL command..." << endl;
    device->mmioWrite32(0, ENGINE_CMD_WORD0, (OPCODE_MATMUL << 0) | (1 << 8) | (12 << 16));
    device->mmioWrite32(0, ENGINE_CMD_WORD0+4, 0);
    device->mmioWrite32(0, ENGINE_CMD_WORD0+8, (4 << 13) | (4 << 5));
    device->mmioWrite32(0, ENGINE_CMD_WORD0+12, (32 << 8));
    device->mmioWrite32(0, ENGINE_CMD_SUBMIT, 0x1);

    usleep(1000);

    uint32_t status = device->mmioRead32(0, ENGINE_STATUS);
    uint32_t debug = device->mmioRead32(0, ENGINE_DEBUG);

    uint8_t mc_state = (status >> 16) & 0xF;
    uint8_t mc_state_next = (status >> 20) & 0xF;

    uint8_t submitted = (debug >> 16) & 0xFF;
    uint8_t read = (debug >> 8) & 0xFF;
    uint8_t completed = debug & 0xFF;
    uint8_t pending = submitted - completed;

    cout << "\nCommand Queue State:" << endl;
    cout << "  Submitted: " << (int)submitted << endl;
    cout << "  Read:      " << (int)read << endl;
    cout << "  Completed: " << (int)completed << endl;
    cout << "  Pending:   " << (int)pending << endl;

    cout << "\nMaster Control State:" << endl;
    cout << "  MC state:      " << (int)mc_state << " (0=IDLE)" << endl;
    cout << "  MC state_next: " << (int)mc_state_next << endl;

    cout << "\n=== Analysis ===" << endl;
    cout << "cmd_fifo_count should be: " << (int)pending << endl;
    cout << "cmd_fifo_empty should be: " << (pending == 0 ? "TRUE" : "FALSE") << endl;
    
    if (mc_state == 0) {
        cout << "\n❌ MC stuck in IDLE - command not executing!" << endl;
        cout << "Root cause: MC sees cmd_fifo_count=0 or cmd_fifo_empty=TRUE" << endl;
        cout << "But wrapper has pending=" << (int)pending << " commands" << endl;
    } else {
        cout << "\n✅ MC executing command (left IDLE)" << endl;
    }

    return 0;
}
