#include <iostream>
#include <iomanip>
#include <memory>
#include <unistd.h>
#include "vp815.hpp"

using namespace std;
using namespace achronix;

#define ENGINE_DEBUG     0x44
#define ENGINE_CMD_WORD0 0x28
#define ENGINE_CMD_SUBMIT 0x38
#define ENGINE_STATUS    0x3C
#define OPCODE_MATMUL    0xF2

int main() {
    cout << "\n=== Command Queue Debug (Enhanced) ===" << endl;

    unique_ptr<VP815> device = make_unique<VP815>(0);

    // Decode debug register (new format)
    auto decode_debug = [](uint32_t debug) {
        uint8_t opcode = (debug >> 24) & 0xFF;
        uint8_t submitted = (debug >> 16) & 0xFF;
        uint8_t read = (debug >> 8) & 0xFF;
        uint8_t completed = debug & 0xFF;

        cout << "  ENGINE_DEBUG: 0x" << hex << setw(8) << setfill('0') << debug << dec << endl;
        cout << "    Opcode:    0x" << hex << setw(2) << (int)opcode << dec;
        if (opcode == OPCODE_MATMUL) cout << " (MATMUL)";
        cout << endl;
        cout << "    Submitted: " << (int)submitted << endl;
        cout << "    Read:      " << (int)read << endl;
        cout << "    Completed: " << (int)completed << endl;
        cout << "    Pending:   " << (submitted - completed) << " commands" << endl;
    };

    // Read initial state
    uint32_t debug_before = device->mmioRead32(0, ENGINE_DEBUG);
    cout << "Before command:" << endl;
    decode_debug(debug_before);

    // Issue MATMUL command
    cout << "\nIssuing MATMUL command..." << endl;
    device->mmioWrite32(0, ENGINE_CMD_WORD0, (OPCODE_MATMUL << 0) | (1 << 8) | (12 << 16));
    device->mmioWrite32(0, ENGINE_CMD_WORD0+4, 0);
    device->mmioWrite32(0, ENGINE_CMD_WORD0+8, (4 << 13) | (4 << 5));
    device->mmioWrite32(0, ENGINE_CMD_WORD0+12, (32 << 8));
    device->mmioWrite32(0, ENGINE_CMD_SUBMIT, 0x1);

    // Poll status
    cout << "\nPolling engine status..." << endl;
    for (int i = 0; i < 10; i++) {
        usleep(1000);  // 1ms

        uint32_t status = device->mmioRead32(0, ENGINE_STATUS);
        uint32_t debug = device->mmioRead32(0, ENGINE_DEBUG);

        uint8_t mc_state = (status >> 16) & 0xF;
        uint8_t dc_state = (status >> 8) & 0xF;
        uint8_t ce_state = status & 0xF;

        uint8_t submitted = (debug >> 16) & 0xFF;
        uint8_t read = (debug >> 8) & 0xFF;
        uint8_t completed = debug & 0xFF;

        cout << "  [" << setw(2) << i << "] ";
        cout << "MC=" << mc_state << " DC=" << dc_state << " CE=" << ce_state;
        cout << " | sub=" << (int)submitted << " rd=" << (int)read << " cmp=" << (int)completed;
        cout << " | pend=" << (submitted - completed) << endl;

        if (mc_state == 0 && dc_state == 0 && ce_state == 0 && (submitted == completed)) {
            cout << "\n✅ Command completed after " << (i+1) << " polls" << endl;
            break;
        }
    }

    // Final state
    cout << "\nAfter command:" << endl;
    uint32_t debug_after = device->mmioRead32(0, ENGINE_DEBUG);
    decode_debug(debug_after);

    // Analysis
    uint8_t sub_before = (debug_before >> 16) & 0xFF;
    uint8_t cmp_before = debug_before & 0xFF;
    uint8_t sub_after = (debug_after >> 16) & 0xFF;
    uint8_t cmp_after = debug_after & 0xFF;

    cout << "\n=== Analysis ===" << endl;
    if (sub_after > sub_before) {
        cout << "✅ Command was submitted (count increased)" << endl;
    } else {
        cout << "❌ Command was NOT submitted" << endl;
    }

    if (cmp_after > cmp_before) {
        cout << "✅ Command was completed (completion count increased)" << endl;
    } else {
        cout << "❌ Command did NOT complete" << endl;
    }

    return 0;
}
