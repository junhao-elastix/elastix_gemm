// Test MS2.0 state machine without GDDR6 access
// Tests WAIT_DISPATCH and WAIT_MATMUL commands that don't require memory
#include <iostream>
#include <iomanip>
#include <memory>
#include <chrono>
#include <thread>
#include "vp815.hpp"

using namespace std;
using namespace achronix;

#define ENGINE_CMD_WORD0    10
#define ENGINE_CMD_WORD1    11
#define ENGINE_CMD_WORD2    12
#define ENGINE_CMD_WORD3    13
#define ENGINE_CMD_SUBMIT   14
#define ENGINE_STATUS       15
#define ENGINE_DEBUG        17  // FIXED: Was 16, should be 17 per RTL

void issueCommand(unique_ptr<VP815>& device, uint32_t w0, uint32_t w1, uint32_t w2, uint32_t w3) {
    device->mmioWrite32(0, ENGINE_CMD_WORD0 * 4, w0);
    device->mmioWrite32(0, ENGINE_CMD_WORD1 * 4, w1);
    device->mmioWrite32(0, ENGINE_CMD_WORD2 * 4, w2);
    device->mmioWrite32(0, ENGINE_CMD_WORD3 * 4, w3);

    // Submit with pulse
    device->mmioWrite32(0, ENGINE_CMD_SUBMIT * 4, 0x1);
    this_thread::sleep_for(chrono::microseconds(10));
    device->mmioWrite32(0, ENGINE_CMD_SUBMIT * 4, 0x0);
}

void readStates(unique_ptr<VP815>& device, const string& label) {
    uint32_t status, debug;
    device->mmioRead32(0, ENGINE_STATUS * 4, status);
    device->mmioRead32(0, ENGINE_DEBUG * 4, debug);

    cout << label << ":" << endl;
    cout << "  STATUS: 0x" << hex << setw(8) << setfill('0') << status << dec << endl;
    cout << "    Engine Busy:         " << (status & 0x1) << endl;
    cout << "    CE State:            " << ((status >> 4) & 0xF) << endl;
    cout << "    DC State:            " << ((status >> 8) & 0xF) << endl;
    cout << "    MC State (current):  " << ((status >> 12) & 0xF) << endl;
    cout << "    MC State (next):     " << ((status >> 16) & 0xF) << endl;
    cout << "  DEBUG: 0x" << hex << setw(8) << setfill('0') << debug << dec << endl;
    cout << "    Captured Opcode:     0x" << hex << setw(2) << ((debug >> 24) & 0xFF) << dec << endl;
    cout << "    Submit Total:        " << ((debug >> 16) & 0xFF) << endl;
    cout << "    Payload Words:       " << ((debug >> 8) & 0x7) << endl;
    cout << "    Count Nonzero:       " << ((debug >> 4) & 0x1) << endl;
    cout << "    Count Value:         " << (debug & 0xF) << endl;
    cout << endl;
}

int main() {
    cout << "MS2.0 State Machine Test (NO GDDR6 Access)" << endl;
    cout << "===========================================" << endl << endl;

    // Initialize device
    unique_ptr<VP815> device;
    try {
        device = make_unique<VP815>(0);
        cout << "✅ Device initialized" << endl << endl;
    } catch (const exception& e) {
        cerr << "ERROR: " << e.what() << endl;
        return 1;
    }

    // Read initial state
    readStates(device, "Initial State");

    // Test 1: WAIT_DISPATCH command (0xF3)
    // This should complete immediately since no DISPATCH commands were issued
    cout << "Test 1: WAIT_DISPATCH Command (0xF3)" << endl;
    cout << "Command word0: [31:24]=wait_id(0), [23:16]=len(4), [15:8]=id(1), [7:0]=op(0xF3)" << endl;

    uint32_t cmd_wait_disp_w0 = (0x00 << 24) | (4 << 16) | (1 << 8) | (0xF3 << 0);  // wait_id=0, len=4, id=1, op=0xF3
    uint32_t cmd_wait_disp_w1 = 0x00000000;

    issueCommand(device, cmd_wait_disp_w0, cmd_wait_disp_w1, 0, 0);
    cout << "✅ Command submitted" << endl << endl;

    // Wait a bit for processing
    this_thread::sleep_for(chrono::milliseconds(1));

    readStates(device, "After WAIT_DISPATCH");

    // Test 2: WAIT_MATMUL command (0xF4)
    // This should also complete immediately
    cout << "Test 2: WAIT_MATMUL Command (0xF4)" << endl;
    cout << "Command word0: [31:24]=wait_id(0), [23:16]=len(4), [15:8]=id(2), [7:0]=op(0xF4)" << endl;

    uint32_t cmd_wait_tile_w0 = (0x00 << 24) | (4 << 16) | (2 << 8) | (0xF4 << 0);  // wait_id=0, len=4, id=2, op=0xF4
    uint32_t cmd_wait_tile_w1 = 0x00000000;

    issueCommand(device, cmd_wait_tile_w0, cmd_wait_tile_w1, 0, 0);
    cout << "✅ Command submitted" << endl << endl;

    // Wait a bit for processing
    this_thread::sleep_for(chrono::milliseconds(1));

    readStates(device, "After WAIT_MATMUL");

    // Test 3: Multiple WAIT commands in sequence
    cout << "Test 3: Rapid WAIT_DISPATCH Sequence (5 commands)" << endl;
    for (int i = 0; i < 5; i++) {
        uint32_t w0 = (0x00 << 24) | (4 << 16) | ((10 + i) << 8) | (0xF3 << 0);  // wait_id=0, len=4, varying id
        issueCommand(device, w0, 0, 0, 0);
        cout << "  Command " << (i+1) << " submitted (id=" << (10+i) << ")" << endl;
        this_thread::sleep_for(chrono::microseconds(100));
    }
    cout << "✅ All commands submitted" << endl << endl;

    // Wait for completion
    this_thread::sleep_for(chrono::milliseconds(2));

    readStates(device, "After Rapid Sequence");

    // Final state check - should be back to IDLE
    uint32_t status;
    device->mmioRead32(0, ENGINE_STATUS * 4, status);
    uint32_t mc_state = (status >> 12) & 0xF;  // FIXED: MC at bits [15:12]

    if (mc_state == 0) {
        cout << "✅ SUCCESS: Master Control returned to IDLE (state=0)" << endl;
        cout << "✅ Command FIFO logic is working correctly!" << endl;
        return 0;
    } else {
        cout << "❌ FAILURE: Master Control stuck in state=" << mc_state << endl;
        return 1;
    }
}
