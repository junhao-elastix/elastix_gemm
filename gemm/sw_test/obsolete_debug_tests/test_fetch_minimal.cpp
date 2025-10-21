// Minimal FETCH command test - NO DMA write first
// Tests if FETCH command triggers dispatcher FSM without device hang
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

void readStates(unique_ptr<VP815>& device, const string& label, bool detailed = false) {
    uint32_t status, debug;
    device->mmioRead32(0, ENGINE_STATUS * 4, status);
    device->mmioRead32(0, ENGINE_DEBUG * 4, debug);

    uint32_t mc_state = (status >> 12) & 0xF;
    uint32_t dc_state = (status >> 8) & 0xF;
    uint32_t ce_state = (status >> 4) & 0xF;
    uint32_t mc_next = (status >> 16) & 0xF;
    uint32_t busy = status & 0x1;

    cout << label << ": MC=" << mc_state << " DC=" << dc_state << " CE=" << ce_state;

    if (detailed) {
        cout << " (Next=" << mc_next << " Busy=" << busy << ")";
        uint32_t opcode = (debug >> 24) & 0xFF;
        uint32_t submit_total = (debug >> 16) & 0xFF;
        cout << " | Debug: op=0x" << hex << setw(2) << setfill('0') << opcode
             << " submit=" << dec << submit_total;
    }
    cout << endl;
}

int main() {
    cout << "=== MINIMAL FETCH COMMAND TEST ===" << endl;
    cout << "Testing FETCH without preliminary DMA write" << endl;
    cout << "===================================" << endl << endl;

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
    readStates(device, "Initial State", true);
    cout << endl;

    // Build FETCH command
    // Format: [31:24]=reserved(0), [23:16]=len(12), [15:8]=id(1), [7:0]=op(0xF0)
    // Payload word1: Start address (in 128B chunks) = 0 (GDDR6 address 0x0)
    // Payload word2: Number of lines = 16 (16 × 32 bytes = 512 bytes)

    cout << "Issuing FETCH command:" << endl;
    cout << "  Opcode: 0xF0 (FETCH)" << endl;
    cout << "  ID: 1" << endl;
    cout << "  Length: 12 bytes" << endl;
    cout << "  Start Address: 0x0 (GDDR6)" << endl;
    cout << "  Lines to fetch: 16 (512 bytes)" << endl << endl;

    uint32_t cmd_fetch_word0 = (0x00 << 24) | (12 << 16) | (1 << 8) | (0xF0 << 0);
    uint32_t cmd_fetch_word1 = 0x00000000;  // Start address = 0
    uint32_t cmd_fetch_word2 = 16;          // 16 lines

    issueCommand(device, cmd_fetch_word0, cmd_fetch_word1, cmd_fetch_word2, 0);
    cout << "✅ Command submitted" << endl << endl;

    // Monitor states for up to 1000 iterations (100ms total @ 100µs per sample)
    cout << "Monitoring FSM states (100µs per sample, 100ms max):" << endl;
    cout << "Iter | MC | DC | CE | Status" << endl;
    cout << "-----+----+----+----+-------" << endl;

    uint32_t prev_mc = 99, prev_dc = 99, prev_ce = 99;
    bool mc_returned_to_idle = false;
    bool dc_returned_to_idle = false;
    int mc_idle_at = -1;
    int dc_idle_at = -1;

    for (int i = 0; i < 1000; i++) {
        uint32_t status;
        device->mmioRead32(0, ENGINE_STATUS * 4, status);

        uint32_t mc_state = (status >> 12) & 0xF;
        uint32_t dc_state = (status >> 8) & 0xF;
        uint32_t ce_state = (status >> 4) & 0xF;

        // Check for device hang (0xFFFFFFFF pattern)
        if (status == 0xFFFFFFFF) {
            cout << "\n❌ DEVICE HANG DETECTED at iteration " << i << endl;
            cout << "   STATUS register = 0xFFFFFFFF (PCIe link issue)" << endl;
            return 1;
        }

        // Print when state changes or every 100 iterations
        if (mc_state != prev_mc || dc_state != prev_dc || ce_state != prev_ce || (i % 100 == 0)) {
            cout << setw(4) << i << " |"
                 << setw(3) << dec << mc_state << " |"
                 << setw(3) << dec << dc_state << " |"
                 << setw(3) << dec << ce_state << " |";

            if (mc_state == 0 && prev_mc != 0 && !mc_returned_to_idle) {
                cout << " MC→IDLE";
                mc_returned_to_idle = true;
                mc_idle_at = i;
            }
            if (dc_state == 0 && prev_dc != 0 && !dc_returned_to_idle) {
                cout << " DC→IDLE";
                dc_returned_to_idle = true;
                dc_idle_at = i;
            }
            cout << endl;

            prev_mc = mc_state;
            prev_dc = dc_state;
            prev_ce = ce_state;
        }

        // Check for completion
        if (mc_state == 0 && dc_state == 0 && i > 10) {
            cout << "\n✅ Both FSMs returned to IDLE after " << i << " iterations (~"
                 << (i * 100) << "µs)" << endl;
            break;
        }

        // Check for stuck states
        if (i == 999) {
            cout << "\n⚠️ TIMEOUT: FSMs did not return to IDLE within 100ms" << endl;
            cout << "   Final states: MC=" << mc_state << " DC=" << dc_state << " CE=" << ce_state << endl;
        }

        this_thread::sleep_for(chrono::microseconds(100));
    }

    // Final state check
    cout << endl;
    readStates(device, "Final State", true);
    cout << endl;

    // Summary
    cout << "=== TEST SUMMARY ===" << endl;
    if (mc_returned_to_idle) {
        cout << "✅ Master Control FSM: Completed (returned to IDLE at " << mc_idle_at << " iterations)" << endl;
    } else {
        cout << "❌ Master Control FSM: Did not return to IDLE" << endl;
    }

    if (dc_returned_to_idle) {
        cout << "✅ Dispatcher Control FSM: Completed (returned to IDLE at " << dc_idle_at << " iterations)" << endl;
    } else {
        cout << "❌ Dispatcher Control FSM: Did not return to IDLE" << endl;
    }

    if (mc_returned_to_idle && dc_returned_to_idle) {
        cout << "\n🎉 FETCH COMMAND COMPLETED SUCCESSFULLY!" << endl;
        cout << "   NAP/GDDR6 path is operational (no device hang)" << endl;
        return 0;
    } else {
        cout << "\n❌ FETCH COMMAND DID NOT COMPLETE" << endl;
        cout << "   Check FSM states and debug further" << endl;
        return 1;
    }
}
