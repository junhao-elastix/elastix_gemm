// Debug FETCH command - monitor states in real-time
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

#define GDDR6_BASE          0x00000000ULL

int main() {
    cout << "FETCH Command Debug Test" << endl;
    cout << "=========================" << endl << endl;

    // Initialize device
    unique_ptr<VP815> device;
    try {
        device = make_unique<VP815>(0);
        cout << "✅ Device initialized" << endl << endl;
    } catch (const exception& e) {
        cerr << "ERROR: " << e.what() << endl;
        return 1;
    }

    // Write small test pattern to GDDR6
    cout << "Writing test pattern to GDDR6..." << endl;
    uint8_t test_data[512];
    for (int i = 0; i < 512; i++) {
        test_data[i] = i & 0xFF;
    }
    device->dmaWrite(GDDR6_BASE, 512, (char*)test_data);
    cout << "✅ 512 bytes written" << endl << endl;

    // Read initial state
    uint32_t status, debug;
    device->mmioRead32(0, ENGINE_STATUS * 4, status);
    device->mmioRead32(0, ENGINE_DEBUG * 4, debug);

    cout << "Initial State:" << endl;
    cout << "  MC State: " << ((status >> 12) & 0xF) << endl;  // FIXED: MC at [15:12]
    cout << "  DC State: " << ((status >> 8) & 0xF) << endl;   // FIXED: DC at [11:8]
    cout << "  CE State: " << ((status >> 4) & 0xF) << endl << endl;  // FIXED: CE at [7:4]

    // Issue FETCH command
    cout << "Issuing FETCH command (16 lines from GDDR6 @ 0x0)..." << endl;

    uint32_t cmd_word0 = (0xF0 << 0) | (1 << 8) | (12 << 16);  // FETCH, id=1, len=12
    uint32_t cmd_word1 = 0x00000000;  // GDDR6 address 0
    uint32_t cmd_word2 = 16;          // 16 lines
    uint32_t cmd_word3 = 0x00000000;

    device->mmioWrite32(0, ENGINE_CMD_WORD0 * 4, cmd_word0);
    device->mmioWrite32(0, ENGINE_CMD_WORD1 * 4, cmd_word1);
    device->mmioWrite32(0, ENGINE_CMD_WORD2 * 4, cmd_word2);
    device->mmioWrite32(0, ENGINE_CMD_WORD3 * 4, cmd_word3);

    // Submit with pulse
    device->mmioWrite32(0, ENGINE_CMD_SUBMIT * 4, 0x1);
    this_thread::sleep_for(chrono::microseconds(10));
    device->mmioWrite32(0, ENGINE_CMD_SUBMIT * 4, 0x0);

    cout << "✅ Command submitted" << endl << endl;

    // Monitor states for 1000 iterations (100ms total)
    cout << "Monitoring states (100µs per sample, 100ms total):" << endl;
    cout << "Iter | MC | DC | CE | MC_Next | Debug" << endl;
    cout << "-----+----+----+----+---------+------" << endl;

    uint32_t prev_mc = 99, prev_dc = 99, prev_ce = 99;
    int stable_count = 0;

    for (int i = 0; i < 1000; i++) {
        device->mmioRead32(0, ENGINE_STATUS * 4, status);
        device->mmioRead32(0, ENGINE_DEBUG * 4, debug);

        uint32_t mc_state = (status >> 12) & 0xF;  // FIXED: MC at [15:12]
        uint32_t dc_state = (status >> 8) & 0xF;   // FIXED: DC at [11:8]
        uint32_t ce_state = (status >> 4) & 0xF;   // FIXED: CE at [7:4]
        uint32_t mc_next = (status >> 16) & 0xF;   // FIXED: MC_Next at [19:16]

        // Print when state changes or every 100 iterations
        if (mc_state != prev_mc || dc_state != prev_dc || ce_state != prev_ce || (i % 100 == 0)) {
            cout << setw(4) << i << " |"
                 << setw(3) << dec << mc_state << " |"
                 << setw(3) << dec << dc_state << " |"
                 << setw(3) << dec << ce_state << " |"
                 << setw(8) << dec << mc_next << " | 0x"
                 << hex << setw(8) << setfill('0') << debug << dec << endl;

            prev_mc = mc_state;
            prev_dc = dc_state;
            prev_ce = ce_state;
            stable_count = 0;
        } else {
            stable_count++;
        }

        // If MC returns to IDLE, we're done
        if (mc_state == 0 && i > 10) {
            cout << "\n✅ Master Control returned to IDLE after " << i << " iterations" << endl;
            break;
        }

        // If stuck in same state for 200 iterations, likely hung
        if (stable_count > 200) {
            cout << "\n❌ HUNG: States stable for 200+ iterations" << endl;
            cout << "   MC=" << mc_state << ", DC=" << dc_state << ", CE=" << ce_state << endl;
            break;
        }

        this_thread::sleep_for(chrono::microseconds(100));
    }

    // Final state check
    cout << endl;
    device->mmioRead32(0, ENGINE_STATUS * 4, status);
    device->mmioRead32(0, ENGINE_DEBUG * 4, debug);

    cout << "Final State:" << endl;
    cout << "  MC State: " << ((status >> 12) & 0xF) << endl;  // FIXED: MC at [15:12]
    cout << "  DC State: " << ((status >> 8) & 0xF) << endl;   // FIXED: DC at [11:8]
    cout << "  CE State: " << ((status >> 4) & 0xF) << endl;   // FIXED: CE at [7:4]
    cout << "  Debug: 0x" << hex << setw(8) << setfill('0') << debug << dec << endl;

    return 0;
}
