#include <iostream>
#include <iomanip>
#include <cstring>
#include <cstdlib>
#include <memory>
#include "vp815.hpp"

using namespace std;
using namespace achronix;

// Register offsets matching RTL
#define REG_ENGINE_STATUS   0x08
#define REG_ENGINE_BYPASS   0x24  // ENGINE_BYPASS_CTRL at offset 9 * 4 = 0x24

int main(int argc, char* argv[]) {
    // Parse bypass mode from command line (default = 1)
    uint32_t bypass_mode = 1;
    if (argc > 1) {
        bypass_mode = atoi(argv[1]);
        if (bypass_mode > 2) {
            cerr << "Invalid bypass mode: " << bypass_mode << " (valid: 0-2)" << endl;
            return -1;
        }
    }

    cout << "\n=== Bypass Mode Test ===" << endl;

    // Initialize device using vp815 class
    unique_ptr<VP815> device;
    try {
        device = make_unique<VP815>(0);
        cout << "✅ Device initialized successfully\n" << endl;
    } catch (const exception& e) {
        cerr << "❌ Failed to initialize device: " << e.what() << endl;
        return -1;
    }

    // Read current bypass mode
    uint32_t bypass_val;
    device->mmioRead32(0, REG_ENGINE_BYPASS, bypass_val);
    cout << "Current bypass mode: 0x" << hex << setw(8) << setfill('0') << bypass_val
         << " (mode=" << dec << (bypass_val & 0x3) << ")" << endl;

    // Set bypass mode
    const char* mode_desc[] = {"Normal", "CE bypass", "Test pattern"};
    cout << "\nSetting bypass mode to " << bypass_mode << " (" << mode_desc[bypass_mode] << ")..." << endl;
    device->mmioWrite32(0, REG_ENGINE_BYPASS, bypass_mode);

    // Verify write
    device->mmioRead32(0, REG_ENGINE_BYPASS, bypass_val);
    cout << "Bypass mode after write: 0x" << hex << setw(8) << setfill('0') << bypass_val
         << " (mode=" << dec << (bypass_val & 0x3) << ")" << endl;

    if ((bypass_val & 0x3) != bypass_mode) {
        cerr << "❌ Failed to set bypass mode" << endl;
        return -1;
    }
    cout << "✅ Bypass mode set successfully" << endl;

    // Read initial engine status
    uint32_t status;
    device->mmioRead32(0, REG_ENGINE_STATUS, status);
    cout << "\nInitial ENGINE_STATUS: 0x" << hex << setw(5) << setfill('0') << status << dec << endl;
    cout << "  mc_state = 0x" << hex << ((status >> 16) & 0xF) << dec << endl;
    cout << "  dc_state = 0x" << hex << ((status >> 8) & 0xF) << dec << endl;
    cout << "  ce_state = 0x" << hex << (status & 0xF) << dec << endl;

    cout << "\n✅ Bypass mode " << bypass_mode << " configured" << endl;
    cout << "Ready to test with test_ms2_gemm_full" << endl;

    return 0;
}
