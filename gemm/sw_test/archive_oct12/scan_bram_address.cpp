// Scan for Result BRAM at new NAP location
// Tests different address offsets to find where BRAM is mapped

#include <iostream>
#include <iomanip>
#include <cstdint>
#include <Achronix_device.h>

using namespace std;

int main() {
    ACX_DEV_PCIe_device* device = nullptr;

    if (acx_device_init(&device, ACX_DEV_ACHRONIX, 0) != ACX_SDK_STATUS_OK) {
        cerr << "Failed to initialize device" << endl;
        return 1;
    }

    cout << "Scanning for Result BRAM (testing NAP address change from [8][7] to [3][5])..." << endl;

    // Known old address
    uint64_t old_addr = 0x4460008000ULL;

    // Try scanning different NAP encodings
    uint64_t test_addrs[] = {
        0x4460008000ULL,  // Original [8][7]
        0x4438008000ULL,  // Guess for [3][5] based on pattern
        0x4430008000ULL,  // Another guess
        0x4435008000ULL,  // Another guess
        0x443F008000ULL,  // Linear calc guess
        0x4447008000ULL,  // Another pattern
    };

    cout << "\nTesting addresses:" << endl;
    for (int i = 0; i < 6; i++) {
        uint64_t addr = test_addrs[i];

        // Try writing a test pattern
        uint32_t test_pattern = 0xDEADBEEF;
        acx_device_write32(device, addr, test_pattern);

        // Read back
        uint32_t readback;
        acx_device_read32(device, addr, &readback);

        cout << "  0x" << hex << setw(12) << setfill('0') << addr << ": ";
        if (readback == test_pattern) {
            cout << "✅ BRAM FOUND! (write/read successful)" << endl;
        } else if (readback == 0xFFFFFFFF) {
            cout << "❌ No device (0xFFFFFFFF)" << endl;
        } else {
            cout << "⚠️  Read 0x" << hex << readback << " (different value)" << endl;
        }
    }

    acx_device_close(device);
    return 0;
}
