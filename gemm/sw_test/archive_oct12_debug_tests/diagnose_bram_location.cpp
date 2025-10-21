// Diagnose BRAM location mismatch after NAP move
// Check: Where is writer writing? Where are we reading?

#include <iostream>
#include <iomanip>
#include "vp815.hpp"

using namespace std;

int main() {
    cout << "=== BRAM Location Diagnosis ===" << endl;

    auto device = make_unique<achronix::VP815>(0);

    uint64_t old_addr = 0x4460008000ULL;  // NAP[8][7] - OLD location

    // Pattern: Try addresses near NAP[3][5]
    // If NAP[8][7] = 0x4460008000, then pattern might be:
    // Base 0x44 + (NAP_encoding) + offset 0x8000

    uint64_t test_addrs[] = {
        0x4460008000ULL,  // OLD: NAP[8][7]
        0x4438008000ULL,  // Guess: NAP[3][5] pattern 1
        0x4335008000ULL,  // Guess: NAP[3][5] pattern 2
        0x4430008000ULL,  // Guess: NAP[3][5] pattern 3
        0x4434008000ULL,  // Guess: NAP[3][5] pattern 4
        0x4470008000ULL,  // ATU BRAM: NAP[7][7]
    };

    const char* labels[] = {
        "OLD [8][7]",
        "Guess [3][5] v1",
        "Guess [3][5] v2",
        "Guess [3][5] v3",
        "Guess [3][5] v4",
        "ATU [7][7]"
    };

    cout << "\n[Test 1] Checking if BRAMs exist at these addresses..." << endl;
    for (int i = 0; i < 6; i++) {
        uint32_t pattern = 0x12340000 + i;
        uint32_t readback;

        device->mmioWrite32(2, test_addrs[i], pattern);  // BAR2 for BRAM
        device->mmioRead32(2, test_addrs[i], readback);

        cout << "  " << labels[i] << " (0x" << hex << test_addrs[i] << "): ";
        if (readback == pattern) {
            cout << "✅ BRAM EXISTS (R/W works)" << endl;
        } else if (readback == 0xFFFFFFFF) {
            cout << "❌ NO DEVICE (0xFFFFFFFF)" << endl;
        } else {
            cout << "⚠️  READ 0x" << hex << readback << " (unexpected)" << endl;
        }
    }

    cout << "\n[Test 2] Check ENGINE_RESULT_COUNT register..." << endl;
    uint32_t result_count;
    device->mmioRead32(0, 0x28, result_count);  // ENGINE_RESULT_COUNT at offset 0x28
    cout << "  Result count: " << dec << result_count << " (writer thinks it wrote this many)" << endl;

    if (result_count > 0) {
        cout << "  ✅ Writer IS active (count > 0)" << endl;
        cout << "  → Problem is likely: reading from WRONG BRAM address" << endl;
    } else {
        cout << "  ❌ Writer NOT active (count = 0)" << endl;
        cout << "  → Problem is: writer signals not reaching BRAM" << endl;
    }

    cout << "\n[Test 3] If writer was active, try to find where data went..." << endl;
    if (result_count > 0) {
        cout << "  Scanning all test addresses for non-zero data:" << endl;
        for (int i = 0; i < 6; i++) {
            uint32_t data;
            device->mmioRead32(2, test_addrs[i], data);  // BAR2 for BRAM
            cout << "    " << labels[i] << ": 0x" << hex << setw(8) << setfill('0') << data;
            if (data != 0 && data != 0xFFFFFFFF) {
                cout << " ← DATA FOUND!" << endl;
            } else {
                cout << endl;
            }
        }
    }

    return 0;
}
