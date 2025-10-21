#include <iostream>
#include <iomanip>
#include <memory>
#include "vp815.hpp"

using namespace std;
using namespace achronix;

#define NAP_ERROR_STATUS  18  // Register 18 @ offset 0x48

int main() {
    unique_ptr<VP815> device;
    try {
        device = make_unique<VP815>(0);
        cout << "✅ Device initialized" << endl;
    } catch (const exception& e) {
        cerr << "ERROR: " << e.what() << endl;
        return 1;
    }

    uint32_t nap_status;
    device->mmioRead32(0, NAP_ERROR_STATUS * 4, nap_status);
    
    cout << "NAP Error Status (Reg 18 @ 0x48): 0x" << hex << setw(8) << setfill('0') << nap_status << endl;
    cout << "  error_valid: " << dec << ((nap_status >> 3) & 0x1) << endl;
    cout << "  error_info:  0x" << hex << (nap_status & 0x7) << dec << endl;
    
    return 0;
}
