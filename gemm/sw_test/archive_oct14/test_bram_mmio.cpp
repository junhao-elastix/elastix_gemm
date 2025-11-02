#include "vp815.hpp"
#include "Achronix_util.h"
#include <iostream>
#include <vector>

using namespace std;
using namespace achronix;

int main() {
    cout << "=== Result BRAM MMIO Test ===" << endl;
    
    try {
        VP815 device(0);
        if (!device.isReady()) {
            cerr << "ERROR: Device not ready" << endl;
            return 1;
        }
        
        // Try reading from result BRAM using MMIO on different BARs
        cout << "\n[Test] Trying MMIO read from different BARs..." << endl;
        
        for (uint32_t bar = 0; bar < 6; bar++) {
            try {
                uint32_t value = device.mmioRead32(bar, 0x0);
                cout << "  BAR" << bar << "[0x0] = 0x" << hex << value << dec << endl;
            } catch (...) {
                cout << "  BAR" << bar << ": Not accessible" << endl;
            }
        }
        
        return 0;
        
    } catch (const exception& e) {
        cerr << "ERROR: " << e.what() << endl;
        return 1;
    }
}
