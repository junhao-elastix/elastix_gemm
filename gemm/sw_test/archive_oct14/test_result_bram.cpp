#include "vp815.hpp"
#include "Achronix_util.h"
#include <iostream>
#include <vector>
#include <iomanip>

using namespace std;
using namespace achronix;

// Result BRAM at NAP[3][4]
#define BRAM_RESULT_BASE        0x4130000000ULL

int main() {
    cout << "=== Result BRAM DMA Test ===" << endl;
    
    try {
        VP815 device(0);
        if (!device.isReady()) {
            cerr << "ERROR: Device not ready" << endl;
            return 1;
        }
        
        device.print_info();
        
        // Try to write some test data to BRAM
        cout << "\n[Test 1] Writing test pattern to result BRAM..." << endl;
        vector<uint32_t> test_data(16);
        for (size_t i = 0; i < test_data.size(); i++) {
            test_data[i] = 0x1000 + i;
        }
        
        if (!device.dmaWrite(BRAM_RESULT_BASE, test_data.size() * sizeof(uint32_t), 
                            (char*)test_data.data())) {
            cerr << "  ERROR: DMA write failed" << endl;
            return 1;
        }
        cout << "  [PASS] DMA write successful" << endl;
        
        // Try to read it back
        cout << "\n[Test 2] Reading back from result BRAM..." << endl;
        vector<uint32_t> read_data(16, 0);
        if (!device.dmaRead(BRAM_RESULT_BASE, read_data.size() * sizeof(uint32_t), 
                           (char*)read_data.data())) {
            cerr << "  ERROR: DMA read failed" << endl;
            return 1;
        }
        cout << "  [PASS] DMA read successful" << endl;
        
        // Verify data
        cout << "\n[Test 3] Verifying data..." << endl;
        bool match = true;
        for (size_t i = 0; i < test_data.size(); i++) {
            if (read_data[i] != test_data[i]) {
                cout << "  Mismatch at [" << i << "]: wrote 0x" << hex << test_data[i] 
                     << ", read 0x" << read_data[i] << dec << endl;
                match = false;
            }
        }
        
        if (match) {
            cout << "  [PASS] Data integrity verified!" << endl;
            cout << "\n=== Result BRAM DMA is working ===" << endl;
            return 0;
        } else {
            cout << "  [FAIL] Data mismatch" << endl;
            return 1;
        }
        
    } catch (const exception& e) {
        cerr << "ERROR: " << e.what() << endl;
        return 1;
    }
}


