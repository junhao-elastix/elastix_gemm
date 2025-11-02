#include <iostream>
#include <vector>
#include <cstring>
#include "vp815.hpp"

using namespace std;
using namespace achronix;

int main() {
    cout << "=== Large DMA Read Test ===" << endl;
    
    VP815 device(0);
    if (!device.isReady()) {
        cerr << "Device not ready" << endl;
        return 1;
    }
    
    device.print_info();
    
    // Test progressively larger sizes
    vector<size_t> test_sizes = {256, 1024, 4096, 8192, 16896};
    
    const uint64_t test_addr = 0x0;  // GDDR6 base
    
    for (size_t size : test_sizes) {
        cout << "\n=== Testing " << size << " bytes ===" << endl;
        
        vector<uint8_t> write_buf(size);
        vector<uint8_t> read_buf(size, 0);
        
        // Fill with pattern
        for (size_t i = 0; i < size; i += 4) {
            uint32_t value = 0xDEAD0000 + (i / 4);
            memcpy(&write_buf[i], &value, 4);
        }
        
        // Write
        cout << "  Writing " << size << " bytes..." << flush;
        if (!device.dmaWrite(test_addr, size, (char*)write_buf.data())) {
            cerr << " FAILED" << endl;
            continue;
        }
        cout << " OK" << endl;
        
        // Read back
        cout << "  Reading " << size << " bytes..." << flush;
        if (!device.dmaRead(test_addr, size, (char*)read_buf.data())) {
            cerr << " FAILED" << endl;
            continue;
        }
        cout << " OK" << endl;
        
        // Verify
        bool match = (write_buf == read_buf);
        cout << "  Verification: " << (match ? "PASS" : "FAIL") << endl;
        
        if (!match) {
            cout << "  First mismatch at offset: ";
            for (size_t i = 0; i < size; ++i) {
                if (write_buf[i] != read_buf[i]) {
                    cout << i << " (wrote 0x" << hex << (int)write_buf[i] 
                         << ", read 0x" << (int)read_buf[i] << dec << ")" << endl;
                    break;
                }
            }
        }
    }
    
    return 0;
}



