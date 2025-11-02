#include <iostream>
#include <iomanip>
#include <fstream>
#include <vector>
#include "../../../eus/shell/devices/acx/vp815/api/vp815.hpp"
#include "Achronix_device.h"
#include "Achronix_util.h"

using namespace std;
using namespace achronix;

int main() {
    try {
        VP815 device(0);
        
        // Read back left matrix from GDDR6 to verify DMA write
        uint64_t gddr6_left = 0x0;
        vector<uint8_t> readback(64);  // First 64 bytes
        
        if (!device.dmaRead(gddr6_left, 64, (char*)readback.data())) {
            cerr << "ERROR: Failed to read from GDDR6" << endl;
            return 1;
        }
        
        cout << "First 64 bytes from GDDR6 left matrix (addr 0x0):" << endl;
        for (int i = 0; i < 64; i++) {
            cout << hex << setw(2) << setfill('0') << (unsigned)readback[i] << " ";
            if ((i+1) % 16 == 0) cout << endl;
        }
        cout << dec << endl;
        
        // Also read first 64 bytes from right matrix
        uint64_t gddr6_right = 0x4200;
        if (!device.dmaRead(gddr6_right, 64, (char*)readback.data())) {
            cerr << "ERROR: Failed to read from GDDR6 right" << endl;
            return 1;
        }
        
        cout << "\nFirst 64 bytes from GDDR6 right matrix (addr 0x4200):" << endl;
        for (int i = 0; i < 64; i++) {
            cout << hex << setw(2) << setfill('0') << (unsigned)readback[i] << " ";
            if ((i+1) % 16 == 0) cout << endl;
        }
        cout << dec << endl;
        
        return 0;
    } catch (const exception& e) {
        cerr << "ERROR: " << e.what() << endl;
        return 1;
    }
}
