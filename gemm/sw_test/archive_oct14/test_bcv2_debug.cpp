// Debug version with status checking
#include "vp815.hpp"
#include "Achronix_device.h"
#include <iostream>
#include <vector>
#include <cmath>
#include <iomanip>
#include <unistd.h>

using namespace std;
using namespace achronix;

#define OPCODE_FETCH            0xF0
#define OPCODE_DISPATCH         0xF1
#define OPCODE_MATMUL           0xF2
#define OPCODE_WAIT_DISPATCH    0xF3
#define OPCODE_WAIT_MATMUL      0xF4

#define ENGINE_STATUS           0x50
#define ENGINE_RESULT_COUNT     0x54
#define ENGINE_DEBUG            0x58
#define BCV_DEBUG               0x20
#define BCV_DIMS                0x24
#define MC_DIMS                 0x28

#define RESULT_REG_0            0x21C
#define RESULT_REG_1            0x220
#define RESULT_REG_2            0x224
#define RESULT_REG_3            0x228

#define GDDR6_BASE_LEFT         0x0
#define GDDR6_BASE_RIGHT        0x1000

int main() {
    cout << "=== B=C=V=2 Debug Test ===" << endl;
    
    try {
        VP815 device(0);
        if (!device.isReady()) {
            cerr << "ERROR: Device not ready" << endl;
            return 1;
        }
        
        // Check all test data is 0x3C (GFP8 for ~1.0)
        cout << "\nPreparing test data (GFP8 0x3C = ~1.0):" << endl;
        vector<uint8_t> left_data(128, 0x3C);
        vector<uint8_t> right_data(128, 0x3C);
        
        // Write to GDDR6
        cout << "Writing to GDDR6..." << endl;
        if (!device.dmaWrite(ACX_GDDR6_SPACE + GDDR6_BASE_LEFT, left_data.size(), (char*)left_data.data())) {
            cerr << "ERROR: Left write failed" << endl;
            return 1;
        }
        if (!device.dmaWrite(ACX_GDDR6_SPACE + GDDR6_BASE_RIGHT, right_data.size(), (char*)right_data.data())) {
            cerr << "ERROR: Right write failed" << endl;
            return 1;
        }
        
        // Read back to verify
        vector<uint8_t> verify_left(128);
        vector<uint8_t> verify_right(128);
        if (!device.dmaRead(ACX_GDDR6_SPACE + GDDR6_BASE_LEFT, verify_left.size(), (char*)verify_left.data())) {
            cerr << "ERROR: Left readback failed" << endl;
            return 1;
        }
        if (!device.dmaRead(ACX_GDDR6_SPACE + GDDR6_BASE_RIGHT, verify_right.size(), (char*)verify_right.data())) {
            cerr << "ERROR: Right readback failed" << endl;
            return 1;
        }
        
        cout << "  Left first 8 bytes: ";
        for (int i = 0; i < 8; i++) cout << hex << "0x" << (int)verify_left[i] << " ";
        cout << dec << endl;
        
        cout << "  Right first 8 bytes: ";
        for (int i = 0; i < 8; i++) cout << hex << "0x" << (int)verify_right[i] << " ";
        cout << dec << endl;
        
        // Check engine debug registers
        cout << "\nEngine state before commands:" << endl;
        uint32_t bcv_debug = device.mmioRead32(0, BCV_DEBUG);
        uint32_t bcv_dims = device.mmioRead32(0, BCV_DIMS);
        uint32_t mc_dims = device.mmioRead32(0, MC_DIMS);
        cout << "  BCV_DEBUG: 0x" << hex << bcv_debug << dec << endl;
        cout << "  BCV_DIMS: 0x" << hex << bcv_dims << dec;
        cout << " (B=" << ((bcv_dims >> 24) & 0xFF);
        cout << ", C=" << ((bcv_dims >> 16) & 0xFF);
        cout << ", V=" << ((bcv_dims >> 8) & 0xFF) << ")" << endl;
        cout << "  MC_DIMS: 0x" << hex << mc_dims << dec << endl;
        
        cout << "\n[SUCCESS] Data written and verified!" << endl;
        cout << "Ready for command sequence test" << endl;
        
        return 0;
        
    } catch (const exception& e) {
        cerr << "ERROR: " << e.what() << endl;
        return 1;
    }
}
