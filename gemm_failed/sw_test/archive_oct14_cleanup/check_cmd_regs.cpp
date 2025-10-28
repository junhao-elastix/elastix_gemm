#include "vp815.hpp"
#include <iostream>
#include <iomanip>
using namespace std;
using namespace achronix;

int main() {
    VP815 device(0);
    if (!device.isReady()) return 1;
    
    cout << "Writing test command words..." << endl;
    device.mmioWrite32(0, 0x3C, 0xDEADBEEF);
    device.mmioWrite32(0, 0x40, 0xCAFEBABE);
    device.mmioWrite32(0, 0x44, 0x12345678);
    device.mmioWrite32(0, 0x48, 0x87654321);
    
    cout << "Reading back..." << endl;
    uint32_t w0 = device.mmioRead32(0, 0x3C);
    uint32_t w1 = device.mmioRead32(0, 0x40);
    uint32_t w2 = device.mmioRead32(0, 0x44);
    uint32_t w3 = device.mmioRead32(0, 0x48);
    
    cout << "  CMD_WORD0: 0x" << hex << setw(8) << setfill('0') << w0 << dec << endl;
    cout << "  CMD_WORD1: 0x" << hex << setw(8) << setfill('0') << w1 << dec << endl;
    cout << "  CMD_WORD2: 0x" << hex << setw(8) << setfill('0') << w2 << dec << endl;
    cout << "  CMD_WORD3: 0x" << hex << setw(8) << setfill('0') << w3 << dec << endl;
    
    if (w0 == 0xDEADBEEF && w1 == 0xCAFEBABE && w2 == 0x12345678 && w3 == 0x87654321) {
        cout << "\n✓ Command registers are readable/writable" << endl;
    } else {
        cout << "\n✗ Command registers NOT working correctly!" << endl;
    }
    
    return 0;
}
