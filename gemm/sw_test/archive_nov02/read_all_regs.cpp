#include <iostream>
#include <iomanip>
#include "../../../eus/shell/devices/acx/vp815/api/vp815.hpp"

using namespace std;
using namespace achronix;

int main() {
    try {
        VP815 device(0);
        
        cout << "Key Engine Registers:" << endl;
        cout << "  0x50 (STATUS):        0x" << hex << setw(8) << setfill('0') << device.mmioRead32(0, 0x50) << dec << endl;
        cout << "  0x54 (RESULT_COUNT):  0x" << hex << setw(8) << setfill('0') << device.mmioRead32(0, 0x54) << dec << endl;
        cout << "  0x58 (DEBUG):         0x" << hex << setw(8) << setfill('0') << device.mmioRead32(0, 0x58) << dec << endl;
        cout << "  0x60 (BRAM_WR_CNT):   0x" << hex << setw(8) << setfill('0') << device.mmioRead32(0, 0x60) << dec << endl;
        cout << "  0x64 (DC_DEBUG):      0x" << hex << setw(8) << setfill('0') << device.mmioRead32(0, 0x64) << dec << endl;
        
        return 0;
    } catch (const exception& e) {
        cerr << "ERROR: " << e.what() << endl;
        return 1;
    }
}
