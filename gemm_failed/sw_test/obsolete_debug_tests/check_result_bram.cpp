#include <iostream>
#include <iomanip>
#include "../../../eus/shell/devices/acx/vp815/api/vp815.hpp"

using namespace std;

int main() {
    VP815 device(0);
    
    cout << "Reading Result BRAM (first 16 words):" << endl;
    for (int i = 0; i < 16; i++) {
        uint32_t val = device.bar2Read32(0x8000 + i*4);
        cout << "  [" << dec << i << "]: 0x" << hex << setw(8) << setfill('0') << val << dec << endl;
    }
    
    return 0;
}
