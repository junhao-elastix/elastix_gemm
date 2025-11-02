#include <iostream>
#include <iomanip>
#include "vp815.hpp"

using namespace std;
using namespace achronix;

int main() {
    VP815 device;
    
    cout << "Reading Result BRAM (BAR2 @ 0x4460008000):" << endl;
    uint64_t result_bram = 0x4460008000ULL;
    
    uint16_t results[16];
    if (!device.dmaRead(result_bram, 32, (char*)results)) {
        cerr << "ERROR: DMA read failed" << endl;
        return 1;
    }
    
    cout << "FP16 values (hex):" << endl;
    for (int i = 0; i < 16; i++) {
        cout << "  [" << dec << i << "] = 0x" << hex << setw(4) << setfill('0') 
             << results[i] << dec << endl;
    }
    
    return 0;
}
