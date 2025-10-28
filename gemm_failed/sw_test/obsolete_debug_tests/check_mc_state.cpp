#include <iostream>
#include <iomanip>
#include <memory>
#include "vp815.hpp"

using namespace std;
using namespace achronix;

#define ENGINE_STATUS 0x3C

int main() {
    unique_ptr<VP815> device = make_unique<VP815>(0);
    uint32_t status = device->mmioRead32(0, ENGINE_STATUS);
    
    cout << "ENGINE_STATUS: 0x" << hex << setw(8) << setfill('0') << status << dec << endl;
    cout << "  MC state: " << ((status >> 16) & 0xF);
    
    int mc = (status >> 16) & 0xF;
    if (mc == 0) cout << " (IDLE)";
    else if (mc == 1) cout << " (READ_HDR)";
    else if (mc == 5) cout << " (DECODE)";
    else if (mc == 8) cout << " (EXEC_TILE)";
    else if (mc == 11) cout << " (WAIT_DONE)";
    cout << endl;
    
    cout << "  DC state: " << ((status >> 8) & 0xF) << endl;
    cout << "  CE state: " << (status & 0xF) << endl;
    
    return 0;
}
