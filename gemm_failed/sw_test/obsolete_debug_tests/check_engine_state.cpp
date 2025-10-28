#include <iostream>
#include <iomanip>
#include "../../../eus/shell/devices/acx/vp815/api/vp815.hpp"
using namespace std;
using namespace achronix;

int main() {
    VP815 device(0);
    
    cout << "=== Engine Status Registers ===" << endl;
    
    uint32_t status = device.mmioRead32(0, 0x3C);  // ENGINE_STATUS
    cout << "ENGINE_STATUS (Reg 15 @ 0x3C): 0x" << hex << setw(8) << setfill('0') << status << dec << endl;
    cout << "  MC State (current): " << ((status >> 8) & 0xF) << endl;
    cout << "  DC State: " << ((status >> 4) & 0xF) << endl;
    cout << "  CE State: " << (status & 0xF) << endl;
    cout << "  MC State (next): " << ((status >> 12) & 0xF) << endl;
    
    uint32_t cmd_ptr = device.mmioRead32(0, 0x38);  // ENGINE_CMD_PTR
    cout << "\nENGINE_CMD_PTR (Reg 14 @ 0x38): " << cmd_ptr << endl;
    
    uint32_t result_count = device.mmioRead32(0, 0x40);  // ENGINE_RESULT_COUNT
    cout << "ENGINE_RESULT_COUNT (Reg 16 @ 0x40): " << result_count << endl;
    
    cout << "\n=== Command Registers ===" << endl;
    cout << "ENGINE_CMD_WORD0 (@ 0x28): 0x" << hex << setw(8) << setfill('0') 
         << device.mmioRead32(0, 0x28) << dec << endl;
    cout << "ENGINE_CMD_WORD1 (@ 0x2C): 0x" << hex << setw(8) << setfill('0') 
         << device.mmioRead32(0, 0x2C) << dec << endl;
    cout << "ENGINE_CMD_WORD2 (@ 0x30): 0x" << hex << setw(8) << setfill('0') 
         << device.mmioRead32(0, 0x30) << dec << endl;
    cout << "ENGINE_CMD_WORD3 (@ 0x34): 0x" << hex << setw(8) << setfill('0') 
         << device.mmioRead32(0, 0x34) << dec << endl;
    
    return 0;
}
