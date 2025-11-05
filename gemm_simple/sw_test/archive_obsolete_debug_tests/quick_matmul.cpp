#include <iostream>
#include <iomanip>
#include <chrono>
#include <thread>
#include "../../eus/shell/devices/acx/vp815/api/vp815.hpp"

#define ENGINE_STATUS 0x24
#define ENGINE_CMD0 0x28

using namespace std;

int main() {
    achronix::VP815 device(0);
    
    // Reset engine
    cout << "Resetting engine..." << endl;
    device.mmioWrite32(0, 0x0, 0x2);
    this_thread::sleep_for(chrono::milliseconds(10));
    device.mmioWrite32(0, 0x0, 0x0);
    this_thread::sleep_for(chrono::milliseconds(10));
    
    // Check status
    uint32_t status = device.mmioRead32(0, ENGINE_STATUS);
    cout << "ENGINE_STATUS after reset: 0x" << hex << status << dec << endl;
    cout << "  mc_state: " << ((status >> 16) & 0xF) << endl;
    cout << "  dc_state: " << ((status >> 8) & 0xF) << endl;
    cout << "  ce_state: " << ((status >> 4) & 0xF) << endl;
    cout << "  busy: " << (status & 0x1) << endl;
    
    // Send simple MATMUL command
    cout << "\nSending MATMUL command..." << endl;
    device.mmioWrite32(0, ENGINE_CMD0, 0xc09f2);     // opcode=0xF2, id=9, len=12
    device.mmioWrite32(0, ENGINE_CMD0+4, 0x20108000); // word1
    device.mmioWrite32(0, ENGINE_CMD0+8, 0x80100);    // word2
    device.mmioWrite32(0, ENGINE_CMD0+12, 0x20210);   // word3
    
    // Monitor status for 5 seconds
    cout << "\nMonitoring engine status for 5 seconds..." << endl;
    for (int i = 0; i < 50; i++) {
        this_thread::sleep_for(chrono::milliseconds(100));
        status = device.mmioRead32(0, ENGINE_STATUS);
        uint32_t mc_state = (status >> 16) & 0xF;
        uint32_t dc_state = (status >> 8) & 0xF;
        uint32_t ce_state = (status >> 4) & 0xF;
        uint32_t busy = status & 0x1;
        
        cout << "  [" << (i+1)*100 << "ms] MC=" << mc_state 
             << " DC=" << dc_state 
             << " CE=" << ce_state 
             << " busy=" << busy << endl;
        
        if (!busy) {
            cout << "Engine completed!" << endl;
            break;
        }
    }
    
    return 0;
}
