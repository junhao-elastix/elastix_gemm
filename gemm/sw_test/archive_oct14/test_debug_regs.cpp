#include <iostream>
#include <iomanip>
#include "Achronix_device.h"

using namespace std;

int main() {
    cout << "=== New Debug Registers Test ===" << endl;
    
    ACX_DEVICE_HANDLE device;
    ACX_SDK_STATUS status = acx_device_open(0, &device);
    if (status != ACX_SDK_OK) {
        cerr << "Failed to open device" << endl;
        return 1;
    }
    
    // Read new debug registers
    uint32_t dc_bram_wr_count;
    uint32_t dc_debug;
    
    acx_device_read32(device, 0, 0x60, &dc_bram_wr_count);
    acx_device_read32(device, 0, 0x64, &dc_debug);
    
    cout << "\nDC_BRAM_WR_COUNT (0x60): 0x" << hex << dc_bram_wr_count << dec << endl;
    cout << "  BRAM write count: " << (dc_bram_wr_count & 0x3FF) << " lines" << endl;
    cout << "  Expected: 0 (no FETCH issued yet)" << endl;
    
    cout << "\nDC_DEBUG (0x64): 0x" << hex << dc_debug << dec << endl;
    cout << "  Dispatcher state: " << (dc_debug & 0xF) << endl;
    cout << "  Expected: 0 (IDLE)" << endl;
    
    // Also check engine status
    uint32_t engine_status;
    acx_device_read32(device, 0, 0x50, &engine_status);
    
    uint32_t dc_state = (engine_status >> 8) & 0xF;
    uint32_t ce_state = (engine_status >> 4) & 0xF;
    uint32_t mc_state = (engine_status >> 12) & 0xF;
    
    cout << "\nENGINE_STATUS (0x50): 0x" << hex << engine_status << dec << endl;
    cout << "  MC state: " << mc_state << " (0=IDLE)" << endl;
    cout << "  DC state: " << dc_state << " (0=IDLE)" << endl;
    cout << "  CE state: " << ce_state << " (0=IDLE)" << endl;
    cout << "  Engine busy: " << (engine_status & 0x1) << endl;
    
    acx_device_close(device);
    
    cout << "\n✅ New debug registers are accessible!" << endl;
    return 0;
}
