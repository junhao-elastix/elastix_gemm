#include <iostream>
#include <iomanip>
#include "acxpcie.h"

using namespace std;

int main() {
    // Initialize device
    acxpcie_device_t dev_handle;
    if (acxpcie_init(&dev_handle, 0) != ACXPCIE_SUCCESS) {
        cerr << "Failed to initialize device" << endl;
        return 1;
    }
    
    // Check result count register
    uint32_t result_count;
    acxpcie_mmio_read32(dev_handle, 0, 0x54, &result_count);
    cout << "Result count register: " << dec << result_count << " (0x" << hex << result_count << ")" << dec << endl;
    
    // Check status
    uint32_t status;
    acxpcie_mmio_read32(dev_handle, 0, 0x50, &status);
    cout << "ENGINE_STATUS: 0x" << hex << status << dec << endl;
    cout << "  mc_state: " << ((status >> 12) & 0xF) << endl;
    cout << "  dc_state: " << ((status >> 8) & 0xF) << endl;
    cout << "  ce_state: " << ((status >> 4) & 0xF) << endl;
    cout << "  busy: " << (status & 0x1) << endl;
    
    // Try reading first few FP16 values from BRAM (BAR2)
    cout << "\nReading first 16 FP16 values from Result BRAM (BAR2 offset 0):" << endl;
    for (int i = 0; i < 16; i++) {
        uint32_t val;
        acxpcie_mmio_read32(dev_handle, 2, i*4, &val);
        cout << "  Word[" << dec << i << "] = 0x" << hex << setw(8) << setfill('0') << val << dec << endl;
    }
    
    acxpcie_close(dev_handle);
    return 0;
}
