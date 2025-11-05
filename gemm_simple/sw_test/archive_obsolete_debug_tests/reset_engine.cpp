// ============================================================================
// Engine Soft Reset Utility
//
// Asserts and releases soft-reset (Control Register bit 1) to clear all
// MS2.0 GEMM engine state and return FSMs to IDLE.
//
// Usage:
//   ./reset_engine
//
// Expected behavior:
//   - All FSMs (MC, DC, CE) return to state 0 (IDLE)
//   - Command FIFO cleared
//   - Engine ready for new commands
//
// Author: Debug utility for MS2.0 GEMM engine
// Date: Fri Oct 10 2025
// ============================================================================

#include <iostream>
#include <iomanip>
#include <unistd.h>
#include <memory>
#include "vp815.hpp"

using namespace std;

int main() {
    cout << "=== MS2.0 GEMM Engine Soft Reset ===" << endl;

    // Initialize device
    unique_ptr<achronix::VP815> device;
    try {
        device = make_unique<achronix::VP815>(0);
    } catch (const exception& e) {
        cerr << "ERROR: Failed to initialize device: " << e.what() << endl;
        return 1;
    }
    
    // Read status before reset
    uint32_t status_before;
    device->mmioRead32(0, 0x3C, status_before);
    cout << "\nEngine status BEFORE reset:" << endl;
    cout << "  ENGINE_STATUS: 0x" << hex << status_before << dec << endl;
    cout << "    mc_state: " << ((status_before >> 16) & 0xF) << endl;
    cout << "    dc_state: " << ((status_before >> 8) & 0xF) << endl;
    cout << "    ce_state: " << (status_before & 0xF) << endl;
    
    // Assert soft-reset (Control Register bit 1)
    cout << "\nAsserting soft-reset (Control[1] = 1)..." << endl;
    device->mmioWrite32(0, 0x0, 0x2);
    
    // Hold reset for 10ms
    usleep(10000);
    
    // Check status during reset (should show IDLE)
    uint32_t status_during;
    device->mmioRead32(0, 0x3C, status_during);
    cout << "  Status DURING reset: 0x" << hex << status_during << dec << endl;
    
    // Release soft-reset
    cout << "\nReleasing soft-reset (Control[1] = 0)..." << endl;
    device->mmioWrite32(0, 0x0, 0x0);
    
    // Wait for reset to complete
    usleep(10000);
    
    // Read status after reset
    uint32_t status_after;
    device->mmioRead32(0, 0x3C, status_after);
    cout << "\nEngine status AFTER reset:" << endl;
    cout << "  ENGINE_STATUS: 0x" << hex << status_after << dec << endl;
    cout << "    mc_state: " << ((status_after >> 16) & 0xF);
    if (((status_after >> 16) & 0xF) == 0) cout << " ✅ IDLE";
    cout << endl;
    cout << "    dc_state: " << ((status_after >> 8) & 0xF);
    if (((status_after >> 8) & 0xF) == 0) cout << " ✅ IDLE";
    cout << endl;
    cout << "    ce_state: " << (status_after & 0xF);
    if ((status_after & 0xF) == 0) cout << " ✅ IDLE";
    cout << endl;
    
    // Verify all FSMs returned to IDLE
    bool all_idle = (((status_after >> 16) & 0xF) == 0) &&
                    (((status_after >> 8) & 0xF) == 0) &&
                    ((status_after & 0xF) == 0);
    
    if (all_idle) {
        cout << "\n✅ Engine soft-reset SUCCESSFUL - All FSMs in IDLE" << endl;
        return 0;
    } else {
        cout << "\n❌ Engine soft-reset FAILED - FSMs not in IDLE" << endl;
        return 1;
    }
}
