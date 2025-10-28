#include "vp815.hpp"
#include <iostream>
#include <iomanip>

using namespace std;
using namespace achronix;

int main() {
    cout << "=== Complete Engine Debug Dump ===" << endl;
    
    VP815 device(0);
    if (!device.isReady()) {
        cerr << "ERROR: Device not ready" << endl;
        return 1;
    }
    
    // Read ALL engine-related registers
    cout << "\nControl/Status:" << endl;
    uint32_t ctrl = device.mmioRead32(0, 0x00);
    cout << "  CONTROL (0x00): 0x" << hex << setw(8) << setfill('0') << ctrl << dec << endl;
    
    uint32_t engine_status = device.mmioRead32(0, 0x30);
    cout << "  ENGINE_STATUS (0x30): 0x" << hex << setw(8) << setfill('0') << engine_status << dec;
    cout << " (busy=" << (engine_status & 0x1) << ")" << endl;
    
    uint32_t engine_result_count = device.mmioRead32(0, 0x34);
    cout << "  ENGINE_RESULT_COUNT (0x34): 0x" << hex << setw(8) << setfill('0') << engine_result_count << dec;
    cout << " (" << (engine_result_count & 0xFFFF) << " FP16)" << endl;
    
    uint32_t engine_debug = device.mmioRead32(0, 0x38);
    cout << "  ENGINE_DEBUG (0x38): 0x" << hex << setw(8) << setfill('0') << engine_debug << dec << endl;
    
    // Try reading the command FIFO status (if accessible)
    cout << "\nCommand Interface:" << endl;
    uint32_t cmd_w0 = device.mmioRead32(0, 0x3C);
    uint32_t cmd_w1 = device.mmioRead32(0, 0x40);
    uint32_t cmd_w2 = device.mmioRead32(0, 0x44);
    uint32_t cmd_w3 = device.mmioRead32(0, 0x48);
    uint32_t cmd_submit = device.mmioRead32(0, 0x4C);
    cout << "  CMD_WORD0 (0x3C): 0x" << hex << setw(8) << setfill('0') << cmd_w0 << dec << endl;
    cout << "  CMD_WORD1 (0x40): 0x" << hex << setw(8) << setfill('0') << cmd_w1 << dec << endl;
    cout << "  CMD_WORD2 (0x44): 0x" << hex << setw(8) << setfill('0') << cmd_w2 << dec << endl;
    cout << "  CMD_WORD3 (0x48): 0x" << hex << setw(8) << setfill('0') << cmd_w3 << dec << endl;
    cout << "  CMD_SUBMIT (0x4C): 0x" << hex << setw(8) << setfill('0') << cmd_submit << dec << endl;
    
    // Check if there's a FIFO count register
    cout << "\nTrying additional debug registers:" << endl;
    for (uint32_t offset = 0x50; offset <= 0x64; offset += 4) {
        uint32_t val = device.mmioRead32(0, offset);
        cout << "  0x" << hex << setw(3) << setfill('0') << offset << ": 0x" 
             << setw(8) << setfill('0') << val << dec << endl;
    }
    
    return 0;
}
