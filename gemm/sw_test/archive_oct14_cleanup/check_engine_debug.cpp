#include "vp815.hpp"
#include <iostream>
#include <iomanip>

using namespace std;
using namespace achronix;

int main() {
    cout << "=== Engine Debug Register Check ===" << endl;
    
    VP815 device(0);
    if (!device.isReady()) {
        cerr << "ERROR: Device not ready" << endl;
        return 1;
    }
    
    // Read all engine debug registers
    uint32_t engine_status = device.mmioRead32(0, 0x30);
    uint32_t engine_result_count = device.mmioRead32(0, 0x34);
    uint32_t engine_debug = device.mmioRead32(0, 0x38);
    
    cout << "\nEngine Status Registers:" << endl;
    cout << "  ENGINE_STATUS (0x30): 0x" << hex << setw(8) << setfill('0') << engine_status << dec;
    cout << " (busy=" << (engine_status & 0x1) << ")" << endl;
    
    cout << "  ENGINE_RESULT_COUNT (0x34): 0x" << hex << setw(8) << setfill('0') << engine_result_count << dec;
    cout << " (" << dec << (engine_result_count & 0xFFFF) << " FP16 results)" << endl;
    
    cout << "  ENGINE_DEBUG (0x38): 0x" << hex << setw(8) << setfill('0') << engine_debug << dec << endl;
    
    // Decode ENGINE_STATUS
    uint8_t mc_state = (engine_status >> 8) & 0xF;
    uint8_t mc_state_next = (engine_status >> 12) & 0xF;
    uint8_t dc_state = (engine_status >> 4) & 0xF;
    uint8_t ce_state = (engine_status >> 16) & 0xF;
    
    cout << "\n  Decoded ENGINE_STATUS:" << endl;
    cout << "    mc_state: 0x" << hex << (int)mc_state << dec << endl;
    cout << "    mc_state_next: 0x" << hex << (int)mc_state_next << dec << endl;
    cout << "    dc_state: 0x" << hex << (int)dc_state << dec << endl;
    cout << "    ce_state: 0x" << hex << (int)ce_state << dec << endl;
    
    // Read result FIFO count from engine
    uint32_t result_fifo_count = (engine_result_count >> 16) & 0x7FFF;
    cout << "\n  Result FIFO count: " << result_fifo_count << endl;
    
    // Read result registers
    cout << "\nResult Registers:" << endl;
    uint32_t r0 = device.mmioRead32(0, 0x21C);
    uint32_t r1 = device.mmioRead32(0, 0x220);
    uint32_t r2 = device.mmioRead32(0, 0x224);
    uint32_t r3 = device.mmioRead32(0, 0x228);
    
    cout << "  RESULT_REG_0: 0x" << hex << setw(8) << setfill('0') << r0 << dec;
    cout << " (FP16: 0x" << hex << (r0 & 0xFFFF) << ")" << dec << endl;
    cout << "  RESULT_REG_1: 0x" << hex << setw(8) << setfill('0') << r1 << dec;
    cout << " (FP16: 0x" << hex << (r1 & 0xFFFF) << ")" << dec << endl;
    cout << "  RESULT_REG_2: 0x" << hex << setw(8) << setfill('0') << r2 << dec;
    cout << " (FP16: 0x" << hex << (r2 & 0xFFFF) << ")" << dec << endl;
    cout << "  RESULT_REG_3: 0x" << hex << setw(8) << setfill('0') << r3 << dec;
    cout << " (FP16: 0x" << hex << (r3 & 0xFFFF) << ")" << dec << endl;
    
    return 0;
}
