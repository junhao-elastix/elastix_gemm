#include <iostream>
#include <iomanip>
#include "../../../eus/shell/devices/acx/vp815/api/vp815.hpp"

int main() {
    achronix::VP815 device(0);
    
    std::cout << "MS2.0 Engine Status and Command Payload:" << std::endl;
    std::cout << "========================================" << std::endl;
    
    // Engine status
    uint32_t status = device.mmioRead32(0, 0x50);
    std::cout << "ENGINE_STATUS (0x50): 0x" << std::hex << status << std::dec << " (busy=" << (status & 0x1) << ")" << std::endl;
    
    // Result count
    uint32_t result_count = device.mmioRead32(0, 0x54);
    std::cout << "RESULT_COUNT (0x54):  0x" << std::hex << result_count << std::dec << " (" << result_count << " results)" << std::endl;
    
    // MC Payload debug registers
    uint32_t mc_word1 = device.mmioRead32(0, 0x2C);
    uint32_t mc_word2 = device.mmioRead32(0, 0x30);
    uint32_t mc_word3 = device.mmioRead32(0, 0x34);
    
    std::cout << "\nLast Command Payload (MC Debug Registers):" << std::endl;
    std::cout << "MC_PAYLOAD_WORD1 (0x2C): 0x" << std::hex << std::setw(8) << std::setfill('0') << mc_word1 << std::dec << std::endl;
    std::cout << "MC_PAYLOAD_WORD2 (0x30): 0x" << std::hex << std::setw(8) << std::setfill('0') << mc_word2 << std::dec << std::endl;
    std::cout << "MC_PAYLOAD_WORD3 (0x34): 0x" << std::hex << std::setw(8) << std::setfill('0') << mc_word3 << std::dec << std::endl;
    
    return 0;
}
