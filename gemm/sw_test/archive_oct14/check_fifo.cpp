#include "acxpcie_device.h"
#include <iostream>
#include <cstdint>
#include <iomanip>

int main() {
    AcxpcieDev device;
    if (!device.init("/dev/ac7t15xx0")) {
        std::cerr << "Failed to initialize device" << std::endl;
        return 1;
    }

    std::cout << "=== Engine Debug Registers ===" << std::endl;
    
    uint32_t status = device.read_reg(0x50);
    uint32_t result_count = device.read_reg(0x54);
    uint32_t engine_debug = device.read_reg(0x58);
    uint32_t bcv_debug = device.read_reg(0x5C);
    
    std::cout << "ENGINE_STATUS (0x50): 0x" << std::hex << std::setw(8) << std::setfill('0') << status << std::endl;
    std::cout << "  busy: " << ((status >> 0) & 1) << std::endl;
    
    std::cout << "ENGINE_RESULT_COUNT (0x54): " << std::dec << result_count << std::endl;
    
    std::cout << "ENGINE_DEBUG (0x58): 0x" << std::hex << std::setw(8) << std::setfill('0') << engine_debug << std::endl;
    std::cout << "  last_opcode: 0x" << std::hex << ((engine_debug >> 4) & 0xFF) << std::endl;
    std::cout << "  mc_state: 0x" << std::hex << (engine_debug & 0xF) << std::endl;
    std::cout << "  cmd_fifo_count: " << std::dec << ((engine_debug >> 12) & 0x7F) << " / 64" << std::endl;
    
    std::cout << "BCV_DEBUG (0x5C): 0x" << std::hex << std::setw(8) << std::setfill('0') << bcv_debug << std::endl;

    return 0;
}
