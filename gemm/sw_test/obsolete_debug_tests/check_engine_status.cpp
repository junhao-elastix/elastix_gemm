#include <iostream>
#include <iomanip>
#include <cstdint>
#include <unistd.h>
#include "/home/dev/Dev/elastix_gemm/gemm/src/cpp/vp815_device.hpp"

int main() {
    std::cout << "=== Engine Status Detailed Check ===" << std::endl;
    
    auto device = VP815Device::getInstance(0);
    if (!device) {
        std::cerr << "Failed to initialize device" << std::endl;
        return 1;
    }
    
    uint32_t engine_debug, engine_status, result_count;
    device->mmioRead32(0, 0x38, engine_debug);
    device->mmioRead32(0, 0x3C, engine_status);
    device->mmioRead32(0, 0x40, result_count);
    
    std::cout << std::hex;
    std::cout << "ENGINE_DEBUG (0x38): 0x" << engine_debug << std::endl;
    std::cout << "  opcode: 0x" << ((engine_debug >> 24) & 0xFF) << std::endl;
    std::cout << "  cmd_submitted: " << std::dec << ((engine_debug >> 16) & 0xFF) << std::hex << std::endl;
    std::cout << "  payload_words: " << std::dec << ((engine_debug >> 8) & 0xFF) << std::hex << std::endl;
    std::cout << "  nonzero_count: " << std::dec << ((engine_debug >> 4) & 0xF) << std::hex << std::endl;
    std::cout << "  count_low: " << std::dec << (engine_debug & 0xF) << std::hex << std::endl;
    
    std::cout << "\nENGINE_STATUS (0x3C): 0x" << engine_status << std::endl;
    std::cout << "  mc_state_next: 0x" << ((engine_status >> 20) & 0xF) << std::endl;
    std::cout << "  mc_state: 0x" << ((engine_status >> 16) & 0xF) << std::endl;
    std::cout << "  dc_state: 0x" << ((engine_status >> 8) & 0xF) << std::endl;
    std::cout << "  ce_state: 0x" << (engine_status & 0xF) << std::endl;
    
    std::cout << "\nRESULT_COUNT (0x40): " << std::dec << result_count << std::endl;
    
    // Read debug registers
    uint32_t ce_addr, ce_data_low, ce_data_mid, ce_control, dc_write, dc_control;
    device->mmioRead32(0, 0x08, ce_addr);
    device->mmioRead32(0, 0x0C, ce_data_low);
    device->mmioRead32(0, 0x10, ce_data_mid);
    device->mmioRead32(0, 0x14, ce_control);
    device->mmioRead32(0, 0x18, dc_write);
    device->mmioRead32(0, 0x1C, dc_control);
    
    std::cout << "\n=== Debug Registers ===" << std::hex << std::endl;
    std::cout << "CE_BRAM_ADDR (0x08): 0x" << ce_addr << " (dec: " << std::dec << ce_addr << ")" << std::hex << std::endl;
    std::cout << "CE_CONTROL (0x14): 0x" << ce_control << std::endl;
    std::cout << "  rd_en: " << ((ce_control >> 12) & 0x1) << std::endl;
    std::cout << "  load_count: " << ((ce_control >> 11) & 0x1) << std::endl;
    std::cout << "  ce_state: " << std::dec << (ce_control & 0xF) << std::hex << std::endl;
    
    std::cout << "DC_WRITE (0x18): 0x" << dc_write << std::endl;
    std::cout << "  wr_en: " << ((dc_write >> 12) & 0x1) << std::endl;
    std::cout << "  wr_addr: " << std::dec << (dc_write & 0x7FF) << std::hex << std::endl;
    
    std::cout << "DC_CONTROL (0x1C): 0x" << dc_control << std::endl;
    std::cout << "  fetch_done: " << ((dc_control >> 8) & 0x1) << std::endl;
    std::cout << "  disp_done: " << ((dc_control >> 9) & 0x1) << std::endl;
    std::cout << "  dc_state: " << std::dec << (dc_control & 0xF) << std::hex << std::endl;
    
    return 0;
}
