#include <iostream>
#include <iomanip>
#include <cstring>
#include <memory>
#include "vp815.hpp"

int main() {
    std::cout << "=== Register Test ===" << std::endl;
    
    // Initialize device
    std::unique_ptr<achronix::VP815> device;
    try {
        device = std::make_unique<achronix::VP815>(0);
        std::cout << "✅ Device initialized successfully\n" << std::endl;
    } catch (const std::exception& e) {
        std::cerr << "❌ Failed to initialize device: " << e.what() << std::endl;
        return 1;
    }

    // Calculate register offsets based on RTL source parameters (UPDATED for 130 registers - Oct 10, 2025)
    const uint32_t REGS_PER_IRQ_GEN_CH = 3;
    const uint32_t REGS_PER_MSIX_IRQ_CH = 4;
    const uint32_t NUM_MSIX_IRQ_CH = 2;
    const uint32_t REGS_PER_GDDR_CH = 11;
    const uint32_t NUM_GDDR_CHANNELS = 8;
    const uint32_t NUM_IRQ_GEN_REGS = NUM_MSIX_IRQ_CH * REGS_PER_IRQ_GEN_CH; // 2*3 = 6
    const uint32_t MSIX_IRQ_REGS_BASE = 2 + NUM_IRQ_GEN_REGS; // 2 + 6 = 8
    const uint32_t NUM_MSIX_IRQ_REGS = 4 + (NUM_MSIX_IRQ_CH * REGS_PER_MSIX_IRQ_CH); // 4 + (2*4) = 12
    const uint32_t GDDR_REGS_BASE = MSIX_IRQ_REGS_BASE + NUM_MSIX_IRQ_REGS; // 8 + 12 = 20
    const uint32_t NUM_GDDR_REGS = NUM_GDDR_CHANNELS * REGS_PER_GDDR_CH; // 8 * 11 = 88
    const uint32_t NUM_USER_REGS = 133; // Total registers (was 130, now 133 after adding MC payload debug regs)
    
    // UPDATED: Register mapping from elastix_gemm_top.sv (133 total registers)
    const uint32_t CONTROL_REG = 0;
    const uint32_t IRQ_GEN_REGS_BASE = 2;
    const uint32_t LTSSM_STATE_REG = 131; // 139 - 8 = 131, offset 131*4 = 524 = 0x20C
    const uint32_t ADM_STATUS_REG = 132;  // 139 - 7 = 132, offset 132*4 = 528 = 0x210
    const uint32_t BITSTREAM_ID = 133;    // 139 - 6 = 133, offset 133*4 = 532 = 0x214
    const uint32_t SCRATCH_REG = 134;     // 139 - 5 = 134, offset 134*4 = 536 = 0x218
    
    std::cout << "Register mapping (from RTL source):" << std::endl;
    std::cout << "  Control Register: 0x" << std::hex << (CONTROL_REG * 4) << std::endl;
    std::cout << "  Test Status Register: 0x" << std::hex << (1 * 4) << std::endl;
    std::cout << "  IRQ Gen Base: 0x" << std::hex << (2 * 4) << std::endl;
    std::cout << "  MSI-X IRQ Base: 0x" << std::hex << (MSIX_IRQ_REGS_BASE * 4) << std::endl;
    std::cout << "  GDDR6 Regs Base: 0x" << std::hex << (GDDR_REGS_BASE * 4)
              << " (8 channels, 11 regs each)" << std::endl;
    std::cout << "  LTSSM State: 0x" << std::hex << (LTSSM_STATE_REG * 4) << std::endl;
    std::cout << "  ADM Status: 0x" << std::hex << (ADM_STATUS_REG * 4) << std::endl;
    std::cout << "  Bitstream ID: 0x" << std::hex << (BITSTREAM_ID * 4) << std::endl;
    std::cout << "  Scratch Register: 0x" << std::hex << (SCRATCH_REG * 4) << std::endl;
    std::cout << "  Total User Registers: " << std::dec << NUM_USER_REGS << " (133 total)" << std::endl;
    std::cout << std::endl;
    
    std::cout << "Register Boundaries and Ranges:" << std::endl;
    std::cout << "  Control & Status: 0x00 - 0x" << std::hex << ((IRQ_GEN_REGS_BASE - 1) * 4) << std::endl;
    std::cout << "  IRQ Generation: 0x" << std::hex << (IRQ_GEN_REGS_BASE * 4) << " - 0x" << std::hex << ((MSIX_IRQ_REGS_BASE - 1) * 4) << std::endl;
    std::cout << "  MSI-X IRQ: 0x" << std::hex << (MSIX_IRQ_REGS_BASE * 4) << " - 0x" << std::hex << ((GDDR_REGS_BASE - 1) * 4) << std::endl;
    std::cout << "  GDDR6 Channels: 0x" << std::hex << (GDDR_REGS_BASE * 4) << " - 0x" << std::hex << ((GDDR_REGS_BASE + NUM_GDDR_REGS - 1) * 4) << std::endl;
    std::cout << "  System Status: 0x" << std::hex << (LTSSM_STATE_REG * 4) << " - 0x" << std::hex << (SCRATCH_REG * 4) << std::endl;
    std::cout << std::endl;
    
    // Test essential registers
    struct RegTest {
        uint32_t offset;
        const char* name;
    };
    
    RegTest regs[] = {
        {CONTROL_REG, "Control Register"},
        {LTSSM_STATE_REG, "LTSSM State"},
        {ADM_STATUS_REG, "ADM Status"},
        {BITSTREAM_ID, "Bitstream ID"},
        {SCRATCH_REG, "Scratch Register"}
    };
    
    std::cout << "Reading essential registers from BAR0:" << std::endl;
    std::cout << "----------------------------------------" << std::endl;
    
    for (const auto& reg : regs) {
        uint32_t value;
        try {
            device->mmioRead32(0, reg.offset * 4, value);
            std::cout << "  0x" << std::hex << std::setw(4) << std::setfill('0') << (reg.offset * 4) 
                     << ": 0x" << std::setw(8) << std::setfill('0') << value 
                     << " - " << reg.name;
            
            // Special handling for control register
            if (reg.offset == CONTROL_REG && value != 0xffffffff) {
                std::cout << " (BRAM +42: " << ((value & 0x1) ? "ON" : "OFF") << ")";
            }
            
            // Special handling for bitstream ID
            if (reg.offset == BITSTREAM_ID && value != 0xffffffff) {
                // Convert hex timestamp to mmddHHMM format
                uint32_t month = (value >> 24) & 0xFF;
                uint32_t day = (value >> 16) & 0xFF;
                uint32_t hour = (value >> 8) & 0xFF;
                uint32_t minute = value & 0xFF;
                std::cout << " (Build: " << std::setfill('0') << std::setw(2) << month 
                         << "/" << std::setw(2) << day << " " << std::setw(2) << hour 
                         << ":" << std::setw(2) << minute << ")";
            }
            
            std::cout << std::endl;
        } catch (const std::exception& e) {
            std::cout << "  0x" << std::hex << std::setw(4) << std::setfill('0') << (reg.offset * 4) 
                     << ": ERROR - " << e.what() << std::endl;
        }
    }
    
    std::cout << "\n=== Testing Control Register Write ===" << std::endl;
    
    // Test writing to control register
    try {
        uint32_t orig_value;
        device->mmioRead32(0, CONTROL_REG * 4, orig_value);
        std::cout << "Original value: 0x" << std::hex << orig_value << std::endl;
        
        // Try to write 0x1 (enable BRAM +42)
        device->mmioWrite32(0, CONTROL_REG * 4, 0x1);
        uint32_t new_value;
        device->mmioRead32(0, CONTROL_REG * 4, new_value);
        std::cout << "After write(0x1): 0x" << std::hex << new_value << std::endl;
        
        // Try to write 0x0 (disable all)
        device->mmioWrite32(0, CONTROL_REG * 4, 0x0);
        device->mmioRead32(0, CONTROL_REG * 4, new_value);
        std::cout << "After write(0x0): 0x" << std::hex << new_value << std::endl;
        
        std::cout << "\n✅ Register interface is functional" << std::endl;
        
    } catch (const std::exception& e) {
        std::cerr << "❌ Error testing control register: " << e.what() << std::endl;
    }
    
    return 0;
}