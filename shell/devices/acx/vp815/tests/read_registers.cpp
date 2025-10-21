/**
 * @file read_registers.cpp
 * @brief Simple utility to read and display control registers
 * 
 * This utility reads three registers and displays their values:
 * - LTSSM state register (PCIe link state) 
 * - ADM status register (device status)
 * - Scratch register (with MMDDHHMM format detection)
 */

#include "vp815.hpp"
#include <iostream>
#include <iomanip>

using namespace achronix;

int main() {
    std::cout << "=== Register Reader Utility ===" << std::endl;
    std::cout << "Reading control registers from BAR0..." << std::endl;
    std::cout << std::endl;
    
    try {
        VP815 device;
        if (!device.isReady()) {
            std::cerr << "❌ Device not ready!" << std::endl;
            return -1;
        }
        
        std::cout << "✅ Device initialized successfully" << std::endl;
        std::cout << std::endl;
        
        // Register offsets (BAR0) - Updated 2025-01-08 to match dma_test RTL
        const uint32_t LTSSM_STATE_REG_OFFSET = 0x7C;  // Register 31: LTSSM state
        const uint32_t ADM_STATUS_REG_OFFSET  = 0x80;  // Register 32: ADM status  
        const uint32_t SCRATCH_REG_OFFSET     = 0x84;  // Register 33: Scratch register
        
        // Read LTSSM State Register
        uint32_t ltssm_state = 0;
        if (device.mmioRead32(0, LTSSM_STATE_REG_OFFSET, ltssm_state)) {
            std::cout << "📡 LTSSM State Register (0x" << std::hex << LTSSM_STATE_REG_OFFSET << "):" << std::endl;
            std::cout << "   Value: 0x" << std::setfill('0') << std::setw(8) << std::hex << ltssm_state << std::endl;
        } else {
            std::cout << "❌ Failed to read LTSSM state register" << std::endl;
        }
        std::cout << std::endl;
        
        // Read ADM Status Register
        uint32_t adm_status = 0;
        if (device.mmioRead32(0, ADM_STATUS_REG_OFFSET, adm_status)) {
            std::cout << "🔧 ADM Status Register (0x" << std::hex << ADM_STATUS_REG_OFFSET << "):" << std::endl;
            std::cout << "   Value: 0x" << std::setfill('0') << std::setw(8) << std::hex << adm_status << std::endl;
        } else {
            std::cout << "❌ Failed to read ADM status register" << std::endl;
        }
        std::cout << std::endl;
        
        // Read Scratch Register
        uint32_t scratch_value = 0;
        if (device.mmioRead32(0, SCRATCH_REG_OFFSET, scratch_value)) {
            std::cout << "📝 Scratch Register (0x" << std::hex << SCRATCH_REG_OFFSET << "):" << std::endl;
            std::cout << "   Value: 0x" << std::setfill('0') << std::setw(8) << std::hex << scratch_value << std::endl;
            
            // Check if value matches MMDDHHMM format (8 hex digits)
            if (scratch_value >= 0x01010000 && scratch_value <= 0x12312359) {
                // Extract components
                int mm = (scratch_value >> 24) & 0xFF;
                int dd = (scratch_value >> 16) & 0xFF;
                int hours = (scratch_value >> 8) & 0xFF;
                int minutes = scratch_value & 0xFF;
                
                // Basic validation
                if (mm >= 0x1 && mm <= 0x12 && dd >= 0x1 && dd <= 0x31 && hours <= 0x23 && minutes <= 0x59) {
                    std::cout << "   ✅ This bitstream was built on " 
                              << std::setfill('0') << std::setw(2) << std::hex << (int)mm << "/" 
                              << std::setfill('0') << std::setw(2) << std::hex << (int)dd 
                              << " at " << std::setfill('0') << std::setw(2) << std::hex << (int)hours 
                              << ":" << std::setfill('0') << std::setw(2) << std::hex << (int)minutes << std::endl;
                } else {
                    std::cout << "   ⚠️ Warning: Value appears to be in MMDDHHMM format but contains invalid date/time" << std::endl;
                }
            } else {
                std::cout << "   ⚠️ Warning: Unrecognized format (not MMDDHHMM)" << std::endl;
            }
        } else {
            std::cout << "❌ Failed to read scratch register" << std::endl;
        }
        
        return 0;
        
    } catch (const std::exception& e) {
        std::cerr << "❌ Exception: " << e.what() << std::endl;
        return -1;
    }
}