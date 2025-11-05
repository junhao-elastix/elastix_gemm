#include <iostream>
#include <iomanip>
#include <memory>
#include "vp815.hpp"

int main() {
    std::cout << "=== Debug Register Readout ===" << std::endl;
    std::cout << "Reading registers 0x08-0x1C after CE timeout..." << std::endl << std::endl;
    
    std::unique_ptr<achronix::VP815> device;
    try {
        device = std::make_unique<achronix::VP815>(0);
    } catch (const std::exception& e) {
        std::cerr << "Failed to initialize device: " << e.what() << std::endl;
        return 1;
    }
    
    uint32_t reg_0x08, reg_0x0C, reg_0x10, reg_0x14, reg_0x18, reg_0x1C;
    
    device->mmioRead32(0, 0x08, reg_0x08);  // CE_BRAM_ADDR_DEBUG
    device->mmioRead32(0, 0x0C, reg_0x0C);  // CE_BRAM_DATA_LOW
    device->mmioRead32(0, 0x10, reg_0x10);  // CE_BRAM_DATA_MID
    device->mmioRead32(0, 0x14, reg_0x14);  // CE_CONTROL_DEBUG
    device->mmioRead32(0, 0x18, reg_0x18);  // DC_BRAM_WRITE_DEBUG
    device->mmioRead32(0, 0x1C, reg_0x1C);  // DC_CONTROL_DEBUG
    
    std::cout << "0x08 (CE_BRAM_ADDR_DEBUG):   0x" << std::hex << std::setw(8) << std::setfill('0') << reg_0x08 << std::endl;
    std::cout << "  CE BRAM read address: " << std::dec << (reg_0x08 & 0x7FF) << std::endl;
    
    std::cout << "\n0x0C (CE_BRAM_DATA_LOW):     0x" << std::hex << std::setw(8) << std::setfill('0') << reg_0x0C << std::endl;
    std::cout << "  BRAM data [31:0]: " << (reg_0x0C == 0 ? "ALL ZEROS!" : "Has data") << std::endl;
    
    std::cout << "\n0x10 (CE_BRAM_DATA_MID):     0x" << std::hex << std::setw(8) << std::setfill('0') << reg_0x10 << std::endl;
    std::cout << "  BRAM data [63:32]: " << (reg_0x10 == 0 ? "ALL ZEROS!" : "Has data") << std::endl;
    
    std::cout << "\n0x14 (CE_CONTROL_DEBUG):     0x" << std::hex << std::setw(8) << std::setfill('0') << reg_0x14 << std::endl;
    std::cout << "  rd_en: " << ((reg_0x14 >> 7) & 1) << std::endl;
    std::cout << "  load_count: " << std::dec << ((reg_0x14 >> 1) & 0x7) << std::endl;
    std::cout << "  ce_state: " << (reg_0x14 & 0xF) << std::endl;
    
    std::cout << "\n0x18 (DC_BRAM_WRITE_DEBUG):  0x" << std::hex << std::setw(8) << std::setfill('0') << reg_0x18 << std::endl;
    std::cout << "  wr_en: " << ((reg_0x18 >> 11) & 1) << std::endl;
    std::cout << "  wr_addr: " << std::dec << (reg_0x18 & 0x7FF) << std::endl;
    
    std::cout << "\n0x1C (DC_CONTROL_DEBUG):     0x" << std::hex << std::setw(8) << std::setfill('0') << reg_0x1C << std::endl;
    std::cout << "  fetch_done: " << ((reg_0x1C >> 7) & 1) << std::endl;
    std::cout << "  disp_done: " << ((reg_0x1C >> 6) & 1) << std::endl;
    std::cout << "  dc_state: " << std::dec << (reg_0x1C & 0xF) << std::endl;
    
    std::cout << "\n=== Analysis ===" << std::endl;
    if ((reg_0x0C == 0) && (reg_0x10 == 0)) {
        std::cout << "❌ BRAM READ DATA IS ALL ZEROS - BRAM empty or not connected!" << std::endl;
    } else {
        std::cout << "✓ BRAM has data" << std::endl;
    }
    
    if (((reg_0x14 >> 7) & 1) == 1) {
        std::cout << "✓ CE is asserting rd_en (reading BRAM)" << std::endl;
    } else {
        std::cout << "❌ CE NOT asserting rd_en!" << std::endl;
    }
    
    if (((reg_0x1C >> 7) & 1) == 1) {
        std::cout << "✓ DC fetch_done asserted" << std::endl;
    } else {
        std::cout << "❌ DC fetch NOT done!" << std::endl;
    }
    
    if (((reg_0x1C >> 6) & 1) == 1) {
        std::cout << "✓ DC disp_done asserted" << std::endl;
    } else {
        std::cout << "❌ DC dispatch NOT done!" << std::endl;
    }
    
    return 0;
}
