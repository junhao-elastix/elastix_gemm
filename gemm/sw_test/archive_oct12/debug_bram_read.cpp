// Debug: Read raw BRAM contents to see what's written
#include <iostream>
#include <iomanip>
#include "vp815.hpp"

int main() {
    auto device = std::make_unique<achronix::VP815>(0);
    
    std::cout << "Reading raw BRAM result buffer (first 4 lines = 64 FP16 values):\n";
    
    for (int addr = 0; addr < 4; addr++) {
        uint64_t offset = 0x220 + (addr * 32);  // Result buffer @ 0x220
        
        // Read 256-bit line as 8x 32-bit words
        std::cout << "\nBRAM[" << addr << "] @ 0x" << std::hex << offset << ":\n  ";
        for (int w = 0; w < 8; w++) {
            uint32_t word = device->mmioRead32(0, offset + w*4);
            std::cout << std::hex << std::setfill('0') << std::setw(8) << word << " ";
        }
        
        // Decode as FP16 values
        std::cout << "\n  FP16 decode: ";
        for (int w = 0; w < 8; w++) {
            uint32_t word = device->mmioRead32(0, offset + w*4);
            uint16_t fp16_lo = word & 0xFFFF;
            uint16_t fp16_hi = (word >> 16) & 0xFFFF;
            
            // Check for infinity (exp=0x1F, mant=0)
            uint8_t exp_lo = (fp16_lo >> 10) & 0x1F;
            uint8_t exp_hi = (fp16_hi >> 10) & 0x1F;
            
            std::cout << "[" << std::dec << w*2 << "]=0x" << std::hex << fp16_lo 
                     << "(exp=" << std::dec << (int)exp_lo << ") ";
            std::cout << "[" << std::dec << w*2+1 << "]=0x" << std::hex << fp16_hi
                     << "(exp=" << std::dec << (int)exp_hi << ") ";
        }
        std::cout << "\n";
    }
    
    return 0;
}
