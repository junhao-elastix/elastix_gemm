// Simple test: Write to BRAM @ NAP[3][5] and read back
#include <iostream>
#include <iomanip>
#include "vp815.hpp"

int main() {
    auto device = std::make_unique<achronix::VP815>(0);
    
    uint64_t bram_base = 0x4140000000ULL;  // NAP[3][5], offset 0
    
    std::cout << "Testing BRAM @ NAP[3][5] (0x" << std::hex << bram_base << ")" << std::endl;
    
    // Write test pattern
    uint32_t pattern = 0xDEADBEEF;
    device->mmioWrite32(2, bram_base, pattern);
    
    // Read back
    uint32_t readback = device->mmioRead32(2, bram_base);
    
    std::cout << "Wrote:  0x" << std::hex << pattern << std::endl;
    std::cout << "Read:   0x" << std::hex << readback << std::endl;
    
    if (readback == pattern) {
        std::cout << "✅ BRAM write/read works at NAP[3][5]!" << std::endl;
    } else {
        std::cout << "❌ Mismatch!" << std::endl;
    }
    
    return 0;
}
