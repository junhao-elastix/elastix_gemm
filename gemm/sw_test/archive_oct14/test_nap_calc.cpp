#include "Achronix_device.h"
#include "Achronix_util.h"
#include <iostream>
#include <iomanip>

int main() {
    // Result BRAM at NAP[3][4]
    uint64_t calc_addr = acx_util_nap_absolute_addr(ACX_PART_AC7t1500, 3, 4);
    uint64_t hardcoded_addr = 0x4130000000ULL;
    
    std::cout << "NAP[3][4] calculated address: 0x" << std::hex << calc_addr << std::endl;
    std::cout << "Hardcoded address:            0x" << std::hex << hardcoded_addr << std::endl;
    std::cout << "Match: " << (calc_addr == hardcoded_addr ? "YES" : "NO") << std::endl;
    
    return 0;
}
