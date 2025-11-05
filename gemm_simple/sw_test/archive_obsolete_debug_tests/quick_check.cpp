#include <iostream>
#include <iomanip>
#include "../../../acxsdk/include/acx_pcie_device.hpp"

int main() {
    acx_pcie_device device(0, acx_pcie_device::BittWareVFIO);
    uint32_t status = device.mmio_read32(0x24);
    
    std::cout << "ENGINE_STATUS: 0x" << std::hex << status << std::dec << std::endl;
    std::cout << "  mc_state_next: " << ((status >> 20) & 0xF) << std::endl;
    std::cout << "  mc_state: " << ((status >> 16) & 0xF) << std::endl;
    std::cout << "  dc_state: " << ((status >> 8) & 0xF) << std::endl;
    std::cout << "  ce_state: " << ((status >> 4) & 0xF) << std::endl;
    std::cout << "  busy: " << (status & 0x1) << std::endl;
    
    return 0;
}
