#include <iostream>
#include <iomanip>
#include "vp815.hpp"

int main() {
    try {
        auto device = std::make_unique<achronix::VP815>(0);

        std::cout << "=== Register Address Space Scan ===" << std::endl;
        std::cout << "Scanning from 0x00 to 0x1FC (128 registers, step=4)" << std::endl << std::endl;

        std::cout << std::hex << std::setfill('0');

        for (uint32_t addr = 0; addr <= 0x1FC; addr += 4) {
            uint32_t value;
            device->mmioRead32(0, addr, value);

            // Highlight interesting addresses (UPDATED for 128-register mapping)
            std::string note = "";
            if (addr == 0x00) note = " <- Control Reg";
            else if (addr == 0x04) note = " <- Status Reg";
            else if (addr == 0x1F0) note = " <- LTSSM State";
            else if (addr == 0x1F4) note = " <- ADM Status";
            else if (addr == 0x1F8) note = " <- Bitstream ID";
            else if (addr == 0x1FC) note = " <- Scratch Reg";

            // Only print if non-zero or special address
            if (value != 0 || !note.empty()) {
                std::cout << "  0x" << std::setw(4) << addr << ": 0x"
                          << std::setw(8) << value << note;

                if (value == 0xffffffff)
                    std::cout << " ❌";

                std::cout << std::endl;
            }
        }

    } catch (const std::exception& e) {
        std::cerr << "Error: " << e.what() << std::endl;
        return 1;
    }
    return 0;
}
