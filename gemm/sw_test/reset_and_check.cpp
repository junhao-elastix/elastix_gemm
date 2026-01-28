#include <iostream>
#include <iomanip>
#include <cstdint>
#include "vp815_gemm_device.hpp"

// Register offsets from elastix_gemm_top.sv (byte addresses)
constexpr uint32_t CONTROL_REG           = 0x00;
constexpr uint32_t CE_CONTROL_DEBUG      = 0x14;
constexpr uint32_t DC_CONTROL_DEBUG      = 0x1C;
constexpr uint32_t ENGINE_STATUS         = 0x50;
constexpr uint32_t ENGINE_RESULT_COUNT   = 0x54;
constexpr uint32_t ENGINE_DEBUG          = 0x58;
constexpr uint32_t NAP_ERROR_STATUS      = 0x5C;
constexpr uint32_t DC_BRAM_WR_COUNT      = 0x60;
constexpr uint32_t DC_DEBUG              = 0x64;

void print_engine_status(uint32_t status) {
    std::cout << "  Engine Busy:     " << ((status & 0x1) ? "YES" : "NO") << std::endl;
    std::cout << "  MC State:        0x" << std::hex << ((status >> 1) & 0xF) << std::dec << std::endl;
    std::cout << "  DC State:        0x" << std::hex << ((status >> 5) & 0xF) << std::dec << std::endl;
    std::cout << "  CE State:        0x" << std::hex << ((status >> 9) & 0xF) << std::dec << std::endl;
}

void check_all_status(VP815GemmDevice& dev) {
    std::cout << "\n=== GEMM Engine Status ===" << std::endl;

    uint32_t ctrl = dev.mmio_read32(0, CONTROL_REG);
    std::cout << "Control (0x00):        0x" << std::hex << std::setw(8) << std::setfill('0')
              << ctrl << std::dec << std::endl;

    uint32_t status = dev.mmio_read32(0, ENGINE_STATUS);
    std::cout << "Engine Status (0x50):  0x" << std::hex << std::setw(8) << std::setfill('0')
              << status << std::dec << std::endl;
    print_engine_status(status);

    uint32_t result_cnt = dev.mmio_read32(0, ENGINE_RESULT_COUNT);
    std::cout << "Result Count (0x54):   " << result_cnt << std::endl;

    uint32_t debug = dev.mmio_read32(0, ENGINE_DEBUG);
    std::cout << "Engine Debug (0x58):   0x" << std::hex << std::setw(8) << std::setfill('0')
              << debug << std::dec << std::endl;
    std::cout << "  FIFO Count:          " << (debug & 0x1FFF) << std::endl;
    std::cout << "  FIFO Empty:          " << ((debug >> 14) & 0x1) << std::endl;

    uint32_t ce_ctrl = dev.mmio_read32(0, CE_CONTROL_DEBUG);
    std::cout << "CE Control (0x14):     0x" << std::hex << std::setw(8) << std::setfill('0')
              << ce_ctrl << std::dec << std::endl;

    uint32_t dc_dbg = dev.mmio_read32(0, DC_DEBUG);
    std::cout << "DC Debug (0x64):       0x" << std::hex << std::setw(8) << std::setfill('0')
              << dc_dbg << std::dec << std::endl;

    uint32_t nap_err = dev.mmio_read32(0, NAP_ERROR_STATUS);
    std::cout << "NAP Error (0x5C):      0x" << std::hex << std::setw(8) << std::setfill('0')
              << nap_err << std::dec << std::endl;

    std::cout << "==========================\n" << std::endl;
}

int main(int argc, char* argv[]) {
    (void)argc;
    (void)argv;

    try {
        achronix::VP815 vp815;
        VP815GemmDevice dev(vp815);

        std::cout << "VP815 GEMM Engine - Reset and Status Check\n";
        std::cout << "===========================================\n";

        std::cout << "\n--- Before Soft Reset ---";
        check_all_status(dev);

        std::cout << "Performing soft reset..." << std::endl;
        dev.soft_reset();
        std::cout << "Soft reset complete.\n";

        std::cout << "\n--- After Soft Reset ---";
        check_all_status(dev);

        if (dev.wait_idle(1000)) {
            std::cout << "Engine is IDLE and ready.\n";
            return 0;
        } else {
            std::cerr << "Engine not idle after reset.\n";
            return 1;
        }

    } catch (const std::exception& e) {
        std::cerr << "ERROR: " << e.what() << std::endl;
        return 1;
    }
}
