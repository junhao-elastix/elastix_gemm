#include <iostream>
#include <iomanip>
#include <memory>
#include "vp815.hpp"

int main() {
    std::cout << "=== GDDR6 Memory Test ===" << std::endl;

    // Initialize device
    std::unique_ptr<achronix::VP815> device;
    try {
        device = std::make_unique<achronix::VP815>(0);
        std::cout << "✅ Device initialized successfully\n" << std::endl;
    } catch (const std::exception& e) {
        std::cerr << "❌ Failed to initialize device: " << e.what() << std::endl;
        return 1;
    }

    // Register map constants (UPDATED to match elastix_gemm_top.sv with 128 registers)
    const uint32_t REGS_PER_GDDR_CH = 11;
    const uint32_t NUM_GDDR_CHANNELS = 8;
    const uint32_t REGS_PER_IRQ_GEN_CH = 3;
    const uint32_t REGS_PER_MSIX_IRQ_CH = 4;
    const uint32_t NUM_MSIX_IRQ_CH = 2;
    const uint32_t NUM_IRQ_GEN_REGS = NUM_MSIX_IRQ_CH * REGS_PER_IRQ_GEN_CH; // 2*3 = 6
    const uint32_t MSIX_IRQ_REGS_BASE = 2 + NUM_IRQ_GEN_REGS; // 2 + 6 = 8
    const uint32_t NUM_MSIX_IRQ_REGS = 4 + (NUM_MSIX_IRQ_CH * REGS_PER_MSIX_IRQ_CH); // 4 + (2*4) = 12
    const uint32_t GDDR_REGS_BASE = MSIX_IRQ_REGS_BASE + NUM_MSIX_IRQ_REGS; // 8 + 12 = 20
    // NUM_USER_REGS = 128 (hardcoded from RTL, not used in calculations)
    const uint32_t ADM_STATUS_REG = 132; // 139 - 7 = 132, offset 132*4 = 528 = 0x210

    // Check ADM status for GDDR6 training
    uint32_t adm_status;
    device->mmioRead32(0, ADM_STATUS_REG * 4, adm_status);
    std::cout << "ADM Status: 0x" << std::hex << std::setw(8) << std::setfill('0') << adm_status;

    if (adm_status & 0x0A) {
        std::cout << " ✅ GDDR6 training complete\n" << std::endl;
    } else {
        std::cout << " ⚠️  GDDR6 training not complete\n" << std::endl;
    }

    // Read all GDDR6 channel registers
    for (uint32_t ch = 0; ch < NUM_GDDR_CHANNELS; ch++) {
        std::cout << "=== GDDR6 Channel " << std::dec << ch << " Status ===" << std::endl;

        uint32_t ch_base = GDDR_REGS_BASE + (ch * REGS_PER_GDDR_CH);

        // Read channel registers
        uint32_t control, status, total_xact, remaining;
        uint32_t read_bw, write_bw, avg_lat, max_lat, min_lat;

        device->mmioRead32(0, (ch_base + 0) * 4, control);
        device->mmioRead32(0, (ch_base + 1) * 4, status);
        device->mmioRead32(0, (ch_base + 2) * 4, total_xact);
        device->mmioRead32(0, (ch_base + 3) * 4, remaining);
        device->mmioRead32(0, (ch_base + 5) * 4, read_bw);
        device->mmioRead32(0, (ch_base + 6) * 4, write_bw);
        device->mmioRead32(0, (ch_base + 7) * 4, avg_lat);
        device->mmioRead32(0, (ch_base + 8) * 4, max_lat);
        device->mmioRead32(0, (ch_base + 9) * 4, min_lat);

        std::cout << "Control:    0x" << std::hex << std::setw(8) << std::setfill('0') << control << std::endl;
        std::cout << "Status:     0x" << std::setw(8) << status;

        // Decode status bits
        bool running = (status & 0x1);
        bool done = (status & 0x2);
        bool fail = (status & 0x4);

        if (fail) std::cout << " ❌ Failed";
        else if (done) std::cout << " ✅ Done";
        else if (running) std::cout << " 🔄 Running";
        else std::cout << " 🔄 Running/Idle";

        std::cout << std::endl;
        std::cout << "Total Xact: " << std::dec << total_xact << std::endl;
        std::cout << "Remaining:  " << remaining << std::endl;
        std::cout << std::endl;

        std::cout << "Performance Counters:" << std::endl;
        std::cout << "  Read BW:   " << read_bw << std::endl;
        std::cout << "  Write BW:  " << write_bw << std::endl;
        std::cout << "  Avg Lat:   " << avg_lat << " cycles" << std::endl;
        std::cout << "  Max Lat:   " << max_lat << " cycles" << std::endl;
        std::cout << "  Min Lat:   " << min_lat << " cycles" << std::endl;
        std::cout << std::endl;
    }

    return 0;
}
