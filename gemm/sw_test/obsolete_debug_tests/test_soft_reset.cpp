#include <iostream>
#include <memory>
#include <unistd.h>
#include "vp815.hpp"

#define CONTROL_REG          0x00
#define ENGINE_STATUS        0x3C
#define DC_BRAM_WRITE_DEBUG  0x18
#define DC_CONTROL_DEBUG     0x1C

#define ENGINE_CMD_WORD0     0x28
#define ENGINE_CMD_WORD1     0x2C
#define ENGINE_CMD_WORD2     0x30
#define ENGINE_CMD_WORD3     0x34
#define ENGINE_CMD_SUBMIT    0x38

int main() {
    std::cout << "=== Soft-Reset Functionality Test ===" << std::endl;

    // Initialize device
    std::unique_ptr<achronix::VP815> device;
    try {
        device = std::make_unique<achronix::VP815>(0);
        std::cout << "✅ Device initialized" << std::endl;
    } catch (const std::exception& e) {
        std::cerr << "❌ Failed to initialize device: " << e.what() << std::endl;
        return 1;
    }

    // Test 1: Submit a FETCH command (will timeout but leave state dirty)
    std::cout << "\n=== Test 1: Create Dirty State ===" << std::endl;

    // FETCH command: opcode=0xF0, length=528 lines, addr=0x0
    uint32_t word0 = (0 << 24) | (12 << 16) | (0 << 8) | 0xF0;  // FETCH opcode
    uint32_t word1 = 0x0;                                        // Address 0
    uint32_t word2 = (528 << 16);                                // 528 lines
    uint32_t word3 = 0x0;

    device->mmioWrite32(0, ENGINE_CMD_WORD0, word0);
    device->mmioWrite32(0, ENGINE_CMD_WORD1, word1);
    device->mmioWrite32(0, ENGINE_CMD_WORD2, word2);
    device->mmioWrite32(0, ENGINE_CMD_WORD3, word3);
    device->mmioWrite32(0, ENGINE_CMD_SUBMIT, 0x1);

    std::cout << "Submitted FETCH command for 528 lines @ 0x0" << std::endl;

    // Wait for timeout (should take ~5ms)
    usleep(50000);  // 50ms to be safe

    // Check state after timeout
    uint32_t status, bram_debug, ctrl_debug;
    device->mmioRead32(0, ENGINE_STATUS, status);
    device->mmioRead32(0, DC_BRAM_WRITE_DEBUG, bram_debug);
    device->mmioRead32(0, DC_CONTROL_DEBUG, ctrl_debug);

    uint32_t wr_addr = bram_debug & 0x7FF;
    uint32_t dc_state = ctrl_debug & 0xF;

    std::cout << "After FETCH timeout:" << std::endl;
    std::cout << "  Status: 0x" << std::hex << status << std::dec << std::endl;
    std::cout << "  wr_addr: " << wr_addr << " (0x" << std::hex << wr_addr << std::dec << ")" << std::endl;
    std::cout << "  dc_state: " << dc_state << std::endl;

    if (wr_addr > 0) {
        std::cout << "✅ FETCH wrote " << (wr_addr + 1) << " lines (state is dirty)" << std::endl;
    } else {
        std::cout << "⚠️  No data written (unexpected)" << std::endl;
    }

    // Test 2: Apply soft-reset
    std::cout << "\n=== Test 2: Apply Soft-Reset ===" << std::endl;

    std::cout << "Asserting soft-reset (bit 1)..." << std::endl;
    device->mmioWrite32(0, CONTROL_REG, 0x2);  // Set bit 1
    usleep(100);  // Hold for 100µs

    std::cout << "Releasing soft-reset..." << std::endl;
    device->mmioWrite32(0, CONTROL_REG, 0x0);  // Clear bit 1
    usleep(1000);  // Let FSMs settle

    // Check state after reset
    device->mmioRead32(0, ENGINE_STATUS, status);
    device->mmioRead32(0, DC_BRAM_WRITE_DEBUG, bram_debug);
    device->mmioRead32(0, DC_CONTROL_DEBUG, ctrl_debug);

    uint32_t wr_addr_after = bram_debug & 0x7FF;
    uint32_t dc_state_after = ctrl_debug & 0xF;

    std::cout << "After soft-reset:" << std::endl;
    std::cout << "  Status: 0x" << std::hex << status << std::dec << std::endl;
    std::cout << "  wr_addr: " << wr_addr_after << " (0x" << std::hex << wr_addr_after << std::dec << ")" << std::endl;
    std::cout << "  dc_state: " << dc_state_after << std::endl;

    // Verify reset worked
    bool reset_success = (wr_addr_after == 0 && dc_state_after == 0);

    if (reset_success) {
        std::cout << "✅ SOFT-RESET SUCCESSFUL!" << std::endl;
        std::cout << "   - wr_addr cleared to 0" << std::endl;
        std::cout << "   - dc_state returned to IDLE (0)" << std::endl;
    } else {
        std::cout << "❌ SOFT-RESET FAILED!" << std::endl;
        std::cout << "   - wr_addr: " << wr_addr_after << " (expected 0)" << std::endl;
        std::cout << "   - dc_state: " << dc_state_after << " (expected 0)" << std::endl;
    }

    // Test 3: Submit another FETCH after reset
    std::cout << "\n=== Test 3: FETCH After Reset ===" << std::endl;

    device->mmioWrite32(0, ENGINE_CMD_WORD0, word0);
    device->mmioWrite32(0, ENGINE_CMD_WORD1, word1);
    device->mmioWrite32(0, ENGINE_CMD_WORD2, word2);
    device->mmioWrite32(0, ENGINE_CMD_WORD3, word3);
    device->mmioWrite32(0, ENGINE_CMD_SUBMIT, 0x1);

    std::cout << "Submitted FETCH command after reset" << std::endl;
    usleep(50000);

    device->mmioRead32(0, DC_BRAM_WRITE_DEBUG, bram_debug);
    uint32_t wr_addr_second = bram_debug & 0x7FF;

    std::cout << "After second FETCH:" << std::endl;
    std::cout << "  wr_addr: " << wr_addr_second << " (0x" << std::hex << wr_addr_second << std::dec << ")" << std::endl;

    if (wr_addr_second == wr_addr) {
        std::cout << "✅ Second FETCH behaves identically (wrote " << (wr_addr_second + 1) << " lines)" << std::endl;
    } else {
        std::cout << "⚠️  Different behavior: first=" << (wr_addr + 1)
                  << " lines, second=" << (wr_addr_second + 1) << " lines" << std::endl;
    }

    // Final summary
    std::cout << "\n=== Summary ===" << std::endl;
    if (reset_success) {
        std::cout << "✅ Soft-reset functionality VERIFIED" << std::endl;
        std::cout << "   Ready to use for clean sequential testing" << std::endl;
        return 0;
    } else {
        std::cout << "❌ Soft-reset NOT working as expected" << std::endl;
        return 1;
    }
}
