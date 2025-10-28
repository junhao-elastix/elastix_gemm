#include <iostream>
#include <memory>
#include <unistd.h>
#include <iomanip>
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

#define GDDR6_BASE_LEFT      0x0
#define GDDR6_BASE_RIGHT     0x10000

void soft_reset(achronix::VP815* device) {
    device->mmioWrite32(0, CONTROL_REG, 0x2);
    usleep(100);
    device->mmioWrite32(0, CONTROL_REG, 0x0);
    usleep(1000);
}

void issue_fetch(achronix::VP815* device, uint32_t addr, uint32_t lines, const char* label) {
    uint32_t word0 = (12 << 16) | (0 << 8) | 0xF0;  // FETCH opcode
    uint32_t word1 = addr >> 5;  // Convert to line address
    uint32_t word2 = (lines << 16);
    uint32_t word3 = 0x0;
    
    device->mmioWrite32(0, ENGINE_CMD_WORD0, word0);
    device->mmioWrite32(0, ENGINE_CMD_WORD1, word1);
    device->mmioWrite32(0, ENGINE_CMD_WORD2, word2);
    device->mmioWrite32(0, ENGINE_CMD_WORD3, word3);
    device->mmioWrite32(0, ENGINE_CMD_SUBMIT, 0x1);
    
    std::cout << label << ": FETCH " << lines << " lines from 0x" 
              << std::hex << addr << std::dec << std::endl;
}

int main() {
    std::cout << "=== FETCH Burst 33 Investigation ===" << std::endl;
    
    std::unique_ptr<achronix::VP815> device;
    try {
        device = std::make_unique<achronix::VP815>(0);
        std::cout << "✅ Device initialized\n" << std::endl;
    } catch (const std::exception& e) {
        std::cerr << "❌ Failed: " << e.what() << std::endl;
        return 1;
    }
    
    // Load test data to GDDR6
    std::cout << "Loading test data to GDDR6..." << std::endl;
    std::vector<uint8_t> test_data(16896, 0xAA);  // 528 lines × 32 bytes
    
    device->dmaWrite(GDDR6_BASE_LEFT, test_data.size(), reinterpret_cast<char*>(test_data.data()));
    device->dmaWrite(GDDR6_BASE_RIGHT, test_data.size(), reinterpret_cast<char*>(test_data.data()));
    std::cout << "✓ Test data loaded\n" << std::endl;
    
    // Test 1: First FETCH (should complete - 528 lines = 33 bursts)
    std::cout << "=== Test 1: First FETCH (528 lines = 33 bursts) ===" << std::endl;
    soft_reset(device.get());
    
    issue_fetch(device.get(), GDDR6_BASE_LEFT, 528, "FETCH #1");
    usleep(50000);  // Wait 50ms
    
    uint32_t bram_debug, ctrl_debug;
    device->mmioRead32(0, DC_BRAM_WRITE_DEBUG, bram_debug);
    device->mmioRead32(0, DC_CONTROL_DEBUG, ctrl_debug);
    
    uint32_t wr_addr_1 = bram_debug & 0x7FF;
    uint32_t dc_state_1 = ctrl_debug & 0xF;
    
    std::cout << "After FETCH #1:" << std::endl;
    std::cout << "  wr_addr: " << wr_addr_1 << " (" << (wr_addr_1 + 1) << " lines)" << std::endl;
    std::cout << "  dc_state: " << dc_state_1 << std::endl;
    std::cout << "  Expected: 528 lines (33 bursts)" << std::endl;
    
    bool fetch1_success = (wr_addr_1 == 527);
    std::cout << (fetch1_success ? "✅ " : "❌ ") 
              << "FETCH #1: " << (wr_addr_1 + 1) << " lines\n" << std::endl;
    
    // Test 2: Second FETCH without reset (cumulative - 528 more lines = 33 more bursts)
    std::cout << "=== Test 2: Second FETCH without reset ===" << std::endl;
    
    issue_fetch(device.get(), GDDR6_BASE_RIGHT, 528, "FETCH #2");
    usleep(50000);
    
    device->mmioRead32(0, DC_BRAM_WRITE_DEBUG, bram_debug);
    device->mmioRead32(0, DC_CONTROL_DEBUG, ctrl_debug);
    
    uint32_t wr_addr_2 = bram_debug & 0x7FF;
    uint32_t dc_state_2 = ctrl_debug & 0xF;
    
    std::cout << "After FETCH #2:" << std::endl;
    std::cout << "  wr_addr: " << wr_addr_2 << " (" << (wr_addr_2 + 1) << " lines total)" << std::endl;
    std::cout << "  dc_state: " << dc_state_2 << std::endl;
    std::cout << "  Expected: 1056 lines total (66 bursts)" << std::endl;
    
    bool fetch2_success = (wr_addr_2 == 1055);
    std::cout << (fetch2_success ? "✅ " : "❌ ")
              << "FETCH #2: " << (wr_addr_2 + 1) << " total lines\n" << std::endl;
    
    // Analysis
    uint32_t lines_written_by_fetch2 = (wr_addr_2 + 1) - (wr_addr_1 + 1);
    
    std::cout << "=== Analysis ===" << std::endl;
    std::cout << "FETCH #1 wrote: " << (wr_addr_1 + 1) << " lines";
    if (wr_addr_1 == 527) {
        std::cout << " ✅ (33 bursts complete)";
    } else {
        uint32_t bursts1 = (wr_addr_1 + 1) / 16;
        std::cout << " ❌ (only " << bursts1 << " bursts, stopped at burst " << (bursts1 + 1) << ")";
    }
    std::cout << std::endl;
    
    std::cout << "FETCH #2 wrote: " << lines_written_by_fetch2 << " lines";
    if (lines_written_by_fetch2 == 528) {
        std::cout << " ✅ (33 bursts complete)";
    } else {
        uint32_t bursts2 = lines_written_by_fetch2 / 16;
        std::cout << " ❌ (only " << bursts2 << " bursts, stopped at burst " << (bursts2 + 1) << ")";
    }
    std::cout << std::endl;
    
    // Test 3: Reset and try FETCH #2 again from clean state
    std::cout << "\n=== Test 3: FETCH #2 after soft-reset ===" << std::endl;
    soft_reset(device.get());
    
    issue_fetch(device.get(), GDDR6_BASE_RIGHT, 528, "FETCH #2 (clean)");
    usleep(50000);
    
    device->mmioRead32(0, DC_BRAM_WRITE_DEBUG, bram_debug);
    uint32_t wr_addr_3 = bram_debug & 0x7FF;
    
    std::cout << "After FETCH #2 (clean state):" << std::endl;
    std::cout << "  wr_addr: " << wr_addr_3 << " (" << (wr_addr_3 + 1) << " lines)" << std::endl;
    
    if (wr_addr_3 == wr_addr_1) {
        std::cout << "✅ Same as FETCH #1 - issue is NOT specific to 'second FETCH'" << std::endl;
    } else {
        std::cout << "⚠️  Different from FETCH #1 - behavior varies!" << std::endl;
    }
    
    // Summary
    std::cout << "\n=== Summary ===" << std::endl;
    std::cout << "Burst 33 Issue: " << (fetch1_success && fetch2_success ? "NOT REPRODUCED" : "REPRODUCED") << std::endl;
    
    return (fetch1_success && fetch2_success) ? 0 : 1;
}
