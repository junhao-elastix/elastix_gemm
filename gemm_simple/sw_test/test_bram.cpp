#include "vp815.hpp"
#include "Achronix_device.h"
#include "Achronix_util.h"
#include <iostream>
#include <vector>
#include <algorithm>
#include <iomanip>
#include <cstring>
#include <chrono>

using namespace achronix;

// Control register definitions for BRAM +42 increment feature
static constexpr uint32_t CONTROL_REG_BAR = 0;
static constexpr uint64_t CONTROL_REG_OFFSET = 0x00;
static constexpr uint32_t CONTROL_BRAM_INC42_BIT = 0x1;

// Test size constants
static constexpr size_t TEST_SIZE_BYTES = 256; // 256 bytes for simple testing

// BRAM control functions
static bool set_bram_inc42_control(VP815& device, bool bram_enable) {
    uint32_t control_value = bram_enable ? CONTROL_BRAM_INC42_BIT : 0;
    
    std::cout << "Setting BRAM +42 control register: " << (bram_enable ? "ON" : "OFF")
              << " (0x" << std::hex << control_value << std::dec << ")" << std::endl;

    if (!device.mmioWrite32(CONTROL_REG_BAR, CONTROL_REG_OFFSET, control_value)) {
        std::cout << "  ✗ Failed to write control register" << std::endl;
        return false;
    }

    uint32_t readback_value;
    if (!device.mmioRead32(CONTROL_REG_BAR, CONTROL_REG_OFFSET, readback_value)) {
        std::cout << "  ✗ Failed to read back control register" << std::endl;
        return false;
    }

    if (readback_value != control_value) {
        std::cout << "  ✗ Control register mismatch: wrote 0x" << std::hex << control_value
                  << ", read 0x" << readback_value << std::dec << std::endl;
        return false;
    }

    std::cout << "  ✓ Control register verified: 0x" << std::hex << readback_value << std::dec << std::endl;
    return true;
}

static bool get_bram_inc42_control(VP815& device, uint32_t& value) {
    if (!device.mmioRead32(CONTROL_REG_BAR, CONTROL_REG_OFFSET, value)) {
        std::cout << "  ✗ Failed to read control register" << std::endl;
        return false;
    }
    return true;
}

// BRAM DMA round trip test
static bool bram_dma_round_trip(VP815& device, uint64_t base_addr, size_t size, bool expect_inc42 = false) {
    std::cout << "\n=== BRAM DMA Round Trip ===" << std::endl;
    if (expect_inc42) {
        std::cout << "  (Expecting +42 increment on LSB only)" << std::endl;
    }

    const uint64_t addr = base_addr;
    std::vector<uint8_t> write_buf(size);
    std::vector<uint8_t> read_buf(size, 0);

    // Fill write buffer with a pattern
    for (size_t i = 0; i < size; i += 4) {
        uint32_t value = 0x1000 + (i / 4) * 0x11;
        std::memcpy(&write_buf[i], &value, 4);
    }

    std::cout << "Writing " << size << " bytes to 0x" << std::hex << addr << std::dec << std::endl;
    if (!device.dmaWrite(addr, size, reinterpret_cast<char*>(write_buf.data()))) {
        std::cout << "  ✗ DMA write failed" << std::endl;
        return false;
    }

    std::cout << "Reading  " << size << " bytes from 0x" << std::hex << addr << std::dec << std::endl;
    if (!device.dmaRead(addr, size, reinterpret_cast<char*>(read_buf.data()))) {
        std::cout << "  ✗ DMA read failed" << std::endl;
        return false;
    }

    // Check data integrity based on whether +42 increment is expected
    bool match = true;
    if (expect_inc42) {
        // When +42 increment is enabled, verify that only LSB of each 32-bit word is incremented by 42
        for (size_t i = 0; i < size; i += 4) {
            uint32_t written_word, read_word;
            std::memcpy(&written_word, &write_buf[i], 4);
            std::memcpy(&read_word, &read_buf[i], 4);
            
            uint32_t expected_word = written_word + 42;
            if (read_word != expected_word) {
                match = false;
                break;
            }
        }
        std::cout << (match ? "  ✓ Data integrity verified (with +42 increment on LSB only)" : "  ✗ Data mismatch (expected +42 increment on LSB only)") << std::endl;
    } else {
        // Normal case: verify exact match
        match = (write_buf == read_buf);
        std::cout << (match ? "  ✓ Data integrity verified" : "  ✗ Data mismatch") << std::endl;
    }

    // Always print a small sample of the read-back data
    const size_t sample = std::min<size_t>(32, size);
    std::cout << "  Read-back sample (" << sample << " bytes): ";
    for (size_t i = 0; i < sample; ++i) {
        std::cout << std::hex << std::setw(2) << std::setfill('0')
                  << static_cast<int>(read_buf[i]) << " ";
    }
    std::cout << std::dec << std::endl;

    return match;
}

int main(int argc, char* argv[]) {
    try {
        uint32_t device_id = 0;
        bool test_inc42 = false;
        
        // Simple CLI parsing
        for (int i = 1; i < argc; ++i) {
            if (std::strcmp(argv[i], "--device") == 0 && i+1 < argc) {
                device_id = static_cast<uint32_t>(std::stoul(argv[++i]));
            } else if (std::strcmp(argv[i], "--inc42") == 0) {
                test_inc42 = true;
            } else if (std::strcmp(argv[i], "-h") == 0 || std::strcmp(argv[i], "--help") == 0) {
                std::cout << "Usage: test_bram [options]\n";
                std::cout << "Options:\n";
                std::cout << "  --device N          Use device N (default: 0)\n";
                std::cout << "  --inc42             Test BRAM +42 increment\n";
                std::cout << "  -h, --help          Show this help\n";
                std::cout << "\nModes:\n";
                std::cout << "  Default:            Write and read back the same data\n";
                std::cout << "  --inc42:            Write, apply +42 processing, read back +42 data\n";
                return 0;
            }
        }

        std::cout << "=== VP815 BRAM Test ===" << std::endl;
        if (test_inc42) {
            std::cout << "Mode: BRAM +42 increment" << std::endl;
        } else {
            std::cout << "Mode: BRAM normal write/read" << std::endl;
        }
        
        VP815 device(device_id);

        if (!device.isReady()) {
            std::cerr << "Device not ready" << std::endl;
            return 1;
        }

        device.print_info();

        // Display current control register state
        uint32_t initial_control;
        if (!get_bram_inc42_control(device, initial_control)) {
            std::cerr << "Failed to read initial control register state" << std::endl;
            return 1;
        }
        std::cout << "Initial BRAM +42 control register: 0x" << std::hex << initial_control << std::dec 
                  << " (increment " << ((initial_control & CONTROL_BRAM_INC42_BIT) ? "ENABLED" : "DISABLED") << ")" << std::endl;

        // Configure BRAM +42 control
        if (!set_bram_inc42_control(device, test_inc42)) {
            std::cerr << "Failed to configure BRAM +42 control register" << std::endl;
            return 1;
        }

        bool ok = true;
        
        // BRAM via DMA to the BRAM responder used for descriptor lists (BRAM_RESP_DL_SPACE)
        const int axi_bram_resp_dl_col = 9;
        const int axi_bram_resp_dl_row = 7;
        const uint64_t BRAM_RESP_DL_SPACE = acx_util_nap_absolute_addr(ACX_PART_AC7t1500,
                                                                       axi_bram_resp_dl_col,
                                                                       axi_bram_resp_dl_row);
        
        // Use a safe base address that we know works
        const uint64_t BRAM_BASE_ADDR = BRAM_RESP_DL_SPACE + 0x8000;
        
        // Test BRAM DMA round trip
        ok &= bram_dma_round_trip(device, BRAM_BASE_ADDR, TEST_SIZE_BYTES, test_inc42);

        // Always disable +42 increments at the end for safety
        std::cout << "\nCleaning up: disabling +42 increments..." << std::endl;
        if (!set_bram_inc42_control(device, false)) {
            std::cout << "  ⚠ Warning: Failed to disable +42 increments" << std::endl;
        }

        std::cout << "\n=== Final Result: " << (ok ? "SUCCESS" : "FAILURE") << " ===" << std::endl;
        return ok ? 0 : 1;

    } catch (const VP815Exception& e) {
        std::cerr << "VP815 error: " << e.what() << std::endl;
        return 1;
    } catch (const std::exception& e) {
        std::cerr << "Error: " << e.what() << std::endl;
        return 1;
    }
}
