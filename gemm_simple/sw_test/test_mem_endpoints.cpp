#include "vp815.hpp"
#include "Achronix_device.h"
#include "Achronix_util.h"
#include <iostream>
#include <vector>
#include <algorithm>
#include <iomanip>
#include <cstring>

using namespace achronix;

// Memory scanning configuration
static constexpr size_t SCAN_CHUNK_SIZE = 256;  // 256 bytes per test location
static constexpr size_t BRAM_SCAN_INCREMENT = 0x1000;  // 4KB increments for BRAM
static constexpr size_t GDDR6_SCAN_INCREMENT = 0x100000;  // 1MB increments for GDDR6
static constexpr size_t BRAM_MAX_SCAN_SIZE = 0x10000;  // 64KB max scan for BRAM
static constexpr size_t GDDR6_MAX_SCAN_SIZE = 0x10000000;  // 256MB max scan for GDDR6

// GDDR6 address translation function
static uint64_t gddr6_address_translation(uint64_t address) {
    const static uint64_t GDDR6_ADDRESS_MASK = 0x3FFFFFFFUL; // 1GB address space needs a 30 bit mask
    uint64_t channel_address = address & GDDR6_ADDRESS_MASK;
    uint64_t controller_select = (address & ~GDDR6_ADDRESS_MASK) << 3;
    return controller_select | channel_address;
}

// Simple DMA round trip for address space scanning
static bool scan_location(VP815& device, uint64_t addr, size_t size) {
    std::vector<uint8_t> write_buf(size);
    std::vector<uint8_t> read_buf(size, 0);

    // Fill write buffer with a unique pattern based on address
    for (size_t i = 0; i < size; i += 4) {
        uint32_t value = static_cast<uint32_t>(addr + i); // Address-based pattern
        std::memcpy(&write_buf[i], &value, 4);
    }

    std::cout << "  Writing " << size << " bytes to 0x" << std::hex << addr << std::dec;
    if (!device.dmaWrite(addr, size, reinterpret_cast<char*>(write_buf.data()))) {
        std::cout << " - ✗ DMA write failed" << std::endl;
        return false;
    }

    std::cout << " - Reading back";
    if (!device.dmaRead(addr, size, reinterpret_cast<char*>(read_buf.data()))) {
        std::cout << " - ✗ DMA read failed" << std::endl;
        return false;
    }

    // Verify exact match
    bool match = (write_buf == read_buf);
    std::cout << " - " << (match ? "✓ PASS" : "✗ FAIL") << std::endl;
    
    return match;
}

// Scan BRAM address space with increments
static bool scan_bram_address_space(VP815& device, uint64_t base_addr) {
    std::cout << "\n=== BRAM Address Space Scan ===" << std::endl;
    std::cout << "  Base Address: 0x" << std::hex << base_addr << std::dec << std::endl;
    std::cout << "  Scan Increment: 0x" << std::hex << BRAM_SCAN_INCREMENT << std::dec << " (" << (BRAM_SCAN_INCREMENT/1024) << "KB)" << std::endl;
    std::cout << "  Max Scan Size: 0x" << std::hex << BRAM_MAX_SCAN_SIZE << std::dec << " (" << (BRAM_MAX_SCAN_SIZE/1024) << "KB)" << std::endl;
    
    bool all_passed = true;
    size_t locations_tested = 0;
    size_t locations_passed = 0;
    
    for (size_t offset = 0; offset < BRAM_MAX_SCAN_SIZE; offset += BRAM_SCAN_INCREMENT) {
        uint64_t test_addr = base_addr + offset;
        locations_tested++;
        
        if (scan_location(device, test_addr, SCAN_CHUNK_SIZE)) {
            locations_passed++;
        } else {
            all_passed = false;
        }
        
        // Progress indicator every 4 locations
        if (locations_tested % 4 == 0) {
            std::cout << "  Progress: " << locations_tested << " locations tested, " 
                      << locations_passed << " passed" << std::endl;
        }
    }
    
    std::cout << "\n  BRAM Scan Results: " << locations_passed << "/" << locations_tested 
              << " locations passed" << std::endl;
    
    return all_passed;
}

// Scan GDDR6 address space with increments
static bool scan_gddr6_address_space(VP815& device, uint64_t base_addr) {
    std::cout << "\n=== GDDR6 Address Space Scan ===" << std::endl;
    std::cout << "  Base Address: 0x" << std::hex << base_addr << std::dec << std::endl;
    std::cout << "  Scan Increment: 0x" << std::hex << GDDR6_SCAN_INCREMENT << std::dec << " (" << (GDDR6_SCAN_INCREMENT/1024/1024) << "MB)" << std::endl;
    std::cout << "  Max Scan Size: 0x" << std::hex << GDDR6_MAX_SCAN_SIZE << std::dec << " (" << (GDDR6_MAX_SCAN_SIZE/1024/1024) << "MB)" << std::endl;
    
    bool all_passed = true;
    size_t locations_tested = 0;
    size_t locations_passed = 0;
    
    for (size_t offset = 0; offset < GDDR6_MAX_SCAN_SIZE; offset += GDDR6_SCAN_INCREMENT) {
        uint64_t test_addr = gddr6_address_translation(base_addr + offset);
        locations_tested++;
        
        std::cout << "  Location " << locations_tested << ": 0x" << std::hex << (base_addr + offset) 
                  << " -> 0x" << test_addr << std::dec;
        
        if (scan_location(device, test_addr, SCAN_CHUNK_SIZE)) {
            locations_passed++;
        } else {
            all_passed = false;
        }
        
        // Progress indicator every 4 locations
        if (locations_tested % 4 == 0) {
            std::cout << "  Progress: " << locations_tested << " locations tested, " 
                      << locations_passed << " passed" << std::endl;
        }
    }
    
    std::cout << "\n  GDDR6 Scan Results: " << locations_passed << "/" << locations_tested 
              << " locations passed" << std::endl;
    
    return all_passed;
}


int main(int argc, char* argv[]) {
    try {
        uint32_t device_id = 0;
        bool test_bram = false;
        bool test_gddr6 = false;
        bool test_both = false;
        
        // Simple CLI parsing
        for (int i = 1; i < argc; ++i) {
            if (std::strcmp(argv[i], "--device") == 0 && i+1 < argc) {
                device_id = static_cast<uint32_t>(std::stoul(argv[++i]));
            } else if (std::strcmp(argv[i], "--bram") == 0) {
                test_bram = true;
            } else if (std::strcmp(argv[i], "--gddr6") == 0) {
                test_gddr6 = true;
            } else if (std::strcmp(argv[i], "--both") == 0) {
                test_both = true;
            } else if (std::strcmp(argv[i], "-h") == 0 || std::strcmp(argv[i], "--help") == 0) {
                std::cout << "Usage: test_mem_endpoints [options]\n";
                std::cout << "Options:\n";
                std::cout << "  --device N          Use device N (default: 0)\n";
                std::cout << "  --bram              Scan BRAM address space\n";
                std::cout << "  --gddr6             Scan GDDR6 address space\n";
                std::cout << "  --both              Scan both BRAM and GDDR6 address spaces\n";
                std::cout << "  -h, --help          Show this help\n";
                return 0;
            }
        }
        
        // Default to testing both if no specific option is given
        if (!test_bram && !test_gddr6 && !test_both) {
            test_both = true;
        }

        std::cout << "=== VP815 Memory Address Space Scanner ===" << std::endl;
        VP815 device(device_id);

        if (!device.isReady()) {
            std::cerr << "Device not ready" << std::endl;
            return 1;
        }

        device.print_info();

        bool ok = true;
        
        // Get BRAM base address
        const int axi_bram_resp_dl_col = 9;
        const int axi_bram_resp_dl_row = 7;
        const uint64_t BRAM_BASE_ADDR = acx_util_nap_absolute_addr(ACX_PART_AC7t1500,
                                                                   axi_bram_resp_dl_col,
                                                                   axi_bram_resp_dl_row) + 0x8000;
        
        // Get GDDR6 base address
        const uint64_t GDDR6_BASE_ADDR = ACX_GDDR6_SPACE;
        
        // Perform address space scanning based on flags
        if (test_bram || test_both) {
            ok &= scan_bram_address_space(device, BRAM_BASE_ADDR);
        }
        
        if (test_gddr6 || test_both) {
            ok &= scan_gddr6_address_space(device, GDDR6_BASE_ADDR);
        }

        std::cout << "\n=== Result: " << (ok ? "SUCCESS" : "FAILURE") << " ===" << std::endl;
        return ok ? 0 : 1;

    } catch (const VP815Exception& e) {
        std::cerr << "VP815 error: " << e.what() << std::endl;
        return 1;
    } catch (const std::exception& e) {
        std::cerr << "Error: " << e.what() << std::endl;
        return 1;
    }
}


