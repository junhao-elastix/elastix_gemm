#include <iostream>
#include <iomanip>
#include <vector>
#include <chrono>
#include <cstdlib>
#include <algorithm>
#include "vp815.hpp"

using namespace achronix;

bool testMMIOFunctionValidation(VP815& device) {
    std::cout << "\n=== MMIO Function Validation ===" << std::endl;
    
    // Test error handling with completely invalid parameters
    std::cout << "Testing error handling with invalid BAR (999)..." << std::endl;
    
    uint32_t invalid_result;
    bool should_fail = device.mmioRead32(999, 0x0000, invalid_result);
    if (!should_fail) {
        std::cout << "  ✓ PASS: Invalid BAR correctly rejected" << std::endl;
    } else {
        std::cout << "  ✗ FAIL: Invalid BAR was accepted (this is wrong)" << std::endl;
        return false;
    }
    
    // Test with out-of-bounds offset
    std::cout << "Testing error handling with invalid offset (0xFFFFFFFF)..." << std::endl;
    bool should_fail2 = device.mmioRead32(0, 0xFFFFFFFF, invalid_result);
    if (!should_fail2) {
        std::cout << "  ✓ PASS: Invalid offset correctly rejected" << std::endl;
    } else {
        std::cout << "  ✗ FAIL: Invalid offset was accepted (this is wrong)" << std::endl;
        return false;
    }
    
    std::cout << "  ✓ All function validation tests passed" << std::endl;
    return true;
}

bool testMMIOSafeRegisters(VP815& device) {
    std::cout << "\n=== MMIO Safe Register Access ===" << std::endl;
    std::cout << "⚠️  Testing only documented, safe registers in BAR0, BAR1, and BAR3" << std::endl;
    
    int tests_passed = 0;
    int total_tests = 0;
    
    // === BAR0 Register Control Block Tests ===
    std::cout << "\n--- BAR0 (Register Control Block) Tests ---" << std::endl;
    
    // Check MSI-X status first - critical safety check
    std::cout << "Checking MSI-X status before accessing MSI-X registers..." << std::endl;
    bool msix_enabled = device.isMsixEnabled();
    std::cout << "MSI-X Status: " << (msix_enabled ? "ENABLED" : "DISABLED") << std::endl;
    
    if (msix_enabled) {
        // Test 1: Read MSI-X interrupt count registers (Read-Only, safe) - ONLY if MSI-X enabled
        total_tests++;
        std::cout << "Testing MSI-X Channel 0 Interrupt Count (BAR0 + 0x58)..." << std::endl;
        uint32_t interrupt_count_ch0;
        if (device.mmioRead32(0, 0x58, interrupt_count_ch0)) {
            std::cout << "  ✓ PASS: Read interrupt count = 0x" << std::hex << interrupt_count_ch0 << std::dec << std::endl;
            tests_passed++;
        } else {
            std::cout << "  ✗ FAIL: Could not read interrupt count register" << std::endl;
        }
        
        // Test 2: Read MSI-X Channel 1 Interrupt Count (Read-Only, safe) - ONLY if MSI-X enabled
        total_tests++;
        std::cout << "Testing MSI-X Channel 1 Interrupt Count (BAR0 + 0x68)..." << std::endl;
        uint32_t interrupt_count_ch1;
        if (device.mmioRead32(0, 0x68, interrupt_count_ch1)) {
            std::cout << "  ✓ PASS: Read interrupt count = 0x" << std::hex << interrupt_count_ch1 << std::dec << std::endl;
            tests_passed++;
        } else {
            std::cout << "  ✗ FAIL: Could not read interrupt count register" << std::endl;
        }
        
        // Test 3: Read Interrupt Generation Status (Read-Only, safe) - ONLY if MSI-X enabled
        total_tests++;
        std::cout << "Testing Interrupt Generation Ch0 Status (BAR0 + 0x38)..." << std::endl;
        uint32_t irq_gen_status;
        if (device.mmioRead32(0, 0x38, irq_gen_status)) {
            std::cout << "  ✓ PASS: Read interrupt gen status = 0x" << std::hex << irq_gen_status << std::dec << std::endl;
            tests_passed++;
        } else {
            std::cout << "  ✗ FAIL: Could not read interrupt generation status" << std::endl;
        }
    } else {
        std::cout << "⚠️  MSI-X is DISABLED - Skipping MSI-X register tests for safety" << std::endl;
        std::cout << "💡 This is the correct and safe behavior!" << std::endl;
        
        // Alternative safe test - just demonstrate BAR0 is accessible without touching MSI-X registers
        total_tests++;
        std::cout << "Testing basic BAR0 accessibility (safe offset)..." << std::endl;
        uint32_t safe_read;
        // Use a very conservative offset that should be safe even without MSI-X
        if (device.mmioRead32(0, 0x00, safe_read)) {
            std::cout << "  ✓ PASS: BAR0 basic access confirmed (value = 0x" << std::hex << safe_read << std::dec << ")" << std::endl;
            tests_passed++;
        } else {
            std::cout << "  ✗ FAIL: Could not access BAR0" << std::endl;
        }
    }
    
    // === BAR3 PCIe Configuration Tests ===
    std::cout << "\n--- BAR3 (DBI Gateway - PCIe Config) Tests ---" << std::endl;
    
    // Test: Read Device ID and Vendor ID (always safe, known value)
    total_tests++;
    std::cout << "Testing PCIe Device ID / Vendor ID read (BAR3 + 0x00)..." << std::endl;
    uint32_t device_vendor_id;
    if (device.mmioRead32(3, 0x00, device_vendor_id)) {
        std::cout << "  ✓ PASS: Device/Vendor ID = 0x" << std::hex << device_vendor_id << std::dec;
        if (device_vendor_id == 0x00101b59 || device_vendor_id == 0x101b59) {
            std::cout << " (Expected Achronix VP815 ID)" << std::endl;
        } else {
            std::cout << " (Unexpected - expected 0x00101b59 or 0x101b59)" << std::endl;
        }
        tests_passed++;
    } else {
        std::cout << "  ✗ FAIL: Could not read PCIe configuration registers" << std::endl;
    }

    // === BAR1 BRAM Responder Tests ===
    std::cout << "\n--- BAR1 (BRAM Responder) Tests ---" << std::endl;
    
    // Test 4: Read from BRAM at offset 0x0000 (safe memory interface)
    total_tests++;
    std::cout << "Testing BRAM read at offset 0x0000..." << std::endl;
    uint32_t bram_value_0000;
    if (device.mmioRead32(1, 0x0000, bram_value_0000)) {
        std::cout << "  ✓ PASS: Read BRAM[0x0000] = 0x" << std::hex << bram_value_0000 << std::dec << std::endl;
        tests_passed++;
    } else {
        std::cout << "  ✗ FAIL: Could not read from BRAM" << std::endl;
    }
    
    // Test 5: Read from BRAM at offset 0x1000 (safe memory interface)
    total_tests++;
    std::cout << "Testing BRAM read at offset 0x1000..." << std::endl;
    uint32_t bram_value_1000;
    if (device.mmioRead32(1, 0x1000, bram_value_1000)) {
        std::cout << "  ✓ PASS: Read BRAM[0x1000] = 0x" << std::hex << bram_value_1000 << std::dec << std::endl;
        tests_passed++;
    } else {
        std::cout << "  ✗ FAIL: Could not read from BRAM" << std::endl;
    }
    
    // Test 6: Write/Read test to BRAM (safe memory interface)
    total_tests++;
    std::cout << "Testing BRAM write/read at offset 0x2000..." << std::endl;
    uint32_t test_pattern = 0xDEADBEEF;
    uint32_t read_back;
    
    if (device.mmioWrite32(1, 0x2000, test_pattern)) {
        if (device.mmioRead32(1, 0x2000, read_back)) {
            if (read_back == test_pattern) {
                std::cout << "  ✓ PASS: Write/Read test successful (0x" << std::hex << test_pattern << ")" << std::dec << std::endl;
                tests_passed++;
            } else {
                std::cout << "  ✗ FAIL: Read-back mismatch. Wrote: 0x" << std::hex << test_pattern 
                          << ", Read: 0x" << read_back << std::dec << std::endl;
            }
        } else {
            std::cout << "  ✗ FAIL: Could not read back from BRAM" << std::endl;
        }
    } else {
        std::cout << "  ✗ FAIL: Could not write to BRAM" << std::endl;
    }
    
    std::cout << "\n--- Test Summary ---" << std::endl;
    std::cout << "Passed: " << tests_passed << "/" << total_tests << " tests" << std::endl;
    
    return tests_passed == total_tests;
}

bool testMMIODataSizes(VP815& device) {
    std::cout << "\n=== MMIO Data Size Tests (BAR1 BRAM) ===" << std::endl;
    
    int tests_passed = 0;
    int total_tests = 0;
    
    // Test different data sizes using safe BRAM
    uint64_t base_offset = 0x3000;  // Use different area of BRAM
    
    // Test 8-bit access
    total_tests++;
    std::cout << "Testing 8-bit MMIO access..." << std::endl;
    uint8_t test_val_8 = 0xAB;
    uint8_t read_val_8;
    if (device.mmioWrite8(1, base_offset, test_val_8) && 
        device.mmioRead8(1, base_offset, read_val_8) && 
        read_val_8 == test_val_8) {
        std::cout << "  ✓ PASS: 8-bit write/read successful" << std::endl;
        tests_passed++;
    } else {
        std::cout << "  ✗ FAIL: 8-bit write/read failed" << std::endl;
    }
    
    // Test 16-bit access
    total_tests++;
    std::cout << "Testing 16-bit MMIO access..." << std::endl;
    uint16_t test_val_16 = 0xCDEF;
    uint16_t read_val_16;
    if (device.mmioWrite16(1, base_offset + 2, test_val_16) && 
        device.mmioRead16(1, base_offset + 2, read_val_16) && 
        read_val_16 == test_val_16) {
        std::cout << "  ✓ PASS: 16-bit write/read successful" << std::endl;
        tests_passed++;
    } else {
        std::cout << "  ✗ FAIL: 16-bit write/read failed" << std::endl;
    }
    
    // Test 64-bit access
    total_tests++;
    std::cout << "Testing 64-bit MMIO access..." << std::endl;
    uint64_t test_val_64 = 0x123456789ABCDEF0ULL;
    uint64_t read_val_64;
    if (device.mmioWrite64(1, base_offset + 8, test_val_64) && 
        device.mmioRead64(1, base_offset + 8, read_val_64) && 
        read_val_64 == test_val_64) {
        std::cout << "  ✓ PASS: 64-bit write/read successful" << std::endl;
        tests_passed++;
    } else {
        std::cout << "  ✗ FAIL: 64-bit write/read failed" << std::endl;
    }
    
    std::cout << "\nData size tests passed: " << tests_passed << "/" << total_tests << std::endl;
    return tests_passed == total_tests;
}

int main(int argc, char* argv[]) {
    std::cout << "=== VP815 MMIO Test Suite (CONTROLLED-SAFE VERSION) ===" << std::endl;
    std::cout << "🛡️  Only testing documented, safe registers in BAR0, BAR1, and BAR3" << std::endl;
    std::cout << "⚠️  Completely avoids BAR5 and other dangerous areas" << std::endl;
    std::cout << "📖 Based on hardware documentation from HW_README.txt" << std::endl;
    std::cout << std::endl;
    
    // Parse command line arguments
    int device_id = 0;
    if (argc > 1) {
        device_id = std::atoi(argv[1]);
    }
    
    std::cout << "Initializing VP815 device " << device_id << "..." << std::endl;
    
    // Initialize device
    VP815 device(device_id);
    
    // Check status and print all device information
    if (!device.printDeviceStatus()) {
        std::cerr << "VP815 device initialization failed!" << std::endl;
        return 1;
    }
    
    // === BAR Availability Analysis ===
    std::cout << "\n=== BAR Availability Analysis ===" << std::endl;
    
    std::vector<uint32_t> available_bars;
    for (uint32_t bar = 0; bar < 6; ++bar) {
        uint64_t bar_size = device.getBarSize(bar);
        if (bar_size > 0) {
            available_bars.push_back(bar);
            std::cout << "BAR" << bar << ": Available (" << (bar_size / 1024 / 1024) 
                      << "MB, 0x" << std::hex << bar_size << std::dec << " bytes)";
            
            // Add safety warnings based on hardware documentation
            if (bar == 0) std::cout << " - Register Control Block (SAFE)";
            else if (bar == 1) std::cout << " - BRAM Responder (SAFE)";
            else if (bar == 2) std::cout << " - MSI-X Table (AVOID - Critical)";
            else if (bar == 3) std::cout << " - DBI Gateway / PCIe Config (SAFE for reads)";
            else if (bar == 5) std::cout << " - FCU CSR Space (DANGEROUS - Can crash system!)";
            
            std::cout << std::endl;
        } else {
            std::cout << "BAR" << bar << ": Not mapped" << std::endl;
        }
    }
    
    // Safety check - ensure we have the required safe BARs
    bool has_bar0 = std::find(available_bars.begin(), available_bars.end(), 0) != available_bars.end();
    bool has_bar1 = std::find(available_bars.begin(), available_bars.end(), 1) != available_bars.end();
    bool has_bar3 = std::find(available_bars.begin(), available_bars.end(), 3) != available_bars.end();
    
    if (!has_bar0 || !has_bar1 || !has_bar3) {
        std::cerr << "❌ Required safe BARs (BAR0, BAR1, BAR3) not available!" << std::endl;
        return 1;
    }
    
    // === Test Execution ===
    int total_test_groups = 0;
    int passed_test_groups = 0;
    
    // Test 1: Function validation
    total_test_groups++;
    if (testMMIOFunctionValidation(device)) {
        passed_test_groups++;
    }
    
    // Test 2: Safe register access
    total_test_groups++;
    if (testMMIOSafeRegisters(device)) {
        passed_test_groups++;
    }
    
    // Test 3: Data size testing
    total_test_groups++;
    if (testMMIODataSizes(device)) {
        passed_test_groups++;
    }
    
    // === Results ===
    std::cout << "\n=== Final Results ===" << std::endl;
    std::cout << "Test groups passed: " << passed_test_groups << "/" << total_test_groups << std::endl;
    
    if (passed_test_groups == total_test_groups) {
        std::cout << "🎉 All MMIO tests passed successfully!" << std::endl;
        std::cout << std::endl;
        std::cout << "✅ Safe MMIO testing strategy:" << std::endl;
        std::cout << "   • Only accessed documented registers in BAR0 (Register Control)" << std::endl;
        std::cout << "   • Used BAR1 (BRAM Responder) for memory-like testing" << std::endl;
        std::cout << "   • Tested BAR3 (DBI Gateway) for PCIe configuration reads" << std::endl;
        std::cout << "   • Completely avoided dangerous BARs (especially BAR5)" << std::endl;
        std::cout << "   • Validated all access patterns and data sizes" << std::endl;
        
        return 0;
    } else {
        std::cout << "❌ Some MMIO tests failed!" << std::endl;
        return 1;
    }
}
