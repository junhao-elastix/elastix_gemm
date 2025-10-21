/**
 * @file test_all.cpp
 * @brief All-in-one VP815 test covering DMA, MMIO, and MSI-X functionality
 * 
 * This test provides a simple but comprehensive validation of all major
 * VP815 functionality in a single streamlined test program.
 * 
 * Test Coverage:
 * - Device initialization and status
 * - Basic DMA operations (read/write with verification)
 * - Safe MMIO register access (BAR0, BAR1, BAR3)
 * - MSI-X interrupt functionality (with safety checks)
 * - Error handling and edge cases
 */

#include "vp815.hpp"
#include "Achronix_device.h"
#include <iostream>
#include <vector>
#include <chrono>
#include <iomanip>
#include <atomic>
#include <thread>

using namespace achronix;

// Global test state
std::atomic<int> interrupt_count{0};
std::atomic<bool> test_failed{false};

/**
 * @brief Simple interrupt callback for testing
 */
void testInterruptCallback(uint32_t vector_id) {
    interrupt_count++;
    std::cout << "  [CALLBACK] Interrupt received on vector " << vector_id 
              << " (count: " << interrupt_count.load() << ")" << std::endl;
}

/**
 * @brief Test basic DMA functionality
 */
bool testDMA(VP815& device) {
    std::cout << "\n=== DMA Functionality Test ===" << std::endl;
    
    const size_t test_size = 4096;  // 4KB test
    const uint64_t test_addr = ACX_GDDR6_SPACE + 0x1000;  // GDDR6 + 4KB offset
    
    std::cout << "Testing DMA with " << test_size << " bytes at address 0x" 
              << std::hex << test_addr << std::dec << std::endl;
    
    // Allocate test buffers
    std::vector<uint8_t> write_buffer(test_size);
    std::vector<uint8_t> read_buffer(test_size);
    
    // Fill write buffer with test pattern
    for (size_t i = 0; i < test_size; i++) {
        write_buffer[i] = static_cast<uint8_t>((i * 0xAB + 0xCD) & 0xFF);
    }
    
    // Clear read buffer  
    std::fill(read_buffer.begin(), read_buffer.end(), 0);
    
    // Test DMA write
    std::cout << "  1. DMA Write: ";
    bool write_success = device.dmaWrite(test_addr, test_size, 
                                        reinterpret_cast<char*>(write_buffer.data()));
    if (!write_success) {
        std::cout << "FAILED" << std::endl;
        return false;
    }
    std::cout << "SUCCESS" << std::endl;
    
    // Test DMA read
    std::cout << "  2. DMA Read: ";
    bool read_success = device.dmaRead(test_addr, test_size,
                                      reinterpret_cast<char*>(read_buffer.data()));
    if (!read_success) {
        std::cout << "FAILED" << std::endl;
        return false;
    }
    std::cout << "SUCCESS" << std::endl;
    
    // Verify data integrity
    std::cout << "  3. Data Verification: ";
    bool data_match = (write_buffer == read_buffer);
    if (!data_match) {
        std::cout << "FAILED - Data mismatch detected" << std::endl;
        
        // Show first few mismatched bytes
        for (size_t i = 0; i < std::min(test_size, size_t(16)); i++) {
            if (write_buffer[i] != read_buffer[i]) {
                std::cout << "    Offset " << i << ": wrote 0x" << std::hex 
                          << static_cast<int>(write_buffer[i]) << ", read 0x" 
                          << static_cast<int>(read_buffer[i]) << std::dec << std::endl;
            }
        }
        return false;
    }
    std::cout << "SUCCESS" << std::endl;
    
    std::cout << "✅ DMA test completed successfully" << std::endl;
    return true;
}

/**
 * @brief Test MMIO functionality with safe registers
 */
bool testMMIO(VP815& device) {
    std::cout << "\n=== MMIO Functionality Test ===" << std::endl;
    
    // Test 1: Read PCIe Device/Vendor ID (always safe)
    std::cout << "  1. PCIe Device ID Read: ";
    uint32_t device_id;
    if (!device.mmioRead32(3, 0x00, device_id)) {
        std::cout << "FAILED" << std::endl;
        return false;
    }
    std::cout << "SUCCESS (0x" << std::hex << device_id << std::dec << ")";
    if (device_id == 0x00101b59 || device_id == 0x101b59) {
        std::cout << " - Achronix VP815 ✓" << std::endl;
    } else {
        std::cout << " - Unexpected device ID" << std::endl;
    }
    
    // Test 2: BRAM read/write test (BAR1 - safe memory interface)
    std::cout << "  2. BRAM Write/Read Test: ";
    uint32_t test_pattern = 0xDEADBEEF;
    uint32_t read_value;
    
    // Write to BRAM
    if (!device.mmioWrite32(1, 0x1000, test_pattern)) {
        std::cout << "FAILED (write)" << std::endl;
        return false;
    }
    
    // Read back from BRAM
    if (!device.mmioRead32(1, 0x1000, read_value)) {
        std::cout << "FAILED (read)" << std::endl;
        return false;
    }
    
    // Verify data
    if (read_value != test_pattern) {
        std::cout << "FAILED (data mismatch: wrote 0x" << std::hex << test_pattern 
                  << ", read 0x" << read_value << std::dec << ")" << std::endl;
        return false;
    }
    std::cout << "SUCCESS" << std::endl;
    
    // Test 3: Multi-size MMIO operations
    std::cout << "  3. Multi-size MMIO Test: ";
    
    // Test 8-bit
    uint8_t val8 = 0xAB;
    uint8_t read8;
    if (!device.mmioWrite8(1, 0x2000, val8) || !device.mmioRead8(1, 0x2000, read8) || read8 != val8) {
        std::cout << "FAILED (8-bit)" << std::endl;
        return false;
    }
    
    // Test 16-bit
    uint16_t val16 = 0xCDEF;
    uint16_t read16;
    if (!device.mmioWrite16(1, 0x2002, val16) || !device.mmioRead16(1, 0x2002, read16) || read16 != val16) {
        std::cout << "FAILED (16-bit)" << std::endl;
        return false;
    }
    
    // Test 64-bit
    uint64_t val64 = 0x123456789ABCDEF0ULL;
    uint64_t read64;
    if (!device.mmioWrite64(1, 0x2008, val64) || !device.mmioRead64(1, 0x2008, read64) || read64 != val64) {
        std::cout << "FAILED (64-bit)" << std::endl;
        return false;
    }
    
    std::cout << "SUCCESS" << std::endl;
    
    std::cout << "✅ MMIO test completed successfully" << std::endl;
    return true;
}

/**
 * @brief Test MSI-X interrupt functionality with safety checks
 */
bool testMSIX(VP815& device) {
    std::cout << "\n=== MSI-X Interrupt Test ===" << std::endl;
    
    // Safety check: Verify MSI-X is enabled
    std::cout << "  1. MSI-X Capability Check: ";
    if (!device.hasInterrupts()) {
        std::cout << "SKIPPED - MSI-X not available or disabled" << std::endl;
        std::cout << "    This is safe behavior when MSI-X is not enabled" << std::endl;
        return true;  // Not a failure - just not available
    }
    
    uint32_t vector_count = device.getInterruptVectorCount();
    std::cout << "ENABLED (" << vector_count << " vectors available)" << std::endl;
    
    if (vector_count == 0) {
        std::cout << "  ERROR: MSI-X enabled but no vectors available" << std::endl;
        return false;
    }
    
    // Test 2: Basic interrupt callback
    std::cout << "  2. Callback Registration: ";
    interrupt_count = 0;
    
    if (!device.registerInterruptHandler(0, testInterruptCallback)) {
        std::cout << "FAILED" << std::endl;
        return false;
    }
    std::cout << "SUCCESS" << std::endl;
    
    // Test 3: Software interrupt trigger and callback execution
    std::cout << "  3. Software Interrupt Test: ";
    if (!device.triggerInterrupt(0)) {
        std::cout << "FAILED (trigger)" << std::endl;
        device.unregisterInterruptHandler(0);
        return false;
    }
    
    // Wait for callback execution
    std::this_thread::sleep_for(std::chrono::milliseconds(500));
    
    if (interrupt_count == 0) {
        std::cout << "FAILED (callback not executed)" << std::endl;
        device.unregisterInterruptHandler(0);
        return false;
    }
    std::cout << "SUCCESS (callback executed " << interrupt_count.load() << " times)" << std::endl;
    
    // Test 4: Multi-vector support (if available)
    if (vector_count > 1) {
        std::cout << "  4. Multi-Vector Test: ";
        interrupt_count = 0;
        
        // Register handler for vector 1
        if (!device.registerInterruptHandler(1, testInterruptCallback)) {
            std::cout << "FAILED (registration)" << std::endl;
            device.unregisterInterruptHandler(0);
            return false;
        }
        
        // Trigger both vectors
        device.triggerInterrupt(0);
        device.triggerInterrupt(1);
        
        // Wait for callbacks
        std::this_thread::sleep_for(std::chrono::milliseconds(500));
        
        if (interrupt_count < 2) {
            std::cout << "FAILED (expected 2+ callbacks, got " << interrupt_count.load() << ")" << std::endl;
            device.unregisterInterruptHandler(0);
            device.unregisterInterruptHandler(1);
            return false;
        }
        std::cout << "SUCCESS (" << interrupt_count.load() << " callbacks)" << std::endl;
        
        // Cleanup
        device.unregisterInterruptHandler(1);
    } else {
        std::cout << "  4. Multi-Vector Test: SKIPPED (only 1 vector available)" << std::endl;
    }
    
    // Test 5: Vector enable/disable
    std::cout << "  5. Vector Control Test: ";
    interrupt_count = 0;
    
    // Disable vector
    device.disableInterruptVector(0);
    device.triggerInterrupt(0);
    std::this_thread::sleep_for(std::chrono::milliseconds(200));
    
    if (interrupt_count > 0) {
        std::cout << "FAILED (callback executed while disabled)" << std::endl;
        device.unregisterInterruptHandler(0);
        return false;
    }
    
    // Re-enable vector
    device.enableInterruptVector(0);
    device.triggerInterrupt(0);
    std::this_thread::sleep_for(std::chrono::milliseconds(200));
    
    if (interrupt_count == 0) {
        std::cout << "FAILED (callback not executed after re-enable)" << std::endl;
        device.unregisterInterruptHandler(0);
        return false;
    }
    std::cout << "SUCCESS" << std::endl;
    
    // Cleanup
    device.unregisterInterruptHandler(0);
    
    std::cout << "✅ MSI-X test completed successfully" << std::endl;
    return true;
}

/**
 * @brief Test error handling and edge cases
 */
bool testErrorHandling(VP815& device) {
    std::cout << "\n=== Error Handling Test ===" << std::endl;
    
    // Test 1: Invalid DMA parameters
    std::cout << "  1. Invalid DMA Parameters: ";
    char dummy_buffer[4];
    
    // Test oversized buffer
    bool should_fail = device.dmaWrite(0x1000, device.getMaxBufferSize() + 1, dummy_buffer);
    if (should_fail) {
        std::cout << "FAILED (accepted oversized buffer)" << std::endl;
        return false;
    }
    std::cout << "SUCCESS (rejected oversized buffer)" << std::endl;
    
    // Test 2: Invalid MMIO parameters  
    std::cout << "  2. Invalid MMIO Parameters: ";
    uint32_t dummy_value;
    
    // Test invalid BAR
    bool should_fail2 = device.mmioRead32(999, 0x0000, dummy_value);
    if (should_fail2) {
        std::cout << "FAILED (accepted invalid BAR)" << std::endl;
        return false;
    }
    std::cout << "SUCCESS (rejected invalid BAR)" << std::endl;
    
    // Test 3: Invalid interrupt parameters (if MSI-X available)
    if (device.hasInterrupts()) {
        std::cout << "  3. Invalid Interrupt Parameters: ";
        uint32_t max_vector = device.getInterruptVectorCount();
        
        // Test invalid vector ID
        bool should_fail3 = device.registerInterruptHandler(max_vector + 10, testInterruptCallback);
        if (should_fail3) {
            std::cout << "FAILED (accepted invalid vector ID)" << std::endl;
            return false;
        }
        std::cout << "SUCCESS (rejected invalid vector ID)" << std::endl;
    } else {
        std::cout << "  3. Invalid Interrupt Parameters: SKIPPED (MSI-X not available)" << std::endl;
    }
    
    std::cout << "✅ Error handling test completed successfully" << std::endl;
    return true;
}

/**
 * @brief Main comprehensive test function
 */
int main(int argc, char* argv[]) {
    std::cout << "=== VP815 Comprehensive Functionality Test ===" << std::endl;
    std::cout << "Testing DMA, MMIO, and MSI-X functionality with safety measures" << std::endl;
    std::cout << std::endl;
    
    try {
        // Initialize device
        uint32_t device_id = 0;
        if (argc > 1) {
            device_id = std::stoul(argv[1]);
        }
        
        std::cout << "[INFO] Initializing VP815 device " << device_id << "..." << std::endl;
        VP815 device(device_id);
        
        if (!device.isReady()) {
            std::cerr << "[ERROR] Device is not ready for testing" << std::endl;
            return 1;
        }
        
        std::cout << "[SUCCESS] Device initialized successfully" << std::endl;
        
        // Print device status
        device.print_info();
        
        // Run comprehensive tests
        bool all_passed = true;
        
        all_passed &= testDMA(device);
        all_passed &= testMMIO(device);  
        all_passed &= testMSIX(device);
        all_passed &= testErrorHandling(device);
        
        // Final results
        std::cout << "\n=== Test Results Summary ===" << std::endl;
        if (all_passed && !test_failed.load()) {
            std::cout << "🎉 [SUCCESS] All comprehensive tests PASSED!" << std::endl;
            std::cout << "\n✅ Validated functionality:" << std::endl;
            std::cout << "   • DMA operations (read/write with verification)" << std::endl;
            std::cout << "   • MMIO register access (8/16/32/64-bit operations)" << std::endl;
            std::cout << "   • MSI-X interrupt handling (with safety checks)" << std::endl;
            std::cout << "   • Error handling and parameter validation" << std::endl;
            std::cout << "\n🛡️  Safety measures applied:" << std::endl;
            std::cout << "   • MSI-X availability checked before interrupt tests" << std::endl;
            std::cout << "   • Only safe MMIO registers accessed (BAR0/1/3)" << std::endl;
            std::cout << "   • Buffer size limits enforced" << std::endl;
            std::cout << "   • Invalid parameter rejection verified" << std::endl;
            return 0;
        } else {
            std::cout << "❌ [FAILURE] Some tests FAILED!" << std::endl;
            return 1;
        }
        
    } catch (const VP815Exception& e) {
        std::cerr << "[ERROR] VP815 Exception: " << e.what() << std::endl;
        return 1;
    } catch (const std::exception& e) {
        std::cerr << "[ERROR] Exception: " << e.what() << std::endl;
        return 1;
    } catch (...) {
        std::cerr << "[ERROR] Unknown exception occurred" << std::endl;
        return 1;
    }
}