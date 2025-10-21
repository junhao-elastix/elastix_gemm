// =============================================================================
// test_dma_access.cpp
// =============================================================================
// Verify DMA read/write access to Result BRAM and check GDDR6 status
//
// Test Flow:
//   1. Write/read Result BRAM via DMA and verify
//   2. Check result registers are accessible
//   3. Write/read GDDR6 memory via DMA and verify
//   4. Verify GDDR6 training status
// =============================================================================

#include <iostream>
#include <iomanip>
#include <vector>
#include <cstring>
#include <memory>
#include <unistd.h>
#include "vp815.hpp"
#include "Achronix_device.h"
#include "Achronix_util.h"

using namespace achronix;

// Register offsets (from elastix_gemm_top.sv)
static constexpr uint32_t CONTROL_REG      = 0;
static constexpr uint32_t TEST_STATUS_REG  = 1;
static constexpr uint32_t ADM_STATUS_REG   = 132;  // 0x210
static constexpr uint32_t BITSTREAM_ID     = 133;  // 0x214
static constexpr uint32_t SCRATCH_REG      = 134;  // 0x218
static constexpr uint32_t RESULT_REG_0     = 135;  // 0x21C
static constexpr uint32_t RESULT_REG_1     = 136;  // 0x220
static constexpr uint32_t RESULT_REG_2     = 137;  // 0x224
static constexpr uint32_t RESULT_REG_3     = 138;  // 0x228

// DMA parameters
static constexpr uint32_t TEST_SIZE_BYTES  = 256;  // Test with 256 bytes (1 BRAM line)
static constexpr uint32_t TEST_PATTERN_0   = 0xDEADBEEF;

// Result BRAM DMA address at NAP[3][4]
// Must use SDK function acx_util_nap_absolute_addr() to calculate NAP address
// Will be initialized in main() after device initialization
static uint64_t RESULT_BRAM_BASE = 0;

// GDDR6 address translation (from test_mem_endpoints.cpp)
static uint64_t gddr6_address_translation(uint64_t address) {
    const static uint64_t GDDR6_ADDRESS_MASK = 0x3FFFFFFFUL; // 1GB address space needs a 30 bit mask
    uint64_t channel_address = address & GDDR6_ADDRESS_MASK;
    uint64_t controller_select = (address & ~GDDR6_ADDRESS_MASK) << 3;
    return controller_select | channel_address;
}

// =============================================================================
// Helper Functions
// =============================================================================

bool check_device_health(VP815& device) {
    uint32_t adm_status, test_status, bitstream_id;
    
    std::cout << "\n[Device Health Check]" << std::endl;
    
    if (!device.mmioRead32(0, ADM_STATUS_REG * 4, adm_status)) {
        std::cout << "  ADM Status:    [ERROR] Cannot read" << std::endl;
        return false;
    }
    std::cout << "  ADM Status:    0x" << std::hex << std::setw(8) << std::setfill('0') << adm_status;
    if ((adm_status & 0x3) == 0x3) {
        std::cout << " (GDDR6 trained) [OK]" << std::dec << std::endl;
    } else {
        std::cout << " (GDDR6 not ready) [WARN]" << std::dec << std::endl;
    }
    
    if (!device.mmioRead32(0, TEST_STATUS_REG * 4, test_status)) {
        std::cout << "  Test Status:   [ERROR] Cannot read" << std::endl;
        return false;
    }
    std::cout << "  Test Status:   0x" << std::hex << std::setw(8) << std::setfill('0') << test_status << std::dec << std::endl;
    
    if (!device.mmioRead32(0, BITSTREAM_ID * 4, bitstream_id)) {
        std::cout << "  Bitstream ID:  [ERROR] Cannot read" << std::endl;
        return false;
    }
    std::cout << "  Bitstream ID:  0x" << std::hex << std::setw(8) << std::setfill('0') << bitstream_id << std::dec << std::endl;
    
    // Check if device is responsive with scratch register test
    uint32_t scratch_val = 0xA5A5A5A5;
    if (!device.mmioWrite32(0, SCRATCH_REG * 4, scratch_val)) {
        std::cout << "  Scratch test:  [FAIL] Cannot write" << std::endl;
        return false;
    }
    
    uint32_t readback;
    if (!device.mmioRead32(0, SCRATCH_REG * 4, readback)) {
        std::cout << "  Scratch test:  [FAIL] Cannot read" << std::endl;
        return false;
    }
    
    if (readback != scratch_val) {
        std::cout << "  Scratch test:  [FAIL] Wrote 0x" << std::hex << scratch_val 
                  << ", read 0x" << readback << std::dec << std::endl;
        return false;
    }
    std::cout << "  Scratch test:  [PASS]" << std::endl;
    
    return true;
}

// =============================================================================
// Test 1: Result BRAM DMA Access
// =============================================================================

bool test_result_bram_dma(VP815& device) {
    std::cout << "\n========================================" << std::endl;
    std::cout << "Test 1: Result BRAM DMA Access" << std::endl;
    std::cout << "========================================" << std::endl;
    
    // Allocate host buffers
    std::vector<uint32_t> write_buffer(TEST_SIZE_BYTES / 4);
    std::vector<uint32_t> read_buffer(TEST_SIZE_BYTES / 4);
    
    // Initialize write buffer with test pattern
    std::cout << "[BRAM] Preparing test pattern (" << TEST_SIZE_BYTES << " bytes)..." << std::endl;
    for (size_t i = 0; i < TEST_SIZE_BYTES / 4; i++) {
        write_buffer[i] = TEST_PATTERN_0 + i;
    }
    
    // Write to BRAM via DMA
    std::cout << "[BRAM] Writing to Result BRAM via DMA..." << std::endl;
    if (!device.dmaWrite(RESULT_BRAM_BASE, TEST_SIZE_BYTES, reinterpret_cast<char*>(write_buffer.data()))) {
        std::cout << "[BRAM] Write failed" << std::endl;
        return false;
    }
    std::cout << "[BRAM] Write complete: " << TEST_SIZE_BYTES << " bytes" << std::endl;
    
    // Small delay for write to settle
    usleep(1000);
    
    // Read back via DMA
    std::cout << "[BRAM] Reading back from Result BRAM via DMA..." << std::endl;
    if (!device.dmaRead(RESULT_BRAM_BASE, TEST_SIZE_BYTES, reinterpret_cast<char*>(read_buffer.data()))) {
        std::cout << "[BRAM] Read failed" << std::endl;
        return false;
    }
    std::cout << "[BRAM] Read complete: " << TEST_SIZE_BYTES << " bytes" << std::endl;
    
    // Verify data
    std::cout << "[BRAM] Verifying data..." << std::endl;
    int mismatches = 0;
    for (size_t i = 0; i < TEST_SIZE_BYTES / 4; i++) {
        if (read_buffer[i] != write_buffer[i]) {
            std::cout << "[BRAM] Mismatch at word " << i << ": wrote 0x" << std::hex 
                      << write_buffer[i] << ", read 0x" << read_buffer[i] << std::dec << std::endl;
            mismatches++;
            if (mismatches >= 10) {
                std::cout << "[BRAM] ... (showing first 10 mismatches)" << std::endl;
                break;
            }
        }
    }
    
    if (mismatches == 0) {
        std::cout << "[BRAM] Verification: [PASS] All data matches!" << std::endl;
        return true;
    } else {
        std::cout << "[BRAM] Verification: [FAIL] " << mismatches << " mismatches" << std::endl;
        return false;
    }
}

// =============================================================================
// Test 2: Result Register Access
// =============================================================================

bool test_result_registers(VP815& device) {
    std::cout << "\n========================================" << std::endl;
    std::cout << "Test 2: Result Register Access" << std::endl;
    std::cout << "========================================" << std::endl;
    
    // Read result registers
    std::cout << "[REG] Reading result registers..." << std::endl;
    uint32_t result[4];
    bool success = true;
    
    for (int i = 0; i < 4; i++) {
        if (!device.mmioRead32(0, (RESULT_REG_0 + i) * 4, result[i])) {
            std::cout << "[REG] Failed to read RESULT_" << i << std::endl;
            success = false;
        }
    }
    
    if (!success) {
        std::cout << "[REG] [FAIL] Cannot read result registers" << std::endl;
        return false;
    }
    
    std::cout << "[REG] Result registers:" << std::endl;
    for (int i = 0; i < 4; i++) {
        std::cout << "      RESULT_" << i << ": 0x" << std::hex << std::setw(8) << std::setfill('0') 
                  << result[i] << " (FP16: 0x" << std::setw(4) << (result[i] & 0xFFFF) 
                  << ")" << std::dec << std::endl;
    }
    
    // Check if registers are readable (not all 0xFFFFFFFF)
    if (result[0] == 0xFFFFFFFF && result[1] == 0xFFFFFFFF &&
        result[2] == 0xFFFFFFFF && result[3] == 0xFFFFFFFF) {
        std::cout << "[REG] [WARN] All registers read 0xFFFFFFFF (device may be hung)" << std::endl;
        return false;
    }
    
    std::cout << "[REG] [PASS] Registers accessible" << std::endl;
    return true;
}

// =============================================================================
// Test 3: GDDR6 Memory DMA Access
// =============================================================================

bool test_gddr6_memory_dma(VP815& device, uint64_t gddr6_base) {
    std::cout << "\n========================================" << std::endl;
    std::cout << "Test 3: GDDR6 Memory DMA Access" << std::endl;
    std::cout << "========================================" << std::endl;
    
    // Check if GDDR6 is trained first
    uint32_t adm_status;
    if (!device.mmioRead32(0, ADM_STATUS_REG * 4, adm_status)) {
        std::cout << "[GDDR6] Cannot read ADM status" << std::endl;
        return false;
    }
    
    if ((adm_status & 0x3) != 0x3) {
        std::cout << "[GDDR6] ADM Status: 0x" << std::hex << adm_status << std::dec << std::endl;
        std::cout << "[GDDR6] [SKIP] GDDR6 not trained, cannot test memory" << std::endl;
        return false;
    }
    
    std::cout << "[GDDR6] ADM Status: 0x" << std::hex << adm_status << " (trained) [OK]" << std::dec << std::endl;
    
    // Test write/read to GDDR6 memory
    std::vector<uint32_t> write_buffer(TEST_SIZE_BYTES / 4);
    std::vector<uint32_t> read_buffer(TEST_SIZE_BYTES / 4);
    
    // Initialize with test pattern
    std::cout << "[GDDR6] Preparing test pattern (" << TEST_SIZE_BYTES << " bytes)..." << std::endl;
    for (size_t i = 0; i < TEST_SIZE_BYTES / 4; i++) {
        write_buffer[i] = 0xABCD0000 + i;  // Different pattern from BRAM test
    }
    
    // Translate GDDR6 address
    uint64_t translated_addr = gddr6_address_translation(gddr6_base);
    std::cout << "[GDDR6] Base address: 0x" << std::hex << gddr6_base << std::endl;
    std::cout << "[GDDR6] Translated address: 0x" << translated_addr << std::dec << std::endl;
    
    // Write to GDDR6
    std::cout << "[GDDR6] Writing to GDDR6 memory via DMA..." << std::endl;
    if (!device.dmaWrite(translated_addr, TEST_SIZE_BYTES, reinterpret_cast<char*>(write_buffer.data()))) {
        std::cout << "[GDDR6] Write failed" << std::endl;
        return false;
    }
    std::cout << "[GDDR6] Write complete: " << TEST_SIZE_BYTES << " bytes" << std::endl;
    
    // Small delay
    usleep(1000);
    
    // Read back from GDDR6
    std::cout << "[GDDR6] Reading back from GDDR6 memory via DMA..." << std::endl;
    if (!device.dmaRead(translated_addr, TEST_SIZE_BYTES, reinterpret_cast<char*>(read_buffer.data()))) {
        std::cout << "[GDDR6] Read failed" << std::endl;
        return false;
    }
    std::cout << "[GDDR6] Read complete: " << TEST_SIZE_BYTES << " bytes" << std::endl;
    
    // Verify data
    std::cout << "[GDDR6] Verifying data..." << std::endl;
    int mismatches = 0;
    for (size_t i = 0; i < TEST_SIZE_BYTES / 4; i++) {
        if (read_buffer[i] != write_buffer[i]) {
            std::cout << "[GDDR6] Mismatch at word " << i << ": wrote 0x" << std::hex 
                      << write_buffer[i] << ", read 0x" << read_buffer[i] << std::dec << std::endl;
            mismatches++;
            if (mismatches >= 10) {
                std::cout << "[GDDR6] ... (showing first 10 mismatches)" << std::endl;
                break;
            }
        }
    }
    
    if (mismatches == 0) {
        std::cout << "[GDDR6] Verification: [PASS] All data matches!" << std::endl;
        std::cout << "[GDDR6] GDDR6 memory is accessible via DMA" << std::endl;
        return true;
    } else {
        std::cout << "[GDDR6] Verification: [FAIL] " << mismatches << " mismatches" << std::endl;
        return false;
    }
}

// =============================================================================
// Test 4: GDDR6 Status Check
// =============================================================================

bool test_gddr6_status_check(VP815& device) {
    std::cout << "\n========================================" << std::endl;
    std::cout << "Test 4: GDDR6 Status Check" << std::endl;
    std::cout << "========================================" << std::endl;
    
    uint32_t adm_status;
    if (!device.mmioRead32(0, ADM_STATUS_REG * 4, adm_status)) {
        std::cout << "[STATUS] Cannot read ADM status" << std::endl;
        return false;
    }
    
    std::cout << "[STATUS] ADM Status: 0x" << std::hex << adm_status << std::dec << std::endl;
    std::cout << "[STATUS] Bit[0] (GDDR6 ready): " << ((adm_status & 0x1) ? "1 [OK]" : "0 [FAIL]") << std::endl;
    std::cout << "[STATUS] Bit[1] (GDDR6 trained): " << ((adm_status & 0x2) ? "1 [OK]" : "0 [FAIL]") << std::endl;
    
    if ((adm_status & 0x3) == 0x3) {
        std::cout << "[STATUS] [PASS] GDDR6 fully trained and ready" << std::endl;
        return true;
    } else {
        std::cout << "[STATUS] [WARN] GDDR6 not fully ready" << std::endl;
        return false;
    }
}

// =============================================================================
// Main Test Flow
// =============================================================================

int main() {
    std::cout << "========================================" << std::endl;
    std::cout << "DMA Access Test - Result BRAM & GDDR6" << std::endl;
    std::cout << "========================================" << std::endl;
    
    // Initialize device
    std::unique_ptr<VP815> device;
    try {
        device = std::make_unique<VP815>(0);
        std::cout << "Device initialized successfully" << std::endl;
    } catch (const std::exception& e) {
        std::cerr << "Failed to initialize device: " << e.what() << std::endl;
        return 1;
    }
    
    // Calculate Result BRAM base address using SDK utility
    // NAP[3][5] for Result BRAM DMA bridge (matches placement constraint NOC[3][5])
    RESULT_BRAM_BASE = acx_util_nap_absolute_addr(ACX_PART_AC7t1500, 3, 5);
    std::cout << "Result BRAM NAP[3][5] address: 0x" << std::hex << RESULT_BRAM_BASE << std::dec << std::endl;
    
    // Check device health
    if (!check_device_health(*device)) {
        std::cerr << "Device health check failed" << std::endl;
        return 1;
    }
    
    // Get GDDR6 base address
    const uint64_t GDDR6_BASE_ADDR = ACX_GDDR6_SPACE;
    
    // Run tests
    int tests_passed = 0;
    int tests_run = 0;
    
    // Test 1: Result BRAM DMA
    tests_run++;
    if (test_result_bram_dma(*device)) {
        tests_passed++;
    }
    
    // Test 2: Result registers
    tests_run++;
    if (test_result_registers(*device)) {
        tests_passed++;
    }
    
    // Test 3: GDDR6 Memory DMA
    tests_run++;
    if (test_gddr6_memory_dma(*device, GDDR6_BASE_ADDR)) {
        tests_passed++;
    }
    
    // Test 4: GDDR6 Status check
    tests_run++;
    if (test_gddr6_status_check(*device)) {
        tests_passed++;
    }
    
    // Summary
    std::cout << "\n========================================" << std::endl;
    std::cout << "Test Summary" << std::endl;
    std::cout << "========================================" << std::endl;
    std::cout << "Tests passed: " << tests_passed << " / " << tests_run << std::endl;
    
    if (tests_passed == tests_run) {
        std::cout << "\n[OVERALL] ALL TESTS PASSED" << std::endl;
        std::cout << "Summary:" << std::endl;
        std::cout << "  - Result BRAM DMA: Working" << std::endl;
        std::cout << "  - Result registers: Accessible" << std::endl;
        std::cout << "  - GDDR6 memory DMA: Working" << std::endl;
        std::cout << "  - GDDR6 status: Trained and ready" << std::endl;
        std::cout << "\nReady to integrate result adapter!" << std::endl;
        return 0;
    } else {
        std::cout << "\n[OVERALL] SOME TESTS FAILED" << std::endl;
        std::cout << "Passed: " << tests_passed << " / " << tests_run << std::endl;
        std::cout << "Fix DMA access issues before proceeding" << std::endl;
        return 1;
    }
}
