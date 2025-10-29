#include <iostream>
#include <iomanip>
#include <memory>
#include <vector>
#include <chrono>
#include <cstring>
#include <random>
#include <cstdlib>
#include "vp815.hpp"
#include "Achronix_device.h"
#include "Achronix_DMA.h"
#include "Achronix_util.h"

// Constants for linked-list DMA
#define DESCRIPTOR_SIZE 24
#define BRAM_DESCRIPTOR_MAX_NUM 340  // 16KB BRAM / 24 bytes / 2 - 2
#define BUFFER_MAX_SIZE 0x400000UL   // 4MB maximum per descriptor

// Function to print usage information
void print_usage(const char* program_name) {
    std::cout << "Usage: " << program_name << " [options]" << std::endl;
    std::cout << "Options:" << std::endl;
    std::cout << "  -c, --channel <num>    DMA channel number (0-3, default: 0)" << std::endl;
    std::cout << "  -l, --list <num>       Use linked-list mode with <num> descriptors (default: 0)" << std::endl;
    std::cout << "  -b, --buffer_size <num> Buffer size per descriptor in bytes (default: 4MB)" << std::endl;
    std::cout << "  -h, --help            Show this help message" << std::endl;
    std::cout << std::endl;
    std::cout << "Examples:" << std::endl;
    std::cout << "  " << program_name << " -c 1                    # Test DMA channel 1" << std::endl;
    std::cout << "  " << program_name << " -l 10                   # Test 10x4MB = 40MB transfer" << std::endl;
    std::cout << "  " << program_name << " -l 5 -b 0x200000        # Test 5x2MB = 10MB transfer" << std::endl;
    std::cout << "  " << program_name << "                         # Test DMA channel 0 (default)" << std::endl;
}

// Function to parse command line arguments
int parse_arguments(int argc, char* argv[], int& channel, int& list_num, size_t& buffer_size) {
    channel = 0; // default channel
    list_num = 0; // default: no linked-list mode
    buffer_size = 0x400000UL; // default: 4MB
    
    for (int i = 1; i < argc; i++) {
        std::string arg = argv[i];
        
        if (arg == "-h" || arg == "--help") {
            print_usage(argv[0]);
            return 1; // help requested
        }
        else if (arg == "-c" || arg == "--channel") {
            if (i + 1 < argc) {
                try {
                    channel = std::stoi(argv[i + 1]);
                    if (channel < 0 || channel > 3) {
                        std::cerr << "Error: Channel must be between 0 and 3" << std::endl;
                        return -1;
                    }
                    i++; // skip next argument
                } catch (const std::exception& e) {
                    std::cerr << "Error: Invalid channel number '" << argv[i + 1] << "'" << std::endl;
                    return -1;
                }
            } else {
                std::cerr << "Error: Channel number required after -c/--channel" << std::endl;
                return -1;
            }
        }
        else if (arg == "-l" || arg == "--list") {
            if (i + 1 < argc) {
                try {
                    list_num = std::stoi(argv[i + 1]);
                    if (list_num < 0 || list_num > BRAM_DESCRIPTOR_MAX_NUM) {
                        std::cerr << "Error: List descriptors must be between 0 and " 
                                  << BRAM_DESCRIPTOR_MAX_NUM << std::endl;
                        return -1;
                    }
                    i++; // skip next argument
                } catch (const std::exception& e) {
                    std::cerr << "Error: Invalid list number '" << argv[i + 1] << "'" << std::endl;
                    return -1;
                }
            } else {
                std::cerr << "Error: List number required after -l/--list" << std::endl;
                return -1;
            }
        }
        else if (arg == "-b" || arg == "--buffer_size") {
            if (i + 1 < argc) {
                try {
                    buffer_size = std::stoull(argv[i + 1], nullptr, 0); // Support hex input
                    if (buffer_size == 0 || buffer_size > BUFFER_MAX_SIZE) {
                        std::cerr << "Error: Buffer size must be between 1 and 0x" 
                                  << std::hex << BUFFER_MAX_SIZE << " (" 
                                  << std::dec << BUFFER_MAX_SIZE << " bytes)" << std::endl;
                        return -1;
                    }
                    i++; // skip next argument
                } catch (const std::exception& e) {
                    std::cerr << "Error: Invalid buffer size '" << argv[i + 1] << "'" << std::endl;
                    return -1;
                }
            } else {
                std::cerr << "Error: Buffer size required after -b/--buffer_size" << std::endl;
                return -1;
            }
        }
        else {
            std::cerr << "Error: Unknown argument '" << arg << "'" << std::endl;
            print_usage(argv[0]);
            return -1;
        }
    }
    
    return 0; // success
}

// Function to generate test data pattern
void generate_test_data(uint32_t* buffer, size_t size_words, uint32_t pattern) {
    for (size_t i = 0; i < size_words; i++) {
        switch (pattern) {
            case 0: // Sequential pattern
                buffer[i] = static_cast<uint32_t>(i);
                break;
            case 1: // DEADBEEF pattern
                buffer[i] = 0xDEADBEEF;
                break;
            case 2: // Random pattern
                buffer[i] = static_cast<uint32_t>(rand());
                break;
            case 3: // Checkerboard pattern
                buffer[i] = (i % 2) ? 0xAAAAAAAA : 0x55555555;
                break;
            default:
                buffer[i] = pattern;
                break;
        }
    }
}

// Function to verify test data
bool verify_test_data(const uint32_t* buffer, size_t size_words, uint32_t pattern, const uint32_t* reference_data = nullptr) {
    for (size_t i = 0; i < size_words; i++) {
        uint32_t expected;
        switch (pattern) {
            case 0: // Sequential pattern
                expected = static_cast<uint32_t>(i);
                break;
            case 1: // DEADBEEF pattern
                expected = 0xDEADBEEF;
                break;
            case 2: // Random pattern - use reference data if provided
                if (reference_data) {
                    expected = reference_data[i];
                } else {
                    // For random pattern without reference, just check that data is not all zeros
                    if (buffer[i] == 0) {
                        std::cout << "Random data verification: word " << i << " is zero" << std::endl;
                        return false;
                    }
                    continue; // Skip detailed verification for random data
                }
                break;
            case 3: // Checkerboard pattern
                expected = (i % 2) ? 0xAAAAAAAA : 0x55555555;
                break;
            default:
                expected = pattern;
                break;
        }
        if (buffer[i] != expected) {
            std::cout << "Data mismatch at word " << i << ": expected 0x" 
                      << std::hex << expected << ", got 0x" << buffer[i] << std::endl;
            return false;
        }
    }
    return true;
}

// Function to perform DMA round-trip test with timing
bool dma_roundtrip_test(ACX_DMA_engine_context* engine, size_t buffer_size_bytes, 
                       uint32_t test_pattern, int channel = 0) {
    const uint64_t dev_address = ACX_GDDR6_SPACE;
    
    // Allocate host buffer
    std::vector<uint32_t> host_buffer(buffer_size_bytes / sizeof(uint32_t));
    generate_test_data(host_buffer.data(), host_buffer.size(), test_pattern);
    
    std::cout << "  Testing " << std::dec << buffer_size_bytes << " bytes (0x" 
              << std::hex << buffer_size_bytes << ") with pattern " << test_pattern << "... ";
    
    // Host to Device transfer with timing
    auto h2d_start = std::chrono::high_resolution_clock::now();
    
    ACX_DMA_transaction* h2d_transaction = nullptr;
    ACX_SDK_STATUS status = acx_dma_start_xfer_h2d(
        host_buffer.data(), buffer_size_bytes, dev_address, channel, engine, &h2d_transaction);
    
    if (status != ACX_SDK_STATUS_OK) {
        std::cout << "FAILED (H2D alloc)" << std::endl;
        return false;
    }
    
    // Wait for H2D completion
    ACX_DMA_TRANSFER_STATUS xfer_status = acx_dma_wait(h2d_transaction, 5000);
    if (xfer_status != ACX_DMA_XFER_COMPLETE) {
        acx_dma_halt_tactn(h2d_transaction);
        acx_dma_cleanup_tactn(h2d_transaction);
        std::cout << "FAILED (H2D timeout)" << std::endl;
        return false;
    }
    
    auto h2d_end = std::chrono::high_resolution_clock::now();
    auto h2d_duration = std::chrono::duration_cast<std::chrono::microseconds>(h2d_end - h2d_start);
    
    acx_dma_cleanup_tactn(h2d_transaction);
    
    // Device to Host transfer with timing
    auto d2h_start = std::chrono::high_resolution_clock::now();
    
    ACX_DMA_transaction* d2h_transaction = nullptr;
    status = acx_dma_start_xfer_d2h(buffer_size_bytes, dev_address, channel, engine, &d2h_transaction);
    
    if (status != ACX_SDK_STATUS_OK) {
        std::cout << "FAILED (D2H alloc)" << std::endl;
        return false;
    }
    
    // Wait for D2H completion
    xfer_status = acx_dma_wait(d2h_transaction, 5000);
    if (xfer_status != ACX_DMA_XFER_COMPLETE) {
        acx_dma_halt_tactn(d2h_transaction);
        acx_dma_cleanup_tactn(d2h_transaction);
        std::cout << "FAILED (D2H timeout)" << std::endl;
        return false;
    }
    
    auto d2h_end = std::chrono::high_resolution_clock::now();
    auto d2h_duration = std::chrono::duration_cast<std::chrono::microseconds>(d2h_end - d2h_start);
    
    // Verify data integrity
    bool data_match = verify_test_data(
        static_cast<const uint32_t*>(d2h_transaction->dma_buffer->data), 
        host_buffer.size(), test_pattern, 
        (test_pattern == 2) ? host_buffer.data() : nullptr);
    
    acx_dma_cleanup_tactn(d2h_transaction);
    
    // Calculate bandwidth
    double h2d_bandwidth = (double)buffer_size_bytes / (h2d_duration.count() / 1000000.0) / (1024.0 * 1024.0);
    double d2h_bandwidth = (double)buffer_size_bytes / (d2h_duration.count() / 1000000.0) / (1024.0 * 1024.0);
    
    if (data_match) {
        std::cout << "PASSED" << std::endl;
        std::cout << "    H2D: " << std::dec << h2d_duration.count() << " us (" 
                  << std::fixed << std::setprecision(2) << h2d_bandwidth << " MB/s)" << std::endl;
        std::cout << "    D2H: " << std::dec << d2h_duration.count() << " us (" 
                  << std::fixed << std::setprecision(2) << d2h_bandwidth << " MB/s)" << std::endl;
        return true;
    } else {
        std::cout << "FAILED (data mismatch)" << std::endl;
        return false;
    }
}

int main(int argc, char* argv[]) {
    // Parse command line arguments
    int channel;
    int list_num;
    size_t buffer_size;
    int parse_result = parse_arguments(argc, argv, channel, list_num, buffer_size);
    if (parse_result == 1) {
        return 0; // help requested
    } else if (parse_result == -1) {
        return 1; // error
    }
    
    std::cout << "=== Enhanced GDDR6 Memory Test with DMA ===" << std::endl;
    std::cout << "Testing DMA Channel: " << std::dec << channel << std::endl;

    // Initialize VP815 device for register access
    std::unique_ptr<achronix::VP815> device;
    try {
        device = std::make_unique<achronix::VP815>(0);
        std::cout << "✅ VP815 device initialized successfully" << std::endl;
    } catch (const std::exception& e) {
        std::cerr << "❌ Failed to initialize VP815 device: " << e.what() << std::endl;
        return 1;
    }

    // Initialize ACX device for DMA operations
    ACX_DEV_PCIe_device* acx_device = acx_dev_init_pcie_device_idx(0);
    if (acx_device == nullptr || acx_device->status != ACX_SDK_STATUS_OK) {
        std::cerr << "❌ Failed to initialize ACX device" << std::endl;
        return 1;
    }
    
    // Set device part name
    acx_device->part_name = ACX_PART_AC7t1500;
    
    // Check PCIe link health
    if (acx_util_pci_link_is_up(acx_device) != ACX_SDK_STATUS_OK) {
        std::cerr << "❌ PCIe link appears to be down" << std::endl;
        acx_dev_cleanup_pcie_device(acx_device);
        return 1;
    }
    
    std::cout << "✅ ACX device initialized successfully" << std::endl;

    // Register map constants
    const uint32_t REGS_PER_GDDR_CH = 11;
    const uint32_t REGS_PER_IRQ_GEN_CH = 3;
    const uint32_t REGS_PER_MSIX_IRQ_CH = 4;
    const uint32_t NUM_MSIX_IRQ_CH = 2;
    const uint32_t NUM_IRQ_GEN_REGS = NUM_MSIX_IRQ_CH * REGS_PER_IRQ_GEN_CH; // 2*3 = 6
    const uint32_t MSIX_IRQ_REGS_BASE = 2 + NUM_IRQ_GEN_REGS; // 2 + 6 = 8
    const uint32_t NUM_MSIX_IRQ_REGS = 4 + (NUM_MSIX_IRQ_CH * REGS_PER_MSIX_IRQ_CH); // 4 + (2*4) = 12
    const uint32_t GDDR_REGS_BASE = MSIX_IRQ_REGS_BASE + NUM_MSIX_IRQ_REGS; // 8 + 12 = 20
    const uint32_t ADM_STATUS_REG = 132; // offset 132*4 = 528 = 0x210

    // Check ADM status for GDDR6 training
    uint32_t adm_status;
    device->mmioRead32(0, ADM_STATUS_REG * 4, adm_status);
    std::cout << "ADM Status: 0x" << std::hex << std::setw(8) << std::setfill('0') << adm_status;

    if (adm_status & 0x0A) {
        std::cout << " ✅ GDDR6 training complete" << std::endl;
    } else {
        std::cout << " ⚠️  GDDR6 training not complete" << std::endl;
        std::cout << "⚠️  DMA tests may fail without proper GDDR6 training" << std::endl;
    }

    // Focus on selected channel only (comment out multi-channel testing)
    const uint32_t TEST_CHANNEL = static_cast<uint32_t>(channel);
    std::cout << "\n=== GDDR6 Channel " << std::dec << TEST_CHANNEL << " Status ===" << std::endl;

    uint32_t ch_base = GDDR_REGS_BASE + (TEST_CHANNEL * REGS_PER_GDDR_CH);

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

    // Comment out multi-channel testing
    /*
    // Read all GDDR6 channel registers
    for (uint32_t ch = 0; ch < NUM_GDDR_CHANNELS; ch++) {
        std::cout << "=== GDDR6 Channel " << std::dec << ch << " Status ===" << std::endl;
        // ... channel testing code ...
    }
    */

    // Set up DMA engine
    std::cout << "\n=== DMA Engine Setup ===" << std::endl;
    ACX_DMA_engine_context engine;
    acx_dma_build_engine_cntx(&engine, acx_device, channel);
    acx_dma_init_engine_cntx(&engine);

    if (engine.status != ACX_SDK_STATUS_OK) {
        std::cerr << "❌ Failed to setup DMA engine" << std::endl;
        acx_dev_cleanup_pcie_device(acx_device);
        return 1;
    }
    std::cout << "✅ DMA engine configured successfully" << std::endl;

    // DMA Testing with Multiple Buffer Sizes
    std::cout << "\n=== DMA Round-Trip Tests ===" << std::endl;
    
    // Test buffer sizes: 1KB, 4KB, 16KB, 64KB, 256KB, 4MB (maximum)
    std::vector<size_t> test_sizes = {0x4UL, 0x40UL, 0x400UL, 0x4000UL, 0x40000UL, 0x400000UL, 0x4000000UL};
    std::vector<uint32_t> test_patterns = {0, 1, 2, 3}; // Sequential, DEADBEEF, Random, Checkerboard
    
    int total_tests = 0;
    int passed_tests = 0;
    
    for (size_t buffer_size : test_sizes) {
        std::cout << "\nBuffer Size: " << std::dec << buffer_size << " bytes (0x" 
                  << std::hex << buffer_size << ")" << std::endl;
        
        for (uint32_t pattern : test_patterns) {
            total_tests++;
            if (dma_roundtrip_test(&engine, buffer_size, pattern, channel)) {
                passed_tests++;
            }
        }
    }
    
    // Summary
    std::cout << "\n=== Test Summary ===" << std::endl;
    std::cout << "Total Tests: " << std::dec << total_tests << std::endl;
    std::cout << "Passed: " << passed_tests << std::endl;
    std::cout << "Failed: " << (total_tests - passed_tests) << std::endl;
    std::cout << "Success Rate: " << std::fixed << std::setprecision(1) 
              << (100.0 * passed_tests / total_tests) << "%" << std::endl;
    
    if (passed_tests == total_tests) {
        std::cout << "✅ All DMA tests PASSED!" << std::endl;
    } else {
        std::cout << "❌ Some DMA tests FAILED!" << std::endl;
    }

    // Cleanup
    acx_dev_cleanup_pcie_device(acx_device);
    return (passed_tests == total_tests) ? 0 : 1;
}
