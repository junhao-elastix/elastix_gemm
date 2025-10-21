#include "vp815.hpp"
#include "Achronix_device.h"
#include <iostream>
#include <iomanip>
#include <cstring>
#include <vector>
#include <algorithm>

using namespace achronix;

int main(int argc, char* argv[]) {
    try {
        std::cout << "=== Simple VP815 DMA Test ===" << std::endl;
        
        // Get device ID from command line, default to 0
        uint32_t device_id = 0;
        if (argc > 1) {
            device_id = std::stoul(argv[1]);
        }
        
        std::cout << "Initializing VP815 device " << device_id << "..." << std::endl;
        
        // This single line replaces 20+ lines of SDK initialization!
        VP815 device(device_id);
        
        // Check status and print all device information in one call
        if (!device.printDeviceStatus()) {
            std::cerr << "VP815 device initialization failed!" << std::endl;
            return 1;
        }
        
        // Round trip DMA test - Write and Read back
        std::cout << "\n=== DMA Round Trip Test ===" << std::endl;
        
        const size_t buffer_size = 4096;  // 4KB test buffer (max supported: 4MB)
        const uint64_t device_address = ACX_GDDR6_SPACE + 0x1000;  // GDDR6 memory space + 4KB offset
        
        // Validate buffer size against device constraints
        if (buffer_size > VP815::getMaxBufferSize()) {
            std::cerr << "Error: Buffer size " << buffer_size 
                      << " bytes exceeds maximum supported size of " 
                      << VP815::getMaxBufferSize() << " bytes" << std::endl;
            return 1;
        }
        
        std::cout << "Using device address: 0x" << std::hex << device_address << std::dec 
                  << " (GDDR6 space + 0x1000 offset)" << std::endl;
        std::cout << "Buffer size: " << buffer_size << " bytes (max supported: " 
                  << (VP815::getMaxBufferSize() / 1024 / 1024) << "MB)" << std::endl;
        
        // Allocate regular memory buffers (DMA buffer management is now internal)
        std::vector<uint8_t> write_buffer(buffer_size);
        std::vector<uint8_t> read_buffer(buffer_size);
        
        std::cout << "Allocated regular memory buffers (DMA buffers handled internally)" << std::endl;
        std::cout << "  Write buffer: " << static_cast<void*>(write_buffer.data()) << std::endl;
        std::cout << "  Read buffer:  " << static_cast<void*>(read_buffer.data()) << std::endl;
        
        // Fill write buffer with test pattern
        uint32_t* write_words = reinterpret_cast<uint32_t*>(write_buffer.data());
        for (size_t i = 0; i < buffer_size/4; ++i) {
            write_words[i] = 0xDEADBEEF + (i * 0x11111111);
        }
        
        // Clear read buffer
        std::fill(read_buffer.begin(), read_buffer.end(), 0);
        
        std::cout << "\nStep 1: Writing " << buffer_size << " bytes to device address 0x" 
                  << std::hex << device_address << std::dec << std::endl;
        
        // Write data to device (DMA buffer allocation/deallocation handled internally)
        bool write_success = device.dmaWrite(device_address, buffer_size, reinterpret_cast<char*>(write_buffer.data()));
        if (!write_success) {
            std::cerr << "DMA write failed!" << std::endl;
            return 1;
        }
        std::cout << "  DMA write completed successfully" << std::endl;
        
        std::cout << "\nStep 2: Reading back " << buffer_size << " bytes from device address 0x" 
                  << std::hex << device_address << std::dec << std::endl;
        
        // Read data back from device (DMA buffer allocation/deallocation handled internally)
        bool read_success = device.dmaRead(device_address, buffer_size, reinterpret_cast<char*>(read_buffer.data()));
        if (!read_success) {
            std::cerr << "DMA read failed!" << std::endl;
            return 1;
        }
        std::cout << "  DMA read completed successfully" << std::endl;
        
        std::cout << "\nStep 3: Verifying data integrity..." << std::endl;
        
        // Compare write and read buffers
        bool data_match = (write_buffer == read_buffer);
        
        if (data_match) {
            std::cout << "  ✓ SUCCESS: Data integrity verified - write and read data match!" << std::endl;
        } else {
            std::cout << "  ✗ FAILURE: Data mismatch detected!" << std::endl;
            
            // Show first few mismatched bytes for debugging
            std::cout << "  First 32 bytes comparison:" << std::endl;
            for (int i = 0; i < 32; ++i) {
                if (write_buffer[i] != read_buffer[i]) {
                    std::cout << "    Offset " << std::dec << std::setw(2) << i 
                              << ": wrote 0x" << std::hex << std::setw(2) << std::setfill('0') 
                              << static_cast<int>(write_buffer[i])
                              << ", read 0x" << std::setw(2) << std::setfill('0') 
                              << static_cast<int>(read_buffer[i]) << std::endl;
                }
            }
        }
        
        // Display sample data
        std::cout << "\nSample data (first 16 bytes):" << std::endl;
        std::cout << "  Written: ";
        for (int i = 0; i < 16; ++i) {
            std::cout << std::hex << std::setw(2) << std::setfill('0') 
                      << static_cast<int>(write_buffer[i]) << " ";
        }
        std::cout << std::endl;
        std::cout << "  Read:    ";
        for (int i = 0; i < 16; ++i) {
            std::cout << std::hex << std::setw(2) << std::setfill('0') 
                      << static_cast<int>(read_buffer[i]) << " ";
        }
        std::cout << std::dec << std::endl;
        
        std::cout << "\n=== DMA Test completed successfully ===" << std::endl;
        
        return data_match ? 0 : 1;  // Return success only if DMA test passed
        
    } catch (const VP815Exception& e) {
        std::cerr << "VP815 error: " << e.what() << std::endl;
        return 1;
    } catch (const std::exception& e) {
        std::cerr << "Error: " << e.what() << std::endl;
        return 1;
    }
} 