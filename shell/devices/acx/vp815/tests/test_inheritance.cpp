#include "vp815.hpp"
#include <iostream>
#include <vector>

using namespace achronix;

// Function that takes a Device pointer - demonstrates polymorphism
void test_device_interface(Device* device) {
    std::cout << "=== Testing Device Interface (Polymorphism) ===" << std::endl;
    
    // Test Device interface functions
    std::cout << "Device BDF: " << device->bdf.to_str() << std::endl;
    std::cout << "Device Ready: " << (device->ready ? "Yes" : "No") << std::endl;
    
    // Test print_info (calls VP815's implementation)
    std::cout << "\nCalling Device::print_info():" << std::endl;
    device->print_info();
    
    // Test generic DMA interface
    std::cout << "\n=== Testing Generic DMA Interface ===" << std::endl;
    std::vector<uint8_t> test_data = {0xDE, 0xAD, 0xBE, 0xEF};
    
    bool write_success = device->dmaWrite(0x1000, test_data.size(), 
                                          reinterpret_cast<char*>(test_data.data()));
    std::cout << "Generic DMA Write: " << (write_success ? "SUCCESS" : "FAILED") << std::endl;
    
    std::vector<uint8_t> read_data(test_data.size());
    bool read_success = device->dmaRead(0x1000, read_data.size(), 
                                        reinterpret_cast<char*>(read_data.data()));
    std::cout << "Generic DMA Read: " << (read_success ? "SUCCESS" : "FAILED") << std::endl;
    
    if (write_success && read_success) {
        bool data_match = (test_data == read_data);
        std::cout << "Data Integrity: " << (data_match ? "VERIFIED" : "FAILED") << std::endl;
    }
    
    // Test generic MMIO interface  
    std::cout << "\n=== Testing Generic MMIO Interface ===" << std::endl;
    
    // Test 32-bit MMIO read from BAR3 (device ID) using generic interface
    // Address encoding: BAR3 = 3, so use (3ULL << 60) | offset
    uint64_t generic_addr = (3ULL << 60) | 0x00;  // BAR3 offset 0x00
    char mmio_buf[4];
    
    bool mmio_success = device->mmioRead(generic_addr, 4, mmio_buf);
    if (mmio_success) {
        uint32_t device_id = *reinterpret_cast<uint32_t*>(mmio_buf);
        std::cout << "Generic MMIO Read (Device ID): 0x" << std::hex << device_id << std::dec;
        if (device_id == 0x101b59) {
            std::cout << " (Achronix VP815) ✓" << std::endl;
        } else {
            std::cout << " (Unexpected)" << std::endl;
        }
    } else {
        std::cout << "Generic MMIO Read: FAILED" << std::endl;
    }
}

int main() {
    try {
        std::cout << "=== VP815 Device Inheritance Test ===" << std::endl;
        
        // Create VP815 instance
        VP815 vp815_device(0);
        
        std::cout << "✓ VP815 device created successfully" << std::endl;
        std::cout << "✓ VP815 inherits from Device class" << std::endl;
        
        // Test polymorphism - pass VP815 as Device*
        test_device_interface(&vp815_device);
        
        std::cout << "\n=== Testing VP815-Specific Features ===" << std::endl;
        
        // These functions are specific to VP815, not in Device base class
        std::cout << "VP815 DMA Channels: " << vp815_device.getDmaChannelCount() << std::endl;
        std::cout << "VP815 MSI-X Enabled: " << (vp815_device.isMsixEnabled() ? "Yes" : "No") << std::endl;
        std::cout << "VP815 Part Name: " << vp815_device.getPartName() << std::endl;
        
        // Test VP815 can be used as both Device* and VP815*
        Device* device_ptr = &vp815_device;  // Polymorphic usage
        VP815* vp815_ptr = &vp815_device;    // Direct usage
        
        std::cout << "\n✓ Polymorphism test successful!" << std::endl;
        std::cout << "✓ Device interface: " << (device_ptr ? "Available" : "Not Available") << std::endl;
        std::cout << "✓ VP815 interface: " << (vp815_ptr ? "Available" : "Not Available") << std::endl;
        
        return 0;
        
    } catch (const std::exception& e) {
        std::cerr << "Error: " << e.what() << std::endl;
        return 1;
    }
}