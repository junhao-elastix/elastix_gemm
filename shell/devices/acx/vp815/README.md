# Achronix VP815 - Device Guide

Comprehensive guide for using the Achronix VP815 FPGA card with the Elastix Unified Shell (EUS).

## Overview

The VP815 is an Achronix FPGA card featuring:
- **FPGA**: ACX_PART_AC7t1500 
- **Interface**: PCIe Gen5 x16
- **Memory**: GDDR6, DDR4, BRAM endpoints
- **DMA**: 4 independent channels with round-robin arbitration
- **Inheritance**: Extends the common Device interface for polymorphic usage

## Quick Start

### Basic VP815 Usage

```cpp
#include "vp815.hpp"
using namespace achronix;

try {
    // Initialize VP815 device (device ID 0)
    VP815 device(0);
    
    // Check device status and print comprehensive info
    if (!device.printDeviceStatus()) {
        std::cerr << "Device not ready" << std::endl;
        return 1;
    }
    
    // Simple MMIO read - PCIe device/vendor ID (always safe, known value)
    uint32_t device_vendor_id;
    if (device.mmioRead32(3, 0x00, device_vendor_id)) {
        std::cout << "Device/Vendor ID: 0x" << std::hex << device_vendor_id;
        if (device_vendor_id == 0x101b59) {
            std::cout << " (Achronix VP815)" << std::endl;
        } else {
            std::cout << " (Unexpected)" << std::endl;
        }
    }
    
    // Simple DMA operation (no manual buffer management needed)
    std::vector<uint8_t> buffer(4096);
    // Fill buffer with data
    std::fill(buffer.begin(), buffer.end(), 0xAA);
    
    // Transfer to device (DMA buffer allocation/cleanup handled automatically)
    bool success = device.dmaWrite(0x10000, 4096, reinterpret_cast<char*>(buffer.data()));
    std::cout << "DMA transfer: " << (success ? "OK" : "FAILED") << std::endl;
    
} catch (const achronix::DeviceException& e) {
    std::cerr << "Device error: " << e.what() << std::endl;
    return 1;
}
```

## ⚠️ MMIO Safety Guidelines

**MMIO operations can crash the host system if incorrect addresses are accessed.** Always follow these safety protocols for VP815:

### Safe BAR Access Patterns

```cpp
// BAR0 (Register Control Block) - Use documented offsets only
uint32_t basic_status;
device.mmioRead32(0, 0x00, basic_status);  // Basic register access

// BAR1 (BRAM Responder) - Safe for memory-like operations
uint32_t bram_data;
device.mmioRead32(1, 0x1000, bram_data);   // BRAM read
device.mmioWrite32(1, 0x2000, 0xDEADBEEF); // BRAM write

// BAR3 (DBI Gateway / PCIe Config) - Safe for reading configuration
uint32_t device_vendor_id;
device.mmioRead32(3, 0x00, device_vendor_id);  // Returns 0x101b59 (Device ID 0x0010 + Vendor ID 0x1b59)

// BAR5 (FCU CSR Space) - NEVER ACCESS - Can crash system!
// device.mmioRead32(5, 0x0000, value);  // DON'T DO THIS!
```

### Hardware-Specific BAR Map

```
✅ SAFE:
  BAR0: Register Control Block (use documented offsets only)
  BAR1: BRAM Responder (memory interface, any offset)
  BAR3: DBI Gateway / PCIe Config (safe for reading configuration registers)

⚠️  CAUTION:
  BAR2: MSI-X Table (critical system resource)

❌ DANGEROUS:
  BAR5: FCU CSR Space (can crash host system)
```

### MSI-X Validation (Required for Interrupt Handlings)

**Always check MSI-X status before accessing MSI-X registers:**

```cpp
// CRITICAL: Check MSI-X status first
if (device.isMsixEnabled()) {
    // Safe to access MSI-X registers (0x38, 0x58, 0x68, etc.)
    uint32_t interrupt_count;
    bool success = device.mmioRead32(0, 0x58, interrupt_count);
} else {
    // MSI-X disabled - DO NOT access MSI-X registers
    std::cout << "MSI-X disabled - skipping MSI-X register access" << std::endl;
}
```

## DMA Buffer Constraints

### Maximum Buffer Size

**DMA transfers are limited to 4MB (0x400000 bytes) per operation.**

```cpp
// CORRECT: Within 4MB limit
void* buffer = device.allocateDmaBuffer(4 * 1024 * 1024);  // 4MB - OK

// INCORRECT: Exceeds limit - will be rejected
void* large_buffer = device.allocateDmaBuffer(8 * 1024 * 1024);  // 8MB - FAIL

// Check maximum allowed size
size_t max_size = VP815::getMaxBufferSize();  // Returns 0x400000 (4MB)
```

### DMA Channel Architecture

- **4 DMA channels** available (round-robin allocation)
- **Universal memory access**: All channels can access GDDR6, DDR4, and BRAM
- **NoC contention**: Multiple channels may compete for memory controller bandwidth
- **Arbitration**: Hardware uses weighted round-robin for channel arbitration

## Complete API Reference

### Device Initialization

```cpp
class VP815 : public Device {  // Inherits from common Device interface
public:
    // Device initialization
    VP815(uint32_t device_id = 0, uint32_t num_dma_channels = 4);     // Initialize by device index
    VP815(const std::string& device_bdf, uint32_t num_dma_channels = 4); // Initialize by BDF string
    VP815(const BDF& device_bdf, uint32_t num_dma_channels = 4);      // Initialize by BDF object
    ~VP815();                                                         // Automatic cleanup
```

### Device Status and Information

```cpp
    // Device interface implementation (inherited from Device)
    void print_info() override;              // Print comprehensive device info
    bool program(const char* bitstream) override;   // Program device with bitstream
    
    // VP815-specific device information
    bool printDeviceStatus() const;          // Comprehensive device info (VP815-specific)
    bool isReady() const;                    // Check if device is operational
    bool isMsixEnabled() const;              // Check MSI-X capability status
    uint64_t getBarSize(uint32_t bar_num) const;    // Get BAR size in bytes
    uint32_t getMsixVectorCount() const;     // Get number of MSI-X vectors
```

### MMIO Operations

```cpp
    // Generic MMIO interface (inherited from Device) 
    bool mmioRead(uint64_t addr, size_t size, char* buf) override;  // Generic read
    bool mmioWrite(uint64_t addr, size_t size, char* buf) override; // Generic write
    
    // VP815-specific MMIO operations (by data size and BAR)
    bool mmioRead8(uint32_t bar_num, uint64_t offset, uint8_t& value);
    bool mmioRead16(uint32_t bar_num, uint64_t offset, uint16_t& value);
    bool mmioRead32(uint32_t bar_num, uint64_t offset, uint32_t& value);
    bool mmioRead64(uint32_t bar_num, uint64_t offset, uint64_t& value);
    
    bool mmioWrite8(uint32_t bar_num, uint64_t offset, uint8_t value);
    bool mmioWrite16(uint32_t bar_num, uint64_t offset, uint16_t value);
    bool mmioWrite32(uint32_t bar_num, uint64_t offset, uint32_t value);
    bool mmioWrite64(uint32_t bar_num, uint64_t offset, uint64_t value);
```

### Advanced DMA Operations

```cpp
    // Advanced DMA operations (for specialized use cases)
    uint64_t getDmaPhysicalAddress(void* buffer);    // Get physical address for external DMA buffers
```

### DMA Operations

```cpp
    // DMA operations (automatic channel selection) - matches shell.hpp interface
    bool dmaWrite(uint64_t addr, size_t size, char* buf);
    bool dmaRead(uint64_t addr, size_t size, char* buf);
    
    // DMA operations with timeout (extended interface)
    bool dmaWrite(uint64_t addr, size_t size, char* buf, uint32_t timeout_ms);
    bool dmaRead(uint64_t addr, size_t size, char* buf, uint32_t timeout_ms);
    
    // DMA operations (explicit channel control)
    bool dmaWriteChannel(uint64_t addr, size_t size, char* buf, uint32_t channel, uint32_t timeout_ms = 5000);
    bool dmaReadChannel(uint64_t addr, size_t size, char* buf, uint32_t channel, uint32_t timeout_ms = 5000);
```

### Constants and Constraints

```cpp
    // Buffer size constraints
    static constexpr size_t getMaxBufferSize() { return DMA_BUFFER_MAX_SIZE; }        // 4MB limit
    static constexpr size_t getDefaultBufferSize() { return DMA_BUFFER_DEFAULT_SIZE; } // 4KB default
};
```

## Example Programs

### Simple DMA Example

```cpp
#include "vp815.hpp"

int main() {
    try {
        achronix::VP815 device(0);
        
        // Check device is ready
        if (!device.printDeviceStatus()) {
            std::cerr << "Device not ready" << std::endl;
            return 1;
        }
        
        // Allocate 1MB buffer (within 4MB limit) - regular memory
        std::vector<uint32_t> buffer(256 * 1024);  // 1MB = 256K words
        
        // Fill with test pattern
        for (int i = 0; i < 256*1024; i++) {
            buffer[i] = i;
        }
        
        // Transfer to device GDDR6 at address 0x0 (DMA buffer management automatic)
        bool success = device.dmaWrite(0x0, buffer.size() * sizeof(uint32_t), reinterpret_cast<char*>(buffer.data()));
        
        if (success) {
            std::cout << "DMA transfer completed successfully" << std::endl;
        }
        
    } catch (const achronix::DeviceException& e) {
        std::cerr << "Error: " << e.what() << std::endl;
        return 1;
    }
    
    return 0;
}
```

### Safe MMIO Example

```cpp
#include "vp815.hpp"

int main() {
    try {
        achronix::VP815 device(0);
        
        // Always check device status first
        if (!device.printDeviceStatus()) {
            return 1;
        }
        
        // CRITICAL: Check MSI-X status before accessing MSI-X registers
        if (device.isMsixEnabled()) {
            uint32_t interrupt_count;
            if (device.mmioRead32(0, 0x58, interrupt_count)) {
                std::cout << "MSI-X interrupt count: " << interrupt_count << std::endl;
            }
        } else {
            std::cout << "MSI-X disabled - using basic register access" << std::endl;
            uint32_t basic_status;
            if (device.mmioRead32(0, 0x00, basic_status)) {
                std::cout << "Basic status: 0x" << std::hex << basic_status << std::endl;
            }
        }
        
        // Safe BRAM access (BAR1)
        uint32_t bram_data;
        if (device.mmioRead32(1, 0x1000, bram_data)) {
            std::cout << "BRAM data: 0x" << std::hex << bram_data << std::endl;
        }
        
        // Safe PCIe configuration read (BAR3) - always returns known value
        uint32_t device_vendor_id;
        if (device.mmioRead32(3, 0x00, device_vendor_id)) {
            std::cout << "Device/Vendor ID: 0x" << std::hex << device_vendor_id;
            if (device_vendor_id == 0x101b59) {
                std::cout << " (Achronix VP815)" << std::endl;
            } else {
                std::cout << " (Unexpected)" << std::endl;
            }
        }
        
    } catch (const achronix::DeviceException& e) {
        std::cerr << "Error: " << e.what() << std::endl;
        return 1;
    }
    
    return 0;
}
```

## Thread Safety

- **Device initialization/cleanup**: Not thread-safe (single-threaded initialization required)
- **DMA buffer management**: Thread-safe (internal mutex protection)
- **DMA channel allocation**: Thread-safe (atomic counter for round-robin)
- **MMIO operations**: Safe if accessing different registers simultaneously
- **Multiple devices**: Can be used safely from different threads

## Memory Management

- **Automatic cleanup**: Device resources freed in destructor
- **Simplified DMA**: No manual DMA buffer management - use regular memory buffers
- **Internal buffer handling**: DMA buffer allocation/deallocation handled automatically
- **Move semantics**: Efficient resource transfer supported
- **Copy prevention**: Copy construction/assignment disabled to prevent resource duplication

## Polymorphic Usage

The VP815 class inherits from the common `Device` interface, enabling polymorphic usage:

```cpp
#include "vp815.hpp"

// Function that accepts any Device - demonstrates polymorphism
void process_device(Device* device) {
    // Use generic Device interface - calls VP815 implementations
    device->print_info();                    // Calls VP815::print_info()
    
    std::vector<uint8_t> data = {0xDE, 0xAD, 0xBE, 0xEF};
    device->dmaWrite(0x1000, data.size(), reinterpret_cast<char*>(data.data()));
    device->dmaRead(0x1000, data.size(), reinterpret_cast<char*>(data.data()));
    
    // Generic MMIO - BAR3 device ID using address encoding (3ULL << 60) | offset
    char mmio_buf[4];
    device->mmioRead((3ULL << 60) | 0x00, 4, mmio_buf);
}

int main() {
    VP815 vp815_device(0);          // Create VP815 instance
    
    // Use as Device* (polymorphic)
    process_device(&vp815_device);
    
    // Use as VP815* (access VP815-specific features)
    std::cout << "DMA Channels: " << vp815_device.getDmaChannelCount() << std::endl;
    std::cout << "MSI-X Status: " << vp815_device.isMsixEnabled() << std::endl;
    std::cout << "Part Name: " << vp815_device.getPartName() << std::endl;
    
    return 0;
}
```

**Benefits of Inheritance:**
- ✅ **Polymorphic usage**: VP815 can be used wherever Device* is expected
- ✅ **Interface compliance**: Implements all required Device methods
- ✅ **Extended functionality**: Adds VP815-specific methods beyond base Device
- ✅ **Code reusability**: Generic functions work with any Device-derived class

## Troubleshooting

### Common Issues

1. **Device not found**: Check device ID or BDF notation
2. **PCIe link down**: Ensure FPGA is properly programmed with VP815 bitstream
3. **DMA failures**: Verify device addresses are valid for your bitstream
4. **Permission errors**: Run with appropriate privileges for PCIe access
5. **MMIO crashes**: Always validate MSI-X status and avoid BAR5
6. **DMA size errors**: Respect 4MB buffer size limit
7. **Build errors**: Ensure absolute paths in Makefile point to correct SDK installation

### Debug Build

Use `make debug` to build with debug symbols and enable additional logging:

```cpp
#ifdef DEBUG
    std::cout << "Debug: DMA transaction created" << std::endl;
#endif
```

### Hardware Safety Checklist

- ✅ Check MSI-X status before accessing MSI-X registers
- ✅ Use only documented register offsets in BAR0
- ✅ Test MMIO operations with BAR1 (BRAM) first
- ✅ Validate DMA buffer sizes ≤ 4MB
- ✅ Never access BAR5 (can crash system)
- ✅ Check device status before operations

## Quick Test Validation

To quickly validate your VP815 setup, run the all-in-one test:

```bash
cd tests
PROJ_ROOT=/path/to/your/project make all_test
./test_all
```

This single test validates DMA, MMIO, and MSI-X functionality with built-in safety measures.
