#pragma once

#include <memory>
#include <vector>
#include <cstdint>
#include <string>
#include "shell.hpp"  // For Device base class

// Forward declarations to avoid exposing SDK headers in public interface
struct _ACX_DEV_PCIe_device;
struct _ACX_DMA_engine_context;
struct _ACX_MMIO_handle;
struct _ACX_MSIX_context;

namespace achronix {

// DMA Buffer Size Constraints (matching SDK limitations)
static constexpr size_t DMA_BUFFER_MAX_SIZE = 0x400000UL;  // 4MB - DMA engine does not support transfers > one VM Page
static constexpr size_t DMA_BUFFER_DEFAULT_SIZE = 0x1000UL;  // 4KB - Default buffer size

/**
 * @brief High-level wrapper for Achronix VP815 FPGA device
 * 
 * This class provides a simplified interface to the Achronix SDK,
 * hiding the complexity of engine contexts, handles, and low-level operations.
 * It supports DMA transfers, MMIO operations, and MSI-X interrupts.
 * Inherits from Device to provide common FPGA device interface.
 */
class VP815 : public Device {
public:
    /**
     * @brief Construct a new VP815 object
     * 
     * @param device_id PCIe device index (default: 0)
     * @param num_dma_channels Number of DMA channels to initialize (default: 4)
     */
    explicit VP815(uint32_t device_id = 0, uint32_t num_dma_channels = 4);
    
    /**
     * @brief Construct a new VP815 object using BDF notation
     * 
     * @param device_bdf PCIe Bus:Device.Function notation (e.g., "0000:01:00.0")
     * @param num_dma_channels Number of DMA channels to initialize (default: 4)
     */
    explicit VP815(const std::string& device_bdf, uint32_t num_dma_channels = 4);
    
    /**
     * @brief Construct a new VP815 object using BDF object
     * 
     * @param device_bdf BDF object representing PCIe Bus:Device.Function
     * @param num_dma_channels Number of DMA channels to initialize (default: 4)
     */
    explicit VP815(const BDF& device_bdf, uint32_t num_dma_channels = 4);
    
    /**
     * @brief Destroy the VP815 object and clean up all resources
     */
    ~VP815();

    // Disable copy constructor and assignment operator
    VP815(const VP815&) = delete;
    VP815& operator=(const VP815&) = delete;

    // Enable move constructor and assignment operator
    VP815(VP815&& other) noexcept;
    VP815& operator=(VP815&& other) noexcept;

    /**
     * @brief Check if device is properly initialized and ready
     * 
     * @return true if device is ready for operations
     */
    bool isReady() const;

    /**
     * @brief Check device status and print comprehensive information
     * 
     * Prints device info, PCIe link status, part name, BAR information,
     * DMA channel count, and MSI-X status to stdout.
     * 
     * @return true if device is ready for operations
     */
    bool printDeviceStatus() const;

    /**
     * @brief Get device information string
     * 
     * @return std::string Device description and status
     */
    std::string getDeviceInfo() const;

    // ==================== Device Interface Implementation ====================
    
    /**
     * @brief Print device information (implements Device::print_info)
     * 
     * Prints comprehensive device status including PCIe link, BARs, DMA channels, etc.
     */
    void print_info() override;
    
    /**
     * @brief Program device with bitstream (implements Device::program)
     * 
     * @param bitstream Path to bitstream file
     * @return true if programming successful
     */
    bool program(const char* bitstream) override;
    
    /**
     * @brief Generic MMIO write (implements Device::mmioWrite)
     * 
     * @param addr Full address including BAR selection
     * @param size Number of bytes to write
     * @param buf Buffer containing data to write
     * @return true if write successful
     */
    bool mmioWrite(uint64_t addr, size_t size, char* buf) override;
    
    /**
     * @brief Generic MMIO read (implements Device::mmioRead)
     * 
     * @param addr Full address including BAR selection
     * @param size Number of bytes to read
     * @param buf Buffer to receive read data
     * @return true if read successful
     */
    bool mmioRead(uint64_t addr, size_t size, char* buf) override;

    // ==================== DMA Operations ====================

    /**
     * @brief Transfer data from host to device (implements Device::dmaWrite)
     * 
     * Automatically handles DMA buffer allocation, data copying, transfer, and cleanup.
     * The user only needs to provide a regular memory buffer.
     * 
     * @param addr Target address on device
     * @param size Number of bytes to transfer (max 4MB)
     * @param buf Host buffer containing data to transfer (regular memory)
     * @return true if transfer completed successfully
     */
    bool dmaWrite(uint64_t addr, size_t size, char* buf) override;

    /**
     * @brief Transfer data from device to host (implements Device::dmaRead)
     * 
     * Automatically handles DMA buffer allocation, transfer, data copying, and cleanup.
     * The user only needs to provide a regular memory buffer to receive data.
     * 
     * @param addr Source address on device
     * @param size Number of bytes to transfer (max 4MB)
     * @param buf Host buffer to receive data (regular memory)
     * @return true if transfer completed successfully
     */
    bool dmaRead(uint64_t addr, size_t size, char* buf) override;

    /**
     * @brief Transfer data from host to device with timeout
     * 
     * Extended version with timeout parameter for specialized use cases.
     * 
     * @param addr Target address on device
     * @param size Number of bytes to transfer (max 4MB)
     * @param buf Host buffer containing data to transfer (regular memory)
     * @param timeout_ms Timeout in milliseconds
     * @return true if transfer completed successfully
     */
    bool dmaWrite(uint64_t addr, size_t size, char* buf, uint32_t timeout_ms);

    /**
     * @brief Transfer data from device to host with timeout
     * 
     * Extended version with timeout parameter for specialized use cases.
     * 
     * @param addr Source address on device
     * @param size Number of bytes to transfer (max 4MB)
     * @param buf Host buffer to receive data (regular memory)
     * @param timeout_ms Timeout in milliseconds
     * @return true if transfer completed successfully
     */
    bool dmaRead(uint64_t addr, size_t size, char* buf, uint32_t timeout_ms);

    // ==================== Advanced DMA Operations (Channel Control) ====================

    /**
     * @brief Transfer data from host to device using specific channel
     * 
     * Automatically handles DMA buffer allocation, data copying, transfer, and cleanup.
     * 
     * @param addr Target address on device
     * @param size Number of bytes to transfer (max 4MB)
     * @param buf Host buffer containing data to transfer (regular memory)
     * @param channel Specific DMA channel to use
     * @param timeout_ms Timeout in milliseconds (default: 5000)
     * @return true if transfer completed successfully
     */
    bool dmaWriteChannel(uint64_t addr, size_t size, char* buf, uint32_t channel, 
                         uint32_t timeout_ms = 5000);

    /**
     * @brief Transfer data from device to host using specific channel
     * 
     * Automatically handles DMA buffer allocation, transfer, data copying, and cleanup.
     * 
     * @param addr Source address on device
     * @param size Number of bytes to transfer (max 4MB)
     * @param buf Host buffer to receive data (regular memory)
     * @param channel Specific DMA channel to use
     * @param timeout_ms Timeout in milliseconds (default: 5000)
     * @return true if transfer completed successfully
     */
    bool dmaReadChannel(uint64_t addr, size_t size, char* buf, uint32_t channel,
                        uint32_t timeout_ms = 5000);

    /**
     * @brief Get number of available DMA channels
     * 
     * @return Number of DMA channels available
     */
    uint32_t getDmaChannelCount() const;

    // ==================== MMIO Operations ====================

    /**
     * @brief Read 8-bit value from device memory
     * 
     * @param bar_num BAR number (0-5)
     * @param offset Offset within BAR
     * @param value Reference to store read value
     * @return true if read successful
     */
    bool mmioRead8(uint32_t bar_num, uint64_t offset, uint8_t& value);

    /**
     * @brief Read 16-bit value from device memory
     * 
     * @param bar_num BAR number (0-5)
     * @param offset Offset within BAR
     * @param value Reference to store read value
     * @return true if read successful
     */
    bool mmioRead16(uint32_t bar_num, uint64_t offset, uint16_t& value);

    /**
     * @brief Read 32-bit value from device memory
     * 
     * @param bar_num BAR number (0-5)
     * @param offset Offset within BAR
     * @param value Reference to store read value
     * @return true if read successful
     */
    bool mmioRead32(uint32_t bar_num, uint64_t offset, uint32_t& value);

    /**
     * @brief Read 64-bit value from device memory
     * 
     * @param bar_num BAR number (0-5)
     * @param offset Offset within BAR
     * @param value Reference to store read value
     * @return true if read successful
     */
    bool mmioRead64(uint32_t bar_num, uint64_t offset, uint64_t& value);

    /**
     * @brief Write 8-bit value to device memory
     * 
     * @param bar_num BAR number (0-5)
     * @param offset Offset within BAR
     * @param value Value to write
     * @return true if write successful
     */
    bool mmioWrite8(uint32_t bar_num, uint64_t offset, uint8_t value);

    /**
     * @brief Write 16-bit value to device memory
     * 
     * @param bar_num BAR number (0-5)
     * @param offset Offset within BAR
     * @param value Value to write
     * @return true if write successful
     */
    bool mmioWrite16(uint32_t bar_num, uint64_t offset, uint16_t value);

    /**
     * @brief Write 32-bit value to device memory
     * 
     * @param bar_num BAR number (0-5)
     * @param offset Offset within BAR
     * @param value Value to write
     * @return true if write successful
     */
    bool mmioWrite32(uint32_t bar_num, uint64_t offset, uint32_t value);

    /**
     * @brief Write 64-bit value to device memory
     * 
     * @param bar_num BAR number (0-5)
     * @param offset Offset within BAR
     * @param value Value to write
     * @return true if write successful
     */
    bool mmioWrite64(uint32_t bar_num, uint64_t offset, uint64_t value);

    // Convenience overloads that return values directly (throws on error)
    uint8_t  mmioRead8(uint32_t bar_num, uint64_t offset);
    uint16_t mmioRead16(uint32_t bar_num, uint64_t offset);
    uint32_t mmioRead32(uint32_t bar_num, uint64_t offset);
    uint64_t mmioRead64(uint32_t bar_num, uint64_t offset);

    // ==================== Device Interface Implementation (Interrupts) ====================
    
    /**
     * @brief Check if device supports interrupts (implements Device::hasInterrupts)
     * 
     * @return true if MSI-X interrupts are available and enabled
     */
    bool hasInterrupts() const override;
    
    /**
     * @brief Get number of interrupt vectors (implements Device::getInterruptVectorCount)
     * 
     * @return Number of available MSI-X interrupt vectors
     */
    uint32_t getInterruptVectorCount() const override;
    
    /**
     * @brief Register callback for interrupt (implements Device::registerInterruptHandler)
     * 
     * @param vector_id Interrupt vector ID (0 to vector_count-1)
     * @param handler Callback function to execute when interrupt occurs
     * @return true if registration successful
     */
    bool registerInterruptHandler(uint32_t vector_id, InterruptHandler handler) override;
    
    /**
     * @brief Unregister interrupt callback (implements Device::unregisterInterruptHandler)
     * 
     * @param vector_id Interrupt vector ID to unregister
     * @return true if unregistration successful
     */
    bool unregisterInterruptHandler(uint32_t vector_id) override;
    
    /**
     * @brief Start interrupt handling system (implements Device::startInterruptHandling)
     * 
     * @return true if interrupt system started successfully
     */
    bool startInterruptHandling() override;
    
    /**
     * @brief Stop interrupt handling system (implements Device::stopInterruptHandling)
     */
    void stopInterruptHandling() override;
    
    /**
     * @brief Wait for interrupt (implements Device::waitForInterrupt)
     * 
     * @param vector_id Interrupt vector ID to wait for
     * @param timeout_ms Timeout in milliseconds
     * @return true if interrupt received within timeout
     */
    bool waitForInterrupt(uint32_t vector_id, uint32_t timeout_ms = 5000) override;
    
    /**
     * @brief Cancel interrupt wait (implements Device::cancelInterruptWait)
     * 
     * @param vector_id Interrupt vector ID to cancel wait for
     */
    void cancelInterruptWait(uint32_t vector_id) override;
    
    /**
     * @brief Enable all interrupts (implements Device::enableInterrupts)
     * 
     * @return true if all interrupts enabled successfully
     */
    bool enableInterrupts() override;
    
    /**
     * @brief Disable all interrupts (implements Device::disableInterrupts)
     * 
     * @return true if all interrupts disabled successfully
     */
    bool disableInterrupts() override;

    // ==================== Extended Interrupt Operations ====================
    
    /**
     * @brief Enable specific interrupt vector (VP815-specific)
     * 
     * @param vector_id Interrupt vector ID to enable
     * @return true if successfully enabled
     */
    bool enableInterruptVector(uint32_t vector_id);
    
    /**
     * @brief Disable specific interrupt vector (VP815-specific)
     * 
     * @param vector_id Interrupt vector ID to disable
     * @return true if successfully disabled
     */
    bool disableInterruptVector(uint32_t vector_id);
    
    /**
     * @brief Check if specific interrupt vector is enabled (VP815-specific)
     * 
     * @param vector_id Interrupt vector ID to check
     * @return true if vector is enabled
     */
    bool isInterruptVectorEnabled(uint32_t vector_id) const;

    /**
     * @brief Trigger MSI-X interrupt (for testing) - implements Device::triggerInterrupt
     * 
     * @param vector_id Interrupt vector ID
     * @return true if interrupt triggered successfully
     */
    bool triggerInterrupt(uint32_t vector_id) override;

    /**
     * @brief Check if MSI-X is enabled on device
     * 
     * @return true if MSI-X is enabled
     */
    bool isMsixEnabled() const;

    /**
     * @brief Get number of available MSI-X vectors
     * 
     * @return Number of MSI-X vectors, 0 if not available
     */
    uint32_t getMsixVectorCount() const;

    // ==================== Utility Functions ====================

    /**
     * @brief Get BAR size
     * 
     * @param bar_num BAR number (0-5)
     * @return BAR size in bytes, 0 if invalid
     */
    uint64_t getBarSize(uint32_t bar_num) const;

    /**
     * @brief Check if PCIe link is up
     * 
     * @return true if PCIe link is operational
     */
    bool isPcieLinkUp() const;

    /**
     * @brief Get device part name
     * 
     * @return std::string Device part name (e.g., "AC7t1500")
     */
    std::string getPartName() const;

    /**
     * @brief Get maximum DMA buffer size supported by the device
     * 
     * @return Maximum buffer size in bytes (4MB)
     */
    static constexpr size_t getMaxBufferSize() { return DMA_BUFFER_MAX_SIZE; }

private:
    // Private implementation class to hide SDK details
    class Impl;
    std::unique_ptr<Impl> pImpl;

    // Private helper methods
    void initializeDevice(uint32_t device_id, const std::string& bdf, uint32_t num_dma_channels);
    void cleanup();
    
    // ==================== Private VP815-Specific Operations ====================
    
    // Private DMA buffer management (internal use only)
    void* allocateDmaBuffer(size_t size_bytes);
    void freeDmaBuffer(void* buffer);
    uint64_t getDmaPhysicalAddress(void* buffer);
    
    // Private DBI operations (Achronix-specific, not available on AMD devices)
    bool dbiRead(uint64_t reg_addr, uint32_t& value);
    bool dbiWrite(uint64_t reg_addr, uint32_t value);
    
    // Private interrupt management
    void startInterruptThreads();
    void stopInterruptThreads();
    void interruptWorkerThread(uint32_t vector_id);
};

/**
 * @brief Exception class for VP815 operations
 */
class VP815Exception : public std::exception {
public:
    explicit VP815Exception(const std::string& message) : message_(message) {}
    const char* what() const noexcept override { return message_.c_str(); }

private:
    std::string message_;
};

} // namespace achronix 