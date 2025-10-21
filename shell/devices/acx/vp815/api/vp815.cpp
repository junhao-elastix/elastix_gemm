#include "vp815.hpp"

// Include all necessary SDK headers (using absolute paths via ACXSDK_ROOT/include)
#include "Achronix_SDK.h"
#include "Achronix_device.h"
#include "Achronix_DMA.h"
#include "Achronix_MMIO.h"
#include "Achronix_MSIX.h"
#include "Achronix_util.h"
#include "Achronix_status.h"

#include <iostream>
#include <sstream>
#include <map>
#include <mutex>
#include <stdexcept>
#include <cstring>
#include <atomic>
#include <thread>
#include <condition_variable>
#include <unordered_map>
#include <functional>

namespace achronix {

// Private implementation class that holds all SDK resources
class VP815::Impl {
public:
    // Core device resources
    ACX_DEV_PCIe_device* pcie_device = nullptr;
    ACX_DMA_engine_context dma_engine;
    ACX_MSIX_context msix_context;
    
    // DMA buffer tracking
    std::map<void*, ACX_DMA_buffer*> dma_buffers;
    std::mutex dma_buffers_mutex;
    
    // Initialization parameters
    uint32_t device_id = 0;
    std::string device_bdf;
    uint32_t num_dma_channels = 4;
    bool initialized = false;
    bool is_bdf_init = false;
    
    // Channel management
    std::atomic<uint32_t> next_channel{0};
    std::mutex channel_mutex;

    // Device info cache
    std::string part_name_str;
    uint64_t bar_sizes[6] = {0};
    
    // Interrupt callback management
    std::unordered_map<uint32_t, Device::InterruptHandler> interrupt_handlers;
    std::unordered_map<uint32_t, std::thread> interrupt_threads;
    std::unordered_map<uint32_t, bool> interrupt_enabled;
    std::unordered_map<uint32_t, std::atomic<bool>> thread_stop_flags;
    std::mutex interrupt_mutex;
    bool interrupt_system_running = false;

    ~Impl() {
        cleanup();
    }

    void cleanup() {
        if (!initialized) return;

        // Stop interrupt system first
        stopInterruptSystem();

        // Clean up DMA buffers
        {
            std::lock_guard<std::mutex> lock(dma_buffers_mutex);
            for (auto& pair : dma_buffers) {
                if (pair.second) {
                    acx_dma_free_buf(pair.second);
                }
            }
            dma_buffers.clear();
        }

        // Clean up device
        if (pcie_device) {
            acx_dev_cleanup_pcie_device(pcie_device);
            pcie_device = nullptr;
        }

        initialized = false;
    }
    
    /**
     * @brief Stop interrupt handling system and clean up all threads
     */
    void stopInterruptSystem() {
        std::lock_guard<std::mutex> lock(interrupt_mutex);
        if (!interrupt_system_running) return;
        
        // Signal all threads to stop
        for (auto& pair : thread_stop_flags) {
            pair.second.store(true);
        }
        
        // Wait for all threads to complete
        for (auto& pair : interrupt_threads) {
            if (pair.second.joinable()) {
                pair.second.join();
            }
        }
        
        // Clear all data structures
        interrupt_handlers.clear();
        interrupt_threads.clear();
        interrupt_enabled.clear();
        thread_stop_flags.clear();
        interrupt_system_running = false;
    }

    bool initializeDevice() {
        try {
            // Initialize PCIe device
            if (is_bdf_init) {
                pcie_device = acx_dev_init_pcie_device_bdf(device_bdf.c_str());
            } else {
                pcie_device = acx_dev_init_pcie_device_idx(device_id);
            }

            if (!pcie_device || pcie_device->status != ACX_SDK_STATUS_OK) {
                std::ostringstream oss;
                oss << "Failed to initialize PCIe device ";
                if (is_bdf_init) {
                    oss << device_bdf;
                } else {
                    oss << device_id;
                }
                throw VP815Exception(oss.str());
            }

            // Check PCIe link health
            if (acx_util_pci_link_is_up(pcie_device) != ACX_SDK_STATUS_OK) {
                throw VP815Exception("PCIe link is down");
            }

            // Set part name (default to AC7t1500 for VP815)
            pcie_device->part_name = ACX_PART_AC7t1500;

            // Cache part name string
            part_name_str = acx_part_name_to_string(pcie_device->part_name);

            // Cache BAR sizes
            for (int i = 0; i < 6; i++) {
                acx_dev_get_bar_size(pcie_device, i, &bar_sizes[i]);
            }

            // Initialize DMA engine
            ACX_SDK_STATUS status = acx_dma_build_engine_cntx(&dma_engine, pcie_device, 0);
            if (status != ACX_SDK_STATUS_OK) {
                throw VP815Exception("Failed to build DMA engine context");
            }

            status = acx_dma_init_engine_cntx(&dma_engine);
            if (status != ACX_SDK_STATUS_OK) {
                throw VP815Exception("Failed to initialize DMA engine context");
            }

            // Initialize MSI-X context
            status = acx_msix_get_context(pcie_device, &msix_context);
            if (status != ACX_SDK_STATUS_OK) {
                // MSI-X might not be available, which is okay
                std::cerr << "Warning: MSI-X context initialization failed" << std::endl;
            }

            initialized = true;
            return true;

        } catch (...) {
            cleanup();
            throw;
        }
    }

    bool isDeviceReady() const {
        if (!initialized || !pcie_device) return false;
        return acx_dev_is_fabric_ready(pcie_device) == ACX_SDK_STATUS_OK;
    }

    std::string getDeviceInfoString() const {
        if (!initialized || !pcie_device) {
            return "Device not initialized";
        }

        std::ostringstream oss;
        oss << "Achronix " << part_name_str << " Device ";
        if (is_bdf_init) {
            oss << device_bdf;
        } else {
            oss << device_id;
        }
        oss << " - Status: " << (isDeviceReady() ? "Ready" : "Not Ready");
        oss << " - MSI-X: " << (acx_msix_is_enabled(pcie_device) == ACX_SDK_STATUS_ENABLE ? "Enabled" : "Disabled");
        return oss.str();
    }

    uint32_t getNextChannel() {
        // Simple round-robin channel allocation
        uint32_t channel = next_channel.fetch_add(1) % num_dma_channels;
        return channel;
    }

    bool dmaTransfer(const void* buffer, uint64_t device_address, size_t size_bytes,
                     uint32_t channel, uint32_t timeout_ms, bool is_write) {
        if (!initialized || !buffer) return false;
        
        // Validate buffer size against DMA engine limitations
        if (size_bytes == 0 || size_bytes > DMA_BUFFER_MAX_SIZE) {
            std::cerr << "DMA transfer size " << size_bytes 
                      << " bytes exceeds maximum allowed size of " 
                      << DMA_BUFFER_MAX_SIZE << " bytes (4MB)" << std::endl;
            return false;
        }

        // Allocate DMA-coherent buffer
        ACX_DMA_buffer* dma_buf = acx_dma_alloc_buf(pcie_device, size_bytes);
        if (!dma_buf || !dma_buf->virt_addr) {
            std::cerr << "Failed to allocate DMA buffer of size " << size_bytes << " bytes" << std::endl;
            return false;
        }

        bool success = false;
        
        try {
            if (is_write) {
                // Copy user data to DMA buffer
                std::memcpy(dma_buf->virt_addr, buffer, size_bytes);
            }

            // Perform DMA transfer
            ACX_DMA_transaction* transaction = nullptr;
            ACX_SDK_STATUS status;

            if (is_write) {
                status = acx_dma_start_xfer_h2d(
                    dma_buf->virt_addr, 
                    static_cast<uint32_t>(size_bytes), 
                    device_address, 
                    channel, 
                    &dma_engine, 
                    &transaction
                );
            } else {
                status = acx_dma_start_xfer_d2h(
                    static_cast<uint32_t>(size_bytes), 
                    device_address, 
                    channel, 
                    &dma_engine, 
                    &transaction
                );
            }

            if (status == ACX_SDK_STATUS_OK && transaction) {
                // Wait for completion
                ACX_DMA_TRANSFER_STATUS transfer_status = acx_dma_wait(transaction, timeout_ms);
                success = (transfer_status == ACX_DMA_XFER_COMPLETE);

                if (!is_write && success) {
                    // For reads, copy data from DMA buffer to user buffer
                    if (transaction->dma_buffer && transaction->dma_buffer->data) {
                        std::memcpy(const_cast<void*>(buffer), transaction->dma_buffer->data, size_bytes);
                    } else {
                        // Fallback: copy from our allocated buffer
                        std::memcpy(const_cast<void*>(buffer), dma_buf->virt_addr, size_bytes);
                    }
                }

                // Clean up transaction
                acx_dma_cleanup_tactn(transaction);
            }
        } catch (const std::exception& e) {
            std::cerr << "DMA transfer exception: " << e.what() << std::endl;
            success = false;
        } catch (...) {
            std::cerr << "Unknown DMA transfer exception" << std::endl;
            success = false;
        }

        // Always free the DMA buffer
        acx_dma_free_buf(dma_buf);

        return success;
    }
};

// ==================== Constructor/Destructor ====================

VP815::VP815(uint32_t device_id, uint32_t num_dma_channels) 
    : Device(BDF(0, device_id, 0)), pImpl(std::make_unique<Impl>()) {
    initializeDevice(device_id, "", num_dma_channels);
}

VP815::VP815(const std::string& device_bdf, uint32_t num_dma_channels)
    : Device(BDF(device_bdf)), pImpl(std::make_unique<Impl>()) {
    initializeDevice(0, device_bdf, num_dma_channels);
}

VP815::VP815(const BDF& device_bdf, uint32_t num_dma_channels)
    : Device(device_bdf), pImpl(std::make_unique<Impl>()) {
    initializeDevice(0, device_bdf.to_str(), num_dma_channels);
}

VP815::~VP815() = default;

VP815::VP815(VP815&& other) noexcept = default;
VP815& VP815::operator=(VP815&& other) noexcept = default;

void VP815::initializeDevice(uint32_t device_id, const std::string& bdf, uint32_t num_dma_channels) {
    pImpl->device_id = device_id;
    pImpl->device_bdf = bdf;
    pImpl->num_dma_channels = num_dma_channels;
    pImpl->is_bdf_init = !bdf.empty();
    
    if (!pImpl->initializeDevice()) {
        ready = false;  // Set Device base class ready flag
        throw VP815Exception("Failed to initialize device");
    }
    
    ready = true;  // Set Device base class ready flag on successful initialization
}

void VP815::cleanup() {
    pImpl->cleanup();
}

// ==================== Device Status ====================

bool VP815::isReady() const {
    return pImpl->isDeviceReady();
}

bool VP815::printDeviceStatus() const {
    bool ready = pImpl->isDeviceReady();
    
    std::cout << "=== Achronix Device Status ===" << std::endl;
    std::cout << pImpl->getDeviceInfoString() << std::endl;
    
    if (!pImpl->initialized || !pImpl->pcie_device) {
        std::cout << "Device not properly initialized" << std::endl;
        return false;
    }
    
    // PCIe Link Status
    std::cout << "PCIe Link: " << (isPcieLinkUp() ? "UP" : "DOWN") << std::endl;
    
    // Part Information
    std::cout << "FPGA Part: " << pImpl->part_name_str << std::endl;
    
    // BAR Information
    std::cout << "\nBAR Information:" << std::endl;
    bool has_bars = false;
    for (uint32_t i = 0; i < 6; ++i) {
        uint64_t size = pImpl->bar_sizes[i];
        if (size > 0) {
            has_bars = true;
            std::cout << "  BAR" << i << ": ";
            if (size >= 1024*1024*1024) {
                std::cout << (size / (1024*1024*1024)) << " GB";
            } else if (size >= 1024*1024) {
                std::cout << (size / (1024*1024)) << " MB";
            } else if (size >= 1024) {
                std::cout << (size / 1024) << " KB";
            } else {
                std::cout << size << " bytes";
            }
            std::cout << " (0x" << std::hex << size << std::dec << ")" << std::endl;
        }
    }
    if (!has_bars) {
        std::cout << "  No accessible BARs found" << std::endl;
    }
    
    // DMA Information
    std::cout << "\nDMA Information:" << std::endl;
    std::cout << "  Available channels: " << pImpl->num_dma_channels << std::endl;
    std::cout << "  Current channel: " << (pImpl->next_channel.load() % pImpl->num_dma_channels) << std::endl;
    
    // MSI-X Information
    std::cout << "\nInterrupt Information:" << std::endl;
    if (isMsixEnabled()) {
        uint32_t vectors = getMsixVectorCount();
        std::cout << "  MSI-X: Enabled (" << vectors << " vectors)" << std::endl;
    } else {
        std::cout << "  MSI-X: Disabled or not available" << std::endl;
    }
    
    std::cout << "\nDevice Status: " << (ready ? "READY" : "NOT READY") << std::endl;
    std::cout << "===============================" << std::endl;
    
    return ready;
}

std::string VP815::getDeviceInfo() const {
    return pImpl->getDeviceInfoString();
}

// ==================== Device Interface Implementation ====================

void VP815::print_info() {
    printDeviceStatus();
}

bool VP815::program(const char* bitstream) {
    // Note: VP815 programming is typically handled externally via Vivado or ACE tools
    // This function could be extended to support bitstream programming if the SDK provides it
    (void)bitstream; // Suppress unused parameter warning
    
    std::cerr << "Warning: VP815 bitstream programming not implemented in this version." << std::endl;
    std::cerr << "Please use Vivado or ACE tools to program the VP815 FPGA." << std::endl;
    return false;
}

bool VP815::mmioWrite(uint64_t addr, size_t size, char* buf) {
    if (!pImpl->initialized || !buf || size == 0) {
        return false;
    }
    
    // Extract BAR number from upper bits of address
    // For VP815, we'll use a simple encoding: BAR number in bits [63:60]
    uint32_t bar_num = static_cast<uint32_t>((addr >> 60) & 0xF);
    uint64_t offset = addr & 0x0FFFFFFFFFFFFFFFULL; // Lower 60 bits
    
    // Handle different sizes
    if (size == 1) {
        return mmioWrite8(bar_num, offset, static_cast<uint8_t>(buf[0]));
    } else if (size == 2) {
        uint16_t value = *reinterpret_cast<uint16_t*>(buf);
        return mmioWrite16(bar_num, offset, value);
    } else if (size == 4) {
        uint32_t value = *reinterpret_cast<uint32_t*>(buf);
        return mmioWrite32(bar_num, offset, value);
    } else if (size == 8) {
        uint64_t value = *reinterpret_cast<uint64_t*>(buf);
        return mmioWrite64(bar_num, offset, value);
    } else {
        // For arbitrary sizes, write byte by byte
        for (size_t i = 0; i < size; ++i) {
            if (!mmioWrite8(bar_num, offset + i, static_cast<uint8_t>(buf[i]))) {
                return false;
            }
        }
        return true;
    }
}

bool VP815::mmioRead(uint64_t addr, size_t size, char* buf) {
    if (!pImpl->initialized || !buf || size == 0) {
        return false;
    }
    
    // Extract BAR number from upper bits of address
    // For VP815, we'll use a simple encoding: BAR number in bits [63:60]
    uint32_t bar_num = static_cast<uint32_t>((addr >> 60) & 0xF);
    uint64_t offset = addr & 0x0FFFFFFFFFFFFFFFULL; // Lower 60 bits
    
    // Handle different sizes
    if (size == 1) {
        uint8_t value;
        bool success = mmioRead8(bar_num, offset, value);
        if (success) buf[0] = static_cast<char>(value);
        return success;
    } else if (size == 2) {
        uint16_t value;
        bool success = mmioRead16(bar_num, offset, value);
        if (success) *reinterpret_cast<uint16_t*>(buf) = value;
        return success;
    } else if (size == 4) {
        uint32_t value;
        bool success = mmioRead32(bar_num, offset, value);
        if (success) *reinterpret_cast<uint32_t*>(buf) = value;
        return success;
    } else if (size == 8) {
        uint64_t value;
        bool success = mmioRead64(bar_num, offset, value);
        if (success) *reinterpret_cast<uint64_t*>(buf) = value;
        return success;
    } else {
        // For arbitrary sizes, read byte by byte
        for (size_t i = 0; i < size; ++i) {
            uint8_t value;
            if (!mmioRead8(bar_num, offset + i, value)) {
                return false;
            }
            buf[i] = static_cast<char>(value);
        }
        return true;
    }
}

// ==================== DMA Operations ====================

// Standard interface matching shell.hpp
bool VP815::dmaWrite(uint64_t addr, size_t size, char* buf) {
    uint32_t channel = pImpl->getNextChannel();
    return pImpl->dmaTransfer(buf, addr, size, channel, 5000, true);
}

bool VP815::dmaRead(uint64_t addr, size_t size, char* buf) {
    uint32_t channel = pImpl->getNextChannel();
    return pImpl->dmaTransfer(buf, addr, size, channel, 5000, false);
}

// Extended interface with timeout
bool VP815::dmaWrite(uint64_t addr, size_t size, char* buf, uint32_t timeout_ms) {
    uint32_t channel = pImpl->getNextChannel();
    return pImpl->dmaTransfer(buf, addr, size, channel, timeout_ms, true);
}

bool VP815::dmaRead(uint64_t addr, size_t size, char* buf, uint32_t timeout_ms) {
    uint32_t channel = pImpl->getNextChannel();
    return pImpl->dmaTransfer(buf, addr, size, channel, timeout_ms, false);
}

bool VP815::dmaWriteChannel(uint64_t addr, size_t size, char* buf, uint32_t channel, 
                            uint32_t timeout_ms) {
    if (channel >= pImpl->num_dma_channels) {
        return false;  // Invalid channel
    }
    return pImpl->dmaTransfer(buf, addr, size, channel, timeout_ms, true);
}

bool VP815::dmaReadChannel(uint64_t addr, size_t size, char* buf, uint32_t channel,
                           uint32_t timeout_ms) {
    if (channel >= pImpl->num_dma_channels) {
        return false;  // Invalid channel
    }
    return pImpl->dmaTransfer(buf, addr, size, channel, timeout_ms, false);
}

void* VP815::allocateDmaBuffer(size_t size_bytes) {
    if (!pImpl->initialized) return nullptr;
    
    // Validate buffer size against DMA engine limitations
    if (size_bytes == 0 || size_bytes > DMA_BUFFER_MAX_SIZE) {
        std::cerr << "DMA buffer allocation size " << size_bytes 
                  << " bytes exceeds maximum allowed size of " 
                  << DMA_BUFFER_MAX_SIZE << " bytes (4MB)" << std::endl;
        return nullptr;
    }

    ACX_DMA_buffer* dma_buf = acx_dma_alloc_buf(pImpl->pcie_device, size_bytes);
    if (!dma_buf || !dma_buf->virt_addr) {
        return nullptr;
    }

    // Track the buffer
    {
        std::lock_guard<std::mutex> lock(pImpl->dma_buffers_mutex);
        pImpl->dma_buffers[dma_buf->virt_addr] = dma_buf;
    }

    return dma_buf->virt_addr;
}

void VP815::freeDmaBuffer(void* buffer) {
    if (!buffer || !pImpl->initialized) return;

    std::lock_guard<std::mutex> lock(pImpl->dma_buffers_mutex);
    auto it = pImpl->dma_buffers.find(buffer);
    if (it != pImpl->dma_buffers.end()) {
        acx_dma_free_buf(it->second);
        pImpl->dma_buffers.erase(it);
    }
}

uint64_t VP815::getDmaPhysicalAddress(void* buffer) {
    if (!buffer || !pImpl->initialized) return 0;

    std::lock_guard<std::mutex> lock(pImpl->dma_buffers_mutex);
    auto it = pImpl->dma_buffers.find(buffer);
    if (it != pImpl->dma_buffers.end() && it->second->dma_addr) {
        return reinterpret_cast<uint64_t>(it->second->dma_addr);
    }
    return 0;
}

uint32_t VP815::getDmaChannelCount() const {
    return pImpl->num_dma_channels;
}

// ==================== MMIO Operations ====================

bool VP815::mmioRead8(uint32_t bar_num, uint64_t offset, uint8_t& value) {
    if (!pImpl->initialized) return false;
    return acx_mmio_read_bar_8(pImpl->pcie_device, bar_num, offset, &value) == ACX_SDK_STATUS_OK;
}

bool VP815::mmioRead16(uint32_t bar_num, uint64_t offset, uint16_t& value) {
    if (!pImpl->initialized) return false;
    return acx_mmio_read_bar_16(pImpl->pcie_device, bar_num, offset, &value) == ACX_SDK_STATUS_OK;
}

bool VP815::mmioRead32(uint32_t bar_num, uint64_t offset, uint32_t& value) {
    if (!pImpl->initialized) return false;
    return acx_mmio_read_bar_32(pImpl->pcie_device, bar_num, offset, &value) == ACX_SDK_STATUS_OK;
}

bool VP815::mmioRead64(uint32_t bar_num, uint64_t offset, uint64_t& value) {
    if (!pImpl->initialized) return false;
    return acx_mmio_read_bar_64(pImpl->pcie_device, bar_num, offset, &value) == ACX_SDK_STATUS_OK;
}

bool VP815::mmioWrite8(uint32_t bar_num, uint64_t offset, uint8_t value) {
    if (!pImpl->initialized) return false;
    return acx_mmio_write_bar_8(pImpl->pcie_device, bar_num, offset, value) == ACX_SDK_STATUS_OK;
}

bool VP815::mmioWrite16(uint32_t bar_num, uint64_t offset, uint16_t value) {
    if (!pImpl->initialized) return false;
    return acx_mmio_write_bar_16(pImpl->pcie_device, bar_num, offset, value) == ACX_SDK_STATUS_OK;
}

bool VP815::mmioWrite32(uint32_t bar_num, uint64_t offset, uint32_t value) {
    if (!pImpl->initialized) return false;
    return acx_mmio_write_bar_32(pImpl->pcie_device, bar_num, offset, value) == ACX_SDK_STATUS_OK;
}

bool VP815::mmioWrite64(uint32_t bar_num, uint64_t offset, uint64_t value) {
    if (!pImpl->initialized) return false;
    return acx_mmio_write_bar_64(pImpl->pcie_device, bar_num, offset, value) == ACX_SDK_STATUS_OK;
}

// Convenience overloads that throw on error
uint8_t VP815::mmioRead8(uint32_t bar_num, uint64_t offset) {
    uint8_t value;
    if (!mmioRead8(bar_num, offset, value)) {
        throw VP815Exception("MMIO read8 failed");
    }
    return value;
}

uint16_t VP815::mmioRead16(uint32_t bar_num, uint64_t offset) {
    uint16_t value;
    if (!mmioRead16(bar_num, offset, value)) {
        throw VP815Exception("MMIO read16 failed");
    }
    return value;
}

uint32_t VP815::mmioRead32(uint32_t bar_num, uint64_t offset) {
    uint32_t value;
    if (!mmioRead32(bar_num, offset, value)) {
        throw VP815Exception("MMIO read32 failed");
    }
    return value;
}

uint64_t VP815::mmioRead64(uint32_t bar_num, uint64_t offset) {
    uint64_t value;
    if (!mmioRead64(bar_num, offset, value)) {
        throw VP815Exception("MMIO read64 failed");
    }
    return value;
}

// ==================== Interrupt Operations ====================

bool VP815::waitForInterrupt(uint32_t vector_id, uint32_t timeout_ms) {
    if (!pImpl->initialized) return false;
    return acx_msix_interrupt_wait(pImpl->pcie_device, vector_id, timeout_ms) == ACX_SDK_STATUS_OK;
}

void VP815::cancelInterruptWait(uint32_t vector_id) {
    if (pImpl->initialized) {
        acx_msix_cancel_wait(pImpl->pcie_device, vector_id);
    }
}

bool VP815::triggerInterrupt(uint32_t vector_id) {
    if (!pImpl->initialized) return false;
    return acx_msix_interrupt(pImpl->pcie_device, vector_id) == ACX_SDK_STATUS_OK;
}

bool VP815::isMsixEnabled() const {
    if (!pImpl->initialized) return false;
    return acx_msix_is_enabled(pImpl->pcie_device) == ACX_SDK_STATUS_ENABLE;
}

uint32_t VP815::getMsixVectorCount() const {
    if (!pImpl->initialized) return 0;
    uint32_t table_size = 0;
    if (acx_msix_get_table_size(pImpl->pcie_device, &table_size) == ACX_SDK_STATUS_OK) {
        return table_size;
    }
    return 0;
}

// ==================== Device Interface Implementation (Callback-based Interrupts) ====================

bool VP815::hasInterrupts() const {
    return isMsixEnabled() && getMsixVectorCount() > 0;
}

uint32_t VP815::getInterruptVectorCount() const {
    return getMsixVectorCount();
}

bool VP815::registerInterruptHandler(uint32_t vector_id, InterruptHandler handler) {
    if (!pImpl->initialized || !hasInterrupts()) {
        std::cerr << "[VP815] Cannot register interrupt handler: device not ready or MSI-X not available" << std::endl;
        return false;
    }
    
    if (vector_id >= getInterruptVectorCount()) {
        std::cerr << "[VP815] Invalid vector ID " << vector_id << " (max: " << getInterruptVectorCount()-1 << ")" << std::endl;
        return false;
    }
    
    std::lock_guard<std::mutex> lock(pImpl->interrupt_mutex);
    
    // Initialize interrupt system if not running
    if (!pImpl->interrupt_system_running) {
        pImpl->interrupt_system_running = true;
    }
    
    // Stop existing thread for this vector if any
    if (pImpl->interrupt_threads.find(vector_id) != pImpl->interrupt_threads.end()) {
        pImpl->thread_stop_flags[vector_id].store(true);
        if (pImpl->interrupt_threads[vector_id].joinable()) {
            pImpl->interrupt_threads[vector_id].join();
        }
    }
    
    // Register the handler
    pImpl->interrupt_handlers[vector_id] = handler;
    pImpl->interrupt_enabled[vector_id] = true;
    pImpl->thread_stop_flags[vector_id].store(false);
    
    // Start new worker thread for this vector
    pImpl->interrupt_threads[vector_id] = std::thread(&VP815::interruptWorkerThread, this, vector_id);
    
    std::cout << "[VP815] Registered interrupt handler for vector " << vector_id << std::endl;
    return true;
}

bool VP815::unregisterInterruptHandler(uint32_t vector_id) {
    if (!pImpl->initialized) return false;
    
    std::lock_guard<std::mutex> lock(pImpl->interrupt_mutex);
    
    // Stop thread for this vector
    if (pImpl->thread_stop_flags.find(vector_id) != pImpl->thread_stop_flags.end()) {
        pImpl->thread_stop_flags[vector_id].store(true);
    }
    
    if (pImpl->interrupt_threads.find(vector_id) != pImpl->interrupt_threads.end()) {
        if (pImpl->interrupt_threads[vector_id].joinable()) {
            pImpl->interrupt_threads[vector_id].join();
        }
        pImpl->interrupt_threads.erase(vector_id);
    }
    
    // Remove handler and settings
    pImpl->interrupt_handlers.erase(vector_id);
    pImpl->interrupt_enabled.erase(vector_id);
    pImpl->thread_stop_flags.erase(vector_id);
    
    std::cout << "[VP815] Unregistered interrupt handler for vector " << vector_id << std::endl;
    return true;
}

bool VP815::startInterruptHandling() {
    if (!pImpl->initialized) return false;
    
    std::lock_guard<std::mutex> lock(pImpl->interrupt_mutex);
    if (!pImpl->interrupt_system_running) {
        pImpl->interrupt_system_running = true;
        std::cout << "[VP815] Interrupt handling system started" << std::endl;
    }
    return true;
}

void VP815::stopInterruptHandling() {
    if (!pImpl->initialized) return;
    
    pImpl->stopInterruptSystem();
    std::cout << "[VP815] Interrupt handling system stopped" << std::endl;
}

bool VP815::enableInterrupts() {
    if (!pImpl->initialized) return false;
    
    std::lock_guard<std::mutex> lock(pImpl->interrupt_mutex);
    uint32_t vector_count = getInterruptVectorCount();
    for (uint32_t i = 0; i < vector_count; i++) {
        pImpl->interrupt_enabled[i] = true;
    }
    std::cout << "[VP815] All interrupts enabled (" << vector_count << " vectors)" << std::endl;
    return true;
}

bool VP815::disableInterrupts() {
    if (!pImpl->initialized) return false;
    
    std::lock_guard<std::mutex> lock(pImpl->interrupt_mutex);
    uint32_t vector_count = getInterruptVectorCount();
    for (uint32_t i = 0; i < vector_count; i++) {
        pImpl->interrupt_enabled[i] = false;
    }
    std::cout << "[VP815] All interrupts disabled (" << vector_count << " vectors)" << std::endl;
    return true;
}

// ==================== Extended VP815-specific Interrupt Operations ====================

bool VP815::enableInterruptVector(uint32_t vector_id) {
    if (!pImpl->initialized || vector_id >= getInterruptVectorCount()) return false;
    
    std::lock_guard<std::mutex> lock(pImpl->interrupt_mutex);
    pImpl->interrupt_enabled[vector_id] = true;
    return true;
}

bool VP815::disableInterruptVector(uint32_t vector_id) {
    if (!pImpl->initialized || vector_id >= getInterruptVectorCount()) return false;
    
    std::lock_guard<std::mutex> lock(pImpl->interrupt_mutex);
    pImpl->interrupt_enabled[vector_id] = false;
    return true;
}

bool VP815::isInterruptVectorEnabled(uint32_t vector_id) const {
    if (!pImpl->initialized || vector_id >= getInterruptVectorCount()) return false;
    
    std::lock_guard<std::mutex> lock(pImpl->interrupt_mutex);
    auto it = pImpl->interrupt_enabled.find(vector_id);
    return it != pImpl->interrupt_enabled.end() && it->second;
}

// ==================== Private Interrupt Thread Management ====================

void VP815::interruptWorkerThread(uint32_t vector_id) {
    std::cout << "[VP815] Starting interrupt worker thread for vector " << vector_id << std::endl;
    
    while (!pImpl->thread_stop_flags[vector_id].load()) {
        // Wait for interrupt with reasonable timeout
        bool interrupt_received = waitForInterrupt(vector_id, 1000); // 1 second timeout
        
        if (interrupt_received) {
            // Check if handler is still enabled and registered
            Device::InterruptHandler handler;
            bool should_execute = false;
            
            {
                std::lock_guard<std::mutex> lock(pImpl->interrupt_mutex);
                if (pImpl->interrupt_enabled[vector_id] && 
                    pImpl->interrupt_handlers.find(vector_id) != pImpl->interrupt_handlers.end()) {
                    
                    std::cout << "[VP815] Executing callback for vector " << vector_id << std::endl;
                    handler = pImpl->interrupt_handlers[vector_id];
                    should_execute = true;
                }
            } // Mutex automatically unlocked here
            
            if (should_execute) {
                try {
                    handler(vector_id);
                } catch (const std::exception& e) {
                    std::cerr << "[VP815] Exception in interrupt handler for vector " << vector_id 
                              << ": " << e.what() << std::endl;
                } catch (...) {
                    std::cerr << "[VP815] Unknown exception in interrupt handler for vector " << vector_id << std::endl;
                }
            }
        }
        // Continue loop (timeout or interrupt, both are normal)
    }
    
    std::cout << "[VP815] Stopping interrupt worker thread for vector " << vector_id << std::endl;
}

// ==================== DBI Operations ====================

bool VP815::dbiRead(uint64_t reg_addr, uint32_t& value) {
    if (!pImpl->initialized) return false;
    return acx_mmio_read_dbi(pImpl->pcie_device, reg_addr, &value) == ACX_SDK_STATUS_OK;
}

bool VP815::dbiWrite(uint64_t reg_addr, uint32_t value) {
    if (!pImpl->initialized) return false;
    return acx_mmio_write_dbi(pImpl->pcie_device, reg_addr, value) == ACX_SDK_STATUS_OK;
}

// ==================== Utility Functions ====================

uint64_t VP815::getBarSize(uint32_t bar_num) const {
    if (!pImpl->initialized || bar_num >= 6) return 0;
    return pImpl->bar_sizes[bar_num];
}

bool VP815::isPcieLinkUp() const {
    if (!pImpl->initialized) return false;
    return acx_util_pci_link_is_up(pImpl->pcie_device) == ACX_SDK_STATUS_OK;
}

std::string VP815::getPartName() const {
    if (!pImpl->initialized) return "Unknown";
    return pImpl->part_name_str;
}

} // namespace achronix 