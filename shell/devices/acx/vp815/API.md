# Achronix SDK API Reference

This document provides a comprehensive reference for the Achronix Software Development Kit (SDK) APIs and constants.

## Table of Contents

- [Core Data Types](#core-data-types)
- [Device Management](#device-management)
- [Memory-Mapped I/O (MMIO)](#memory-mapped-io-mmio)
- [Direct Memory Access (DMA)](#direct-memory-access-dma)
- [MSI-X Interrupts](#msi-x-interrupts)
- [Address Translation Unit (ATU)](#address-translation-unit-atu)
- [IP Block Management](#ip-block-management)
- [Bitstream Programming](#bitstream-programming)
- [Utility Functions](#utility-functions)
- [Logging Macros](#logging-macros)
- [Status Codes](#status-codes)
- [Version Information](#version-information)

## Core Data Types

### Constants

#### Memory Address Spaces
```c
#define ACX_GDDR6_SPACE  (uint64_t)0x00000000000  // Base address of GDDR6 endpoint in 42-bit NoC space
#define ACX_NAP_SPACE    (uint64_t)0x04000000000  // Base address of NAP endpoints in 42-bit NoC space
#define ACX_CSR_SPACE    (uint64_t)0x08000000000  // Base address of Control Status Registers endpoint
#define ACX_FCU_SPACE    (uint64_t)0x0C000000000  // Base address of FPGA Control Unit endpoint
#define ACX_DDR4_SPACE   (uint64_t)0x10000000000  // Base address of DDR4 endpoint in 42-bit NoC space
#define ACX_NUM_BARS     6                        // Maximum number of Base Address Registers
```

#### Part Numbers
```c
typedef enum {
    ACX_PART_AC7t1500,   // AC7t1500 FPGA part
    ACX_PART_AC7t1400,   // AC7t1400 FPGA part  
    ACX_PART_AC7t800ES0, // AC7t800ES0 FPGA part
} ACX_DEV_PART_NAME;
```

#### SDK Version
```c
#define ACX_SDK_MAJOR_VERSION  2
#define ACX_SDK_MINOR_VERSION  2
#define ACX_SDK_PATCH_VERSION  0
```

## Device Management

### Device Structure
```c
typedef struct {
    ACX_PCIE_dev_handle handle;              // Low-level PCIe device handle
    uint32_t            device_id;           // Device index managed by this object
    ACX_BAR_handle      bar_handles[6];      // Array of BAR handles
    uint64_t            bar_sizes[6];        // Array of BAR sizes
    ACX_DEV_PART_NAME   part_name;           // FPGA part name
    uint32_t            function_num;        // Physical function number
    ACX_IP_block       *ip_blocks;           // Array of IP blocks
    uint32_t            num_ip_blocks;       // Number of IP blocks
    ACX_IP_block       *dbi_interface_block; // DBI interface IP block
    ACX_SDK_STATUS      status;              // Device status
} ACX_DEV_PCIe_device;
```

### Device Management APIs
```c
// Device initialization and cleanup
ACX_DEV_PCIe_device* acx_dev_init_pcie_device_idx(uint32_t device_id);
ACX_DEV_PCIe_device* acx_dev_init_pcie_device_bdf(const char *bdf);
void acx_dev_cleanup_pcie_device(ACX_DEV_PCIe_device *device);

// Device status and information
ACX_SDK_STATUS acx_dev_is_fabric_ready(ACX_DEV_PCIe_device *device);
ACX_SDK_STATUS acx_dev_get_bar_size(ACX_DEV_PCIe_device *device, uint32_t bar_id, uint64_t *size_ptr);
ACX_SDK_STATUS acx_dev_get_bar_start(ACX_DEV_PCIe_device *device, uint32_t bar_id, uint8_t host_perspective, uint64_t *start_ptr);
const char* acx_part_name_to_string(ACX_DEV_PART_NAME name);

// Low-level PCIe functions
uint32_t acx_pcie_get_num_devices();
void acx_pcie_get_sdk_version(uint32_t *major_version, uint32_t *minor_version, uint32_t *patch_version);
ACX_SDK_STATUS acx_pcie_get_device_info(ACX_PCIE_dev_handle device_hand, ACX_PCIE_device_info *info);
```

## Memory-Mapped I/O (MMIO)

### MMIO Handle Management
```c
typedef struct _ACX_MMIO_handle *ACX_MMIO_handle;

// MMIO handle operations
ACX_SDK_STATUS acx_mmio_open_hand_constant(ACX_DEV_PCIe_device *device, unsigned bar, 
                                          uint64_t offset, uint64_t length, 
                                          struct ACX_MMIO_attributes *attributes, 
                                          ACX_MMIO_handle *handle_p);
ACX_SDK_STATUS acx_mmio_close_hand(ACX_MMIO_handle handle);
ACX_SDK_STATUS acx_mmio_get_hand_counts(ACX_MMIO_handle handle, int clear, struct ACX_MMIO_counts *counts_p);
ACX_SDK_STATUS acx_mmio_set_hand_trace_mask(ACX_MMIO_handle handle, uint32_t mask);
```

### MMIO Trace Constants
```c
#define ACX_MMIO_TRACE_MANAGEMENT   (1 << 0)  // Enable tracing of MMIO management operations
#define ACX_MMIO_TRACE_COUNTS       (1 << 1)  // Enable tracing of count operations
#define ACX_MMIO_TRACE_WRITES       (1 << 2)  // Enable tracing of write operations
#define ACX_MMIO_TRACE_READS        (1 << 3)  // Enable tracing of read operations
```

### MMIO Read/Write APIs
```c
// Handle-based MMIO operations
ACX_SDK_STATUS acx_mmio_write_uint8(ACX_MMIO_handle handle, uint64_t offset, uint8_t value);
ACX_SDK_STATUS acx_mmio_write_uint16(ACX_MMIO_handle handle, uint64_t offset, uint16_t value);
ACX_SDK_STATUS acx_mmio_write_uint32(ACX_MMIO_handle handle, uint64_t offset, uint32_t value);
ACX_SDK_STATUS acx_mmio_write_uint64(ACX_MMIO_handle handle, uint64_t offset, uint64_t value);
ACX_SDK_STATUS acx_mmio_read_uint8(ACX_MMIO_handle handle, uint64_t offset, uint8_t *value_p);
ACX_SDK_STATUS acx_mmio_read_uint16(ACX_MMIO_handle handle, uint64_t offset, uint16_t *value_p);
ACX_SDK_STATUS acx_mmio_read_uint32(ACX_MMIO_handle handle, uint64_t offset, uint32_t *value_p);
ACX_SDK_STATUS acx_mmio_read_uint64(ACX_MMIO_handle handle, uint64_t offset, uint64_t *value_p);

// Direct BAR operations
ACX_SDK_STATUS acx_mmio_write_bar_8(ACX_DEV_PCIe_device *device, uint32_t bar_num, uint32_t bar_offset, uint8_t value);
ACX_SDK_STATUS acx_mmio_write_bar_16(ACX_DEV_PCIe_device *device, uint32_t bar_num, uint32_t bar_offset, uint16_t value);
ACX_SDK_STATUS acx_mmio_write_bar_32(ACX_DEV_PCIe_device *device, uint32_t bar_num, uint32_t bar_offset, uint32_t value);
ACX_SDK_STATUS acx_mmio_write_bar_64(ACX_DEV_PCIe_device *device, uint32_t bar_num, uint32_t bar_offset, uint64_t value);
ACX_SDK_STATUS acx_mmio_read_bar_8(ACX_DEV_PCIe_device *device, uint32_t bar_num, uint32_t bar_offset, uint8_t *value);
ACX_SDK_STATUS acx_mmio_read_bar_16(ACX_DEV_PCIe_device *device, uint32_t bar_num, uint32_t bar_offset, uint16_t *value);
ACX_SDK_STATUS acx_mmio_read_bar_32(ACX_DEV_PCIe_device *device, uint32_t bar_num, uint32_t bar_offset, uint32_t *value);
ACX_SDK_STATUS acx_mmio_read_bar_64(ACX_DEV_PCIe_device *device, uint32_t bar_num, uint32_t bar_offset, uint64_t *value);

// DBI interface operations
ACX_SDK_STATUS acx_mmio_write_dbi(ACX_DEV_PCIe_device *device, uint64_t reg_addr, uint32_t value);
ACX_SDK_STATUS acx_mmio_read_dbi(ACX_DEV_PCIe_device *device, uint64_t reg_addr, uint32_t *value);
```

## Direct Memory Access (DMA)

### DMA Constants
```c
#define ACX_DMA_CHANNELS 4  // Maximum number of DMA channels
```

### DMA Enumerations
```c
typedef enum {
    ACX_DMA_HOST_TO_DEVICE,  // Transfer from host to device memory
    ACX_DMA_DEVICE_TO_HOST,  // Transfer from device to host memory
} ACX_DMA_DIRECTION;

typedef enum {
    ACX_DMA_XFER_UNDEFINED,  // Undefined status
    ACX_DMA_XFER_RESERVED,   // Channel configured but not started
    ACX_DMA_XFER_RUNNING,    // Channel actively transferring data
    ACX_DMA_XFER_HALTED,     // Error condition detected, DMA stopped
    ACX_DMA_XFER_STOPPED,    // DMA completed or manually stopped
    ACX_DMA_XFER_COMPLETE,   // Transfer complete with size verification
    ACX_DMA_XFER_ERROR,      // Error occurred, transfer state unknown
} ACX_DMA_TRANSFER_STATUS;

typedef enum {
    ACX_DMA_TACTN_UNDEFINED,  // Transaction not configured
    ACX_DMA_TACTN_BUFFER,     // Single buffer transaction
    ACX_DMA_TACTN_LIST,       // Linked-list transaction
} ACX_DMA_TACTN_MODE;
```

### DMA Data Structures
```c
typedef struct {
    ACX_DEV_PCIe_device *device;        // Device that owns this buffer
    ACX_DMA_buffer_handle buffer_handle; // Driver-agnostic buffer handle
    uint64_t size_in_bytes;              // Buffer size
    void *data;                          // Virtual address for host access
    void *dma_addr;                      // Physical address for DMA engine
} ACX_DMA_buffer;

typedef struct {
    ACX_DEV_PCIe_device *device;
    uint32_t dma_engine_controller_id;
    ACX_SDK_STATUS status;
} ACX_DMA_engine_context;

typedef struct {
    uint32_t channel;            // DMA channel index
    ACX_DMA_DIRECTION direction; // Transfer direction
    uint64_t device_address;     // Device memory address
    uint64_t buffer_offset;      // Host buffer offset
    uint64_t byte_count;         // Number of bytes to transfer
    ACX_DMA_TACTN_MODE mode;     // Transaction mode
    union {
        ACX_DMA_buffer *dma_buffer;  // For single-buffer mode
        struct {
            ACX_DMA_list_node *list_node;
            ACX_DMA_LIST_STATE list_xfer_state;
        };
    };
    ACX_DMA_engine_context *engine_cntx;
    ACX_DMA_TRANSFER_STATUS status;
} ACX_DMA_transaction;
```

### DMA APIs
```c
// Engine and context management
ACX_SDK_STATUS acx_dma_build_engine_cntx(ACX_DMA_engine_context *engine_cntx, ACX_DEV_PCIe_device *device, uint32_t dma_engine_controller_id);
ACX_SDK_STATUS acx_dma_init_engine_cntx(ACX_DMA_engine_context *engine_cntx);
ACX_SDK_STATUS acx_dma_get_xfer_cntx_tatcn(ACX_DMA_xfer_context *transfer_cntx, ACX_DMA_transaction *transaction);

// High-level transfer functions
ACX_SDK_STATUS acx_dma_start_xfer_h2d(void *buffer, uint32_t size_in_bytes, uint64_t device_address, 
                                     uint32_t channel, ACX_DMA_engine_context *engine_cntx, 
                                     ACX_DMA_transaction **transaction);
ACX_SDK_STATUS acx_dma_start_xfer_d2h(uint32_t size_in_bytes, uint64_t device_address, uint32_t channel, 
                                     ACX_DMA_engine_context *engine_cntx, 
                                     ACX_DMA_transaction **transaction);

// Transfer control
ACX_SDK_STATUS acx_dma_config_xfer(ACX_DMA_transaction *dma_transaction);
ACX_SDK_STATUS acx_dma_start_xfer(ACX_DMA_transaction *dma_transaction);
ACX_SDK_STATUS acx_dma_halt_tactn(ACX_DMA_transaction *dma_transaction);
ACX_DMA_TRANSFER_STATUS acx_dma_wait(ACX_DMA_transaction *dma_transaction, uint32_t timeout_in_ms);
ACX_DMA_TRANSFER_STATUS acx_dma_update_status(ACX_DMA_transaction *dma_transaction);

// Memory management
ACX_DMA_buffer* acx_dma_alloc_buf(ACX_DEV_PCIe_device *device, uint64_t size_in_bytes);
void acx_dma_free_buf(ACX_DMA_buffer *buffer);
ACX_SDK_STATUS acx_dma_memset_buf(ACX_DMA_buffer *buffer, uint8_t value);

// Transaction management
ACX_DMA_transaction* acx_dma_alloc_tactn(ACX_DMA_engine_context *engine_cntx);
void acx_dma_cleanup_tactn(ACX_DMA_transaction *transaction);
ACX_SDK_STATUS acx_dma_build_buf_tactn(ACX_DMA_transaction *transaction, ACX_DMA_buffer *buffer, uint8_t channel,
                                      ACX_DMA_DIRECTION direction, uint64_t device_address, uint64_t buffer_offset, 
                                      uint64_t byte_count);

// String conversion utilities
const char* acx_dma_direction_to_string(ACX_DMA_DIRECTION direction);
const char* acx_dma_xfer_status_to_string(ACX_DMA_TRANSFER_STATUS status);
const char* acx_dma_tactn_mode_to_string(ACX_DMA_TACTN_MODE mode);
```

## MSI-X Interrupts

### MSI-X Constants
```c
#define ACX_MSIX_BAR_IDX 2  // BAR used for MSI-X vector table and pending bits
```

### MSI-X Data Structures
```c
typedef union {
    uint32_t value;
    struct {
        uint32_t RESERVED0       : 16;
        uint32_t TABLE_SIZE      : 11; // Size of MSI-X vector table
        uint32_t RESERVED1       : 3;
        uint32_t FUNCTION_MASK   : 1;  // MSI-X function mask bit
        uint32_t PCI_MSIX_ENABLE : 1;  // MSI-X enable bit
    };
} ACX_MSIX_cap_id_next_ctrl_reg;

typedef union {
    uint32_t value;
    struct {
        uint32_t VECTOR    : 11; // MSI-X doorbell vector
        uint32_t RESERVED0 : 1;
        uint32_t TC        : 3;  // Traffic class
        uint32_t VF_ACTIVE : 1;  // Virtual function active
        uint32_t VF        : 8;  // Virtual function number
        uint32_t PF        : 5;  // Physical function number
        uint32_t RESERVED1 : 3;
    };
} ACX_MSIX_doorbell_reg;

typedef struct {
    ACX_MSIX_cap_id_next_ctrl_reg  msix_cap_id_next_ctrl_reg;
    ACX_MSIX_table_offset_reg      msix_table_offset_reg;
    ACX_MSIX_pba_offset_reg        msix_pba_offset_reg;
    ACX_MSIX_address_match_low_reg msix_address_match_low;
    uint32_t                       msix_address_match_high;
    ACX_MSIX_doorbell_reg          msix_doorbell;
    ACX_MSIX_ram_ctrl_reg          msix_ram_ctrl;
} ACX_MSIX_context;
```

### MSI-X APIs
```c
// Context and status
ACX_SDK_STATUS acx_msix_get_context(ACX_DEV_PCIe_device *device, ACX_MSIX_context *context);
ACX_SDK_STATUS acx_msix_is_enabled(ACX_DEV_PCIe_device *device);
ACX_SDK_STATUS acx_msix_get_table_size(ACX_DEV_PCIe_device *device, uint32_t *table_size);

// Vector management
ACX_SDK_STATUS acx_msix_get_vector(ACX_DEV_PCIe_device *device, uint32_t index, uint64_t *message_address, uint32_t *message_data, uint32_t *mask_bit);
ACX_SDK_STATUS acx_msix_get_pending_bit(ACX_DEV_PCIe_device *device, uint32_t index, uint32_t *pending_bit);
ACX_SDK_STATUS acx_msix_set_function_mask(ACX_DEV_PCIe_device *device, uint32_t value);
ACX_SDK_STATUS acx_msix_set_vector_mask(ACX_DEV_PCIe_device *device, uint32_t index, uint32_t value);

// Interrupt operations
ACX_SDK_STATUS acx_msix_interrupt(ACX_DEV_PCIe_device *device, uint32_t message_id);
ACX_SDK_STATUS acx_msix_interrupt_wait(ACX_DEV_PCIe_device *device, uint32_t message_id, uint32_t timeout_ms);
void acx_msix_cancel_wait(ACX_DEV_PCIe_device *device, uint32_t message_id);

// Debug functions
void acx_msix_print_context(ACX_MSIX_context *context);
void acx_msix_print_vectors(ACX_DEV_PCIe_device *device);
void acx_msix_print_pending_bits(ACX_DEV_PCIe_device *device);
```

## Address Translation Unit (ATU)

### ATU Constants
```c
#define ACX_NUM_ATU_REGIONS 100  // Total number of ATU regions available
```

### ATU Enumerations
```c
typedef enum {
    ACX_ATU_MODE_BAR_MATCH,     // BAR match mode
    ACX_ATU_MODE_ADDRESS_MATCH, // Address match mode
    ACX_ATU_MODE_NONE,          // No mode set
    ACX_ATU_MODE_NUM_MODES,
} ACX_ATU_MODE;
```

### ATU Data Structures
```c
typedef struct {
    int region_num;
    union _U_iatu_region_ctrl_1_inbound iatu_region_ctrl_1_inbound;
    union _U_iatu_region_ctrl_2_inbound iatu_region_ctrl_2_inbound;
    uint32_t iatu_region_ctrl_3_inbound;
    uint32_t iatu_lwr_base_addr_inbound;
    uint32_t iatu_upper_base_addr_inbound;
    uint32_t iatu_lwr_limit_addr_inbound;
    uint32_t iatu_upper_limit_addr_inbound;
    uint32_t iatu_lwr_target_addr_inbound;
    uint32_t iatu_upper_target_addr_inbound;
} ACX_ATU_region_context;

typedef struct {
    ACX_ATU_region_context regions[ACX_NUM_ATU_REGIONS];
} ACX_ATU_context;
```

### ATU APIs
```c
// Context management
ACX_SDK_STATUS acx_atu_get_context(ACX_DEV_PCIe_device *device, ACX_ATU_context *context);
ACX_SDK_STATUS acx_atu_get_region_context(ACX_DEV_PCIe_device *device, int region_num, ACX_ATU_region_context *context);
ACX_SDK_STATUS acx_atu_config_region(ACX_DEV_PCIe_device *device, ACX_ATU_region_context *context);

// Region property getters
int acx_atu_get_region_num(ACX_ATU_region_context *atu_region);
uint64_t acx_atu_get_base_addr(ACX_ATU_region_context *atu_region);
uint64_t acx_atu_get_limit_addr(ACX_ATU_region_context *atu_region);
uint64_t acx_atu_get_target_addr(ACX_ATU_region_context *atu_region);
ACX_SDK_STATUS acx_atu_get_enable(ACX_ATU_region_context *atu_region);
ACX_ATU_MODE acx_atu_get_mode(ACX_ATU_region_context *atu_region);
uint32_t acx_atu_get_bar_num(ACX_ATU_region_context *atu_region);
uint32_t acx_atu_get_function_num(ACX_ATU_region_context *atu_region);

// Region property setters
void acx_atu_set_region_num(ACX_ATU_region_context *atu_region, int region_num);
void acx_atu_set_base_addr(ACX_ATU_region_context *atu_region, uint64_t base_addr);
void acx_atu_set_limit_addr(ACX_ATU_region_context *atu_region, uint64_t limit_addr);
void acx_atu_set_target_addr(ACX_ATU_region_context *atu_region, uint64_t target_addr);
void acx_atu_set_enable(ACX_ATU_region_context *atu_region, ACX_SDK_STATUS enable);
void acx_atu_set_mode(ACX_ATU_region_context *atu_region, ACX_ATU_MODE mode);
void acx_atu_set_bar_num(ACX_ATU_region_context *atu_region, uint32_t bar_num);
void acx_atu_set_function_num(ACX_ATU_region_context *atu_region, uint32_t func_num);

// Region discovery
int acx_atu_find_bar_regions(ACX_DEV_PCIe_device *device, uint32_t bar_num, 
                             uint32_t num_buf_elements, ACX_ATU_region_context *regions);
int acx_atu_find_function_regions(ACX_DEV_PCIe_device *device, uint32_t function_num, 
                                  uint32_t num_buf_elements, ACX_ATU_region_context *regions);

// Utility functions
const char* acx_atu_mode_to_string(ACX_ATU_MODE mode);
void acx_atu_print_region(ACX_ATU_region_context *context);
void acx_atu_print_context(ACX_ATU_context *context, uint8_t print_disabled_regions);
```

## IP Block Management

### IP Block Data Structures
```c
typedef struct {
    ACX_BAR_handle bar_handle;  // BAR handle for accessing this IP block
    uint32_t bar_offset;        // Beginning offset address within BAR
    uint32_t bar_limit;         // Ending offset address within BAR
    struct {
        uint8_t initialized : 1; // Block successfully initialized
        uint8_t enabled     : 1; // Block enabled by programmer
        uint8_t status      : 6; // 6-bit application-specific status
    };
    char *tag;     // Unique string identifier for this IP block
    void *details; // Implementation-specific details
} ACX_IP_block;

// Function pointer types
typedef uint32_t (*ACX_IP_initializer)(ACX_DEV_PCIe_device *device, ACX_IP_block *ip_block, void *details);
typedef void (*ACX_IP_cleaner)(ACX_DEV_PCIe_device *device, ACX_IP_block *ip_block);
```

### IP Block Management APIs
```c
// Registration functions
ACX_SDK_STATUS acx_ip_register_initializer(ACX_IP_initializer initializer_function, char *block_tag);
ACX_SDK_STATUS acx_ip_register_cleaner(ACX_IP_cleaner cleaner_function, char *block_tag);
ACX_SDK_STATUS acx_ip_remove_initializer(char *block_tag);
ACX_SDK_STATUS acx_ip_remove_cleaner(char *block_tag);

// Execution functions
ACX_SDK_STATUS acx_ip_initialize_ips(ACX_DEV_PCIe_device *device, void *details);
void acx_ip_cleanup_ips(ACX_DEV_PCIe_device *device);
```

## Bitstream Programming

### Bitstream Programming Enumerations
```c
typedef enum {
    ACX_PBS_STATUS_SUCCESS,            // Bitstream programmed successfully
    ACX_PBS_STATUS_PCI_ERROR,          // PCIe link error
    ACX_PBS_STATUS_FILE_ERROR,         // Could not open bitstream file
    ACX_PBS_STATUS_BUFFER_ALLOC_ERROR, // Buffer allocation failed
    ACX_PBS_STATUS_DBI_READ_ERROR,     // DBI access error
    ACX_PBS_STATUS_RUN_DMA_ERROR,      // DMA transfer error
    ACX_PBS_STATUS_PROGRAM_FAIL,       // Programming failed or timeout
} ACX_PBS_STATUS;
```

### Bitstream Programming APIs
```c
ACX_PBS_STATUS acx_pbs_program_bitstream(ACX_DEV_PCIe_device *device, const char *pciefilename, uint8_t encrypted);
```

## Utility Functions

### Time and Delay Functions
```c
void acx_util_wait_seconds(long num_seconds);
void acx_util_wait_milliseconds(long num_milliseconds);
void acx_util_wait_microseconds(long num_microseconds);
void acx_util_clock_gettime(timespec *time);
double acx_util_to_sec(timespec *time);
void acx_util_ms_to_timespec(uint32_t m_secs, timespec *time);
int acx_util_time_comp(timespec *time0, timespec *time1);
void acx_util_add_timespec(timespec *time0, timespec *time1, timespec *res);
void acx_util_sub_timespec(timespec *time0, timespec *time1, timespec *res);
```

### Hardware Utility Functions
```c
uint64_t acx_util_nap_absolute_addr(ACX_DEV_PART_NAME part, int col, int row);
ACX_SDK_STATUS acx_util_pci_link_is_up(ACX_DEV_PCIe_device *device);
```

### Value Swap Functions
```c
void acx_util_swap64(uint64_t *a, uint64_t *b);
void acx_util_swap32(uint32_t *a, uint32_t *b);
void acx_util_swap16(uint16_t *a, uint16_t *b);
void acx_util_swap8(uint8_t *a, uint8_t *b);
```

### Linear Map Data Structure
```c
typedef struct _ACX_util_linear_map *ACX_util_linear_map;

ACX_SDK_STATUS acx_util_linear_map_create(ACX_util_linear_map *map_ptr);
void acx_util_linear_map_free(ACX_util_linear_map map);
uint32_t acx_util_linear_map_size(ACX_util_linear_map map);
char* acx_util_linear_map_get_index_key(ACX_util_linear_map map, uint32_t index);
void* acx_util_linear_map_get_index_item(ACX_util_linear_map map, uint32_t index);
void* acx_util_linear_map_find(ACX_util_linear_map map, char *key);
ACX_SDK_STATUS acx_util_linear_map_add(ACX_util_linear_map map, char *key, void *item);
ACX_SDK_STATUS acx_util_linear_map_delete(ACX_util_linear_map map, char *key);
```

## Logging Macros

### Logging Macros
```c
#define ACX_PRINT_INFO(...)    fprintf(stdout, __VA_ARGS__)
#define ACX_PRINT_WARNING(...) fprintf(stderr, "WARNING: " __VA_ARGS__)
#define ACX_PRINT_ERROR(...)   fprintf(stderr, "ERROR: " __VA_ARGS__)
```

**Usage:** These macros can be redefined to redirect SDK logging to custom destinations such as log files or syslog.

## Status Codes

### ACX_SDK_STATUS Enumeration
```c
typedef enum {
    ACX_SDK_STATUS_UNDEFINED = 0,    // Current state is undefined
    ACX_SDK_STATUS_OK,               // Operation successful or state valid
    ACX_SDK_STATUS_INDEX_OUT_RANGE,  // Index beyond valid range
    ACX_SDK_STATUS_SIZE_OUT_RANGE,   // Size too large or too small
    ACX_SDK_STATUS_ADDR_OUT_RANGE,   // Address beyond legal range
    ACX_SDK_STATUS_CHAN_OUT_RANGE,   // Channel beyond legal range
    ACX_SDK_STATUS_ARG_NULL,         // One or more arguments was null
    ACX_SDK_STATUS_TARGET_NULL,      // Target of operation was null
    ACX_SDK_STATUS_BAD_MODE,         // Incorrect mode for requested operation
    ACX_SDK_STATUS_ALREADY_EXISTS,   // Item/data already exists
    ACX_SDK_STATUS_NOT_MAPPED,       // Target not currently mapped
    ACX_SDK_STATUS_RUNNING,          // Operation already in progress
    ACX_SDK_STATUS_BAD_STATE,        // State error/mismatch occurred
    ACX_SDK_STATUS_ERROR,            // Generic error
    ACX_SDK_STATUS_ENABLE,           // Target is enabled
    ACX_SDK_STATUS_DISABLE,          // Target is disabled
    ACX_SDK_STATUS_ALLOC_FAIL,       // Resource allocation failed
    ACX_SDK_STATUS_BAR_OPEN_FAIL,    // One or more BARs failed to open
    ACX_SDK_STATUS_ADDR_UNALIGNED,   // Unaligned MMIO operation attempt
    ACX_SDK_STATUS_INVALID_HANDLE,   // Invalid or NULL handle
    ACX_SDK_STATUS_NOT_READY,        // Target not ready or busy
    ACX_SDK_STATUS_NO_INIT,          // Target not initialized
    ACX_SDK_STATUS_NOT_SUPPORTED,    // Operation not supported
    ACX_SDK_STATUS_TIMEOUT,          // Operation timed out
    ACX_SDK_STATUS_CANCELLED,        // Operation was cancelled
    ACX_SDK_STATUS_MISSED_INTERRUPT, // Interrupt was missed
    ACX_SDK_STATUS_NUM_STATUSES,     // Number of status enums
} ACX_SDK_STATUS;
```

### Status Utility Function
```c
const char* acx_sdk_status_to_string(ACX_SDK_STATUS status);
```

## Version Information

### Version Constants
```c
#define ACX_SDK_MAJOR_VERSION  2
#define ACX_SDK_MINOR_VERSION  2  
#define ACX_SDK_PATCH_VERSION  0
```

### Version Query Function
```c
void acx_pcie_get_sdk_version(uint32_t *major_version, uint32_t *minor_version, uint32_t *patch_version);
```

---

## Notes

1. **Error Handling**: Most functions return `ACX_SDK_STATUS` to indicate success or specific error conditions.

2. **Memory Management**: DMA buffers require special allocation/deallocation using SDK functions rather than standard malloc/free.

3. **Thread Safety**: The SDK is not explicitly thread-safe. Applications should implement appropriate locking mechanisms.

4. **Driver Dependencies**: Function behavior may vary depending on the underlying PCIe driver (Achronix, BittWare DKMS, or BittWare VFIO).

5. **Alignment Requirements**: MMIO operations may require specific alignment depending on data width (8, 16, 32, or 64-bit).

6. **Resource Cleanup**: Always match device initialization with cleanup, and buffer allocation with deallocation to prevent resource leaks.