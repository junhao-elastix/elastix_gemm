# Elastix GEMM Software Test Suite

**Last Updated**: Mon Oct 20 21:02:35 PDT 2025
**Status**: ✅ **CLEANED** - Essential tests only (32+ debug tests archived)

## Overview

This streamlined software test suite validates the Elastix GEMM FPGA design with 128-register configuration, focusing on production-ready tests for MS2.0 GEMM engine validation. All debug and development tests have been archived in `obsolete_debug_tests/` (see [Archive README](obsolete_debug_tests/README.md) for details).

**Essential Test Count**: 8 core tests covering device health, memory subsystems, and GEMM operations.

## Test Architecture

### Hardware Components Tested

- **Register Control Block**: 128 user registers with MMIO access and system control
- **MS2.0 GEMM Engine**: Matrix multiplication engine on GDDR6 Channel 1
- **BRAM Responders**: Multiple instances for different DMA use cases
- **GDDR6 Memory System**: 8-channel GDDR6 with packet generation infrastructure
- **PCIe Interface**: BAR mapping, MSI-X interrupts, DMA channels
- **AXI4 Interface**: Burst transfers, NoC routing, memory data processing
- **Status Monitoring**: Real-time system status and GDDR6 training monitoring

### Essential Test Components (Production-Ready)

1. **`test_registers`** - Device health and register interface validation (128 registers)
2. **`test_gddr6`** - GDDR6 channel status and training validation (8 channels)
3. **`test_bram`** - BRAM DMA functionality validation
4. **`scan_registers`** - Register address space diagnostic (0x00-0x1FC)
5. **`test_mem_endpoints`** - Memory address space validation (BRAM + GDDR6)
6. **`DMA_simple_example`** - Basic DMA round-trip validation
7. **`DMA_example`** - Advanced DMA testing with performance metrics
8. **`test_ms2_gemm_full`** - MS2.0 GEMM engine full integration test

### Archived Tests (32+ files)

Development and debug tests have been moved to `obsolete_debug_tests/`:
- Bypass feature tests (7 files) - Feature removed in Oct 7 cleanup
- Debug utilities (10+ files) - One-time debugging tools
- Intermediate tests (10+ files) - Superseded by test_ms2_gemm_full.cpp
- Feature-specific tests (5+ files) - Now integrated into core tests

See [obsolete_debug_tests/README.md](obsolete_debug_tests/README.md) for complete archive documentation.

## Build System

### Prerequisites

- Achronix SDK with development headers
- C++14 compatible compiler (GCC recommended)
- VP815 FPGA bitstream loaded and PCIe link established

### Compilation

```bash
# Build all test binaries
make all

# Build specific tests
make test_registers
make test_mem_endpoints
make test_bram
make test_gddr6
make scan_registers
make dma_example
make dma_simple_example

# Run test execution targets
make test_basic          # Run basic register functionality test
make test_memory         # Run GDDR6 channel status test
make test_scan          # Run register address space scan
make test_all           # Run all core tests
make validate           # Quick validation (recommended after flash)

# Clean build artifacts
make clean
```

### Build Configuration

The Makefile configures:
- **Compiler**: g++ with C++14 standard
- **Optimization**: -O2 for performance testing
- **SDK Paths**: Achronix SDK include and library directories
- **Linking**: Static linking with SDK libraries

## Test Details

### 1. Register Interface Test (`test_registers`)

#### Purpose
Validates the register control interface and verifies proper MMIO operations.

#### Test Coverage
- **Register Mapping**: 128 user registers from 0x0 to 0x1FC
- **Control Register**: Bit 0 controls BRAM +42 increment processing
- **System Status**: LTSSM state, ADM status, bitstream ID, scratch register
- **Read/Write Operations**: MMIO read/write functionality
- **Register Boundaries**: Complete address space validation

#### Usage
```bash
./test_registers
```

#### Expected Output
```
✅ Device initialized successfully
📌 Bitstream ID: 0x10031121 (Build: 10/03 11:21)
Register mapping (from RTL source):
  Control Register: 0x0
  Test Status Register: 0x4
  ...
✅ Register interface is functional
```

---

### 2. Register Address Space Scanner (`scan_registers`)

#### Purpose
Comprehensive register address space scanning for the complete 128-register configuration, providing visibility into all register locations and their current values.

#### Test Coverage
- **Address Range**: 0x00 to 0x1FC (128 registers, 4-byte aligned)
- **Special Registers**: Highlights control, status, and system registers
- **Value Display**: Shows non-zero values and special register annotations
- **Error Detection**: Identifies 0xffffffff values indicating potential issues

#### Usage
```bash
./scan_registers
```

#### Expected Output
```
=== Register Address Space Scan ===
Scanning from 0x00 to 0x1FC (128 registers, step=4)

  0x0000: 0x00000000 <- Control Reg
  0x0004: 0x00000000 <- Status Reg
  0x1F0: 0x00000000 <- LTSSM State
  0x1F4: 0x00000003 <- ADM Status
  0x1F8: 0x10031121 <- Bitstream ID
  0x1FC: 0x00000000 <- Scratch Reg
```

---

### 3. Memory Address Space Scanner (`test_mem_endpoints`)

#### Purpose
Comprehensive address space scanning for both BRAM and GDDR6 memory endpoints with configurable increments and focused testing without +42 processing.

#### Test Modes
- **BRAM Mode**: Scan BRAM address space with 4KB increments
- **GDDR6 Mode**: Scan GDDR6 address space with 1MB increments  
- **Dual Mode**: Scan both BRAM and GDDR6 address spaces (default)

#### Command Line Options
```bash
--device N          # Use device N (default: 0)
--bram              # Scan BRAM address space only
--gddr6             # Scan GDDR6 address space only
--both              # Scan both BRAM and GDDR6 address spaces
-h, --help          # Show help information
```

#### Scanning Configuration
- **BRAM**: 4KB increments, 64KB max scan (16 locations)
- **GDDR6**: 1MB increments, 256MB max scan (256 locations)
- **Chunk Size**: 256 bytes per test location
- **Pattern**: Address-based unique data pattern for verification

#### Test Scenarios

##### BRAM Address Space Scanning
```bash
./test_mem_endpoints --bram
```
- **Base Address**: 0x4460008000 (BRAM responder for descriptor lists)
- **Scan Increment**: 4KB (0x1000)
- **Max Scan Size**: 64KB (0x10000)
- **Locations Tested**: 16 locations
- **Verification**: Exact byte-for-byte data matching

##### GDDR6 Address Space Scanning
```bash
./test_mem_endpoints --gddr6
```
- **Base Address**: 0x0 (GDDR6 space)
- **Scan Increment**: 1MB (0x100000)
- **Max Scan Size**: 256MB (0x10000000)
- **Locations Tested**: 256 locations
- **Address Translation**: GDDR6 address translation applied
- **Verification**: Exact byte-for-byte data matching

##### Dual Memory Scanning (Default)
```bash
./test_mem_endpoints
```
- **BRAM**: 16 locations with 4KB increments
- **GDDR6**: 256 locations with 1MB increments
- **Total Coverage**: Comprehensive address space validation
- **Verification**: Both endpoints tested independently

#### Expected Output
```
=== VP815 Memory Address Space Scanner ===
=== BRAM Address Space Scan ===
  Base Address: 0x4460008000
  Scan Increment: 0x1000 (4KB)
  Max Scan Size: 0x10000 (64KB)
  Writing 256 bytes to 0x4460008000 - Reading back - ✓ PASS
  Writing 256 bytes to 0x4460009000 - Reading back - ✓ PASS
  ...
  BRAM Scan Results: 16/16 locations passed

=== GDDR6 Address Space Scan ===
  Base Address: 0x0
  Scan Increment: 0x100000 (1MB)
  Max Scan Size: 0x10000000 (256MB)
  Location 1: 0x0 -> 0x0  Writing 256 bytes to 0x0 - Reading back - ✓ PASS
  Location 2: 0x100000 -> 0x100000  Writing 256 bytes to 0x100000 - Reading back - ✓ PASS
  ...
  GDDR6 Scan Results: 256/256 locations passed
```

### 4. BRAM DMA Testing (`test_bram`)

#### Purpose
Pure BRAM DMA testing with two focused modes: normal write/read and +42 increment processing.

#### Test Modes
- **Normal Mode**: Basic DMA write/read verification without +42 processing
- **+42 Mode**: DMA write/read with +42 increment processing on LSB only

#### Command Line Options
```bash
--device N          # Use device N (default: 0)
--inc42             # Test BRAM +42 increment
-h, --help          # Show help information
```

#### Test Scenarios

##### Normal BRAM DMA Test
```bash
./test_bram
```
- **Functionality**: Basic DMA write/read round trip
- **Data Pattern**: Sequential 32-bit word pattern
- **Verification**: Exact data match verification
- **Size**: 256 bytes test data

##### BRAM +42 Increment Test
```bash
./test_bram --inc42
```
- **Functionality**: DMA write with +42 increment processing
- **Processing**: +42 added to LSB of each 32-bit word
- **Verification**: Data integrity with +42 increment verification
- **Control**: BRAM +42 control register management

#### Expected Output
```
=== VP815 BRAM Test ===
Mode: BRAM normal write/read
Initial BRAM +42 control register: 0x0 (increment DISABLED)
Setting BRAM +42 control register: OFF (0x0)
  ✓ Control register verified: 0x0

=== BRAM DMA Round Trip ===
Writing 256 bytes to 0x4460008000
Reading  256 bytes from 0x4460008000
  ✓ Data integrity verified
  Read-back sample (32 bytes): 00 10 00 00 11 10 00 00 22 10 00 00 33 10 00 00 44 10 00 00 55 10 00 00 66 10 00 00 77 10 00 00 

Cleaning up: disabling +42 increments...
Setting BRAM +42 control register: OFF (0x0)
  ✓ Control register verified: 0x0

=== Final Result: SUCCESS ===
```

### 5. GDDR6 Channel Status Test (`test_gddr6`)

#### Purpose
Validates GDDR6 memory channel status and training completion across all 8 GDDR6 channels, providing comprehensive monitoring of memory subsystem health.

#### Test Coverage
- **ADM Status**: GDDR6 training completion status
- **Channel Status**: Individual status for all 8 GDDR6 channels
- **Performance Counters**: Read/write bandwidth and latency metrics
- **Channel Control**: Control register status for each channel

#### Usage
```bash
./test_gddr6
```

#### Expected Output
```
=== GDDR6 Memory Test ===
✅ Device initialized successfully

ADM Status: 0x0000000a ✅ GDDR6 training complete

=== GDDR6 Channel 0 Status ===
Control:    0x00000000
Status:     0x00000002 ✅ Done
Total Xact: 0
Remaining:  0

Performance Counters:
  Read BW:   0
  Write BW:  0
  Avg Lat:   0 cycles
  Max Lat:   0 cycles
  Min Lat:   0 cycles

=== GDDR6 Channel 1 Status ===
Control:    0x00000000
Status:     0x00000002 ✅ Done
...
```

### 6. Comprehensive DMA Test (`DMA_example`)

#### Purpose
Advanced DMA testing with multiple endpoints, transfer modes, and performance measurement.

#### Command Line Options
```bash
-e, --endpoint      # Endpoint type: DDR4, GDDR6, BRAM (default: GDDR6)
-d, --direction     # Transfer direction: H2D, D2H, H2D2H_SIM, H2D2H_DUP
-b, --buffer_size   # Buffer size in bytes (max: 4MB)
-l, --list          # Linked-list mode with N descriptors
-c, --channel       # DMA channel number (0-3)
-n, --num_iters     # Number of iterations
-f, --fill          # Fill pattern: random, deadbeef
```

#### Test Scenarios

##### BRAM Endpoint Testing
```bash
./dma_example --endpoint BRAM --direction H2D2H_SIM --buffer_size 0x100
```
- **Transfer Mode**: Host → Device → Host (simplex)
- **Buffer Size**: 256 bytes
- **Verification**: Data integrity check

##### Linked-list Mode Testing
```bash
./dma_example --endpoint BRAM --direction H2D2H_SIM --buffer_size 0x100 --list 4
```
- **Descriptors**: 4 linked descriptors
- **Total Size**: 1024 bytes (4 × 256)
- **Performance**: Higher bandwidth with burst transfers

##### Performance Testing
```bash
./dma_example --endpoint BRAM --num_iters 10 --buffer_size 0x1000
```
- **Iterations**: 10 test runs
- **Statistics**: Average time, bandwidth measurement
- **Reliability**: Success/failure rate analysis

#### Expected Output
```
Starting DMA from Host to Device on channel #0...
HOST_TO_DEVICE transfer of 256 (0x100) bytes in 0.017613 milliseconds 
from 0xffe3b000 to 0x43e0000000 (13.861 MB/Sec): ACX_DMA_XFER_COMPLETE

Buffer compare: PASSED
Final results: 2 of 2 iterations passed (0 dma timeouts, 0 buffer compare failures)
```

### 7. Simple DMA Test (`DMA_simple_example`)

#### Purpose
Basic DMA functionality validation with minimal complexity.

#### Test Flow
1. **Device Initialization**: PCIe device and DMA engine setup
2. **H2D Transfer**: Host buffer → Device memory (GDDR6)
3. **D2H Transfer**: Device memory → Host buffer
4. **Data Verification**: memcmp() comparison

#### Usage
```bash
./dma_simple_example [device_id|BDF]
```

#### Expected Output
```
finished engine config
started h2d transfer
h2d transfer complete
started d2h transfer
d2h transfer complete. Comparing sent and received data...
SUCCESS: sent and received data matched
```

## Hardware-Software Interface

### NAP Address Mapping

The software calculates BRAM addresses using the Achronix SDK utility:

```cpp
const uint64_t BRAM_RESP_DL_SPACE = acx_util_nap_absolute_addr(
    ACX_PART_AC7t1500,
    axi_bram_resp_dl_col,  // Column 9
    axi_bram_resp_dl_row    // Row 7
);
```

### Control Register Interface

The +42 increment functionality is controlled via MMIO:

```cpp
// Enable +42 increment
device.mmioWrite32(0, 0x00, 0x1);

// Disable +42 increment  
device.mmioWrite32(0, 0x00, 0x0);
```

### DMA Transfer Flow

1. **Buffer Allocation**: SDK allocates DMA-capable memory
2. **Transfer Initiation**: DMA engine configured with source/destination
3. **Data Transfer**: AXI4 burst transfer to/from BRAM
4. **Completion**: Transfer status and data verification
5. **Cleanup**: DMA buffer deallocation

## Test Results and Validation

### Success Criteria

- **Register Interface**: All MMIO operations complete successfully
- **DMA Operations**: Transfers complete within timeout limits
- **Data Integrity**: Read-back data matches expected values
- **+42 Processing**: Correct increment applied when enabled
- **Performance**: Transfer rates within expected ranges

### Performance Metrics

- **Transfer Rate**: ~15 MB/sec for 256-byte transfers
- **Latency**: ~15-17 ms for round-trip operations
- **Reliability**: 100% success rate in normal operation
- **Scalability**: Supports up to 4MB transfers

### Error Handling

- **Timeout Detection**: DMA operations timeout after 5 seconds
- **Data Mismatch**: Detailed reporting of byte-level differences
- **Device Errors**: PCIe link status and device readiness checks
- **Resource Cleanup**: Automatic cleanup on test completion

## Troubleshooting

### Common Issues

1. **Device Not Ready**: Ensure FPGA bitstream is loaded and PCIe link is up
2. **DMA Timeouts**: Check for resource conflicts or hardware issues
3. **Data Mismatches**: Verify +42 increment settings match test expectations
4. **Permission Errors**: Ensure proper access to PCIe device

### Debug Information

- **Verbose Output**: Use `-v` flag for detailed DMA status
- **Register Dumps**: Control register state displayed in all tests
- **Transfer Logs**: Detailed timing and bandwidth information
- **Error Context**: Specific failure points identified

## Future Enhancements

### Planned Features

- **Multi-endpoint Testing**: Simultaneous testing of multiple memory types
- **Stress Testing**: Extended duration and high-frequency testing
- **Performance Profiling**: Detailed bandwidth and latency analysis
- **Automated Testing**: CI/CD integration and regression testing

### Extensibility

The test framework is designed for easy extension:
- **New Test Cases**: Simple addition of new test functions
- **Hardware Features**: Support for additional processing modes
- **Performance Metrics**: Custom measurement and reporting
- **Integration**: Easy integration with larger test suites

## Conclusion

This software test suite provides comprehensive validation of the BRAM DMA hardware design, ensuring reliable operation of both basic DMA functionality and the advanced +42 increment processing feature. The tests demonstrate excellent alignment between software expectations and hardware implementation, providing confidence in the overall system reliability and performance.
