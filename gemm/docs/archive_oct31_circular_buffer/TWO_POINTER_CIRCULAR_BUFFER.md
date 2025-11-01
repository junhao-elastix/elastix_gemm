# Two-Pointer Circular Buffer Implementation

**Date**: October 31, 2025
**Modified Files**: `gemm/sw_test/test_gemm.cpp`
**Status**: ✅ Compiled successfully, ready for hardware testing

---

## Overview

The MS2.0 GEMM engine result collection has been upgraded from a simple write-counter system to a **two-pointer circular buffer** architecture. This enables more efficient result management and supports future multi-test queuing scenarios.

### Key Concept

```
Circular Buffer (8192 FP16 results capacity):
┌──────────────────────────────────────────────┐
│  [used entries]          [free space]        │
│  ↑                       ↑                   │
│  rd_ptr (host)           wr_ptr (hardware)   │
└──────────────────────────────────────────────┘
   0                                        8191

used_entries = wr_ptr - rd_ptr (with wrapping)
```

**Hardware** writes results and increments `wr_ptr`
**Host** reads results and increments `rd_ptr`

---

## Register Interface

Three new registers have been added for circular buffer management:

| Register | Offset | R/W | Description |
|----------|--------|-----|-------------|
| **REG_RD_PTR** | 0x230 (140) | R/W | Host read pointer (0-8191) |
| **REG_WR_PTR** | 0x234 (141) | R/O | Hardware write pointer (0-8191) |
| **REG_USED_ENTRIES** | 0x238 (142) | R/O | Available results (0-8192) |
| ENGINE_WRITE_TOP | 0x22C (139) | R/W | **DEPRECATED** - now reads wr_ptr for compatibility |

### Legacy Compatibility

- Reading `ENGINE_WRITE_TOP` (0x22C) now returns the same value as `REG_WR_PTR` (0x234)
- Writing 0 to `ENGINE_WRITE_TOP` (0x22C) still triggers partial buffer flush (does NOT reset pointers)

---

## Implementation Changes in test_gemm.cpp

### 1. **Initialization** (Lines 286-293)

```cpp
// Reset circular buffer read pointer for this test
uint32_t host_rd_ptr = 0;  // Initialize to 0 at start of each test
gemm_device.mmio_write32(0, 0x230, host_rd_ptr);
```

**Behavior**: Reset `rd_ptr` to 0 at the start of each test to match simulation behavior.

### 2. **Result Reading** (Lines 421-451)

```cpp
// Step 1: Read circular buffer pointers
uint32_t wr_ptr = gemm_device.mmio_read32(0, 0x234) & 0x1FFF;  // Hardware write pointer
uint32_t used_entries = gemm_device.mmio_read32(0, 0x238) & 0x3FFF;  // Available results

// Step 2: Verify we have enough results
if (used_entries < result_count_expected) {
    // Wait and retry
}
```

**Changes from old implementation**:
- ❌ Old: Read `write_top` from 0x22C
- ✅ New: Read `wr_ptr` from 0x234 and `used_entries` from 0x238
- ✅ New: Explicit verification of available results before reading

### 3. **Partial Buffer Handling** (Lines 463-486)

```cpp
// If we have partial results (< 16), force a flush
if (partial_results > 0 && (complete_lines * 16) < result_count_expected) {
    gemm_device.mmio_write32(0, 0x22C, 0x00000000);  // Trigger flush
    usleep(100);

    // Re-read wr_ptr after flush
    wr_ptr = gemm_device.mmio_read32(0, 0x234) & 0x1FFF;
    complete_lines = (wr_ptr + 15) / 16;
}
```

**Changes from old implementation**:
- ❌ Old: Flush reset both the buffer AND the write_top counter
- ✅ New: Flush only writes partial buffer, wr_ptr persists (no reset)

### 4. **Pointer Update After Reading** (Lines 593-609)

```cpp
// Update host read pointer after consuming results
host_rd_ptr = (host_rd_ptr + result_count_expected) & 0x1FFF;  // Wrap at 8192

// Write updated rd_ptr back to hardware
gemm_device.mmio_write32(0, 0x230, host_rd_ptr);

// Note: We do NOT reset wr_ptr - circular buffer is persistent
```

**Changes from old implementation**:
- ❌ Old: Reset `write_top` to 0 after each test
- ✅ New: Update `rd_ptr` to indicate consumption (no reset)
- ✅ New: Buffer is persistent (wraps at 8192)

---

## Behavioral Differences

### Old Implementation (write_top counter)

```
Test 1: write_top = 0 → write 4 results → write_top = 4 → RESET to 0
Test 2: write_top = 0 → write 16 results → write_top = 16 → RESET to 0
Test 3: write_top = 0 → write 128 results → write_top = 128 → RESET to 0
```

**Issues**:
- Counter reset loses track of buffer state
- No true circular buffer capability
- Cannot queue multiple operations

### New Implementation (two-pointer circular buffer)

```
Test 1: rd_ptr = 0, wr_ptr = 0 → write 4 results → wr_ptr = 4, rd_ptr updates to 4
Test 2: rd_ptr = 0, wr_ptr = 4 → write 16 results → wr_ptr = 20, rd_ptr updates to 16
Test 3: rd_ptr = 0, wr_ptr = 20 → write 128 results → wr_ptr = 148, rd_ptr updates to 128
```

**Note**: Current implementation resets `rd_ptr` to 0 at the start of each test to match simulation behavior and ensure isolation.

**Benefits**:
- True circular buffer with 8192 FP16 capacity
- Automatic wrapping at 8192
- Support for future multi-test queuing
- Hardware can track available space (`used_entries`)

---

## Hardware Implementation Reference

### result_fifo_to_simple_bram.sv

The hardware packer module implements:

```systemverilog
// Circular buffer interface
input  logic [12:0] i_rd_ptr,         // Read pointer from host (0-8191)
output logic [12:0] o_wr_ptr,         // Write pointer (0-8191)
output logic [13:0] o_used_entries,   // Valid FP16 results (0-8192)
output logic        o_empty,          // Buffer empty flag
input  logic        i_write_top_reset, // Flush partial buffer
output logic        o_almost_full     // Backpressure (7936/8192 = 7/8 full)
```

**Key Features**:
- 8192 FP16 result capacity (512 BRAM lines × 16 results/line)
- Automatic wrapping at 8192
- Backpressure signal when 7/8 full (7936 results)
- Partial buffer flush support for tests with < 16 results

### Simulation Reference (tb_engine_top.sv)

The testbench demonstrates correct usage:

```systemverilog
// Initialize rd_ptr
initial begin
    result_rd_ptr = 13'b0;
end

// Wait for all results to be packed
while ((result_wr_ptr < expected_results) && (timeout_count < watchdog)) begin
    @(posedge clk);
    timeout_count++;
end

// Read results from BRAM
for (int result_idx = 0; result_idx < expected_results; result_idx++) begin
    // Extract from packed BRAM line
    bram_line = result_idx / 16;
    bram_pos = result_idx % 16;
    fp16_hw = result_bram_model[bram_line][bram_pos*16 +: 16];

    // Update rd_ptr every 16 results (one BRAM line)
    if ((result_idx + 1) % 16 == 0) begin
        result_rd_ptr = result_rd_ptr + 16;
    end
end
```

---

## Testing Recommendations

### Compilation

```bash
cd /home/workstation/elastix_gemm/gemm/sw_test
make clean
make test_gemm
```

**Expected**: ✅ Clean compilation (verified)

### Hardware Testing

```bash
# Run single test with verbose output
./test_gemm -B 4 -C 4 -V 4 -v

# Run full test suite
./test_gemm

# Run with timing profiling
./test_gemm -t
```

**What to verify**:
1. ✅ Circular buffer pointers are displayed correctly
2. ✅ `used_entries` matches expected result count
3. ✅ `rd_ptr` increments correctly after each test
4. ✅ All 10 test configurations pass validation
5. ✅ No 0xffffffff register reads (healthy device)

### Expected Verbose Output

```
[Circular Buffer] Reset rd_ptr to 0
[Circular Buffer] wr_ptr = 16, rd_ptr = 0, used_entries = 16
[DMA Read] Complete lines: 1, Partial results: 0
[DMA Read] Reading 32 bytes from BRAM
[DMA Read] Unpacked 16 FP16 results
Validation: 16/16 matches
[Circular Buffer] Updated rd_ptr to 16
[Circular Buffer] After read: used_entries = 0
```

### Debug Commands

```bash
# Check register interface
./test_registers

# Verify FPGA health
./test_bram

# Monitor GDDR6 status
./test_gddr6
```

### Recovery Procedure

If device hangs (0xffffffff):
```bash
/home/workstation/elastix_gemm/hex.sh
source /home/workstation/rescan
./test_registers
```

---

## Future Enhancements

### 1. **Multi-Test Queuing** (Not Yet Implemented)

```cpp
// Future: Persistent rd_ptr across tests
static uint32_t global_rd_ptr = 0;  // Global state

// Test 1: No reset, start from global_rd_ptr
// Test 2: No reset, continue from where Test 1 left off
// Test 3: No reset, circular buffer wraps automatically
```

**Benefits**:
- Queue multiple GEMM operations
- Batch result retrieval
- Reduced host-device synchronization overhead

### 2. **Asynchronous Result Reading**

```cpp
// Start GEMM operation
gemm_device.tile(...);

// Do other work while hardware computes
process_previous_results();

// Check if results ready
if (used_entries >= expected_results) {
    read_results();
}
```

### 3. **Backpressure Monitoring**

```cpp
// Check if buffer is almost full (7936/8192)
uint32_t almost_full = gemm_device.mmio_read32(0, 0x23C);  // Future register
if (almost_full) {
    drain_results_before_submitting_next_operation();
}
```

---

## Summary

### ✅ Completed
- Two-pointer circular buffer system implemented in test_gemm.cpp
- Register interface for rd_ptr, wr_ptr, used_entries
- Backward compatibility with legacy write_top register
- Compilation verified (no errors)

### 🧪 Pending
- Hardware validation with actual FPGA
- Performance benchmarking
- Multi-test queuing stress test

### 📝 Notes
- Current implementation resets rd_ptr per test (matches simulation)
- Circular buffer capacity: 8192 FP16 results (512 BRAM lines)
- Backpressure threshold: 7936 results (7/8 full)
- Automatic wrapping at 8192 (13-bit pointer)

---

**Questions or Clarifications?**

If you need clarification on:
1. How the circular buffer wrapping works
2. When to use flush vs. pointer update
3. Multi-test queuing scenarios

Please ask! The simulation in `gemm/sim/vector_system_test/tb_engine_top.sv` provides a reference implementation.
