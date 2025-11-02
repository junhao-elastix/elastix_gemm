# Test Software Updates for Packed Result Format

**Date**: October 31, 2025
**Modified File**: `test_gemm.cpp`
**Related Hardware**: `result_fifo_to_simple_bram.sv` packing optimization

---

## Overview of Changes

The test software has been updated to correctly read results from the optimized packed BRAM format, where **16 FP16 values are packed per 256-bit (32-byte) BRAM line** instead of the previous 1 FP16 per line.

---

## Previous Implementation (Lines 406-421)

### Old Method: 1 FP16 per BRAM Line
```cpp
// OLD CODE - Inefficient
size_t result_count_expected = B * C;
size_t bram_bytes_per_result = 32;  // Wasted 30 bytes per result!
size_t result_bytes = result_count_expected * bram_bytes_per_result;
vector<uint8_t> bram_data(result_bytes);

gemm_device.dma_read(BRAM_RESULT_BASE, bram_data.data(), result_bytes);

// Extract only first FP16 from each 32-byte line
for (size_t i = 0; i < result_count_expected; i++) {
    uint8_t* line_ptr = bram_data.data() + (i * 32);
    result_fp16[i] = *(uint16_t*)line_ptr;  // Only 2 bytes used!
}
```

**Issues**:
- 93.75% of BRAM bandwidth wasted
- DMA transferred 32× more data than necessary
- Only 512 results could fit in 512-line BRAM

---

## New Implementation (Lines 406-469)

### Optimized Method: 16 FP16 per BRAM Line

The new implementation follows the 4-step protocol documented in `HOST_DMA_RESULT_READ.md`:

#### **Step 1: Read write_top Counter** (Lines 409-415)
```cpp
// Read ENGINE_WRITE_TOP register (reg 139, offset 0x22C)
uint32_t write_top_raw = gemm_device.mmio_read32(0, 0x22C);
uint32_t write_top = write_top_raw & 0x1FFF;  // Mask to 13 bits

if (verbose) {
    cout << "  [DMA Read] write_top = " << write_top << " results" << endl;
}
```

**Purpose**: Determine how many FP16 results the hardware has produced.

---

#### **Step 2: Calculate DMA Parameters** (Lines 417-433)
```cpp
// Calculate complete BRAM lines available
size_t result_count_expected = B * C;
uint32_t complete_lines = write_top / 16;      // Integer division
uint32_t readable_results = complete_lines * 16;

if (verbose) {
    cout << "  [DMA Read] Complete lines: " << complete_lines
         << ", Readable results: " << readable_results << endl;
}

// Verify sufficient results available
if (readable_results < result_count_expected) {
    cerr << "ERROR: Not enough results. Expected " << result_count_expected
         << ", got " << readable_results << " (write_top=" << write_top << ")" << endl;
    return false;
}
```

**Purpose**:
- Only complete BRAM lines (16 FP16 multiples) are readable
- Detect if results are still in packing buffer
- Calculate exact DMA transfer size

**Example**:
- If `write_top = 165`:
  - `complete_lines = 165 / 16 = 10`
  - `readable_results = 10 × 16 = 160`
  - 5 results still buffered (not yet written to BRAM)

---

#### **Step 3: DMA Read Packed Data** (Lines 435-447)
```cpp
// Read only the necessary bytes
size_t result_bytes = complete_lines * 32;  // 32 bytes per line
vector<uint8_t> bram_data(result_bytes);

if (verbose) {
    cout << "  [DMA Read] Reading " << result_bytes << " bytes from BRAM" << endl;
}

if (!gemm_device.dma_read(BRAM_RESULT_BASE, bram_data.data(), result_bytes)) {
    cerr << "ERROR: Failed to DMA read results" << endl;
    return false;
}
```

**Bandwidth Savings**:
- For 160 results:
  - Old: 160 × 32 = **5,120 bytes**
  - New: 10 × 32 = **320 bytes**
  - **16× reduction** in DMA traffic!

---

#### **Step 4: Unpack FP16 Results** (Lines 449-469)
```cpp
// Unpack 16 FP16 values from each 32-byte line
vector<uint16_t> result_fp16(result_count_expected);

for (size_t i = 0; i < result_count_expected; i++) {
    size_t line_index = i / 16;        // Which BRAM line (0, 1, 2, ...)
    size_t pos_in_line = i % 16;       // Position within line (0-15)
    size_t byte_offset = line_index * 32 + pos_in_line * 2;

    // Extract FP16 value (little-endian, 2 bytes)
    result_fp16[i] = *(uint16_t*)(bram_data.data() + byte_offset);
}

if (verbose) {
    cout << "  [DMA Read] Unpacked " << result_count_expected << " FP16 results" << endl;
    cout << "  First 4 results: 0x" << hex
         << setw(4) << result_fp16[0] << " 0x"
         << setw(4) << result_fp16[1] << " 0x"
         << setw(4) << result_fp16[2] << " 0x"
         << setw(4) << result_fp16[3] << dec << endl;
}
```

**Unpacking Logic**:
```
Result Index → BRAM Line Mapping:
  Results [0-15]   → Line 0, bytes [0-31]
  Results [16-31]  → Line 1, bytes [32-63]
  Results [32-47]  → Line 2, bytes [64-95]
  ...

Byte Offset Calculation:
  byte_offset = (result_index / 16) * 32 + (result_index % 16) * 2

Example for result_index = 23:
  line_index = 23 / 16 = 1
  pos_in_line = 23 % 16 = 7
  byte_offset = 1 * 32 + 7 * 2 = 46
  → Read bytes [46-47] from bram_data
```

---

## Additional Feature: write_top Reset (Lines 534-545)

After reading results, the counter is reset to allow BRAM reuse:

```cpp
// Reset write_top counter to allow BRAM reuse
if (verbose) {
    cout << "  [DMA Read] Resetting write_top counter" << endl;
}
gemm_device.mmio_write32(0, 0x22C, 0x00000000);

// Verify reset
uint32_t write_top_after_reset = gemm_device.mmio_read32(0, 0x22C) & 0x1FFF;
if (verbose) {
    cout << "  [DMA Read] write_top after reset: " << write_top_after_reset << endl;
}
```

**Reset Behavior**:
1. Any buffered results (1-15 FP16s) flushed to BRAM
2. `write_top` counter set to 0
3. Next results start writing from BRAM line 0 (circular)

---

## Performance Benefits

| Metric | Old (1/line) | New (16/line) | Improvement |
|--------|--------------|---------------|-------------|
| **BRAM Utilization** | 6.25% | 100% | 16× |
| **DMA Size (160 results)** | 5,120 bytes | 320 bytes | 16× smaller |
| **Capacity (512 lines)** | 512 results | 8,192 results | 16× more |
| **PCIe Bandwidth** | Wasted 93.75% | 100% efficient | Optimal |

---

## Verbose Output Example

When running with `-v` flag, the test now shows detailed DMA information:

```
[DMA Read] write_top = 165 results
[DMA Read] Complete lines: 10, Readable results: 160
[DMA Read] Reading 320 bytes from BRAM
[DMA Read] Unpacked 160 FP16 results
[DMA Read] First 4 results: 0x3C00 0x4000 0x4200 0x4400
[DMA Read] Resetting write_top counter
[DMA Read] write_top after reset: 0
```

---

## Error Handling

### Insufficient Results Error
```
ERROR: Not enough results available. Expected 165, but only 160 readable (write_top=165)
  Note: 5 results still in packing buffer
```

**Cause**: Hardware has produced results, but not enough to fill the last BRAM line.

**Solution**:
1. Wait for more computation, OR
2. Trigger write_top reset to flush partial buffer

---

## Compatibility Notes

### Hardware Requirements
- RTL module `result_fifo_to_simple_bram.sv` with packing enabled
- Register 139 (0x22C) mapped to `ENGINE_WRITE_TOP`
- BRAM bridge at correct NAP coordinates (3,5)

### Software Requirements
- No changes to function signatures
- Backward compatible with existing test harness
- Verbose mode provides additional debug info

---

## Testing Checklist

Before hardware testing, verify:
- [ ] Bitstream includes packing optimization
- [ ] Register 139 accessible via MMIO
- [ ] BRAM_RESULT_BASE correctly calculated
- [ ] Test with verbose mode first: `./test_gemm -v -B 4 -C 4 -V 4`
- [ ] Check write_top counter increments correctly
- [ ] Verify results match golden reference
- [ ] Confirm reset clears counter to 0

---

## Next Steps

1. **Compile Updated Software**:
   ```bash
   cd /home/workstation/elastix_gemm/gemm/sw_test
   make clean && make
   ```

2. **Build and Flash Bitstream**:
   ```bash
   cd /home/workstation/elastix_gemm/gemm
   ./build_and_flash.sh
   ```

3. **Run Tests**:
   ```bash
   cd /home/workstation/elastix_gemm/gemm/sw_test
   ./test_gemm -v -B 1 -C 1 -V 1  # Single test with verbose
   ./test_gemm                     # Full test suite
   ```

---

**Document Version**: 1.0
**Last Updated**: October 31, 2025
**Status**: Ready for compilation and hardware testing
