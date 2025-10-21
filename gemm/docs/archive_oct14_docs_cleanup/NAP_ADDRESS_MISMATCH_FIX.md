# NAP Address Mismatch - Critical Fix

**Date**: October 14, 2025  
**Issue**: Result BRAM DMA address mismatch between RTL and placement constraint

---

## Root Cause

**Physical Placement** (ace_placements.pdc line 29):
```pdc
set_placement -fixed {i:i_axi_bram_rsp_dma.i_axi_initiator_nap.i_axi_initiator} {s:x_core.NOC[3][5].logic.noc.nap_m}
```
- Result BRAM physically placed at **NOC[3][5]**

**RTL Parameters** (elastix_gemm_top.sv line 411):
```systemverilog
.NAP_COL            (3),  // Column 3
.NAP_ROW            (4),  // Row 4 - INCORRECT!
```
- RTL instantiation specified **NAP[3][4]**

**Software Address Calculation**:
```cpp
BRAM_RESULT_BASE = acx_util_nap_absolute_addr(ACX_PART_AC7t1500, 3, 4);
// Calculated: 0x4130000000 (for NAP[3][4])
// Should be:  0x4138000000 (for NAP[3][5])
```

---

## Symptoms

1. **DMA Write Failure**: Attempting to write to `0x4130000000` caused device hang
2. **All Registers Read 0xFFFFFFFF**: Device dropped from PCIe bus
3. **GDDR6 DMA Also Failed**: Device was completely hung after first failed DMA

---

## Fix Applied

### Hardware (elastix_gemm_top.sv)
**Changed NAP_ROW parameter from 4 to 5:**
```systemverilog
dma_bram_bridge
#(
    .NAP_COL            (3),  // Column 3 - same as engine
    .NAP_ROW            (5),  // Row 5 - MATCHES PLACEMENT CONSTRAINT (NOC[3][5])
    .PROBE_NAME         ("bram_rsp_dma")
)
```

### Software (test_dma_access.cpp, test_ms2_gemm_full.cpp)
**Changed NAP address calculation from [3][4] to [3][5]:**
```cpp
// test_dma_access.cpp line 346
RESULT_BRAM_BASE = acx_util_nap_absolute_addr(ACX_PART_AC7t1500, 3, 5);
// Expected address: 0x4138000000

// test_ms2_gemm_full.cpp line 380
BRAM_RESULT_BASE = acx_util_nap_absolute_addr(ACX_PART_AC7t1500, 3, 5);
```

---

## Verification Steps (After Rebuild & Reboot)

1. **Program FPGA** with new bitstream
2. **Reboot system** to recover from device hang
3. **Run test_dma_access**:
   ```bash
   cd /home/dev/Dev/elastix_gemm/gemm/sw_test
   ./test_dma_access
   ```
   - Should show: `Result BRAM NAP[3][5] address: 0x4138000000`
   - Test 1 (BRAM DMA) should **PASS**
   - Test 2 (Result Registers) should **PASS** (not 0xFFFFFFFF)
   - Test 3 (GDDR6 DMA) should **PASS**

4. **Run full test**:
   ```bash
   ./test_ms2_gemm_full
   ```
   - Should complete Step 10 (DMA read from BRAM) without hanging
   - Should read 16 FP16 results from BRAM successfully

---

## Lesson Learned

**CRITICAL**: Always verify RTL NAP parameters match physical placement constraints!

The Achronix NAP address calculation is:
```
NAP_address = (0x08 << 35) | ((col-1) << 31) | ((row-1) << 28) | offset
```

For NAP[3][5]:
```
NAP[3][5] = (0x08 << 35) | (2 << 31) | (4 << 28) | 0x0
          = 0x0400000000 | 0x0080000000 | 0x0040000000 | 0x0
          = 0x4138000000  ✓ CORRECT
```

For NAP[3][4] (WRONG):
```
NAP[3][4] = (0x08 << 35) | (2 << 31) | (3 << 28) | 0x0
          = 0x0400000000 | 0x0080000000 | 0x0030000000 | 0x0
          = 0x4130000000  ✗ INCORRECT (no hardware at this address!)
```

---

## Files Modified

### Hardware
- `/home/dev/Dev/elastix_gemm/gemm/src/rtl/elastix_gemm_top.sv` (line 411)

### Software  
- `/home/dev/Dev/elastix_gemm/gemm/sw_test/test_dma_access.cpp` (line 346)
- `/home/dev/Dev/elastix_gemm/gemm/sw_test/test_ms2_gemm_full.cpp` (line 380)

### Build Status
- **Hardware**: Rebuilding with corrected NAP[3][5] parameter
- **Software**: Recompiled with corrected address calculation

---

## Expected Results

With the correct NAP[3][5] address:
1. **DMA writes to Result BRAM** should succeed
2. **DMA reads from Result BRAM** should succeed  
3. **Device should remain responsive** (no hang)
4. **Full GEMM test** should complete successfully

The `dma_bram_bridge` at NAP[3][5] provides **bidirectional DMA access** to the Result BRAM, allowing both:
- **Internal writes** from `result_fifo_to_simple_bram` (engine → BRAM)
- **External DMA access** from host (host ↔ BRAM)

This is the correct architecture for result retrieval!


