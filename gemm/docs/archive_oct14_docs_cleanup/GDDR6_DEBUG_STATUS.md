# GDDR6 FETCH Fix - Debug Status

**Date**: October 14, 2025  
**Bitstream**: Build 10/13 16:51

## ✅ CRITICAL FIX APPLIED

### Root Cause Found
The `dispatcher_control.sv` was constructing AXI addresses **without the GDDR6 page ID**, causing all FETCH commands to access the wrong memory location.

**Fixed in dispatcher_control.sv line 571:**
```systemverilog
// OLD (BROKEN):
assign axi_ddr_if.araddr = {(fetch_addr_reg + current_line_reg), {ADDR_BYTE_SHIFT{1'b0}}};

// NEW (FIXED):
assign axi_ddr_if.araddr = {GDDR6_PAGE_ID, 2'b00, (fetch_addr_reg + current_line_reg), {ADDR_BYTE_SHIFT{1'b0}}};
```

## ✅ Confirmed Working
1. **DMA to/from GDDR6**: 33,792 bytes verified ✓
2. **FETCH now actually reads from GDDR6**: Commands no longer complete instantly
3. **Non-zero results**: Hardware now produces `0x3c98, 0x3c98, 0x2180, 0x2180` instead of all zeros

## ❌ Remaining Issues

### Issue 1: Results Don't Match Golden Reference

**Expected** (from golden_B2_C2_V2.hex):
```
0xb414 → -0.254
0x2ecb →  0.224
0x3345 →  0.817
0x326b →  0.653
```

**Hardware Got**:
```
0x3c98 →  1.148
0x3c98 →  1.148
0x2180 →  0.011
0x2180 →  0.011
```

**Analysis**: Values are completely wrong and duplicated. Suggests:
- Dispatcher might be reading wrong BRAM addresses
- Compute engine might have addressing bugs
- GFP8 unpacking might be incorrect
- BCV loop might be indexing incorrectly

### Issue 2: Result Count Shows 1 Instead of 4
```
ENGINE_RESULT_COUNT: 1 FP16 values
```
But we got 4 results from the result registers. The counter might not be incrementing correctly.

### Issue 3: DMA Readback Not Working
From user: "we are not reading back from bram anymore"
- Full test times out at Step 10 (reading results via DMA)
- Simple test reads results via direct register access (works)
- Suggests dma_bram_bridge or result BRAM addressing issue

## 🔬 Required: GDDR6 Simulation

### Why We Need It
Hardware testing has limited visibility:
- Can't see GDDR6 data being read
- Can't see dispatcher BRAM contents
- Can't trace compute engine datapath
- Debug registers are hardwired to zero

### Simulation Plan
Based on `/home/dev/Dev/elastix_gemm/gddr_ref_design/sim/`:

```
Testbench Structure:
├── tb_engine_gddr6.sv (main testbench)
│   ├── reg_control_block (CSR writes - in testbench)
│   ├── elastix_gemm_top (DUT)
│   │   └── engine_top (channel 1)
│   │       ├── csr_to_fifo_bridge
│   │       ├── cmd_fifo
│   │       ├── master_control
│   │       ├── dispatcher_control → NAP interface
│   │       └── compute_engine_modular
│   └── Micron GDDR6 BFM (memory model)
│       └── Connected via NoC/NAP
```

### Test Sequence
1. **Preload GDDR6** with test matrices from left.hex/right.hex
   - Use backdoor write to GDDR6 model
   - Address: Channel 1 (page 2), lines 0-527 for each matrix

2. **Issue Commands via CSR**:
   ```
   FETCH left  (addr=0x0, len=528)
   FETCH right (addr=0x4200, len=528) 
   DISPATCH left (addr=0, len=128)
   WAIT_DISPATCH
   DISPATCH right (addr=528, len=128)
   WAIT_DISPATCH
   MATMUL (B=2, C=2, V=2, left_addr=0, right_addr=528)
   WAIT_MATMUL
   ```

3. **Monitor** (via waveforms):
   - AXI transactions: araddr, arvalid, arready, rdata
   - Dispatcher BRAM writes: wr_addr, wr_data, wr_en
   - Compute engine: BCV indices, accumulator values
   - Result FIFO: result_data, result_valid

### Expected Observations
If working correctly:
- FETCH reads 528 × 32 bytes from GDDR6
- Dispatcher writes to BRAM addresses 0-527 (left), 528-1055 (right)
- DISPATCH configures CE to read from correct BRAM addresses
- MATMUL:
  - B loop: 0, 1
  - C loop: 0, 1
  - V loop: 0, 1
  - Total: 2×2 = 4 results
- Results match golden reference

## 📋 TODO List

### High Priority
1. **Create GDDR6 simulation environment**
   - Copy gddr_ref_design testbench structure
   - Replace gddr_ref_design_top with elastix_gemm_top
   - Add reg_control_block for CSR interface
   - Create Makefile using Riviera-PRO

2. **Implement GDDR6 preload**
   - Read left.hex and right.hex
   - Write to GDDR6 BFM at correct addresses
   - Verify backdoor read

3. **Add comprehensive monitors**
   - AXI transaction logger
   - Dispatcher BRAM content viewer
   - Compute engine datapath tracer
   - Result comparator

### Medium Priority
4. **Debug dispatcher BRAM addressing**
   - Verify 528-line GFP8 format unpacking
   - Check exponent vs mantissa line distinction
   - Validate aligned BRAM read for CE

5. **Debug compute engine BCV loop**
   - Verify B, C, V dimension capture
   - Check NV address calculation
   - Validate accumulator pipeline

6. **Fix result count register**
   - Trace result_fifo writes
   - Check counter increment logic

### Low Priority
7. **Fix DMA readback path**
   - Debug dma_bram_bridge address translation
   - Verify result_bram addressing
   - Check PCIe DMA state machine

## 📁 Key Files

### RTL (Fixed)
- `src/rtl/dispatcher_control.sv` ✓ (GDDR6 page ID added)

### RTL (Need Debug)
- `src/rtl/dispatcher_bram_dual_read.sv` (GFP8 unpacking)
- `src/rtl/gfp8_bcv_controller.sv` (BCV loop indexing)
- `src/rtl/compute_engine_modular.sv` (dot product & accumulator)
- `src/rtl/result_fifo_to_bram.sv` (result capture)
- `src/rtl/dma_bram_bridge.sv` (DMA readback)

### Test Data
- `/home/dev/Dev/elastix_gemm/hex/left.hex` (Matrix A)
- `/home/dev/Dev/elastix_gemm/hex/right.hex` (Matrix B)
- `/home/dev/Dev/elastix_gemm/hex/golden_B2_C2_V2.hex` (Expected results)

### Reference
- `/home/dev/Dev/elastix_gemm/gddr_ref_design/sim/riviera/` (GDDR6 sim example)
- `/home/dev/Dev/elastix_gemm/gddr_ref_design/src/tb/tb_gddr_ref_design.sv`

## 🎯 Success Criteria

Simulation will be considered successful when:
1. ✓ FETCH reads all 528 lines from GDDR6 with correct page ID
2. ✓ Dispatcher BRAM populated with correct GFP8 data
3. ✓ Compute engine produces 4 results matching golden reference
4. ✓ Result count register shows 4
5. ✓ Results can be read via DMA path

## 📊 Progress Summary

| Component | Status | Notes |
|-----------|--------|-------|
| GDDR6 Page ID | ✅ FIXED | dispatcher_control.sv line 571 |
| DMA to GDDR6 | ✅ WORKS | 33,792 bytes verified |
| FETCH Commands | ✅ EXECUTING | Now actually reads from GDDR6 |
| Non-zero Results | ✅ PRODUCING | But wrong values |
| Result Values | ❌ WRONG | Need simulation to debug |
| Result Count | ❌ WRONG | Shows 1 instead of 4 |
| DMA Readback | ❌ BROKEN | Times out |
| GDDR6 Simulation | 🔨 TODO | Critical for debugging |

## 🚀 Next Steps

**Immediate**: Set up GDDR6 simulation environment with proper testbench
**Reason**: Hardware testing lacks visibility into internal datapaths
**Goal**: Identify why results don't match golden reference

The GDDR6 page ID fix was a major breakthrough - we now have non-zero results. 
But simulation is essential to find the remaining bugs in the computation pipeline.


