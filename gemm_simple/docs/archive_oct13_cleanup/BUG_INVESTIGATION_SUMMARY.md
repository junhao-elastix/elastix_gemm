# BUG INVESTIGATION SUMMARY - gfp8_nv_dot Exponent Corruption

**Date**: October 13, 2025  
**Project**: `elastix_gemm/gemm`  
**Test Case**: B=2, C=2, V=2

---

## Critical Bug Fixed: Exponent Corruption During V-loop

### Root Cause
The `gfp8_nv_dot` module's inputs were **continuously connected** to BCV controller's `nv_left_exp` and `nv_right_exp` registers. When the next V iteration started filling new data, it **overwrote these registers while the current computation was still using them**.

### Timeline of Corruption
```
Cycle @37795000: V=0 COMPUTE starts, nv_right_exp = 0x07070706 ✓
Cycle @37825000: V=0 ACCUM completes
Cycle @37835000: V=1 FILL starts
Cycle @37875000: V=1 captures G1 exponent, overwrites nv_right_exp[15:8]
                 nv_right_exp changes: 0x07070706 → 0x07070606 ❌
```

### Evidence
Before fix, `GROUP_DOT` debug showed all 4 groups receiving the same exponents:
```
G0: exp_left=6, exp_right=6  ✓ Correct
G1: exp_left=6, exp_right=6  ❌ Should be (6,7)
G2: exp_left=6, exp_right=6  ❌ Should be (6,7)  
G3: exp_left=6, exp_right=6  ❌ Should be (7,7)
```

All groups used G0's exponents because `nv_right_exp` was corrupted during unpacking.

### Fix Implemented

#### 1. Added Input Registers to `gfp8_nv_dot.sv`
```systemverilog
// INPUT REGISTERS with enable signal
logic [31:0]  exp_left_reg, exp_right_reg;
logic [255:0] man_left_reg [0:3], man_right_reg [0:3];

always_ff @(posedge i_clk or negedge i_reset_n) begin
    if (!i_reset_n) begin
        // reset
    end else if (i_input_valid) begin
        // ONLY sample inputs when i_input_valid is high
        exp_left_reg <= i_exp_left;
        exp_right_reg <= i_exp_right;
        man_left_reg <= i_man_left;
        man_right_reg <= i_man_right;
    end
end
```

#### 2. Added Enable Signal to BCV Controller
```systemverilog
// Pulse i_input_valid high when entering ST_COMPUTE_NV
logic nv_dot_input_valid;
assign nv_dot_input_valid = (state_reg != ST_COMPUTE_NV) && (state_next == ST_COMPUTE_NV);
```

#### 3. Updated Latency
- **Before**: 2 cycles (GROUP_DOT + alignment)
- **After**: 3 cycles (input register + GROUP_DOT + alignment)
- Updated `compute_wait` counter to wait for 3 cycles

### Verification
After fix, registered exponents remain stable:
```
@37785000: exp_right_reg=0x07070706 ✓ V=0 correct value captured
@38685000: exp_right_reg=0x07070706 ✓ Remains stable during V=1's FILL
```

---

## Remaining Issues

### Issue 1: Hardware Produces Wrong Values

**Observation**: Hardware results have **opposite sign and different magnitude** from golden reference.

Python Golden Reference for Result[0,0]:
```
V=0: dot=(-7551, -16) = -0.115   ← NEGATIVE
V=1: dot=(-36619, -18) = -0.140  ← NEGATIVE  
Final: (-16705, -16) = -0.255 → FP16=0xb414
```

Hardware for Result[0,0]:
```
V=0: dot=(+106529, -16) = +1.626  ← POSITIVE
V=1: dot=(+297019, -18) = +1.133  ← POSITIVE
Final: (+180783, -16) = +2.758 → FP16=0x4184
```

**Status**: Under investigation. Possible causes:
- BRAM data loading incorrect
- Mantissa sign handling bug in GFP dot product
- Address calculation error reading wrong memory locations

### Issue 2: Testbench Reads Duplicates

**CE Produces** (unique values):
```
Result[0] = 0x4184
Result[1] = 0x3484  
Result[2] = 0xae32
Result[3] = 0x410c
```

**Testbench Reads** (duplicates):
```
Result[0] = 0x4184  ✓
Result[1] = 0x4184  ❌ Duplicate
Result[2] = 0x3484  ✓
Result[3] = 0x3484  ❌ Duplicate
```

**Status**: Result FIFO read timing issue in testbench.

---

## Files Modified

1. **`src/rtl/gfp8_nv_dot.sv`**:
   - Added `i_input_valid` port
   - Added input registers with enable
   - Changed latency from 2 to 3 cycles

2. **`src/rtl/gfp8_bcv_controller.sv`**:
   - Added `nv_dot_input_valid` signal
   - Updated `compute_wait` to wait 3 cycles
   - Connected `i_input_valid` to NV dot instance

---

## Test Results

**Before Fix**: All results incorrect due to exponent corruption  
**After Fix**: Result[1] is close (diff=0.176), but others still wrong

This confirms the exponent corruption fix is working, but there's a separate issue with the computation producing wrong values.

---

## Next Steps

1. ✅ **COMPLETED**: Fix exponent corruption with input registers
2. **IN PROGRESS**: Investigate why hardware produces opposite-sign results
3. **TODO**: Fix testbench FIFO read duplication
4. **TODO**: Verify BRAM data loading is correct
5. **TODO**: Run all 8 test cases and verify against golden references


