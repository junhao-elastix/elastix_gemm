# BRAM Refactoring Fix - Correcting Poor Implementation

**Date**: October 13, 2025  
**Issue**: Incorrect implementation of BRAM refactoring plan  
**Status**: FIXED

---

## The Problem

The `dispatcher_bram.sv` module was **incorrectly implemented** and did NOT match the refactoring plan we discussed.

### What Was WRONG (Previous Implementation)

```systemverilog
// WRONG: Single shared mantissa BRAM
logic [DATA_WIDTH-1:0] bram_array [0:DEPTH-1];  // 2048 lines

// Both left and right read from THE SAME BRAM
assign o_rd_data_left = bram_array[i_rd_addr_left];   // Reads from shared BRAM
assign o_rd_data_right = bram_array[i_rd_addr_right]; // Reads from shared BRAM
```

**Critical Bug**: Both left and right matrices were reading from address 0 in the SAME BRAM, causing them to get **identical data**!

This is why the hardware produced:
```
left[0:3]=0x634c2e94, right[0:3]=0x634c2e94  ← SAME VALUES!
```

---

## The Refactoring Plan (What We SHOULD Have Done)

From our discussion, the plan was:

1. **Fetch will still fetch two memory blocks** from GDDR6 (left.hex and right.hex)
2. **Left matrix organization**:
   - First 16 lines: Left exponents → 8-bit x 512 memory
   - Next 512 lines: Left mantissas → 256-bit x 512 memory
3. **Right matrix organization**:
   - Next 16 lines: Right exponents → 8-bit x 512 memory
   - Final 512 lines: Right mantissas → 256-bit x 512 memory
4. **Four data output ports**:
   - `o_left_exp` (8-bit)
   - `o_rd_data_left` (256-bit mantissa)
   - `o_right_exp` (8-bit)
   - `o_rd_data_right` (256-bit mantissa)

---

## The Fix (Correct Implementation)

### New Architecture

```systemverilog
// CORRECT: TWO separate mantissa BRAMs
logic [DATA_WIDTH-1:0] left_mantissa_mem [0:MANTISSA_DEPTH-1];   // 256-bit x 512
logic [DATA_WIDTH-1:0] right_mantissa_mem [0:MANTISSA_DEPTH-1];  // 256-bit x 512

// TWO separate exponent BRAMs (already correct)
logic [7:0] left_exp_mem [0:EXP_DEPTH-1];   // 8-bit x 512
logic [7:0] right_exp_mem [0:EXP_DEPTH-1];  // 8-bit x 512
```

### Write Address Mapping

From `dispatcher_control` during FETCH operations:
```
Addresses [0-511]:     Write to left_mantissa_mem
Addresses [512-1023]:  Write to right_mantissa_mem
Exponents:             Written separately via dedicated exp write ports
```

### Read Address Mapping

From `gfp8_bcv_controller` during TILE operations:
```
Left reads:  Address [0-511] from left_mantissa_mem
Right reads: Address [0-511] from right_mantissa_mem
Each uses lower 9 bits of address (independent address spaces)
```

---

## Files Modified

1. **`src/rtl/dispatcher_bram.sv`**:
   - Replaced single `bram_array[2048]` with TWO separate arrays
   - Added `left_mantissa_mem[512]` and `right_mantissa_mem[512]`
   - Fixed write logic to decode address and write to correct BRAM
   - Fixed read logic to read from separate BRAMs
   - Updated module header to document correct architecture

---

## Testing Impact

**Before Fix**: Hardware read **SAME data** for both left and right  
**After Fix**: Hardware will now read **DIFFERENT data** from separate BRAMs

This should resolve the issue where:
```
Golden: dot=(-7551, -16) = -0.115  (NEGATIVE)
Hardware: dot=(+106529, -16) = +1.626  (POSITIVE, WRONG)
```

The hardware was computing with incorrect data because both matrices were reading from the same BRAM address space.

---

## Next Steps

1. ✅ **COMPLETED**: Fix BRAM architecture to use separate left/right BRAMs
2. **TODO**: Run simulation to verify left and right read different data
3. **TODO**: Verify hardware produces correct results matching golden reference
4. **TODO**: Update dispatcher_control to correctly write to [0-511] and [512-1023] address ranges

---

## Lesson Learned

**Always document the architectural plan BEFORE implementing**, and verify the implementation matches the plan. In this case, I failed to:
1. Document the refactoring plan in a separate file
2. Verify the implementation matched the discussed architecture
3. Catch that both left/right were sharing the same BRAM

This mistake caused significant debugging time and incorrect results.


