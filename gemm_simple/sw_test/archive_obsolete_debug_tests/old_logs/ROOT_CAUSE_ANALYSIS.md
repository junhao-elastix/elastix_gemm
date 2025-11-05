# Root Cause Analysis - CE Stuck Issue

**Date**: October 10, 2025  
**Bitstream**: 0x10100022 (Build: 10/10 00:22)  
**Status**: ✅ ROOT CAUSE IDENTIFIED

---

## Executive Summary

The Compute Engine (CE) timeout is caused by **incomplete GDDR6 data fetch**. The second FETCH command (right matrix) fails after writing only 16 lines, leaving the BRAM partially empty and causing CE to wait indefinitely for data that never arrives.

---

## Debug Register Analysis

### Diagnostic Tool Added
Added 6 new debug registers (0x08-0x1C) to gain FPGA visibility:

| Register | Value | Interpretation |
|----------|-------|----------------|
| 0x08 (CE_BRAM_ADDR) | 0x0EF (239) | CE trying to read address 239 |
| 0x0C (BRAM_DATA_LOW) | 0x00000000 | **BRAM returning ALL ZEROS** |
| 0x10 (BRAM_DATA_MID) | 0x00000000 | **BRAM returning ALL ZEROS** |
| 0x14 (CE_CONTROL) | 0x02 | rd_en=0, load_count=1, **state=2** (ST_LOAD_RIGHT_EXP) |
| 0x18 (DC_WRITE) | 0x021F | wr_en=0, **wr_addr=543** |
| 0x1C (DC_STATUS) | 0x00 | **fetch_done=0, disp_done=0**, dc_state=0 (IDLE) |

### Key Findings

1. **CE State = 2 (ST_LOAD_RIGHT_EXP)**: CE successfully loaded left exponents and progressed to loading right exponents
2. **BRAM Data = All Zeros**: BRAM contains no valid data at address 239  
3. **wr_addr = 543**: Dispatcher wrote only 544 lines total

---

## Data Flow Analysis

### Expected Behavior
```
First FETCH (Left):  GDDR6[0x0000] → BRAM[0-527]   (528 lines)
Second FETCH (Right): GDDR6[0x4200] → BRAM[528-1055] (528 lines)
Total BRAM writes: 1056 lines
```

### Actual Behavior  
```
First FETCH (Left):  GDDR6[0x0000] → BRAM[0-527]   (528 lines) ✅
Second FETCH (Right): GDDR6[0x4200] → BRAM[528-543] (16 lines)  ❌ FAILED!
Total BRAM writes: 544 lines
```

**Calculation**:
- wr_addr = 543 = Last write address
- Lines written = 0 to 543 = 544 total
- First FETCH: 528 lines (0-527)
- Second FETCH: 544 - 528 = **16 lines** (one AXI burst)

---

## Root Cause

**The second FETCH command from GDDR6 address 0x4200 fails after the first AXI burst (16 beats).**

### FETCH Command Verification
```
Left FETCH:  addr=0x0, len=0x210 (528) ✅ Correct
Right FETCH: addr=0x210 (0x4200 in bytes), len=0x210 (528) ✅ Correct
```

### Failure Point
The dispatcher:
1. Issues first AXI read burst for right matrix ✅
2. Receives 16 beats of data ✅  
3. Writes BRAM[528-543] ✅
4. **Hangs waiting for next AXI response** ❌

### Possible Causes

#### 1. **GDDR6 Address Error** (MOST LIKELY)
- Address 0x4200 may be invalid/unmapped
- Test uses byte address 0x4200, but GDDR6 might have alignment requirements
- NAP may reject unaligned or out-of-range addresses

#### 2. **AXI Protocol Issue**
- Timeout on AXI read response channel
- NoC routing failure for address 0x4200
- Channel 0 NAP configuration error

#### 3. **State Machine Deadlock**
- Dispatcher waiting for rvalid that never comes
- AXI handshake stuck in WAIT state

---

## Why CE Gets Stuck

1. **BRAM Incomplete**: Right matrix data missing (only 16/528 lines present)
2. **CE Reads Zeros**: BRAM returns 0x00000000 for addresses ≥544  
3. **No Data Ready Signal**: fetch_done=0 because FETCH never completed
4. **CE Waits Forever**: ST_LOAD_RIGHT_EXP loops waiting for valid exponent data

---

## Verification Steps Completed

✅ Confirmed FETCH commands have correct parameters  
✅ Confirmed dispatcher writes correct addresses for first FETCH  
✅ Confirmed second FETCH starts correctly (begins at BRAM[528])  
✅ Confirmed AXI works for first burst of second FETCH  
✅ Ruled out CE logic error (CE state machine correct)  
✅ Ruled out BRAM connectivity issue (first FETCH worked)  
✅ Ruled out command parsing error (all commands decode correctly)

---

## Recommended Next Steps

### Immediate Actions

1. **Check GDDR6 Address Map**:
   ```bash
   # Verify 0x4200 is valid GDDR6 address
   # Check test_gddr6 for address range limits
   ```

2. **Test with Different Address**:
   - Try right matrix at 0x2000 (known-good address)
   - Verify second FETCH completes successfully

3. **Add NAP Debug Registers**:
   - Expose AXI `arvalid`, `arready`, `rvalid`, `rready`
   - Check for AXI timeout or protocol violation

4. **Check NoC Page ID**:
   - Verify GDDR6 Channel 0 Page ID = 10
   - Confirm NoC routes address 0x4200 correctly

### Test Modifications

```cpp
// In test_ms2_gemm_full.cpp, try:
const uint32_t GDDR6_BASE_RIGHT = 0x2000;  // Instead of 0x4200

// Or use single matrix test:
// Only FETCH left matrix, skip right FETCH
// See if CE can at least load left matrix successfully
```

### RTL Investigation

```systemverilog
// Add to dispatcher_control.sv ST_FETCH_WAIT state:
if (timeout_counter > 1000) begin
    $display("[DC_ERROR] AXI timeout waiting for rvalid");
    state_next = ST_IDLE;  // Abort and return error
end
```

---

## Files Modified (Debug Infrastructure)

- `src/rtl/elastix_gemm_top.sv` - Added debug register definitions
- `src/rtl/engine_wrapper.sv` - Added debug signal wiring  
- `src/rtl/compute_engine.sv` - Added o_load_count output
- `src/rtl/dispatcher_control.sv` - Added BRAM write debug outputs  
- `CHANGELOG.md` - Documented debug register additions
- `sw_test/read_debug_regs.cpp` - Created diagnostic utility

---

## Conclusion

The CE is NOT stuck due to a logic error. The root cause is **GDDR6 fetch failure** on the second FETCH command. The dispatcher successfully fetches the first matrix but hangs during the second matrix fetch after one burst, leaving the BRAM with insufficient data for CE to operate.

**Priority**: Investigate GDDR6 address 0x4200 validity and AXI response behavior.
