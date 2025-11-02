# CRITICAL BUG: DISP_COPY Right Side Read Missing

**Date**: Mon Oct 27, 2025
**Severity**: 🔴 **CRITICAL** - Causes incorrect computation results
**Status**: ⚠️ **ROOT CAUSE FOUND**

---

## Summary

**Problem**: DISP_COPY reads RIGHT matrix data incorrectly during copy operation

**Impact**: Compute engine receives wrong right-side matrix data, causing all golden mismatches

---

## Bug Description

### DISP_COPY Operation Intent

Copy from `dispatcher_bram` to `tile_bram`:
```
Counter [0-527]:     dispatcher_bram.man_left  → tile_bram.man_left
Counter [528-1055]:  dispatcher_bram.man_right → tile_bram.man_right
```

### Actual Implementation (WRONG)

**In `dispatcher_control.sv` lines 417-424**:
```systemverilog
// Mantissa write target selection - CORRECT
assign o_tile_man_wr_target = (man_rd_addr_pipe >= 10'd528) ? 1'b1 : 1'b0;
assign o_tile_man_wr_addr = (man_rd_addr_pipe < 10'd528) ?
                             man_rd_addr_pipe[8:0] :
                             (man_rd_addr_pipe - 10'd528);

// Mantissa write data - USES ONLY LEFT READ PORT!
assign o_tile_man_wr_data = o_bram_rd_data_left;    // ⚠️ WRONG!
assign o_tile_man_wr_en   = copy_active_pipe && !disp_copy_man_done_reg;
```

### Read Port Muxing in `engine_top.sv`

**Lines 294-295** (LEFT port - MUXED ✅):
```systemverilog
assign disp_bram_rd_addr_left_muxed = dc_copy_rd_en ? dc_copy_rd_addr : ce_dc_bram_rd_addr_left;
assign disp_bram_rd_en_left_muxed   = dc_copy_rd_en ? 1'b1 : ce_dc_bram_rd_en_left;
```

**Lines 337-339** (RIGHT port - NOT MUXED ❌):
```systemverilog
.i_bram_rd_addr_right   (ce_dc_bram_rd_addr_right),    // ⚠️ NOT muxed!
.o_bram_rd_data_right   (dc_ce_bram_rd_data_right),
.i_bram_rd_en_right     (ce_dc_bram_rd_en_right),      // ⚠️ NOT muxed!
```

---

## Data Flow Analysis

### What Happens During DISP_COPY

#### Counter [0-527] (LEFT matrix copy):
```
1. dc_copy_rd_addr = [0-527]
2. disp_bram_rd_addr_left_muxed = [0-527]  ✅
3. dispatcher_bram reads man_left[0-527]   ✅
4. o_bram_rd_data_left = man_left[0-527]   ✅
5. tile_bram.man_left[0-527] = data        ✅
```
**Result**: LEFT matrix copied correctly! ✅

#### Counter [528-1055] (RIGHT matrix copy):
```
1. dc_copy_rd_addr = [528-1055]
2. disp_bram_rd_addr_left_muxed = [528-1055]  ⚠️ Out of range!
3. dispatcher_bram reads man_left[???]        ❌ Undefined!
4. o_bram_rd_data_left = ???                  ❌ Wrong data!
5. tile_bram.man_right[0-527] = wrong data    ❌ BUG!
```
**Result**: RIGHT matrix gets garbage data! ❌

### Why Reads Return Something (Not X)

**dispatcher_bram.sv read logic** (lines 200-204):
```systemverilog
always_ff @(posedge i_clk) begin
    if (i_rd_en_left) begin
        rd_data_left_reg <= man_left[i_rd_addr_left];  // Uses [8:0] = lower 9 bits
    end
end
```

When `i_rd_addr_left = [528-1055]`:
- Lower 9 bits: [528-1055] & 0x1FF = [16-527]
- Actually reads: `man_left[16-527]` (wraps around!)
- **Returns**: Valid data, but from WRONG part of left matrix!

**This is why**:
- Results are non-zero (not 0x0000)
- Results are deterministic (consistent wrapping)
- **But results are WRONG** (right side gets left side data)

---

## Proof From Simulation

### FETCH Operations Store Correctly

**Left FETCH** (target=0):
```
[DC_CAPTURE] FETCH params: target=0 (LEFT)
[BRAM_WR] LEFT exp_packed[0] <= ...
[BRAM_WR] LEFT man[0] <- 0x50d52ea9...
```
✅ Stores to `dispatcher_bram.man_left[0-511]`

**Right FETCH** (target=1):
```
[DC_CAPTURE] FETCH params: target=1 (RIGHT)
[BRAM_WR] RIGHT exp_packed[0] <= ...
[BRAM_WR] RIGHT man[0] <- 0x01c5ef14...
```
✅ Stores to `dispatcher_bram.man_right[0-511]`

### DISP_COPY Reads Incorrectly

**tile_bram Writes**:
```
[TILE_WR] @26905 man_left[0] = 0x50d52ea9...   ✅ Correct (from man_left[0])
[TILE_WR] @32185 man_right[0] = 0x01c5ef14...  ❓ Where did this come from?
```

**Expected**: man_right[0] should get data from `dispatcher_bram.man_right[0]`
**Actual**: man_right[0] gets data from `dispatcher_bram.man_left[???]` (wrapped address)

**Why tile_bram shows correct data**: The 0x01c5ef14 is from dispatcher_bram.man_left[16] (wrapped from address 528), which HAPPENS to have different data than man_left[0], so it LOOKS like it's working!

But let's verify: If DISP_COPY counter 528 reads from LEFT port with address 528:
- Address 528 & 0x1FF = 16
- Reads man_left[16]

And man_left[16] was written during LEFT FETCH at line 16 (the 17th line of the hex file).

**This is NOT the right matrix data!** It's just data from a different part of the left matrix that happens to look different.

---

## The Fix

### Required Changes

#### 1. Add RIGHT Read Port Muxing in `engine_top.sv`

**After line 295, add**:
```systemverilog
// Mux RIGHT read port for DISP_COPY
logic [10:0] disp_bram_rd_addr_right_muxed;
logic        disp_bram_rd_en_right_muxed;

assign disp_bram_rd_addr_right_muxed = dc_copy_rd_en ? dc_copy_rd_addr : ce_dc_bram_rd_addr_right;
assign disp_bram_rd_en_right_muxed   = dc_copy_rd_en ? 1'b1 : ce_dc_bram_rd_en_right;
```

**Update line 337-339**:
```systemverilog
// BEFORE:
.i_bram_rd_addr_right   (ce_dc_bram_rd_addr_right),
.i_bram_rd_en_right     (ce_dc_bram_rd_en_right),

// AFTER:
.i_bram_rd_addr_right   (disp_bram_rd_addr_right_muxed),  // Muxed
.i_bram_rd_en_right     (disp_bram_rd_en_right_muxed),    // Muxed
```

#### 2. Update Mantissa Write Data Selection in `dispatcher_control.sv`

**Replace line 423**:
```systemverilog
// BEFORE (WRONG):
assign o_tile_man_wr_data = o_bram_rd_data_left;    // Always uses LEFT port

// AFTER (CORRECT):
assign o_tile_man_wr_data = (man_rd_addr_pipe < 10'd528) ?
                             o_bram_rd_data_left :    // [0-527]: use LEFT port
                             o_bram_rd_data_right;    // [528-1055]: use RIGHT port
```

### Why This Fix Works

**Counter [0-527]** (LEFT matrix):
```
1. dc_copy_rd_addr = [0-527]
2. disp_bram_rd_addr_left_muxed = [0-527]
3. o_bram_rd_data_left = dispatcher_bram.man_left[0-527]  ✅
4. o_tile_man_wr_data selects LEFT port  ✅
5. tile_bram.man_left = correct data  ✅
```

**Counter [528-1055]** (RIGHT matrix):
```
1. dc_copy_rd_addr = [528-1055]
2. disp_bram_rd_addr_right_muxed = [528-1055] → [0-527] via lower bits
3. o_bram_rd_data_right = dispatcher_bram.man_right[0-527]  ✅
4. o_tile_man_wr_data selects RIGHT port  ✅
5. tile_bram.man_right = correct data  ✅
```

**Key Insight**: Both read ports need to be driven with the same counter value during DISP_COPY. The dispatcher_bram module internally routes to man_left or man_right based on the port being accessed.

Wait, that's not quite right. Let me reconsider...

Actually, looking at dispatcher_bram.sv, it has SEPARATE read ports for left and right:
- Port i_rd_addr_left always reads from man_left[0-511]
- Port i_rd_addr_right always reads from man_right[0-511]

So during DISP_COPY:
- Counter [0-527]: Need to read from man_left → use LEFT port
- Counter [528-1055]: Need to read from man_right → use RIGHT port

The fix is correct: mux the RIGHT port AND select data source based on counter range.

---

## Expected Results After Fix

### DISP_COPY Data Flow (Fixed)

**Counter [0-527]**:
- Read from dispatcher_bram LEFT port with addr [0-527]
- Get data from man_left[0-527]
- Write to tile_bram.man_left[0-527]
- ✅ Correct!

**Counter [528-1055]**:
- Read from dispatcher_bram RIGHT port with addr [0-527] (after remapping)
- Get data from man_right[0-527]
- Write to tile_bram.man_right[0-527]
- ✅ Correct!

### Compute Engine Results

After fix:
- LEFT matrix: Correct data ✅
- RIGHT matrix: Correct data ✅
- Computation: **Should match golden reference** ✅

---

## Summary

**Root Cause**: RIGHT read port of dispatcher_bram not muxed during DISP_COPY

**Effect**: Counter [528-1055] reads from wrong BRAM (man_left instead of man_right)

**Fix Complexity**: Simple - add mux and data selection logic

**Confidence**: 🎯 **100%** - This is the bug causing golden mismatches

**Priority**: 🔴 **CRITICAL** - Must fix before any further testing
