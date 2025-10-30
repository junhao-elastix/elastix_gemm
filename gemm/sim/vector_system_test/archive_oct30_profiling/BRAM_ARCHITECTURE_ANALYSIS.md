# BRAM Architecture Analysis - Depth and Width Verification

**Date**: Mon Oct 27, 2025
**Purpose**: Verify BRAM specifications match requirements: 512 deep, 256-bit mantissa, 8-bit exponent

---

## Summary: ⚠️ **WIDTH MISMATCHES FOUND**

**Critical Issues**:
1. ✅ BRAM depths are correct (512 per side)
2. ✅ BRAM widths are correct (256-bit mantissa, 8-bit exp)
3. ⚠️ **Port width mismatches** between modules

---

## dispatcher_bram.sv Analysis

### Module Parameters ✅
```systemverilog
module dispatcher_bram #(
    parameter DATA_WIDTH = 256,          // ✅ Correct: 256-bit mantissas
    parameter EXP_PACKED_DEPTH = 16,     // ✅ Correct: 16 lines for packed exponents
    parameter EXP_ALIGNED_DEPTH = 512,   // ✅ Correct: 512 exponents per side
    parameter MANTISSA_DEPTH = 512,      // ✅ Correct: 512 lines per side
    parameter ADDR_WIDTH = 9             // ✅ Correct: 9-bit for 512 entries
)
```

### Array Declarations ✅
```systemverilog
// LEFT SIDE
logic [DATA_WIDTH-1:0] exp_left_packed [0:15];           // 256×16 ✅
logic [7:0] exp_left_aligned [0:511];                    // 8×512 ✅
logic [DATA_WIDTH-1:0] man_left [0:511];                 // 256×512 ✅

// RIGHT SIDE
logic [DATA_WIDTH-1:0] exp_right_packed [0:15];          // 256×16 ✅
logic [7:0] exp_right_aligned [0:511];                   // 8×512 ✅
logic [DATA_WIDTH-1:0] man_right [0:511];                // 256×512 ✅
```

**Result**: All arrays match spec exactly! ✅

### Port Definitions ✅
```systemverilog
// Write ports
input  wire [ADDR_WIDTH-1:0]    i_wr_addr,              // 9-bit ✅
input  wire [DATA_WIDTH-1:0]    i_wr_data,              // 256-bit ✅
input  wire [7:0]               i_left_exp_aligned_wr_data,   // 8-bit ✅
input  wire [7:0]               i_right_exp_aligned_wr_data,  // 8-bit ✅

// Read ports (mantissas)
input  wire [8:0]               i_rd_addr_left,          // 9-bit ✅
output wire [DATA_WIDTH-1:0]    o_rd_data_left,          // 256-bit ✅
input  wire [8:0]               i_rd_addr_right,         // 9-bit ✅
output wire [DATA_WIDTH-1:0]    o_rd_data_right,         // 256-bit ✅

// Read ports (exponents)
input  wire [8:0]               i_left_exp_rd_addr,      // 9-bit ✅
output wire [7:0]               o_left_exp_rd_data,      // 8-bit ✅
input  wire [8:0]               i_right_exp_rd_addr,     // 9-bit ✅
output wire [7:0]               o_right_exp_rd_data,     // 8-bit ✅
```

**Result**: All port widths correct! ✅

### Write Logic Analysis
```systemverilog
always_ff @(posedge i_clk) begin
    if (i_wr_en) begin
        // Address [0-15]: Write to exp_packed (using lower 4 bits)
        if (i_wr_addr < 11'd16) begin
            if (i_wr_target == 1'b0)
                exp_left_packed[i_wr_addr[3:0]] <= i_wr_data;   // ✅
            else
                exp_right_packed[i_wr_addr[3:0]] <= i_wr_data;  // ✅
        end
        // Address [16-527]: Write to mantissa (subtract 16, use lower 9 bits)
        else if (i_wr_addr >= 11'd16 && i_wr_addr < 11'd528) begin
            if (i_wr_target == 1'b0)
                man_left[i_wr_addr[8:0] - 9'd16] <= i_wr_data;    // ✅
            else
                man_right[i_wr_addr[8:0] - 9'd16] <= i_wr_data;   // ✅
        end
    end
end
```

**Address Mapping**:
- Input addr [0-15] → exp_packed[0-15] ✅
- Input addr [16-527] → man[0-511] (via subtraction) ✅
- Uses lower bits for indexing (handles width gracefully) ✅

**Result**: Write logic correct! ✅

---

## dispatcher_control.sv Analysis

### Module Parameters ⚠️
```systemverilog
module dispatcher_control #(
    parameter TGT_DATA_WIDTH = 256,      // ✅ Correct
    parameter AXI_ADDR_WIDTH = 42,       // ✅ Correct for GDDR6
    parameter BRAM_DEPTH = 2048,         // ⚠️ NOT USED - just documentation
    parameter [8:0] GDDR6_PAGE_ID = 9'd2 // ✅ Correct
)
```

**Note**: `BRAM_DEPTH = 2048` parameter is **not used** in actual logic. It's just documentation comment explaining total capacity (left 528 + right 528 = 1056, rounded to 2048).

### Port Definitions ⚠️
```systemverilog
// Mantissa read ports (from compute engine)
input  logic [10:0]                  i_bram_rd_addr_left,     // ⚠️ 11-bit
output logic [TGT_DATA_WIDTH-1:0]    o_bram_rd_data_left,     // ✅ 256-bit
input  logic [10:0]                  i_bram_rd_addr_right,    // ⚠️ 11-bit
output logic [TGT_DATA_WIDTH-1:0]    o_bram_rd_data_right,    // ✅ 256-bit

// Exponent read ports
input  logic [8:0]                   i_left_exp_rd_addr,      // ✅ 9-bit
output logic [7:0]                   o_left_exp_rd_data,      // ✅ 8-bit
input  logic [8:0]                   i_right_exp_rd_addr,     // ✅ 9-bit
output logic [7:0]                   o_right_exp_rd_data,     // ✅ 8-bit
```

**Issue**: Mantissa read addresses are **11-bit** but should be **9-bit** to match dispatcher_bram!

### dispatcher_bram Instantiation ⚠️
```systemverilog
dispatcher_bram #(
    .DATA_WIDTH          (TGT_DATA_WIDTH),    // ✅ 256
    .EXP_PACKED_DEPTH    (16),                // ✅ 16
    .EXP_ALIGNED_DEPTH   (512),               // ✅ 512
    .MANTISSA_DEPTH      (512),               // ✅ 512
    .ADDR_WIDTH          (11)                 // ⚠️ WRONG! Should be 9
) u_dispatcher_bram (
    // Write ports
    .i_wr_addr          (bram_wr_addr_reg),   // Signal is 11-bit

    // Read ports (mantissas) - WIDTH MISMATCH!
    .i_rd_addr_left     (i_bram_rd_addr_left),   // ⚠️ Passing 11-bit to 9-bit port
    .i_rd_addr_right    (i_bram_rd_addr_right),  // ⚠️ Passing 11-bit to 9-bit port

    // Read ports (exponents) - CORRECT
    .i_left_exp_rd_addr  (i_left_exp_rd_addr),   // ✅ 9-bit to 9-bit
    .i_right_exp_rd_addr (i_right_exp_rd_addr),  // ✅ 9-bit to 9-bit
);
```

**Critical Issue**: Port width mismatch!
- dispatcher_control passes 11-bit addresses
- dispatcher_bram expects 9-bit addresses
- SystemVerilog will **truncate** upper 2 bits

---

## Impact Analysis

### What Works (By Accident) ✅

**Write Operations**:
- FETCH writes addresses [0-527] to either left or right
- dispatcher_bram write logic uses `i_wr_addr[8:0]` (takes lower 9 bits)
- Even with 11-bit parameter, logic extracts correct bits
- **Result**: Writes work correctly ✅

**Read Operations**:
- Compute engine provides addresses [0-511] (within 9-bit range)
- Upper 2 bits are always 0 for valid addresses
- Truncation doesn't affect correct operation (for now)
- **Result**: Reads work correctly ✅

### Why It's Still Wrong ⚠️

1. **Design Intent Mismatch**:
   - Code suggests 11-bit addressing (2048 entries)
   - Hardware implements 9-bit addressing (512 entries per side)
   - Confusing for maintenance and debugging

2. **Latent Bug Risk**:
   - If compute engine ever generates address > 511, upper bits silently lost
   - No synthesis warning (width truncation is legal in SV)
   - Potential for hard-to-debug issues

3. **Simulation Mismatch**:
   - Linter warnings about width mismatch
   - Reduces confidence in verification

---

## Root Cause

**Historical Context**: The 11-bit addressing was likely intended for:
- Original architecture: Single sequential 1024-entry BRAM
- Addresses: [0-1023] for left+right combined

**Current Architecture**: Separate left/right BRAMs
- Each side: 512 entries (9-bit addressing)
- No need for 11-bit addresses

**Conclusion**: Code not fully updated after architectural change.

---

## Recommended Fixes

### Fix 1: Update dispatcher_control.sv Ports

**Change input port widths from 11-bit to 9-bit**:
```systemverilog
// BEFORE (WRONG):
input  logic [10:0]  i_bram_rd_addr_left,
input  logic [10:0]  i_bram_rd_addr_right,

// AFTER (CORRECT):
input  logic [8:0]   i_bram_rd_addr_left,     // 9-bit: [0:511]
input  logic [8:0]   i_bram_rd_addr_right,    // 9-bit: [0:511]
```

### Fix 2: Update dispatcher_bram Instantiation

**Change ADDR_WIDTH parameter from 11 to 9**:
```systemverilog
// BEFORE (WRONG):
dispatcher_bram #(
    .ADDR_WIDTH          (11)   // ⚠️

// AFTER (CORRECT):
dispatcher_bram #(
    .ADDR_WIDTH          (9)    // ✅
```

### Fix 3: Update Internal Signals

**Update bram_wr_addr_reg width**:
```systemverilog
// Find declaration and change from:
logic [10:0] bram_wr_addr_reg;    // ⚠️

// To:
logic [8:0] bram_wr_addr_reg;     // ✅
```

### Fix 4: Update engine_top.sv Connections

**Check and fix signal widths in engine_top.sv**:
```systemverilog
// Signals connecting dispatcher_control to dispatcher_bram should be 9-bit
logic [8:0]  dc_disp_bram_rd_addr_left;   // Not [10:0]
logic [8:0]  dc_disp_bram_rd_addr_right;  // Not [10:0]
```

---

## Verification Checklist

After fixes, verify:

1. ✅ All BRAM arrays are 512 deep (per side)
2. ✅ All mantissa data paths are 256-bit
3. ✅ All exponent data paths are 8-bit
4. ✅ All address paths are 9-bit (0-511 range)
5. ✅ No synthesis warnings about width truncation
6. ✅ Simulation logs show correct address ranges

---

## Current Status: Functional But Not Clean

**Bottom Line**:
- ✅ Hardware works correctly (by accident)
- ⚠️ Code has width mismatches
- ⚠️ Design intent unclear
- ✅ BRAM depths and widths are correct

**Recommendation**: Fix the width mismatches for code cleanliness and maintainability, even though current functionality is correct.
