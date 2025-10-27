# Dispatcher 3-Buffer Architecture - Specification & Implementation Plan

**Date**: October 13, 2025  
**Status**: READY FOR IMPLEMENTATION  

---

## Architecture Overview

The dispatcher fetches data from GDDR6 in memory blocks and unpacks them into aligned buffers for the compute engine.

### Memory Block Structure

Each memory block from GDDR6 is **528 lines**:
- **Lines 0-15**: Packed exponents (16 lines × 256 bits)
  - 32 exponents per line × 8 bits = 256 bits
  - Total: 512 exponents (128 native vectors × 4 groups)
- **Lines 16-527**: Mantissa groups (512 lines × 256 bits)
  - One line = one group of 32 GFP8 mantissas
  - 4 lines = 1 native vector (4 groups)
  - 512 lines = 128 native vectors

### Three-Buffer Architecture (Per Side)

Each side (left/right) has **3 buffers**:

1. **`exp_packed`**: 256-bit × 16 (staging for packed exponents)
   - Stores raw exponent data from GDDR6 lines 0-15
   - 32 exponents per line, packed byte-aligned

2. **`exp_aligned`**: 8-bit × 512 (unpacked, one exp per group)
   - One exponent per mantissa group
   - Aligned: exp_aligned[i] corresponds to man[i]
   - Filled during mantissa fetch (parallel unpacking)

3. **`man`**: 256-bit × 512 (mantissas, one group per line)
   - One 256-bit line per group
   - 4 consecutive lines = 1 native vector

### FETCH Operation Flow

**Step 1: Read Exponents (16 cycles)**
- Read lines 0-15 from GDDR6
- Store in exp_packed buffer
- Cannot stall AXI burst

**Step 2: Read Mantissas + Unpack Exponents (512 cycles, parallel)**
- Read lines 16-527 from GDDR6
- Store in man buffer (indices 0-511)
- **Simultaneously**: Unpack exp_packed → exp_aligned
  - Each mantissa line read → unpack one exponent
  - After 512 cycles: all exponents unpacked and aligned

**Result**: No extra latency! Unpacking happens during mantissa fetch.

### Four Output Ports

Dispatcher BRAM provides **4 read ports** to compute engine:
1. `left_exp` (8-bit): From exp_left_aligned
2. `left_man` (256-bit): From man_left  
3. `right_exp` (8-bit): From exp_right_aligned
4. `right_man` (256-bit): From man_right

### Address Mapping

**Unified Addressing**: addr = (nv_idx × 4) + g_idx
- nv_idx = b_idx × V + v_idx (for left: b_idx, for right: c_idx)
- g_idx = group index [0-3]
- Address range: [0-511]
- **No base offsets**, **no +16 adjustment**

---

## Implementation Summary

**Key Changes:**
1. Add left/right indicator to FETCH command (1 bit from reserved field)
2. Implement 6 buffers total: 3 per side (exp_packed, exp_aligned, man)
3. Unpack exponents in parallel with mantissa fetch (no extra latency)
4. Separate left/right mantissa buffers
5. Use unified addressing: (nv_idx)*4 + g_idx, no base addresses

---

## File-by-File Changes

### 1. `src/include/gemm_pkg.sv`

**Purpose**: Add left/right bit to FETCH command structure

**Change**:
```systemverilog
// BEFORE (line 99-103):
typedef struct packed {
    logic [15:0]                   reserved;
    logic [link_len_width_gp-1:0]  len;
    logic [link_addr_width_gp-1:0] start_addr;
} cmd_fetch_s;

// AFTER:
typedef struct packed {
    logic [14:0]                   reserved;    // Reduced from 16 to 15 bits
    logic                          fetch_right; // 0=left, 1=right
    logic [link_len_width_gp-1:0]  len;
    logic [link_addr_width_gp-1:0] start_addr;
} cmd_fetch_s;
```

**Rationale**: Use 1 bit from reserved field to indicate fetch target

---

### 2. `src/rtl/dispatcher_bram.sv`

**Purpose**: Implement 6-buffer architecture (3 per side)

**Current State**: Has single bram_array[2048] OR incorrectly split mantissa buffers

**Target Architecture**:
```systemverilog
// Left side (3 buffers)
logic [255:0] exp_left_packed [0:15];      // Staging: 256-bit x 16
logic [7:0]   exp_left_aligned [0:511];    // Unpacked: 8-bit x 512
logic [255:0] man_left [0:511];            // Mantissas: 256-bit x 512

// Right side (3 buffers)
logic [255:0] exp_right_packed [0:15];     // Staging: 256-bit x 16
logic [7:0]   exp_right_aligned [0:511];   // Unpacked: 8-bit x 512
logic [255:0] man_right [0:511];           // Mantissas: 256-bit x 512
```

**Write Ports** (from dispatcher_control):
- `i_wr_addr[10:0]`: 11-bit address
- `i_wr_data[255:0]`: 256-bit data
- `i_wr_en`: Write enable
- `i_wr_target`: 0=left, 1=right (NEW)

**Address Decode for Writes**:
- Lines [0-15]: Write to exp_{left/right}_packed[addr]
- Lines [16-527]: Write to man_{left/right}[addr-16]

**Read Ports** (to compute engine):
- `o_left_exp[7:0]`: From exp_left_aligned
- `o_rd_data_left[255:0]`: From man_left
- `o_right_exp[7:0]`: From exp_right_aligned
- `o_rd_data_right[255:0]`: From man_right

**Read Address**: [0-511] direct indexing, no offsets

---

### 3. `src/rtl/dispatcher_control.sv`

**Purpose**: Implement parallel exponent unpacking during mantissa fetch

**New Inputs**:
- Add `i_fetch_target` (1-bit, from FETCH command)

**State Machine Updates**:

**Current Flow**:
1. ST_FETCH_INIT → ST_FETCH_READ → ST_FETCH_WAIT → ST_FETCH_DONE
2. ST_UNPACK_EXP (separate phase after fetch)
3. ST_IDLE

**New Flow**:
1. ST_FETCH_INIT → ST_FETCH_READ_EXP (read 16 exp lines)
2. ST_FETCH_READ_MAN (read 512 mantissa lines + unpack in parallel)
3. ST_FETCH_DONE → ST_IDLE

**Parallel Unpacking Logic** (during ST_FETCH_READ_MAN):
```systemverilog
// Counter for mantissa lines read: 0-511
logic [9:0] man_line_count;

// During each mantissa line write:
if (state_reg == ST_FETCH_READ_MAN && axi_ddr_if.rvalid) begin
    // Write mantissa line
    bram_wr_addr_reg <= 16 + man_line_count;
    bram_wr_data_reg <= axi_ddr_if.rdata;
    bram_wr_en_reg <= 1'b1;
    bram_wr_target <= i_fetch_target;
    
    // Simultaneously unpack one exponent
    // Read from exp_packed[man_line_count / 32]
    // Extract byte [man_line_count % 32]
    // Write to exp_aligned[man_line_count]
    exp_unpack_idx <= man_line_count;
    exp_unpack_en <= 1'b1;
    
    man_line_count <= man_line_count + 1;
end
```

**Remove**: Old ST_UNPACK_EXP state (no longer needed)

---

### 4. `src/rtl/master_control.sv`

**Purpose**: Extract and pass fetch_right bit to dispatcher_control

**Changes**:
```systemverilog
// Add output
output logic o_dc_fetch_target,

// In ST_EXEC_FETCH:
cmd_fetch_s fetch_cmd;
fetch_cmd = {payload_word2_reg[15:0], payload_word1_reg};

o_dc_fetch_addr <= fetch_cmd.start_addr;
o_dc_fetch_len  <= fetch_cmd.len;
o_dc_fetch_target <= fetch_cmd.fetch_right;  // NEW
```

---

### 5. `src/rtl/gfp8_bcv_controller.sv`

**Purpose**: Update addressing for separate buffers with no base offset

**Current Addressing** (WRONG):
```systemverilog
left_addr = (nv_idx * 4 + g_idx) + 16;   // +16 offset
right_addr = (nv_idx * 4 + g_idx) + 16;  // Same address!
```

**New Addressing** (CORRECT):
```systemverilog
// Both use same formula, but read from separate BRAMs
addr = (nv_idx * 4 + g_idx);  // 0-511, no offset
// where nv_idx = b_idx * dim_V + v_idx

// Left reads from man_left[addr]
// Right reads from man_right[addr]
```

**Remove**:
- `left_base_reg` and `right_base_reg` (no longer needed)
- `+16` offset in all mantissa address calculations

**Keep**:
- Unified addressing formula
- Exponent address calculation (already correct)

---

### 6. `src/rtl/engine_top.sv`

**Purpose**: Wire through fetch_target signal

**Changes**:
```systemverilog
logic dc_fetch_target;

// master_control instantiation:
.o_dc_fetch_target (dc_fetch_target),

// dispatcher_control instantiation:
.i_fetch_target (dc_fetch_target),
```

---

### 7. `sim/vector_system_test/tb_engine_top.sv`

**Purpose**: Update FETCH command generation to set left/right bit

**Current** (line ~460):
```systemverilog
task automatic generate_fetch_command(
    input logic [7:0] id,
    input logic [link_addr_width_gp-1:0] start_addr,
    input logic [link_len_width_gp-1:0] num_lines,
    output logic [31:0] cmd [0:3]
);
```

**Add Parameter**:
```systemverilog
task automatic generate_fetch_command(
    input logic [7:0] id,
    input logic [link_addr_width_gp-1:0] start_addr,
    input logic [link_len_width_gp-1:0] num_lines,
    input logic fetch_right,  // NEW: 0=left, 1=right
    output logic [31:0] cmd [0:3]
);
    cmd_fetch_s payload;
    payload.start_addr = start_addr;
    payload.len = num_lines;
    payload.fetch_right = fetch_right;  // NEW
    payload.reserved = '0;
    // ... rest of packing
endtask
```

**Update Calls**:
```systemverilog
// Line ~407:
generate_fetch_command(0, 0, 528, 1'b0, fetch_left_cmd);  // fetch_right=0 (left)

// Line ~416:
generate_fetch_command(1, 528, 528, 1'b1, fetch_right_cmd);  // fetch_right=1 (right)
```

---

## Implementation Order

1. **gemm_pkg.sv**: Add fetch_right bit to cmd_fetch_s
2. **master_control.sv**: Extract and output fetch_target
3. **engine_top.sv**: Wire fetch_target signal
4. **dispatcher_bram.sv**: Implement 6-buffer architecture
5. **dispatcher_control.sv**: Implement parallel unpacking
6. **gfp8_bcv_controller.sv**: Remove base addresses, use 0-511 indexing
7. **tb_engine_top.sv**: Update test command generation
8. **Compile and test**: Run simulation

---

## Expected Behavior After Implementation

**FETCH LEFT** (fetch_right=0):
- Reads 528 lines from GDDR6
- Lines 0-15 → exp_left_packed
- Lines 16-527 → man_left (at indices 0-511)
- During write: unpack exp_left_packed → exp_left_aligned

**FETCH RIGHT** (fetch_right=1):
- Reads 528 lines from GDDR6
- Lines 0-15 → exp_right_packed
- Lines 16-527 → man_right (at indices 0-511)
- During write: unpack exp_right_packed → exp_right_aligned

**TILE Operation**:
- BCV calculates: addr = (b_idx*V + v_idx)*4 + g_idx
- Reads man_left[addr] and exp_left_aligned[addr] for left
- Reads man_right[addr] and exp_right_aligned[addr] for right
- **Different data** from separate buffers!

---

## Verification Points

1. **Left/Right Separation**: Verify man_left and man_right contain different data
2. **No +16 Offset**: Verify BCV reads from address 0+ (not 16+)
3. **Parallel Unpacking**: Verify fetch completes in 528 cycles (not 528+512)
4. **Correct Data**: Verify hardware matches golden reference

---

## Rollback Plan

If implementation fails:
1. Revert dispatcher_bram.sv to single bram_array[2048]
2. Keep gfp8_nv_dot.sv input register fix (that was correct!)
3. Fix base addresses: left_base=16, right_base=544

---

**READY TO IMPLEMENT**

