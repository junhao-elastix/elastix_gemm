# Parallel 4-Path Architecture Fix Plan

**Date**: Mon Oct 27, 2025
**Severity**: 🔴 **CRITICAL** - Architecture doesn't match specification
**Reference**: `/home/dev/Dev/elastix_gemm/gemm/SINGLE_ROW_REFERENCE.md` lines 240-260

---

## Executive Summary

**Problem**: Current implementation uses interleaved writes (1024 cycles) instead of parallel 4-path writes (512 cycles)

**Root Cause**: tile_bram has single write port with target selection, forcing sequential writes

**Impact**:
- Wrong architecture (doesn't match spec)
- 2× slower than specified (1024 vs 512 cycles)
- Likely cause of golden mismatches

---

## Specification Requirements

### From SINGLE_ROW_REFERENCE.md Lines 240-260

```systemverilog
// Four Parallel Data Paths
// CRITICAL: All four paths operate simultaneously in the same clock cycle!

// Left Matrix Paths (2 parallel)
exp_left_aligned[0-511]  ↔  tile_bram_left.exp[0-511]   (8-bit exponents)
man_left[0-511]          ↔  tile_bram_left.man[0-511]   (256-bit mantissas)

// Right Matrix Paths (2 parallel)
exp_right_aligned[0-511] ↔  tile_bram_right.exp[0-511]  (8-bit exponents)
man_right[0-511]         ↔  tile_bram_right.man[0-511]  (256-bit mantissas)
```

**During DISPATCH:**
- All four paths read/write in lockstep
- **Single address counter drives all four read addresses**
- **Single write address drives all four write addresses**
- Enables maximum bandwidth utilization (4 × 256-bit + 4 × 8-bit per cycle)

**Duration**: 512 cycles (counter [0-511])

---

## Current Implementation (WRONG)

### tile_bram.sv - Single Write Port

```systemverilog
// CURRENT (WRONG): Single write port with target selection
input  logic                   i_man_wr_en,
input  logic                   i_man_wr_target,     // 0=left, 1=right
input  logic [ADDR_WIDTH-1:0]  i_man_wr_addr,       // 9-bit [0-511]
input  logic [DATA_WIDTH-1:0]  i_man_wr_data,       // 256-bit

always_ff @(posedge i_clk) begin
    if (i_man_wr_en) begin
        if (i_man_wr_target == 1'b0)
            man_left[i_man_wr_addr] <= i_man_wr_data;    // Cycle N
        else
            man_right[i_man_wr_addr] <= i_man_wr_data;   // Cycle N+1
    end
end
```

**Problem**: Can only write to ONE side per cycle, forcing interleaved writes

### dispatcher_control.sv - Interleaved Addressing

```systemverilog
// CURRENT (WRONG): Counter [0-1023] with LSB selecting side
if (!disp_copy_man_done_reg && disp_copy_man_cnt_reg < 1024) begin
    disp_copy_man_cnt_reg <= disp_copy_man_cnt_reg + 1;
    ...
end

assign o_tile_man_wr_target = man_rd_addr_pipe[0];      // LSB selects side
assign o_tile_man_wr_addr   = man_rd_addr_pipe[9:1];    // [9:1] = address
assign o_tile_man_wr_data   = man_rd_addr_pipe[0] ?
                              o_bram_rd_data_right : o_bram_rd_data_left;
```

**Problem**:
- Even cycles write left, odd cycles write right
- Takes 1024 cycles to copy 512 lines to each side
- Violates spec: "single address counter drives all four read addresses"

### engine_top.sv - Single Connection

```systemverilog
// CURRENT (WRONG): Single write port connection
.i_man_wr_target    (dc_tile_man_wr_target),
.i_man_wr_addr      (dc_tile_man_wr_addr),
.i_man_wr_data      (dc_tile_man_wr_data),
.i_man_wr_en        (dc_tile_man_wr_en),
```

**Problem**: Only connects single write path, can't support parallel writes

---

## Required Architecture Changes

### 1. tile_bram.sv - Four Separate Write Ports

```systemverilog
// REQUIRED: Four independent write ports operating in PARALLEL

module tile_bram #(
    parameter DATA_WIDTH = 256,
    parameter ADDR_WIDTH = 9,
    parameter DEPTH = 512
) (
    input  logic i_clk,
    input  logic i_rst_n,

    // ========== FOUR PARALLEL WRITE PORTS (FROM DISPATCHER) ==========
    // Left mantissa write port
    input  logic                   i_man_left_wr_en,
    input  logic [ADDR_WIDTH-1:0]  i_man_left_wr_addr,
    input  logic [DATA_WIDTH-1:0]  i_man_left_wr_data,

    // Right mantissa write port
    input  logic                   i_man_right_wr_en,
    input  logic [ADDR_WIDTH-1:0]  i_man_right_wr_addr,
    input  logic [DATA_WIDTH-1:0]  i_man_right_wr_data,

    // Left exponent write port
    input  logic                   i_exp_left_wr_en,
    input  logic [ADDR_WIDTH-1:0]  i_exp_left_wr_addr,
    input  logic [7:0]             i_exp_left_wr_data,

    // Right exponent write port
    input  logic                   i_exp_right_wr_en,
    input  logic [ADDR_WIDTH-1:0]  i_exp_right_wr_addr,
    input  logic [7:0]             i_exp_right_wr_data,

    // ... (read ports remain unchanged)
);

// Four separate BRAM arrays
logic [DATA_WIDTH-1:0] man_left [0:DEPTH-1];
logic [DATA_WIDTH-1:0] man_right [0:DEPTH-1];
logic [7:0] exp_left [0:DEPTH-1];
logic [7:0] exp_right [0:DEPTH-1];

// PARALLEL write logic (all can execute in same cycle)
always_ff @(posedge i_clk) begin
    if (i_man_left_wr_en)
        man_left[i_man_left_wr_addr] <= i_man_left_wr_data;

    if (i_man_right_wr_en)
        man_right[i_man_right_wr_addr] <= i_man_right_wr_data;

    if (i_exp_left_wr_en)
        exp_left[i_exp_left_wr_addr] <= i_exp_left_wr_data;

    if (i_exp_right_wr_en)
        exp_right[i_exp_right_wr_addr] <= i_exp_right_wr_data;
end

endmodule
```

**Key Change**: Four separate write ports can ALL be active in same cycle

### 2. dispatcher_control.sv - Parallel Outputs

```systemverilog
// REQUIRED: Single counter [0-511] driving four parallel outputs

// Counter: Single address for all four paths
logic [9:0] disp_copy_cnt_reg;  // 10-bit for [0-511]

always_ff @(posedge i_clk) begin
    if (state_reg == ST_DISP_COPY) begin
        if (disp_copy_cnt_reg < 512) begin
            disp_copy_cnt_reg <= disp_copy_cnt_reg + 1;
            if (disp_copy_cnt_reg == 511) begin
                disp_copy_done_reg <= 1'b1;
            end
        end
    end
end

// Pipeline the counter for timing
logic [9:0] copy_addr_pipe;
always_ff @(posedge i_clk) begin
    copy_addr_pipe <= disp_copy_cnt_reg;
end

// FOUR PARALLEL MANTISSA OUTPUTS (all driven by same address)
assign o_tile_man_left_wr_addr  = copy_addr_pipe[8:0];
assign o_tile_man_left_wr_data  = o_bram_rd_data_left;
assign o_tile_man_left_wr_en    = copy_active_pipe && !disp_copy_done_reg;

assign o_tile_man_right_wr_addr = copy_addr_pipe[8:0];
assign o_tile_man_right_wr_data = o_bram_rd_data_right;
assign o_tile_man_right_wr_en   = copy_active_pipe && !disp_copy_done_reg;

// FOUR PARALLEL EXPONENT OUTPUTS (all driven by same address)
assign o_tile_exp_left_wr_addr  = copy_addr_pipe[8:0];
assign o_tile_exp_left_wr_data  = o_left_exp_rd_data;
assign o_tile_exp_left_wr_en    = copy_active_pipe && !disp_copy_done_reg;

assign o_tile_exp_right_wr_addr = copy_addr_pipe[8:0];
assign o_tile_exp_right_wr_data = o_right_exp_rd_data;
assign o_tile_exp_right_wr_en   = copy_active_pipe && !disp_copy_done_reg;
```

**Key Changes**:
- Single counter [0-511] (not [0-1023])
- Four separate write enable/address/data outputs
- All use same address in same cycle
- Duration: 512 cycles

### 3. engine_top.sv - Four Parallel Connections

```systemverilog
// REQUIRED: Four parallel connections from dispatcher to tile_bram

// Signals from dispatcher_control
logic [8:0]  dc_tile_man_left_wr_addr;
logic [255:0] dc_tile_man_left_wr_data;
logic        dc_tile_man_left_wr_en;

logic [8:0]  dc_tile_man_right_wr_addr;
logic [255:0] dc_tile_man_right_wr_data;
logic        dc_tile_man_right_wr_en;

logic [8:0]  dc_tile_exp_left_wr_addr;
logic [7:0]  dc_tile_exp_left_wr_data;
logic        dc_tile_exp_left_wr_en;

logic [8:0]  dc_tile_exp_right_wr_addr;
logic [7:0]  dc_tile_exp_right_wr_data;
logic        dc_tile_exp_right_wr_en;

// Connect to tile_bram
tile_bram u_tile_bram (
    .i_clk(i_clk),
    .i_rst_n(i_rst_n),

    // Four parallel write ports
    .i_man_left_wr_addr   (dc_tile_man_left_wr_addr),
    .i_man_left_wr_data   (dc_tile_man_left_wr_data),
    .i_man_left_wr_en     (dc_tile_man_left_wr_en),

    .i_man_right_wr_addr  (dc_tile_man_right_wr_addr),
    .i_man_right_wr_data  (dc_tile_man_right_wr_data),
    .i_man_right_wr_en    (dc_tile_man_right_wr_en),

    .i_exp_left_wr_addr   (dc_tile_exp_left_wr_addr),
    .i_exp_left_wr_data   (dc_tile_exp_left_wr_data),
    .i_exp_left_wr_en     (dc_tile_exp_left_wr_en),

    .i_exp_right_wr_addr  (dc_tile_exp_right_wr_addr),
    .i_exp_right_wr_data  (dc_tile_exp_right_wr_data),
    .i_exp_right_wr_en    (dc_tile_exp_right_wr_en),

    // ... (read ports remain unchanged)
);
```

**Key Change**: Four separate signal paths for parallel writes

---

## Implementation Plan

### Step 1: Fix tile_bram.sv
- Add four separate write ports
- Remove target selection logic
- Verify all four ports can write in same cycle

### Step 2: Fix dispatcher_control.sv
- Change counter from [0-1023] to [0-511]
- Add four parallel output assignments
- All outputs use same address
- Remove interleaved addressing logic

### Step 3: Fix engine_top.sv
- Add four signal declarations
- Connect all four paths to tile_bram
- Update dispatcher_control instantiation with four outputs

### Step 4: Verify
- Simulation: Check DISP_COPY completes in ~512 cycles
- Simulation: Verify all four BRAMs get correct data
- Check golden results match

---

## Expected Results After Fix

### DISP_COPY Timing
```
Cycle    Action
-----    ------
0        Counter=0: Write all 4 BRAMs at address 0
1        Counter=1: Write all 4 BRAMs at address 1
2        Counter=2: Write all 4 BRAMs at address 2
...
511      Counter=511: Write all 4 BRAMs at address 511
512      DONE signal, return to IDLE
```

**Duration**: 512 cycles (vs. current 1024 cycles)

### Data Flow Verification
```
dispatcher_bram.exp_left[0]    →  tile_bram.exp_left[0]   ✅ Cycle 0
dispatcher_bram.man_left[0]    →  tile_bram.man_left[0]   ✅ Cycle 0
dispatcher_bram.exp_right[0]   →  tile_bram.exp_right[0]  ✅ Cycle 0
dispatcher_bram.man_right[0]   →  tile_bram.man_right[0]  ✅ Cycle 0

(All four transfers happen in SAME cycle!)
```

---

## Validation Checklist

After implementing fixes:

1. ✅ tile_bram has four independent write ports
2. ✅ dispatcher_control uses single counter [0-511]
3. ✅ All four outputs driven by same address
4. ✅ engine_top connects four parallel paths
5. ✅ Simulation shows 512-cycle DISP_COPY duration
6. ✅ All four BRAMs receive correct data
7. ✅ No synthesis warnings about unconnected ports
8. ✅ B1_C1_V1 test matches golden reference

---

## Summary

**Current**: Interleaved writes, 1024 cycles, wrong architecture
**Required**: Parallel 4-path writes, 512 cycles, per specification
**Benefit**: 2× faster, matches spec, should fix golden mismatches

**Critical**: This is not an optimization - it's a correctness fix. The current architecture fundamentally doesn't match the specification.
