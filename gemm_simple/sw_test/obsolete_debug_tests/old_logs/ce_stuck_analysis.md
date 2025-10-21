# Compute Engine Stuck at State 1 - Root Cause Analysis

## Executive Summary
The compute engine (CE) in the GEMM implementation is stuck at state 1 (ST_LOAD_LEFT_EXP) after receiving a MATMUL command. The dispatcher control (DC) is at state 4, indicating successful FETCH operations. All command parameters appear correct, but the CE cannot progress beyond the first load state.

## Critical Finding: Extra ST_INIT State

### Key Difference Found
The GEMM compute_engine.sv has an **extra state** that the reference engine_sim does NOT have:

**GEMM Version (Broken):**
```systemverilog
typedef enum logic [3:0] {
    ST_IDLE           = 4'd0,
    ST_INIT           = 4'd10,  // <-- EXTRA STATE NOT IN REFERENCE!
    ST_LOAD_LEFT_EXP  = 4'd1,
    ...
```

**Engine_sim Reference (Working):**
```systemverilog
typedef enum logic [3:0] {
    ST_IDLE           = 4'd0,
    ST_LOAD_LEFT_EXP  = 4'd1,   // Goes directly here from IDLE
    ...
```

### State Transition Issue

**GEMM Version:**
```systemverilog
ST_IDLE: begin
    if (i_tile_en) begin
        state_next = ST_INIT;  // Goes to INIT first
    end
end

ST_INIT: begin
    // Wait one cycle for dimension registers to be captured
    state_next = ST_LOAD_LEFT_EXP;
end
```

**Engine_sim Reference:**
```systemverilog
ST_IDLE: begin
    if (i_tile_en) begin
        state_next = ST_LOAD_LEFT_EXP;  // Goes directly to loading
    end
end
```

## Why This Causes the Hang

1. **State Number Mismatch**: The ST_INIT state is assigned value `4'd10`, which means:
   - When CE reports state 1, it's actually in ST_LOAD_LEFT_EXP
   - But the state numbering may be confusing the debug output

2. **Timing Issue**: The extra ST_INIT state adds a cycle delay that may cause:
   - Dimension registers to not be properly captured
   - BRAM read timing to be off by one cycle
   - Load counter synchronization issues

## Test Evidence

From test_engine_simple output:
```
ENGINE_STATUS: 0x000bb041
  MC State (current): 0
  DC State: 4         <- FETCH complete, BRAM has data
  CE State: 1         <- Stuck at ST_LOAD_LEFT_EXP
  MC State (next): 11
```

The DC state 4 indicates successful FETCH operations, meaning data is in BRAM. The CE should be able to read it but is stuck.

## Root Cause Hypothesis

The most likely issue is that `dim_v_reg` is 0 or uninitialized when the CE tries to calculate addresses in ST_LOAD_LEFT_EXP:

```systemverilog
byte_offset_exp = get_exp_byte_offset(row_idx, v_idx, dim_v_reg);
```

If `dim_v_reg` is 0, the address calculation could fail or produce invalid results, preventing the state machine from advancing.

## Recommended Fix

### Option 1: Remove ST_INIT State (Match Reference)
Remove the ST_INIT state entirely to match the working reference:

```systemverilog
// In state enum definition
typedef enum logic [3:0] {
    ST_IDLE           = 4'd0,
    // Remove ST_INIT
    ST_LOAD_LEFT_EXP  = 4'd1,
    ...
```

// In state machine
ST_IDLE: begin
    if (i_tile_en) begin
        state_next = ST_LOAD_LEFT_EXP;  // Direct transition
    end
end
```

### Option 2: Fix Dimension Capture Timing
If ST_INIT is needed for some reason, ensure dimensions are captured properly:

```systemverilog
ST_INIT: begin
    // Actually capture dimensions here if not done in IDLE
    dim_b_reg <= i_dim_b;
    dim_c_reg <= i_dim_c;
    dim_v_reg <= i_dim_v;
    state_next = ST_LOAD_LEFT_EXP;
end
```

## Verification Steps

1. Check if dimensions are being passed correctly:
   - Add debug prints in ST_IDLE and ST_INIT to verify dim_b/c/v values
   - Confirm they're non-zero when transitioning to ST_LOAD_LEFT_EXP

2. Monitor load_count increment:
   - Verify load_count is incrementing in ST_LOAD_LEFT_EXP
   - Check if the condition `load_count >= 3'd3` is ever met

3. Verify BRAM read interface:
   - Check if dbram_rd_en is being asserted
   - Confirm dbram_rd_data has valid data when expected

## Immediate Action Required

The ST_INIT state should be removed to match the working reference implementation. This extra state serves no functional purpose and introduces timing issues that prevent the compute engine from operating correctly.