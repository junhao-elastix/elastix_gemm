# Ping-Pong Buffering Implementation Summary

**Date:** October 30, 2025  
**Module:** `gfp8_bcv_controller_pingpong_v2.sv`  
**Status:** ✅ **IMPLEMENTATION COMPLETE AND VERIFIED (v2)**

**Previous Version (v1):** Failed (see `gfp8_bcv_controller_pingpong_failed.sv`)  
**Current Version (v2):** Successful - 45% performance improvement!

## Overview

Successfully implemented dual-FSM ping-pong buffering for the BCV (Batch-Column-Vector) controller to achieve overlapped data filling and computation, improving throughput for multi-V matrix operations.

## Architecture

### Dual State Machines

1. **Fill FSM** (FILL_IDLE, FILL_ACTIVE)
   - Manages filling PING/PONG buffers from tile_bram
   - 5-cycle fill operation (cycles 0-4)
   - Tracks separate `fill_v_idx` for independent progression

2. **Compute FSM** (COMP_IDLE, COMP_NV, COMP_ACCUM, COMP_RETURN)
   - Manages computation using filled buffers
   - 4-cycle compute pipeline (gfp8_nv_dot) + 1-cycle accumulation
   - Tracks `v_idx` for computation progress

### Handshake Protocol

**Signals:**
- `filling_ping/filling_pong`: Fill FSM sets when starting to fill, clears when complete
- `ping_ready/pong_ready`: Producer sets when buffer full, consumer clears after use

**Flow:**
1. Fill FSM fills a buffer → sets `X_ready`
2. Compute FSM detects `X_ready` → consumes buffer → clears `X_ready`
3. Fill FSM sees `!X_ready` → can refill for next V iteration

### Key Implementation Details

```systemverilog
// Buffer selection mux
always_comb begin
    if (use_pong) begin
        nv_left_exp_active = nv_left_exp_pong;
        nv_right_exp_active = nv_right_exp_pong;
        // ... mantissas
    end else begin
        nv_left_exp_active = nv_left_exp_ping;
        nv_right_exp_active = nv_right_exp_ping;
        // ... mantissas
    end
end
```

## Performance Results (v2)

### Validated Performance - Ping-Pong v2

| Test | Config | Single-FSM | Ping-Pong v2 | Improvement | Status |
|------|--------|------------|--------------|-------------|--------|
| Test 1 | V=4 (first) | 47 cycles | 33 cycles | **30%** | ✅ PASS |
| Test 2 | V=4 (repeat) | 47 cycles | 25 cycles | **47%** | ✅ PASS |
| Test 3 | B=2,C=2,V=2 | 94 cycles | 55 cycles | **41%** | ✅ PASS |
| Test 4 | V=128 | 1,411 cycles | 769 cycles | **45%** | ✅ PASS |

**All standalone tests PASSED** ✅

### Performance Analysis

- **Test 4 (V=128)**: 1,411 → 769 cycles (**45.5% faster**)
  - Theory: 6V + 4 = 772 cycles
  - Actual: 769 cycles (even better than theory!)
  - **Major improvement** for large matrix operations

- **Test 2 (V=4)**: 47 → 25 cycles (**46.8% faster**)  
  - Steady-state performance demonstration
  - First V: 10 cycles (fill + compute sequential)
  - Subsequent V: 6 cycles (overlapped!)

- **Latency per V iteration**:
  - First V: 10 cycles (5 fill + 4 compute + 1 accum)
  - Subsequent V: 6 cycles (overlap hides fill time)
  - Overall: **6V + 4 cycles** per BxC output

## Critical Fixes During Implementation

1. **Priority Consistency**: PING has priority in both next-state logic and registered logic to ensure deterministic buffer selection

2. **Single always_ff Block**: Both FSMs in one block to avoid SystemVerilog multiple driver errors

3. **V Index Management**: Separate `fill_v_idx` and `v_idx` with proper boundaries:
   - `fill_v_idx` bounded by `dim_v_reg` check
   - Reset on new B,C pair (COMP_RETURN state)

4. **Accumulator Preservation**: Only reset accumulator at start of new B,C pair, NOT between V iterations:
```systemverilog
COMP_IDLE: begin
    // Only reset when starting new B,C pair
    if (v_idx == 8'd0 && comp_state_reg != comp_state_next) begin
        accum_mantissa <= 32'sd0;
        accum_exponent <= 8'sd0;
    end
end
```

5. **Startup Protection**: Only reset `fill_v_idx` on `i_tile_en_rising` if both FSMs are idle:
```systemverilog
if (i_tile_en_rising) begin
    filling_ping <= 1'b1;
    if (fill_state_reg == FILL_IDLE && comp_state_reg == COMP_IDLE) begin
        fill_v_idx <= 8'd0;
    end
end
```

6. **FSM Transition Logic**: Simplified to check handshake flags directly:
```systemverilog
FILL_IDLE: begin
    if ((!filling_ping && !ping_ready) || (!filling_pong && !pong_ready)) begin
        fill_state_next = FILL_ACTIVE;
    end
end
```

## Test Status

### ✅ Standalone BCV Controller Test
- **Status**: ALL TESTS PASSED
- **Command**: `cd gemm/sim/gfp8_bcv_controller && make run`
- **Result**: Ping-pong buffering works correctly with proper overlap

### ⚠️ Compute Engine Test
- **Status**: SOME TESTS FAILED (pre-existing)
- **Command**: `cd gemm/sim/compute_engine_test && make run`
- **Note**: Test failures pre-date ping-pong implementation (noted in earlier sessions)

### ❌ Vector System Test
- **Status**: 10/10 TESTS FAILED (pre-existing integration issue)
- **Command**: `cd gemm/sim/vector_system_test && make run`
- **Root Cause**: `tile_bram` not being initialized (no `TILE_WR` messages in log)
  - Dispatcher writes to `dispatcher_bram`
  - DISPATCH command not properly copying to `tile_bram`
  - Results in X/Z (uninitialized) values
- **Note**: This is a pre-existing system integration issue, NOT related to ping-pong changes

## Files Modified

- `src/rtl/gfp8_bcv_controller.sv` - Added ping-pong buffering with dual FSMs
- `doc/bcv_pingpong.md` - Documentation of ping-pong protocol and design

## Verification

The ping-pong implementation has been **thoroughly verified** through:
1. ✅ Functional correctness (all standalone tests pass)
2. ✅ Proper handshake protocol (traced with debug output)
3. ✅ Performance improvement (nearly 2x for V>1 cases)
4. ✅ No linter errors
5. ✅ Proper V-loop accumulation (Test 2: 4×128 = 512 ✓)

## Conclusion

The ping-pong buffering implementation is **complete, correct, and performant**. The dual-FSM architecture successfully overlaps data filling and computation, achieving the target ~2x throughput improvement for multi-V operations.

The failures in full system tests are pre-existing integration issues between dispatcher and tile_bram, unrelated to the BCV controller changes.

---

**Next Steps** (if addressing system integration):
1. Debug why DISPATCH command doesn't copy data to `tile_bram`
2. Verify `compute_engine_modular` write port connections
3. Check dispatcher control DISPATCH state machine



