# BCV Controller Latency Analysis
**Date:** October 29, 2025  
**Version:** Optimized Single-FSM with flag-based ready signal (5-cycle fill)

## Summary

The current `gfp8_bcv_controller` implementation achieves **10 cycles per V iteration** using a flag-based approach that eliminates the settle cycle.

## Measured Latency (from vector_system_test simulation)

### Test Case: B=2, C=2, V=64
Measuring consecutive V iterations for B=0, C=0 pair:

```
@134665 [B0,C0] V=29 ACCUM
@134765 [B0,C0] V=30 ACCUM  (Δ = 100 = 10 cycles)
@134865 [B0,C0] V=31 ACCUM  (Δ = 100 = 10 cycles)
@134965 [B0,C0] V=32 ACCUM  (Δ = 100 = 10 cycles)
@135065 [B0,C0] V=33 ACCUM  (Δ = 100 = 10 cycles)
@135165 [B0,C0] V=34 ACCUM  (Δ = 100 = 10 cycles)
```

**Consistent per-V latency: 10 cycles** ✓ Matches documented performance

## Detailed State Breakdown

### Fill Buffer State (ST_FILL_BUFFER) - 5 cycles
**Key Optimization:** Flag-based ready signal eliminates settle cycle

```
Cycle 0: Issue G0 addr (combinational)
Cycle 1: Capture G0, Issue G1 addr
Cycle 2: Capture G1, Issue G2 addr  
Cycle 3: Capture G2, Issue G3 addr
Cycle 4: Capture G3, SET fill_buffer_ready flag
Cycle 5: Transition (on flag)
```

**Innovation:** The ready flag is set in cycle 4 when G3 is captured. The FSM transition happens in cycle 5 based on the flag, eliminating the extra "wait for settle" cycle.

### Compute NV State (ST_COMPUTE_NV) - 4 cycles
```
gfp8_nv_dot 4-cycle pipeline:
  Cycle 0: Input capture
  Cycle 1: Group dot products
  Cycle 2: NV accumulation  
  Cycle 3: Output ready
```
**Compute duration: 4 cycles**

### Accumulate State (ST_ACCUM) - 1 cycle
```
Exponent alignment and mantissa accumulation
```
**Accum duration: 1 cycle**

## Per-V Iteration Breakdown

| Stage | Cycles | Description |
|-------|--------|-------------|
| **FILL_BUFFER** | 5 | TRUE 1-cycle BRAM latency + flag-based ready |
| **COMPUTE_NV** | 4 | gfp8_nv_dot 4-cycle pipeline |
| **ACCUM** | 1 | Exponent alignment and accumulation |
| **TOTAL** | **10** | **Per-V iteration latency** |

## Code Documentation vs Measured

The code header claims:
> Latency per output: 5 (fill) + 4 (compute) + 1 (accum) = 10 cycles per V

Measurements confirm:
- **Documented:** 10 cycles (5 fill + 4 compute + 1 accum)
- **Measured:** 10 cycles ✓ **EXACT MATCH**

## Performance Comparison

### Version History

| Version | Per-V Cycles | Notes |
|---------|--------------|-------|
| Original (pre-refactor) | ~24 | Sequential reads, 3-cycle holds |
| Parallel exp+man reads | 14 | 2-cycle BRAM latency × 4 groups + overhead |
| **Current (flag-based)** | **10** | **1-cycle BRAM latency + flag optimization** |
| Ping-pong (target) | 6 | Overlapped fill+compute (failed in integration) |

### Speedup Analysis
- **vs Original:** 2.4× faster (24 → 10 cycles)
- **vs Previous refactor:** 1.4× faster (14 → 10 cycles)

### Typical Tile Performance (V=64)
- **Per-V:** 10 cycles
- **Total:** 10 × 64 + 1 (return) = **641 cycles** for one B,C output

## Key Innovation: Flag-Based Ready Signal

The critical optimization that achieves 5-cycle fill:

```systemverilog
// In ST_FILL_BUFFER, cycle 4:
if (fill_cycle == 3'd4) begin
    // Capture last group
    nv_left_man[3] <= i_man_left_rd_data;
    nv_right_man[3] <= i_man_right_rd_data;
    fill_buffer_ready <= 1'b1;  // Set flag immediately
    fill_cycle <= fill_cycle + 1;
end

// Next-state logic:
ST_FILL_BUFFER: begin
    if (fill_buffer_ready) begin
        state_next = ST_COMPUTE_NV;  // Transition on flag
    end
end

// Clear flag when entering compute:
ST_COMPUTE_NV: begin
    fill_buffer_ready <= 1'b0;
end
```

This eliminates the extra "settle" cycle that was needed when checking `fill_cycle >= threshold` directly.

## BRAM Latency Clarification

**Important Discovery:** The "1-cycle BRAM latency" refers to the **effective** latency from the BCV controller's perspective:

1. **Cycle N:** BCV issues address (combinational output)
2. **Cycle N:** BRAM registers input address (within same cycle)
3. **Cycle N+1:** BRAM outputs data (registered output)
4. **Cycle N+1:** BCV captures data

From BCV's view: Address out → Data back = **1 cycle apparent latency**

**Physical implementation:** 
- BCV output register: REMOVED (direct combinational connection)
- BRAM input register: EXISTS (internal to BRAM)
- BRAM output register: EXISTS (internal to BRAM)

This is why the documentation says "TRUE 1-cycle BRAM latency" with "DIRECT combinational connection (no BCV output registers!)".

## Bottleneck Analysis

The **5-cycle fill buffer** is still the dominant component (5 out of 10 cycles = 50% of per-V time), but this is now a **fundamental limit** given:
- 4 groups to read
- 1-cycle effective BRAM latency per group
- 1 cycle for transition

**Further optimization requires overlapping fill and compute → Ping-pong architecture**

## Ping-Pong Potential

The attempted ping-pong implementation aimed for:
- **First V:** 10 cycles (5 fill + 4 compute + 1 accum, sequential)
- **V≥1:** 6 cycles (5 fill || 4 compute, overlapped + 1 accum)
  - Max(5 fill, 4 compute) = 5 cycles, but need 1 extra for handshake/transition
- **Theoretical:** 10 + 6×(V-1) = **6V + 4 cycles**

For V=64: 6×64 + 4 = **388 cycles** (vs 641 cycles single-FSM)
**Potential speedup: 1.65× faster than current**

However, ping-pong implementation failed in full system integration tests (vector_system_test, compute_engine_test), despite passing standalone tests (tb_gfp8_bcv_controller).

## Optimization Opportunities

1. **Fix Ping-Pong Implementation** (1.65× potential speedup)
   - Debug the integration issues causing failures in full system tests
   - Root cause appears to be related to `fill_v_idx` management during B,C transitions
   - Standalone tests pass → integration problem, not core logic issue
   
2. **Reduce BRAM Latency** (Unlikely)
   - Current 1-cycle effective latency is near-optimal
   - Fully combinational path would sacrifice timing closure
   
3. **Speculative Prefetch**
   - Start filling next V's data before current V's compute completes
   - This is essentially what ping-pong does
   - No simpler alternative without dual buffers

## Conclusion

The current single-FSM implementation achieves **10 cycles per V**, representing:
- **2.4× improvement** over the original design (~24 cycles)
- **1.4× improvement** over the previous parallel-read version (14 cycles)
- Achieves documented target performance exactly

The flag-based ready signal optimization was the key to eliminating the extra settle cycle and achieving the 5-cycle fill target.

**Remaining opportunity:** The ping-pong implementation has potential for an additional **1.65× speedup** (10 cycles → 6 cycles per V) if the integration bugs can be resolved. This would bring total improvement to **4× faster** than the original design.

## Files
- **Current (working):** `gfp8_bcv_controller.sv` - 10 cycles/V ✓
- **Previous version:** `gfp8_bcv_controller_single_fsm_backup.sv` - 14 cycles/V
- **Failed ping-pong:** `gfp8_bcv_controller_pingpong_failed.sv` - Target 6 cycles/V
- **Very old backup:** `gfp8_bcv_controller_stable.sv.bak` - ~24 cycles/V
