# BCV Controller Dual-FSM Ping-Pong Design (v2)

**Date:** October 30, 2025  
**Status:** Implementation in progress  
**Goal:** Overlap BRAM fill and compute to achieve ~5-6 cycles per V iteration (vs 10 cycles single-FSM)

---

## Lessons from Failed v1 Implementation

### Critical Issues Identified

1. **V-index desynchronization**: Fill FSM advanced `fill_v_idx` independently without proper bounds checking against compute FSM's `v_idx`
2. **B,C transition races**: Fill FSM didn't know when compute FSM moved to new (b,c) pair, causing wrong BRAM addresses
3. **Complex handshake**: 4 flags (filling_ping/pong + ping_ready/pong_ready) with unclear ownership
4. **No backpressure**: Fill FSM could get too far ahead, corrupting buffers still in use

---

## v2 Design Principles

### 1. Explicit State Sharing
```systemverilog
// Compute FSM shares its current position with Fill FSM
logic [7:0] comp_b_idx, comp_c_idx, comp_v_idx;  // Compute FSM's loop counters

// Fill FSM uses these to calculate addresses, but tracks its own progress
logic [7:0] fill_v_idx;  // Which V iteration Fill FSM is working on
```

### 2. Simple Two-Flag Handshake
```systemverilog
// Only 2 flags, clear ownership:
logic ping_ready;  // 1=PING has valid data ready to compute
logic pong_ready;  // 1=PONG has valid data ready to compute

// Producer (Fill FSM): Sets flag when buffer full
// Consumer (Compute FSM): Clears flag when starting to consume buffer
```

### 3. Backpressure Protection
```systemverilog
// Fill FSM only fills if:
// 1. Target buffer is NOT ready (not already full)
// 2. Not too far ahead: fill_v_idx < comp_v_idx + 2
//    (At most 1 buffer ahead: one being computed, one ready)
```

### 4. B,C Transition Synchronization
```systemverilog
// Compute FSM signals when starting new (b,c) pair
logic new_bc_pair_flag;  // Pulsed for 1 cycle when entering COMP_IDLE after COMP_RETURN

// Fill FSM detects this and resets to sync with compute
if (new_bc_pair_flag) begin
    fill_v_idx <= comp_v_idx;  // Sync to compute position
end
```

---

## State Machine Architecture

### Fill FSM States

```
FILL_IDLE:
  - Check conditions to start filling
  - If (target buffer not ready) AND (not too far ahead) AND (more V iterations needed):
      → FILL_ACTIVE
      
FILL_ACTIVE:
  - Fill PING or PONG buffer over 5 cycles (fill_cycle 0→1→2→3→4)
  - Cycle 4: Set ping_ready or pong_ready
  - Cycle 4: Increment fill_v_idx
  - Cycle 5: → FILL_IDLE
```

**Key decisions in FILL_IDLE:**
```systemverilog
// Which buffer to fill? (prefer PING for determinism)
fill_target = (!ping_ready) ? 0 :    // PING not ready? Fill PING
              (!pong_ready) ? 1 :    // PONG not ready? Fill PONG
              0;                      // Both ready? Wait (should not happen)

// Should we fill?
can_fill = (fill_v_idx < dim_v_reg) &&          // More V iterations exist
           (fill_v_idx <= comp_v_idx + 1) &&    // Not too far ahead
           (!ping_ready || !pong_ready);        // At least one buffer available
```

### Compute FSM States

```
COMP_IDLE:
  - Wait for ready buffer: (ping_ready || pong_ready)
  - Select buffer: use_pong = pong_ready (prefer PONG if both ready)
  - Clear the filling_* flag (no longer needed in v2)
  - → COMP_NV
  
COMP_NV:
  - Run gfp8_nv_dot for 4 cycles (compute_wait: 0→1→2→3)
  - → COMP_ACCUM
  
COMP_ACCUM:
  - Clear ready flag: ping_ready or pong_ready (depending on use_pong)
  - Increment comp_v_idx
  - Accumulate result
  - If (comp_v_idx >= dim_v_reg): → COMP_RETURN
  - Else: → COMP_IDLE (next V iteration)
  
COMP_RETURN:
  - Output result
  - Reset comp_v_idx to 0
  - Advance comp_b_idx, comp_c_idx
  - Set new_bc_pair_flag
  - If (all B×C done): → COMP_DONE
  - Else: → COMP_IDLE
  
COMP_DONE:
  - Assert o_tile_done
  - → COMP_IDLE (wait for next tile)
```

---

## Timing Diagram (V=0,1,2,3)

```
Cycle | Fill FSM          | Compute FSM    | fill_v | comp_v | PING | PONG | Notes
------|-------------------|----------------|--------|--------|------|------|------------------
  0   | IDLE              | IDLE           |   0    |   0    |  0   |  0   | i_tile_en rising
  1   | ACTIVE (PING, V0) | IDLE (wait)    |   0    |   0    |  0   |  0   | Fill cycle 0→1
  2   | ACTIVE (PING, V0) | IDLE (wait)    |   0    |   0    |  0   |  0   | Fill cycle 1→2
  3   | ACTIVE (PING, V0) | IDLE (wait)    |   0    |   0    |  0   |  0   | Fill cycle 2→3
  4   | ACTIVE (PING, V0) | IDLE (wait)    |   0    |   0    |  0   |  0   | Fill cycle 3→4
  5   | IDLE              | IDLE (wait)    |   0    |   0    |  0   |  0   | Fill cycle 4→5, PING not ready yet
  6   | IDLE              | IDLE (ready!)  |   1    |   0    |  1   |  0   | PING ready set (delayed 1 cycle)
  7   | ACTIVE (PONG, V1) | NV (PING, V0)  |   1    |   0    |  1   |  0   | Overlap starts! Fill V1, compute V0
  8   | ACTIVE (PONG, V1) | NV (PING, V0)  |   1    |   0    |  1   |  0   | 
  9   | ACTIVE (PONG, V1) | NV (PING, V0)  |   1    |   0    |  1   |  0   | 
 10   | ACTIVE (PONG, V1) | NV (PING, V0)  |   1    |   0    |  1   |  0   | 
 11   | IDLE              | ACCUM (V0)     |   1    |   0    |  0   |  0   | PING cleared, comp_v 0→1
 12   | IDLE              | IDLE (ready!)  |   2    |   1    |  0   |  1   | PONG ready set
 13   | ACTIVE (PING, V2) | NV (PONG, V1)  |   2    |   1    |  0   |  1   | Fill V2, compute V1
 14   | ACTIVE (PING, V2) | NV (PONG, V1)  |   2    |   1    |  0   |  1   | 
 15   | ACTIVE (PING, V2) | NV (PONG, V1)  |   2    |   1    |  0   |  1   | 
 16   | ACTIVE (PING, V2) | NV (PONG, V1)  |   2    |   1    |  0   |  1   | 
 17   | IDLE              | ACCUM (V1)     |   2    |   1    |  0   |  0   | PONG cleared, comp_v 1→2
 18   | IDLE              | IDLE (ready!)  |   3    |   2    |  1   |  0   | PING ready set
 19   | ACTIVE (PONG, V3) | NV (PING, V2)  |   3    |   2    |  1   |  0   | Fill V3, compute V2
...   | (continues)       | (continues)    | ...    | ...    | ...  | ...  | Steady-state: 6 cycles per V
```

**Performance:**
- V=0: 10 cycles (must fill before computing)
- V=1,2,3...: 6 cycles each (fill overlaps with compute)
- Total: 10 + 6×(V-1) = **6V + 4 cycles**

**Comparison:**
- Single-FSM: 10V cycles
- Ping-pong: 6V + 4 cycles
- Improvement: ~40% for large V (e.g., V=128: 1280 → 772 cycles)

---

## BRAM Address Generation

Fill FSM generates addresses based on **compute FSM's current b,c** + **fill FSM's v**:

```systemverilog
// Use comp_b_idx, comp_c_idx (not fill's own copies!)
left_nv_index = left_base_nv + (comp_b_idx * dim_v_reg + fill_v_idx);
right_nv_index = right_base_nv + (comp_c_idx * dim_v_reg + fill_v_idx);
```

This ensures addresses are always correct even during B,C transitions.

---

## Critical Implementation Details

### 1. Startup Sequence

```systemverilog
// On i_tile_en rising edge:
comp_b_idx <= 0;
comp_c_idx <= 0;
comp_v_idx <= 0;
fill_v_idx <= 0;
ping_ready <= 0;
pong_ready <= 0;
new_bc_pair_flag <= 0;

// Fill FSM will automatically start filling PING for V=0
// Compute FSM will wait in IDLE until ping_ready
```

### 2. V-index Increment Timing

```systemverilog
// Fill FSM: Increment when buffer fill COMPLETES (cycle 4)
if (fill_cycle == 3'd4) begin
    fill_v_idx <= fill_v_idx + 1;
end

// Compute FSM: Increment in ACCUM state
COMP_ACCUM: begin
    comp_v_idx <= comp_v_idx + 1;
end
```

### 3. B,C Transition Handling

```systemverilog
// Compute FSM in COMP_RETURN:
comp_v_idx <= 0;
new_bc_pair_flag <= 1'b1;  // Pulse for 1 cycle
// Advance b,c as usual

// Fill FSM detects the pulse:
if (new_bc_pair_flag) begin
    fill_v_idx <= 0;  // Reset to start filling from V=0 for new (b,c)
end
```

### 4. Preventing Overfill

```systemverilog
// In FILL_IDLE, before starting fill:
if (fill_v_idx >= dim_v_reg) begin
    // No more V iterations for this (b,c) pair
    stay_in_IDLE;
end

if (fill_v_idx > comp_v_idx + 1) begin
    // Too far ahead (more than 1 buffer), wait for compute to catch up
    stay_in_IDLE;
end
```

---

## Verification Plan

### Test Cases

1. **Test 1: V=1** (no overlap, same as single-FSM)
   - Expected: ~16 cycles (10 + 6×0 + overhead)
   - Validates basic functionality

2. **Test 2: V=4** (small overlap)
   - Expected: ~28 cycles (10 + 6×3 = 28)
   - Single-FSM: 40 cycles
   - Improvement: 30%

3. **Test 3: V=128** (maximum overlap)
   - Expected: ~772 cycles (10 + 6×127 = 772)
   - Single-FSM: 1280 cycles
   - Improvement: 40%

4. **Test 4: B=2,C=2,V=2** (multiple outputs)
   - Validates B,C transition synchronization
   - Expected: 4 × (10 + 6×1) = 64 cycles

### Debug Signals

```systemverilog
`ifdef SIMULATION
$display("[PINGPONG] @%0t Fill V=%0d, Comp V=%0d, PING=%b, PONG=%b, fill_state=%s, comp_state=%s",
         $time, fill_v_idx, comp_v_idx, ping_ready, pong_ready, 
         fill_state_reg.name(), comp_state_reg.name());
`endif
```

---

## Success Criteria

✅ All 10 compute_engine_test cases pass  
✅ Cycle count reduction: V=128 test shows >35% improvement  
✅ No race conditions: fill_v_idx never exceeds comp_v_idx + 1  
✅ Clean synchronization: B,C transitions work correctly  
✅ No linter errors  

---

## Implementation File

- **New file:** `gfp8_bcv_controller_pingpong_v2.sv`
- **Backup:** Keep `gfp8_bcv_controller.sv` (working single-FSM)
- **After verification:** Replace `gfp8_bcv_controller.sv` with v2

---

**Status:** Ready for implementation 🚀


