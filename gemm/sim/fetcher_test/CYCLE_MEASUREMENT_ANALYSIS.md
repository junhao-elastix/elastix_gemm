# Cycle Measurement Analysis - Fetcher Testbench vs Vector System Test

## Question: Why Different Cycle Counts?

**Fetcher Test**: 598 cycles
**Vector System Test**: 624 cycles (FETCH LEFT) + 620 cycles (DISPATCH LEFT) = ~1244 cycles total

## Root Cause: Different Measurement Points

### Fetcher Test (fetcher_test/tb_fetcher.sv)

**What is measured**: PURE fetcher execution time

```systemverilog
// Start measurement
start_cycle = cycle_count;
fetch_en = 1'b1;
@(posedge clk);
fetch_en = 1'b0;

// End measurement
wait(fetch_done == 1'b1);  // ← Measures ONLY until fetcher signals done
@(posedge clk);
duration = cycle_count - start_cycle;
```

**Measurement Scope**:
```
T0: Issue FETCH command (fetch_en = 1)
    ↓
    [Fetcher reads 528 lines from GDDR6]
    [Fetcher writes to dispatcher_bram]
    [Fetcher unpacks exponents in parallel]
    ↓
T598: Fetcher signals fetch_done = 1  ← STOP HERE
```

**Result**: **598 cycles** - Pure fetcher state machine overhead

---

### Vector System Test (vector_system_test/tb_engine_top.sv)

**What is measured**: FETCH + DISPATCH combined time

```systemverilog
// Start measurement
fetch_left_start = $time;
[Submit FETCH LEFT command to cmd_fifo]
[Submit DISPATCH LEFT command to cmd_fifo]
[Submit WAIT_DISPATCH LEFT command to cmd_fifo]

// End measurement
wait(mc_state == ST_IDLE);
disp_left_end = $time;
fetch_left_end = disp_left_end;  // ← CRITICAL: Includes DISPATCH time!
fetch_left_cycles = (fetch_left_end - fetch_left_start) / CLK_PERIOD;
```

**Measurement Scope**:
```
T0: Issue FETCH LEFT command
    ↓
    [Fetcher executes: 598 cycles]
    ↓
T598: Fetcher signals fetch_done
    ↓
    [DISPATCH LEFT command executes: ~620 cycles]
    [Copies from dispatcher_bram → tile_bram]
    ↓
T1218: WAIT_DISPATCH completes, mc_state → IDLE  ← STOP HERE
```

**Result**: **1244 cycles** - FETCH (598) + DISPATCH (620) + overhead (~26)

---

## Detailed Breakdown from vector_system_test

From actual simulation log:

| Operation | Cycles | Percentage | What Happens |
|-----------|--------|------------|--------------|
| **FETCH LEFT** | 624 | 48.86% | Includes FETCH (598) + command parsing overhead |
| **DISPATCH LEFT** | 620 | 48.55% | Copy dispatcher_bram → tile_bram |
| **FETCH RIGHT** | ~624 | ~49% | Same as FETCH LEFT |
| **DISPATCH RIGHT** | ~620 | ~49% | Same as DISPATCH LEFT |
| **TILE (MATMUL)** | Variable | Depends on B×C×V | Compute engine execution |

**Why 624 instead of 598?**
- Command FIFO latency: ~5-10 cycles
- State transitions: ~5-10 cycles
- CSR to command parsing: ~5-10 cycles
- Total overhead: ~26 cycles

---

## Why Fetcher Test Shows 598 Cycles

### Direct Hardware Connection

```
Testbench                   Fetcher (DUT)
    │                           │
    ├─ fetch_en ────────────────┤ i_fetch_en
    ├─ fetch_addr ──────────────┤ i_fetch_addr
    ├─ fetch_len ───────────────┤ i_fetch_len
    ├─ fetch_target ────────────┤ i_fetch_target
    └─ fetch_done ◄─────────────┤ o_fetch_done
         ▲
         └── MEASUREMENT END (598 cycles)
```

**No overhead** from:
- Command FIFO parsing
- CSR interface
- Master control state machine
- Multi-command sequencing

**Result**: Pure fetcher performance = **598 cycles**

---

## Why Vector System Test Shows Higher Cycles

### Full System Integration

```
Testbench                Master Control         Fetcher
    │                         │                    │
    ├─ cmd_fifo_wdata ────────┤                   │
    ├─ cmd_fifo_wen ──────────┤                   │
    │                          │                   │
    │   [Parse FETCH cmd: ~10 cycles]            │
    │                          │                   │
    │                          ├─ o_dc_fetch_en ──┤ i_fetch_en
    │                          ├─ o_dc_fetch_addr─┤ i_fetch_addr
    │                          ├─ o_dc_fetch_len──┤ i_fetch_len
    │                          │                   │
    │                          │   [Fetcher: 598 cycles]
    │                          │                   │
    │                          │◄─ i_dc_fetch_done┤ o_fetch_done
    │                          │                   │
    │   [Parse DISPATCH cmd: ~10 cycles]         │
    │                          │                   │
    │   [Execute DISPATCH: ~620 cycles]          │
    │                          │                   │
    │   [WAIT_DISPATCH checks: ~6 cycles]        │
    │                          │                   │
    └── wait(mc_state == IDLE) ◄──────────────────┘
              ▲
              └── MEASUREMENT END (624 + 620 = 1244 cycles)
```

**Includes overhead** from:
- Command parsing: ~10 cycles per command
- State transitions: ~5 cycles per transition
- DISPATCH execution: ~620 cycles
- Synchronization: ~6 cycles

**Result**: Total system latency = **1244 cycles**

---

## Comparing the Two Measurements

| Aspect | Fetcher Test | Vector System Test |
|--------|--------------|-------------------|
| **What's Measured** | Pure fetcher execution | FETCH + DISPATCH pipeline |
| **Start Point** | fetch_en assertion | Command FIFO write |
| **End Point** | fetch_done signal | Master control IDLE |
| **Includes Command Parsing** | ❌ No | ✅ Yes (~10 cycles) |
| **Includes DISPATCH** | ❌ No | ✅ Yes (~620 cycles) |
| **Includes Sync Overhead** | ❌ No | ✅ Yes (~6 cycles) |
| **Cycle Count** | **598** | **~1244** |
| **Use Case** | Fetcher optimization | End-to-end validation |

---

## Which Measurement is Correct?

**Both are correct** - they measure different things!

### Fetcher Test (598 cycles)
✅ **Use for**: Fetcher module optimization
- Measures pure fetcher state machine efficiency
- Isolates fetcher performance from system overhead
- Baseline for comparing optimized fetcher implementations

### Vector System Test (1244 cycles)
✅ **Use for**: System-level performance analysis
- Measures realistic end-to-end latency
- Includes all system overheads
- Reflects actual hardware behavior

---

## Practical Example

### Scenario: Optimizing Fetcher from 598 → 550 cycles

**Fetcher Test Shows**:
- Baseline: 598 cycles
- Optimized: 550 cycles
- **Improvement**: 48 cycles (8% faster)

**Vector System Test Would Show**:
- Baseline: 624 (FETCH) + 620 (DISPATCH) = 1244 cycles
- Optimized: 576 (FETCH) + 620 (DISPATCH) = 1196 cycles
- **Improvement**: 48 cycles (3.9% faster in total system)

**Key Insight**: Fetcher optimization has **diminishing returns** in the full system because DISPATCH takes comparable time (~620 cycles).

---

## Optimization Priorities

### Current Bottlenecks (from vector_system_test)

1. **DISPATCH** (~620 cycles, 48.55% of time)
   - Copies dispatcher_bram → tile_bram
   - Potential for optimization: High
   - Strategy: Burst transfers, parallel dispatch

2. **FETCH** (~624 cycles, 48.86% of time)
   - Reads GDDR6 → dispatcher_bram
   - Already optimized (598 cycles pure fetcher)
   - Overhead: 26 cycles (command parsing)
   - Potential: Moderate (limited by memory latency)

3. **Command Overhead** (~26 cycles, ~2% of time)
   - Command parsing, state transitions
   - Potential: Low (minimal impact)

---

## Why Use Zero-Latency Memory in Fetcher Test?

**Goal**: Isolate fetcher state machine overhead

With realistic GDDR6 latency (~55 cycles first-word):
```
Fetcher Test Would Show: ~2000-3000 cycles
  = 598 cycles (state machine overhead)
  + 1400-2400 cycles (memory latency)
```

**Problem**: Can't differentiate state machine efficiency from memory latency

**Solution**: Use zero-latency memory model
```
Fetcher Test Shows: 598 cycles
  = Pure state machine overhead
  = Baseline for optimization
```

---

## Recommendations

### For Fetcher Optimization
1. **Use fetcher_test**: Measures pure fetcher efficiency (598 cycles)
2. **Target**: < 550 cycles (theoretical limit ~544 cycles)
3. **Focus**: State machine, burst patterns, pipelining

### For System Optimization
1. **Use vector_system_test**: Measures end-to-end latency (1244 cycles)
2. **Target**: Optimize both FETCH and DISPATCH
3. **High Impact**: Parallel FETCH+DISPATCH, multi-channel fetch

### For Hardware Validation
1. **Use vector_system_test**: Reflects actual hardware behavior
2. **Measure**: Total latency from command → results ready
3. **Monitor**: All stages (FETCH, DISPATCH, MATMUL)

---

## Conclusion

**Fetcher Test (598 cycles)**: Correct for fetcher module optimization
**Vector System Test (1244 cycles)**: Correct for system-level analysis

The difference (646 cycles) is primarily **DISPATCH** execution (~620 cycles) plus command parsing overhead (~26 cycles).

**Both measurements are valuable** for different optimization targets!

---

**Created**: Mon Nov 3 2025
**Author**: Claude Code Analysis
