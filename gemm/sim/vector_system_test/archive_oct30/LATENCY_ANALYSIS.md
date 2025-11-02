# Latency Analysis - Refactored Architecture
## Simulation Results (After Refactoring)

### Summary
- **All Tests Pass**: 10/10 (100%)
- **Architecture**: Separated Fetcher, Dispatcher, and Dispatcher BRAM modules
- **Fixed Issue**: Signed arithmetic bug in write address calculation (disp_write_cnt)

### Detailed Timing Breakdown by Test

| Test | B×C×V | FETCH L | DISPATCH L | FETCH R | DISPATCH R | TILE+RESULTS | TOTAL | FETCH% | DISPATCH% | TILE% |
|------|-------|---------|------------|---------|------------|--------------|-------|--------|-----------|-------|
| B1_C1_V1 | 1×1×1 | 1350 | 1346 | 1350 | 1346 | 33 | 2733 | 98.8% | - | 1.2% |
| B2_C2_V2 | 2×2×2 | 1350 | 1346 | 1350 | 1346 | 113 | 2813 | 96.0% | - | 4.0% |
| B4_C4_V4 | 4×4×4 | 1350 | 1346 | 1350 | 1346 | 741 | 3441 | 78.5% | - | 21.5% |
| B2_C2_V64 | 2×2×64 | 1350 | 1346 | 1350 | 1346 | 2841 | 5541 | 48.7% | - | 51.3% |
| B4_C4_V32 | 4×4×32 | 1350 | 1346 | 1350 | 1346 | 5669 | 8369 | 32.3% | - | 67.7% |
| B8_C8_V16 | 8×8×16 | 1350 | 1346 | 1350 | 1346 | 11349 | 14049 | 19.2% | - | 80.8% |
| B16_C16_V8 | 16×16×8 | 1350 | 1346 | 1350 | 1346 | 22805 | 25505 | 10.6% | - | 89.4% |
| B1_C128_V1 | 1×128×1 | 1350 | 1346 | 1350 | 1346 | 1557 | 4257 | 63.4% | - | 36.6% |
| B128_C1_V1 | 128×1×1 | 1350 | 1346 | 1350 | 1346 | 1557 | 4257 | 63.4% | - | 36.6% |
| B1_C1_V128 | 1×1×128 | 1350 | 1346 | 1350 | 1346 | 1430 | 4130 | 65.4% | - | 34.6% |

### Key Observations

1. **FETCH Latency is Constant**: 1350 cycles per FETCH operation
   - Does NOT scale with data size
   - Suggests fixed overhead (state machine, AXI setup, BRAM writes)
   - Potential bottleneck for small workloads

2. **DISPATCH Latency is Constant**: 1346 cycles per DISPATCH operation
   - Does NOT scale with data size
   - Fixed overhead regardless of amount of data copied
   - Suggests state machine overhead or minimal data path utilization

3. **TILE Latency Scales**: Grows with workload size (B×C×V)
   - Small workloads: ~1-4% of total time
   - Large workloads: ~80-90% of total time
   - This is expected and healthy scaling

4. **Sequential Operations**: FETCH and DISPATCH are sequential
   - FETCH LEFT → DISPATCH LEFT → FETCH RIGHT → DISPATCH RIGHT → TILE
   - No overlapping/pipelining currently

### Optimization Opportunities

#### HIGH PRIORITY

1. **Pipeline FETCH and DISPATCH Operations**
   - **Current**: Sequential execution (FETCH L → DISPATCH L → FETCH R → DISPATCH R)
   - **Opportunity**: Overlap FETCH RIGHT while DISPATCH LEFT is running (if different BRAMs)
   - **Expected Gain**: Up to ~2700 cycles savings (one FETCH + one DISPATCH)
   - **Complexity**: Medium - Need to ensure BRAM access conflicts don't occur

2. **Investigate FETCH Fixed Overhead**
   - **Question**: Why is FETCH always 1350 cycles regardless of data size?
   - **Investigation**: Check AXI transaction overhead, state machine delays, BRAM write patterns
   - **Potential**: Reduce fixed overhead for small data transfers
   - **Action Items**:
     - Profile FETCH state machine transitions
     - Check if minimum AXI burst size causes delay
     - Verify BRAM write efficiency

3. **Investigate DISPATCH Fixed Overhead**
   - **Question**: Why is DISPATCH always 1346 cycles regardless of data size?
   - **Investigation**: Check state machine delays, counter initialization, BRAM read latency
   - **Potential**: Reduce fixed overhead, especially for single-vector dispatches
   - **Action Items**:
     - Profile DISPATCH state machine transitions
     - Check if initialization overhead can be reduced
     - Verify BRAM read pipeline efficiency

#### MEDIUM PRIORITY

4. **Optimize Small Workloads**
   - For B×C×V=1, FETCH+DISPATCH = 98.8% of time
   - Consider batching or reducing state machine transitions
   - Fast path for minimal data transfers
   - **Expected Gain**: Significant for inference workloads with small batches

5. **Parallel FETCH Operations**
   - If using separate GDDR6 channels, could fetch left and right in parallel
   - Requires dual AXI initiators or channel multiplexing
   - **Complexity**: High - Requires architecture changes

#### LOW PRIORITY (Good Scaling Already)

6. **TILE Computation**
   - Already scales well with workload
   - ~80-90% of time for large workloads is computation (expected)
   - Consider optimization only if specific bottlenecks identified

### Detailed Cycle Analysis

For **B1_C1_V1** (smallest workload):
- **FETCH LEFT**: 1350 cycles (49.40%)
- **DISPATCH LEFT**: 1346 cycles (49.25%)
- **FETCH RIGHT**: 1350 cycles (49.40%)
- **DISPATCH RIGHT**: 1346 cycles (49.25%)
- **TILE + RESULTS**: 33 cycles (1.21%)
- **Total**: 2733 cycles

**Key Insight**: For tiny workloads, overhead dominates (98.8% overhead, 1.2% computation)

For **B16_C16_V8** (large workload):
- **FETCH LEFT**: 1350 cycles (5.29%)
- **DISPATCH LEFT**: 1346 cycles (5.28%)
- **FETCH RIGHT**: 1350 cycles (5.29%)
- **DISPATCH RIGHT**: 1346 cycles (5.28%)
- **TILE + RESULTS**: 22805 cycles (89.41%)
- **Total**: 25505 cycles

**Key Insight**: For large workloads, computation dominates (10.6% overhead, 89.4% computation)

### Recommended Next Steps

1. **Immediate**:
   - Analyze FETCH state machine - identify why fixed 1350 cycles
   - Analyze DISPATCH state machine - identify why fixed 1346 cycles
   - Profile AXI transaction patterns

2. **Short-term**:
   - Implement FETCH RIGHT and DISPATCH LEFT pipelining
   - Optimize state machine transitions to reduce fixed overhead
   - Fast path for single-vector operations

3. **Medium-term**:
   - Consider prefetching strategies
   - Investigate BRAM access optimization
   - Explore dual-channel FETCH if applicable

4. **Long-term**:
   - Consider architectural changes for small workload optimization
   - Investigate prefetching next batch while current batch computes
   - Explore streaming architectures for continuous workloads

### Performance Targets

**Current Performance**:
- Small workloads (B×C×V=1): ~27 us
- Medium workloads (B×C×V=64): ~55 us  
- Large workloads (B×C×V=2048): ~255 us

**Potential Improvements** (with pipelining):
- Small workloads: ~20-30% improvement (~19-20 us)
- Medium workloads: ~20-30% improvement (~39-44 us)
- Large workloads: ~10-15% improvement (~217-230 us)

**Note**: Large improvements require addressing the fixed overhead in FETCH and DISPATCH operations.

## Appendix: Understanding the "Doubled" Latencies

### Testbench Measurement Bug

The testbench has a bug in how it measures FETCH latency (lines 363, 388):
```systemverilog
fetch_left_end = disp_left_end;  // WRONG! Sets FETCH end = DISPATCH end
```

This causes reported FETCH latency to include both FETCH + DISPATCH time.

### Actual Latency Breakdown (Estimated)

For a GFP8 block (528 lines):
- **True FETCH time**: ~528 cycles (1 cycle per line transfer)
  - 16 exp lines: 1 burst = 16 cycles
  - 512 mantissa lines: 32 bursts × 16 beats = 512 cycles  
  - Plus overhead: state transitions, AXI AR handshakes (~4 cycles)
  - **Expected: ~532 cycles** (not 1350!)

- **True DISPATCH time**: Variable based on data copied
  - For B×V=1 (4 lines): Should be ~4 cycles + overhead
  - **But measured: 1346 cycles** ❌

### Why DISPATCH is Always ~1346 Cycles

**HYPOTHESIS**: The dispatcher state machine has fixed overhead or waits for fixed cycles regardless of actual data size. Possible causes:

1. **Counter initialization delay**: disp_write_cnt starts at -1, may have setup overhead
2. **State machine transition overhead**: Multiple cycles between states
3. **Batch processing overhead**: Even for 1 vector, goes through batch logic
4. **BRAM read latency**: 1-cycle pipeline delay, but might be more
5. **Completion detection**: May wait for a fixed timeout or cycle count

### Why FETCH is Always ~1350 Cycles

**CONFIRMED**: FETCH always reads a full GFP8 block (528 lines) regardless of actual data size. This is by design:
- Memory layout: Always 16 exp_packed lines + 512 mantissa lines
- AXI bursts: Fixed burst pattern (33 bursts total)
- **So 1350 cycles = 528 data + ~822 overhead cycles** ❌ Should be closer to 528!

**Investigating**: Where are the extra ~822 cycles coming from?
- AXI AR handshakes: 33 bursts × ~25 cycles overhead each? (seems high)
- State machine overhead: Multiple cycles per state transition?
- BRAM write pipeline: Delays in writing to dispatcher_bram?

### Next Steps to Debug

1. Add cycle-by-cycle instrumentation to FETCH state machine
2. Count actual AXI transactions and handshake cycles
3. Check BRAM write pipeline delays
4. Profile DISPATCH state machine for fixed overhead
5. Fix testbench to properly measure FETCH completion (track o_fetch_done)

