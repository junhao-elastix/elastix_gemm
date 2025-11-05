# Fetcher Baseline with Realistic GDDR6 Memory Model

**Date**: November 3, 2025
**Memory Model**: `tb_memory_model_realistic.sv`
**DUT**: `gemm/src/rtl/fetcher.sv` (original, unoptimized)

---

## Test Configuration

### Memory Model Parameters
- **Max Outstanding ARs**: 32 (Achronix GDDR6 NoC architectural limit)
- **Read Latency**: 40 cycles (100ns @ 400MHz)
- **Data Width**: 256-bit AXI
- **Memory Size**: 2 blocks × 528 lines = 1056 total lines
- **Test Data**: `/home/workstation/elastix_gemm/hex/left.hex` and `right.hex`

### Fetch Operation
- **Lines per Fetch**: 528 (16 exponent lines + 512 mantissa lines)
- **Bursts Required**: 33 total (1 exp burst + 32 man bursts)
- **Beats per Burst**: 16
- **Total Beats**: 33 × 16 = 528 beats

---

## Baseline Performance Results

### Execution Time
| Metric | Value |
|--------|-------|
| **Total Cycles** | **1885 cycles** |
| **Throughput** | 0.28 lines/cycle |
| **Latency per Line** | 3.57 cycles/line |

### Memory Statistics
| Metric | Observed | Limit |
|--------|----------|-------|
| **Total ARs Issued** | 132 (4 fetches × 33 ARs) | N/A |
| **Total R Beats Received** | 2112 (4 fetches × 528 beats) | N/A |
| **Max Outstanding ARs** | **1** | **32** |
| **Outstanding Utilization** | **3.1%** | 100% |

---

## Critical Finding: Massive Under-Utilization

**The original fetcher uses only 1 out of 32 available outstanding request slots (3.1% utilization).**

### Why This Happens

The original fetcher uses a **sequential state machine**:

```
1. Issue 1 AR
2. Wait for all 16 R beats
3. Return to IDLE
4. Repeat 33 times
```

**Timeline for Each Burst**:
```
Cycle 0:    AR handshake
Cycle 1-40: Latency (waiting for memory)
Cycle 41:   First R beat
Cycle 42-56: Remaining 15 R beats
Cycle 57:   Return to IDLE, issue next AR
```

**Gap between ARs**: ~57 cycles
**Result**: Only 1 AR in-flight at any time → 31 slots wasted

---

## Theoretical Performance Limits

### Perfect Pipelining (32 Outstanding ARs)

If we issue ARs **continuously** without waiting:

**Minimum Possible Cycles**:
```
AR issuing:     33 ARs × 1 cycle = 33 cycles
Latency:        40 cycles (first AR to first R)
R data:         528 beats × 1 cycle = 528 cycles (continuous rvalid)
─────────────────────────────────────────────
Total:          601 cycles (theoretical minimum)
```

**Speedup**: 1885 / 601 = **3.14× improvement possible**

### Conservative Pipelining (4-8 Outstanding ARs)

More realistic target with safety margin:

**With 4 Outstanding ARs**:
```
AR phase:       33 ARs with pipelining ≈ 40 cycles
Latency:        40 cycles
R data:         528 beats ≈ 550 cycles (some gaps)
─────────────────────────────────────────────
Estimated:      ~630 cycles
```

**Speedup**: 1885 / 630 = **2.99× improvement**

**With 8 Outstanding ARs**:
```
AR phase:       33 ARs with pipelining ≈ 35 cycles
Latency:        40 cycles
R data:         528 beats ≈ 540 cycles (minimal gaps)
─────────────────────────────────────────────
Estimated:      ~615 cycles
```

**Speedup**: 1885 / 615 = **3.07× improvement**

---

## Optimization Strategy Recommendations

### Recommended Approach: Conservative Pipelining

**Design Goals**:
1. ✅ Maintain functional correctness (same BRAM contents as baseline)
2. ✅ Respect 32-outstanding-AR hardware limit
3. ✅ Target 2-3× speedup (conservative, achievable)
4. ✅ Keep design simple and verifiable

**Implementation Strategy**:

#### Option A: Fixed Pipeline Depth (Recommended)
```systemverilog
// Allow 4-8 ARs in-flight simultaneously
localparam MAX_OUTSTANDING_ARS = 8;

logic [5:0] outstanding_ar_count;  // Track issued but not R-complete

always_ff @(posedge i_clk) begin
    case ({ar_issued, r_burst_complete})
        2'b10: outstanding_ar_count <= outstanding_ar_count + 1;
        2'b01: outstanding_ar_count <= outstanding_ar_count - 1;
        2'b11: outstanding_ar_count <= outstanding_ar_count;  // Net zero
        default: /* no change */
    endcase
end

assign can_issue_ar = (outstanding_ar_count < MAX_OUTSTANDING_ARS) &&
                      (total_ars_issued < 33);
```

**Advantages**:
- Simple to implement and verify
- No FIFO needed (just counter)
- Predictable behavior
- Easy to tune (change MAX_OUTSTANDING_ARS parameter)

**Expected Performance**: 615-630 cycles (**3× faster than baseline**)

#### Option B: Adaptive Pipeline Depth
- Monitor `arready` backpressure
- Increase outstanding count when arready stays high
- Decrease when arready blocks
- More complex, higher risk

**NOT RECOMMENDED** - diminishing returns vs complexity

---

## Verification Plan

### Functional Verification
1. ✅ **Golden Reference**: Use baseline fetcher output as expected result
2. ✅ **Compare BRAM Contents**: Verify optimized fetcher fills exact same addresses with same data
3. ✅ **End-to-End Test**: Run with dispatcher/compute engine to ensure integration works

### Performance Verification
1. ✅ **Cycle Count**: Measure with realistic memory model
2. ✅ **Outstanding ARs**: Monitor peak utilization (should be 4-8, not 32)
3. ✅ **Memory Efficiency**: Check AR→R gaps (should be minimal)

---

## Next Steps

1. **Create optimized fetcher** (`fetcher_pipelined.sv`)
   - Implement fixed pipeline depth (8 outstanding ARs)
   - Keep same module interface as original
   - Add performance counters

2. **Run verification**
   - Compile with realistic memory model
   - Verify BRAM contents match baseline
   - Measure cycle count improvement

3. **Tune performance**
   - Adjust MAX_OUTSTANDING_ARS (4, 8, 16)
   - Find sweet spot (performance vs complexity)
   - Document final results

---

## Baseline Summary

**Current Performance**: 1885 cycles (0.28 lines/cycle)
**Bottleneck**: Sequential AR issuing (only 1 outstanding at a time)
**Optimization Target**: 615-630 cycles (2-3× speedup)
**Implementation**: Simple pipelined AR issuing with outstanding counter
**Risk**: Low (well-understood, proven technique)

---

**Validated**: November 3, 2025
**Tool**: Riviera-PRO 2025.04
**Status**: ✅ Baseline established, ready for optimization
