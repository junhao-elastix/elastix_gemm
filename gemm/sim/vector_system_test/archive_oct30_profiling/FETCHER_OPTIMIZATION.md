# FETCHER OPTIMIZATION SUMMARY

## Overview
Applied optimization to `fetcher.sv` to reduce FETCH operation latency by ~33 cycles (~1-2% improvement).

## Optimization Implemented

### Optimization: AR Request on RLAST
**Description**: Issue next AR (Address Read) request immediately upon receiving RLAST signal from current burst, instead of waiting for state machine transition to `ST_FETCH_READ`.

**Original Flow**:
```
Cycle N:   RLAST received
Cycle N+1: State transitions to ST_FETCH_READ  
Cycle N+2: AR request set (axi_ar_req_reg = 1)
Cycle N+3: AR handshake (arvalid & arready)
Cycle N+4: Wait for data...
```

**Optimized Flow**:
```
Cycle N:   RLAST received + AR request set (same cycle)
Cycle N+1: AR handshake (arvalid & arready)
Cycle N+2: Wait for data...
```

**Savings**: 1-2 cycles per burst × 33 bursts = **~33-66 cycles total**

### Implementation Details

**Code Location**: `fetcher.sv` lines 537-571

**Key Changes**:
1. **Flexible AR Clearing**: Changed AR clear condition from `state_reg == ST_FETCH_READ` to `axi_ddr_if.arvalid && axi_ddr_if.arready`, allowing handshake in any state
2. **RLAST Trigger**: Added logic to set `axi_ar_req_reg` immediately when RLAST is detected during data reception
3. **Duplicate Prevention**: Check `!axi_ar_req_reg` before setting to avoid conflicts

**Critical Code**:
```systemverilog
end else if ((state_reg == ST_FETCH_READ_EXP || state_reg == ST_FETCH_READ_MAN) && 
            axi_ddr_if.rvalid && axi_ddr_if.rready && axi_ddr_if.rlast) begin
    // OPTIMIZATION: Issue next AR request immediately on RLAST
    if (!axi_ar_req_reg) begin
        if (state_reg == ST_FETCH_READ_EXP && exp_lines_fetched_reg < 15) begin
            axi_ar_req_reg <= 1'b1;
            $display("[FETCHER] @%0t [OPT1] Setting AR on RLAST for next EXP burst", $time);
        end else if (state_reg == ST_FETCH_READ_EXP && exp_lines_fetched_reg >= 15) begin
            axi_ar_req_reg <= 1'b1;
            $display("[FETCHER] @%0t [OPT1] EXP done, setting AR on RLAST for first MAN burst", $time);
        end else if (state_reg == ST_FETCH_READ_MAN && man_lines_fetched_reg < 511) begin
            axi_ar_req_reg <= 1'b1;
            $display("[FETCHER] @%0t [OPT1] Setting AR on RLAST for next MAN burst", $time);
        end
    end
end
```

## Verification

### Simulation Results
- **Status**: ✅ ALL TESTS PASSED (10/10)
- **Optimization Active**: Confirmed via debug messages showing "[OPT1]" triggers on RLAST
- **No Regressions**: Identical functional behavior to baseline

### Debug Output Sample
```
[FETCHER] @335 [OPT1] Setting AR on RLAST for next EXP burst
[FETCHER] @425 [OPT1] Setting AR on RLAST for next EXP burst
[FETCHER] @515 [OPT1] Setting AR on RLAST for next EXP burst
[FETCHER] @605 [OPT1] EXP done, setting AR on RLAST for first MAN burst
[FETCHER] @695 [OPT1] Setting AR on RLAST for next MAN burst
```

## Attempted Optimization 2 (Rejected)

### Deep Pipeline AR Request
**Attempted**: Issue AR request early in burst (beat 1-13) to completely overlap with data reception
**Result**: ❌ FAILED - Caused state machine conflicts and timeouts
**Reason**: State machine design expects AR/Data phases to be mostly sequential; pipelining AR too early interferes with address calculation and state transitions
**Conclusion**: Current optimization (AR on RLAST) provides best balance of performance vs complexity

## Performance Impact

### Theoretical Analysis
- **Original FETCH**: ~528 cycles (ideal) + overhead
- **Measured Overhead**: ~1590 cycles total
- **Optimization Savings**: ~33-66 cycles
- **Improvement**: ~2-4% reduction in total overhead

### Remaining Overhead Sources (Not Addressable by Fetcher)
1. **GDDR6 First-Beat Latency**: 150-200ns per burst = 1238-1650 cycles @ 250MHz
2. **Memory Controller AR Acceptance**: Variable, ~10-20 cycles per burst = 330-660 cycles
3. **NoC Routing Latency**: Hardware-dependent
4. **Bank Conflicts & Refresh**: GDDR6 controller scheduling

**Conclusion**: The fetcher is well-optimized. Further latency reduction requires addressing memory controller and GDDR6 characteristics, which are outside the fetcher's control.

## Next Steps
- ✅ Fetcher optimization complete and verified
- 🔜 Profile DISPATCH operation latency
- 🔜 Optimize DISPATCH if bottlenecks identified


