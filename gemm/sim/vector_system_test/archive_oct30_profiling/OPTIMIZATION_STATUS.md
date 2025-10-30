# State Machine Optimization - Status

## Current Status: BLOCKED - Need User Input

### Problem
The initial attempt to eliminate the ST_FETCH_READ ping-pong caused issues:
1. First attempt (direct EXP→MAN transition): Data fetched correctly but wrong amount (19 EXP, 515 MAN instead of 16/512)
2. Second attempt (hybrid EXP→READ→MAN): Watchdog timeout - fetcher got stuck

### Root Cause
The AR-on-RLAST optimization and state transitions need careful coordination:
- AR must be issued at the right time
- State transitions must happen at the right cycle
- Counters (exp_lines_fetched_reg, man_lines_fetched_reg) must be checked at the right point

###  Options Going Forward

**Option 1: Conservative Fix (Safest)**
- Keep ST_FETCH_READ state
- Only eliminate ping-pongs WITHIN a phase (EXP or MAN)
- Still use READ state for phase transitions (INIT→EXP, EXP→MAN)
- Expected savings: ~125 cycles (130 bursts within phases)

**Option 2: Complete Elimination (Riskier, needs careful design)**
- Remove ST_FETCH_READ entirely
- Handle AR issuing within EXP/MAN states
- Need to add logic for phase transition AR requests
- Expected savings: ~132 cycles (all ping-pongs)

**Option 3: Leave As-Is**
- Current optimization (AR-on-RLAST) already saves ~33 cycles
- State machine works correctly
- Total latency: 793 cycles (acceptable)

### Recommendation
Given the complexity and risk of bugs, I recommend **Option 3: Leave the current implementation as-is** for now. The 793-cycle latency is already quite good, and the state machine is proven to work correctly.

**The real bottleneck is NOT the 132-cycle state overhead - it's the fundamental ~660 cycles needed for data transfer with the current memory latency.**

If further optimization is needed, focus on:
1. Memory system improvements (reduce first-beat latency)
2. Wider data bus (transfer more data per cycle)
3. Better burst management

###  Current Performance
- Total FETCH: 793 cycles
- ST_FETCH_READ overhead: 132 cycles (17%)
- Actual data transfer: 660 cycles (83%)
- AXI efficiency: Optimal (0 AR waits, 0 R gaps)

### Files Modified (Need Revert)
- `/home/workstation/elastix_gemm/gemm/src/rtl/fetcher.sv` - state machine changes



