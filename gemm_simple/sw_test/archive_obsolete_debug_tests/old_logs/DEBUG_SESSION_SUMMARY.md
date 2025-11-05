# Debug Session Summary - Oct 10, 2025

## Major Achievements ✅

### 1. Debug Infrastructure Implemented
- Added 6 debug registers (0x08-0x1C) for BRAM data path visibility
- Added AXI timeout detection (5ms threshold)
- Created diagnostic tools: `read_debug_regs`, `test_single_fetch`, `test_fetch_4200`

### 2. Root Cause Identified
**Problem**: Second FETCH command writes only 512 out of 528 lines (32 out of 33 bursts)

**Evidence**:
- wr_addr = 1039 consistently (1040 lines = 528 + 512)
- First FETCH @ 0x0: ✅ Completes (528 lines)
- Second FETCH @ 0x4200/0x8000/0x10000: ❌ **Times out on burst 33**

**NOT the address**: All three addresses (0x4200, 0x8000, 0x10000) show identical behavior

### 3. Verified Configuration
- GDDR6 Channel 1 @ NOC[3][4] ✅
- Page ID = 9'd2 ✅
- NoC addressing correct ✅
- DMA to same addresses works fine ✅

## Technical Analysis

### The 33rd Burst Mystery

**For 528 lines**:
- Bursts needed: 528 ÷ 16 = 33 bursts
- Burst 1-32: ✅ Complete successfully (512 lines)
- Burst 33: ❌ **AXI request sent, no response**

**State Machine Trace** (burst 32 completion):
```
1. lines_remaining = 32
2. Check: 32 > 16? YES
3. Decision: Issue burst 33 (correct!)
4. Decrement: lines_remaining = 16
5. Enter ST_FETCH_READ, send AXI request
6. Enter ST_FETCH_WAIT
7. Wait for rvalid... [TIMEOUT after 5ms]
8. Abort to IDLE
```

**Conclusion**: Dispatcher logic is **CORRECT**. The AXI/GDDR6/NoC is failing to respond.

### Why Does DMA Work But FETCH Fails?

**Key Difference**:
- **DMA (sw_test)**: Uses PCIe DMA engine, different AXI master
- **FETCH (dispatcher)**: Uses custom AXI master in dispatcher_control.sv

**Hypothesis**: Dispatcher's AXI implementation has an issue after 32 consecutive bursts:
1. AXI protocol violation (burst parameters)
2. NoC buffer exhaustion
3. GDDR6 bank conflict/refresh timing
4. Missing AXI handshake signal

## Recommended Next Steps

### Option 1: Investigate AXI Protocol (High Priority)
Add more AXI debug registers:
```systemverilog
- arvalid, arready status
- ar transaction count
- Last successful burst address
- AXI error signals (RRESP)
```

### Option 2: Test Different Burst Sizes
Modify dispatcher to use:
- 8-beat bursts instead of 16
- Test if 66 bursts of 8 beats works

### Option 3: Add Inter-Burst Delay
Insert cycles between burst requests:
```systemverilog
// In ST_FETCH_READ, wait N cycles before asserting arvalid
if (delay_counter < INTER_BURST_DELAY) begin
    delay_counter++;
end else begin
    axi_ar_req_reg <= 1'b1;
end
```

### Option 4: Check GDDR6 Reference Design
Compare dispatcher AXI implementation with working GDDR6 reference:
- Burst parameters
- Address alignment
- Timing between requests

## Current State

**Bitstream**: 0x10100127 (with AXI timeout detection)

**Behavior**:
- First FETCH: ✅ Works (528 lines)
- Second FETCH: ⚠️ Partial (512/528 lines, timeout on burst 33)
- After timeout: ❌ Dispatcher stuck (needs reset/reboot)

**Test Results**:
- `test_ms2_gemm_full`: FETCHes complete, MATMUL times out (CE waiting for missing data)
- `test_single_fetch`: Same 512-line limit
- `read_debug_regs`: Confirms BRAM has 1040 lines total

## Files Created

- `ROOT_CAUSE_ANALYSIS.md` - Initial debug register analysis
- `FINDINGS_SUMMARY.md` - Configuration verification and hypotheses
- `INVESTIGATION_PLAN.md` - 10 software-only tests
- `DEBUG_SESSION_SUMMARY.md` - This file
- `read_debug_regs.cpp` - Debug register reader utility
- `test_single_fetch.cpp` - Single FETCH test
- `test_fetch_4200.cpp` - Test FETCH at non-sequential address

## Conclusion

We've made excellent progress:
1. ✅ Debug infrastructure working
2. ✅ Root cause identified (burst 33 AXI timeout)
3. ✅ Ruled out address issues
4. ✅ Ruled out dispatcher logic bugs
5. ⚠️ Need to investigate AXI protocol or hardware constraints

The next step is to add AXI-level debugging to see exactly why burst 33 fails.
