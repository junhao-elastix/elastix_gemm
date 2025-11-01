# Hardware Test Status - Oct 30, 2025

## Current State

- **Simulation**: 10/10 tests PASS ✅
- **Hardware**: 1/10 tests PASS (only B1_C1_V1) ❌
- **Bitstream**: 10/30 21:00 (Build ID: 0x10302100)

## Test Results Summary

| Test | Expected | HW Results | HW Values | Sim Values | Status |
|------|----------|------------|-----------|------------|--------|
| B1_C1_V1 | 1 | 1 | 0x05f4 | 0x05f4 | ✅ PASS |
| B2_C2_V2 | 4 | 4 | 0x0742, 0x0307, 0x059a, 0x038e | 0x0404, 0x067e, 0x842d, 0x848d | ❌ WRONG VALUES |
| B4_C4_V4 | 16 | 16 | Mixed | All correct | ❌ 2/16 match |
| B8_C8_V16 | 64 | 64 | Mixed | All correct | ❌ 11/64 match |

## Key Findings

###  1. Result Count is Correct
Hardware generates exactly B×C results for all tests. The BCV controller's B×C loop IS working.

### 2. Values are Wrong
Most results have incorrect FP16 values. Pattern analysis:
- **Sim B2_C2_V2**: 0x0404 (pos), 0x067e (pos), **0x842d (neg)**, **0x848d (neg)**
- **HW B2_C2_V2**: 0x0742 (pos), 0x0307 (pos), **0x059a (pos)**, **0x038e (pos)**
- **Issue**: Negative results in simulation appear as positive in hardware

### 3. B=1, C=1, V=1 Works Perfectly
Single result test passes with exact match. This suggests:
- Basic data path works (GDDR6 → dispatcher_bram → tile_bram → compute → result)
- Commands execute correctly
- FP16 conversion works

### 4. Multi-Result Tests Fail
All tests with B>1 or C>1 or V>1 produce wrong values.

## Diagnostics Performed

### Command Encoding ✅
- FETCH, DISPATCH, MATMUL commands verified correct
- Compared testbench vs software encoding: MATCH
- Address calculations correct

### Debug Register Readings
- `BRAM_WR_COUNT` (0x60): Shows 0 ⚠️
  - May indicate FETCH not writing data
  - OR debug signal not connected properly
- `RESULT_COUNT` (0x54): Shows correct B×C count ✅

## Hypotheses to Investigate

### Hypothesis 1: Data Not Fetched from GDDR6
**Evidence**:
- BRAM_WR_COUNT = 0
- Results appear random/wrong

**Counter-Evidence**:
- B1_C1_V1 passes perfectly (uses same FETCH path)
- Wrong values are consistent (not random)

### Hypothesis 2: NV Index Calculation Error
**Evidence**:
- Multi-dimensional tests (B>1, C>1) fail
- Values suggest wrong NVs being read

**Test**:
```systemverilog
// BCV controller calculates:
left_nv_index = left_base_nv + (b_idx * dim_v_reg + v_idx);
right_nv_index = right_base_nv + (c_idx * dim_v_reg + v_idx);
```

### Hypothesis 3: Sign Bit Corruption
**Evidence**:
- Negative FP16 values in simulation appear positive in hardware
- Sign bit issue in accumulation or conversion

### Hypothesis 4: Module Version Mismatch
**Checked**:
- Both simulation and hardware use same `gfp8_bcv_controller.sv`
- No wrapper or ifdef selection
- Same module in filelist.tcl

## Direct-Feed Optimization Analysis

Noticed wasteful double-buffering in current implementation:
1. tile_bram → BCV buffers (nv_left_exp/man) - 1 cycle
2. BCV buffers → gfp8_nv_dot capture - 1 cycle  
3. Total: 2 cycles wasted per V

**Optimization Opportunity**:
- tile_bram NV read is combinational (0-latency)
- Can feed DIRECTLY to gfp8_nv_dot
- Save 1-2 cycles per V iteration
- Simplify state machine (remove ST_FILL_BUFFER)

**Implementation Challenge**:
- Timing: Need NV indices stable BEFORE gfp8_nv_dot capture
- Current attempt failed (indices update same cycle as capture)
- Need careful clock cycle planning

## Next Steps

1. **Verify FETCH operation** with debug signals
2. **Test simpler cases**: B=2,C=1,V=1 and B=1,C=2,V=1
3. **Check NV index calculation** with more debug output
4. **Compare sign handling** between simulation and hardware
5. **Implement direct-feed optimization** (after root cause found)

## Status: Under Investigation

Root cause not yet identified. Hardware generates results but values are incorrect.
Focus should be on data path integrity (FETCH → DISPATCH → tile_bram → compute).












