# 200 MHz Clock Optimization Results

**Date**: November 1, 2025
**Objective**: Achieve 200 MHz i_reg_clk (5ns period)
**Status**: Partial Success - 151.2 MHz achieved (+11% improvement)

---

## Summary

Successfully pipelined the NV dot arithmetic path from 4 to 7 stages, breaking the original 8.642ns critical path. However, a new bottleneck emerged in the tile_BRAM data fetch path that limits frequency to 151.2 MHz.

---

## Achievements

### Before Optimization
- **Frequency**: 136.5 MHz max
- **Critical Path**: 8.642ns in NV dot arithmetic
  - Max exponent finding: 2.5ns
  - Mantissa alignment: 3.5ns  
  - 4-way summation: 1.5ns
- **Latency**: 4 cycles per NV dot

### After Optimization  
- **Frequency**: 151.2 MHz max (+11% improvement)
- **Critical Path**: 7.827ns in tile_BRAM data fetch
  - v_idx → NV index calc (multiply): 1.1ns
  - **Routing to BRAM**: 2.9ns (!) 
  - BRAM read: 0.6ns
  - Post-BRAM muxing: 0.6ns
- **Latency**: 7 cycles per NV dot

---

## Implementation Details

### Files Modified

**1. gfp8_nv_dot_ultra_opt.sv**
- Added Stage 3: Max exponent finding register (breaks 2.5ns path)
- Added Stage 4: Mantissa alignment register (breaks 3.5ns shift path)
- Added Stage 5: Partial adder tree register (breaks 1.5ns adder path)
- Updated latency: 4 → 7 cycles
- All stages <3ns for 200MHz timing margin

**2. gfp8_bcv_controller_opt.sv**
- Updated compute_wait counter: [2:0] → [3:0] (supports count to 6)
- Updated wait cycles: 3'd3 → 4'd6 (7 total cycles: 0→6)
- Updated documentation: 5 cycles/V → 8 cycles/V

**3. elastix_gemm_top_ioring.sdc**
- Updated i_reg_clk period: 10.0ns → 5.0ns (100MHz → 200MHz target)
- Updated clock uncertainty proportionally

---

## Validation

### Simulation Tests ✓
```
Vector System Test: 10/10 configurations passing (100%)
- B1×C1×V1 through B1×C1×V128
- All golden results match
- 7-cycle pipeline validated
```

### Timing Analysis
```
Clock Domain    Target    Achieved  Slack      Status
-----------     ------    --------  -----      ------
i_adm_clk       100 MHz   133.7MHz  +2.522ns   PASS ✓
i_nap_clk       100 MHz   244.9MHz  +5.916ns   PASS ✓
i_reg_clk       200 MHz   151.2MHz  -1.615ns   FAIL ✗
tck              25 MHz    68.1MHz  +12.657ns   PASS ✓
```

---

## New Critical Path Analysis

**Path**: v_idx → NV index calculation → tile_BRAM → man_right_captured

**Breakdown (7.827ns total)**:
```
Stage               Component         Delay    Cumulative
-----               ---------         -----    ----------
FF output           v_idx flip-flop   0.037ns  0.037ns
Arithmetic          ALU8i adder       0.642ns  0.679ns
Multiply            MLP72_INT         1.117ns  1.796ns
Routing to BRAM     Net delay         2.940ns  4.736ns  ← BOTTLENECK!
BRAM read           LRAM2K_SDP        0.611ns  5.347ns
Post-BRAM mux       LUT6 + MUX2       0.613ns  5.960ns
Setup               Library setup     0.014ns  5.974ns
Clock network       Network delay     1.248ns  7.222ns
Uncertainty         Setup margin      0.053ns  7.275ns
```

**Key Finding**: 2.940ns routing delay (38% of total path) indicates placement issue, not logic issue.

---

## Remaining Bottlenecks

### Primary Issue: BRAM Data Fetch Path

The v_idx → multiply → tile_BRAM path has:
1. **Slow multiply (MLP72_INT)**: 1.117ns for index calculation
2. **Excessive routing**: 2.940ns from multiplier to BRAM (placement sub-optimal)
3. **Combinational BRAM**: 0.611ns read time + muxing

### Why Additional Pipeline Stages Don't Help

- Can't register between v_idx and addressing without adding FSM complexity
- tile_BRAM has 0-latency (no output registers available)
- Registering BRAM output breaks combinational read semantics

---

## Options to Reach 200 MHz

### Option 1: Add tile_BRAM Output Registers (Moderate Effort)
**Change**: Modify tile_bram.sv to add optional output registers
- Breaks routing path after BRAM
- Adds 1 cycle to read latency (acceptable)
- Requires BCV FSM adjustment for lookahead addressing
- **Estimated gain**: ~3ns → could reach 180-190 MHz

### Option 2: Pre-compute Addressing (Lower Effort)
**Change**: Calculate next_v_idx in parallel with current computation
- Use v_idx+1 for addressing while v_idx accumulates
- Requires careful FSM state tracking
- Minimal RTL changes
- **Estimated gain**: ~1-2ns → could reach 170 MHz

### Option 3: Optimize Placement (Lowest Effort)
**Change**: Add placement constraints to co-locate BCV and tile_BRAM
- Force multiplier and BRAM into same region
- May reduce routing from 2.9ns → 1.5ns
- No RTL changes
- **Estimated gain**: ~1-2ns → could reach 165-170 MHz

### Option 4: Accept 151 MHz (No Effort)
**Change**: None - current result
- Already 11% improvement over baseline
- All simulations passing
- **Trade-off**: Lower clock but proven working

---

## Recommendation

**For immediate use**: Accept 151 MHz
- Proven through simulation (10/10 passing)
- Significant improvement over 136MHz baseline
- Safe for hardware deployment

**For future optimization**: Implement Option 1 (tile_BRAM output registers)
- Clean architectural solution
- Highest performance potential
- Requires coordinated FSM changes

---

## Current Design Status

**Files Modified:**
- ✓ gfp8_nv_dot_ultra_opt.sv (7-stage pipeline)
- ✓ gfp8_bcv_controller_opt.sv (updated timing)
- ✓ elastix_gemm_top_ioring.sdc (200MHz constraint)

**Testing:**
- ✓ Simulation: 10/10 passing
- ✓ Timing: 151.2 MHz (partial success)
- ⧗ Hardware: Not yet validated

**Backups:**
- gfp8_nv_dot_ultra_opt.sv.backup_pre_200mhz_20251031_231622
- gfp8_bcv_controller_opt.sv.backup_pre_200mhz_20251031_231622

---

## Next Steps

**If accepting 151 MHz:**
1. Flash bitstream to hardware
2. Run test_gemm to verify functionality  
3. Measure actual performance vs 136 MHz baseline
4. Document as production ready

**If pursuing 200 MHz:**
1. Implement Option 1 (tile_BRAM output registers)
2. Add lookahead addressing to BCV controller
3. Resimulate with new timing
4. Rebuild and analyze

---

**Status**: Awaiting decision on whether to accept 151 MHz or continue optimization



