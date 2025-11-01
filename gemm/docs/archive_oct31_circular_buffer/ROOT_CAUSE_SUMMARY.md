# Root Cause Analysis Summary - Oct 30, 2025

## Test Results

| Test Suite | Environment | Status | Details |
|------------|-------------|--------|---------|
| **compute_engine_test** | Simulation | ✅ 10/10 PASS | Compute engine logic validated |
| **vector_system_test** | Simulation | ✅ 10/10 PASS | Full system validated |
| **test_gemm.cpp** | Hardware VP815 | ❌ 1/10 PASS | Only B1_C1_V1 passes |

## Critical Finding

**The compute engine itself is NOT the problem!**

The `compute_engine_test` directly writes test data to tile_bram (simulating DISPATCH) and runs TILE commands. All 10 tests pass, proving:
- ✅ BCV controller B×C×V loop logic is correct
- ✅ NV index calculations are correct  
- ✅ GFP8 dot product computation is correct
- ✅ V-loop accumulation is correct
- ✅ FP16 conversion is correct

## Root Cause Hypothesis

Since hardware fails but simulation passes, the issue is in **data delivery to tile_bram**:

### Most Likely: FETCH/DISPATCH Data Path Issue

**Evidence**:
1. B1_C1_V1 passes (uses minimal data: 1 NV left + 1 NV right)
2. Multi-result tests fail (use multiple NVs from tile_bram)
3. Wrong values suggest wrong data being computed on
4. Compute engine logic validated in isolation

**Possible Issues**:
1. **FETCH Operation**: Data not correctly fetched from GDDR6 to dispatcher_bram
   - Wrong address calculation?
   - Wrong page ID for GDDR6 channel?
   - AXI burst issues?

2. **DISPATCH Operation**: Data not correctly copied from dispatcher_bram to tile_bram
   - Address mapping wrong?
   - Broadcast/distribute mode issue?
   - Write enable timing?

3. **tile_bram Packing**: NV packing logic has bugs
   - Line-to-NV conversion wrong?
   - Exponent byte packing wrong?
   - Group indexing wrong?

### Debug Plan

#### Step 1: Verify GDDR6 Data
Check if matrices are correctly written to GDDR6:
```bash
# Read back from GDDR6 after DMA write
# Compare with hex files
```

#### Step 2: Check FETCH Debug Signals  
Monitor FETCH operation:
- AXI transaction count
- BRAM write addresses
- Data patterns

#### Step 3: Check DISPATCH Debug Signals
Monitor DISPATCH operation:
- Source addresses (dispatcher_bram)
- Destination addresses (tile_bram)
- Write enable patterns
- Column enable processing

#### Step 4: Verify tile_bram Contents
After DISPATCH, read tile_bram memory:
- Check NV[0] matches expected data
- Verify exponent packing
- Confirm mantissa groups

## Observation: Negative Value Issue

**Pattern**:
- Simulation B2_C2_V2: Has negative FP16 values (0x842d, 0x848d with bit 15 set)
- Hardware B2_C2_V2: All positive values (0x0742, 0x0307, 0x059a, 0x038e)

This suggests:
- Sign bit lost or flipped
- Possibly exponent byte ordering issue
- Or mantissa alignment problem

## Direct-Feed Optimization (Deferred)

The optimization to remove intermediate buffering is valid but has timing challenges:
- tile_bram → gfp8_nv_dot direct connection saves 1-2 cycles/V
- But requires indices stable one cycle before capture
- Deferred until after root cause fixed

## Status

- **Compute Engine**: Validated ✅
- **Data Path**: Under investigation ❌
- **Focus**: FETCH → dispatcher_bram → DISPATCH → tile_bram

Next step: Add debug output to hardware test to monitor FETCH/DISPATCH operations.












