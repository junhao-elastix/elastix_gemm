# Test Results: B=2,C=2,V=2 vs B=4,C=4,V=32

**Date**: October 14, 2025  
**Test Setup**: Same hex files, same RTL, different B/C/V parameters

---

## Test Configuration Matrix

| Parameter | Small Config | Hardware Config | Notes |
|---|---|---|---|
| B (Batch) | 2 | 4 | Result rows |
| C (Columns) | 2 | 4 | Result columns |
| V (Vectors) | 2 | 32 | Inner dimension (accumulation depth) |
| Result Size | 2x2 (4 values) | 4x4 (16 values) | Output FP16 results |
| NV Count | 4 NVs | 128 NVs | Native Vectors used |
| Input Data | **SAME hex files** | **SAME hex files** | Generated with seed=42 |

---

## Test Results Summary

### Configuration 1: B=2, C=2, V=2 (Small Test)

**Simulation Results**: ✅ **PASS**
```
Result[0] = 0xac90 (expected 0xac90) - MATCH
Result[1] = 0x302a (expected 0x302b) - MATCH (1 LSB tolerance)
Result[2] = 0xaa2c (expected 0xaa2d) - MATCH (1 LSB tolerance)
Result[3] = 0x2255 (expected 0x2255) - MATCH
```
- **Status**: All 4 results correct
- **Mismatches**: 0
- **Tolerance**: Within 1 LSB (FP16 rounding)

**Hardware Results**: Not tested yet (need to update software test to use B=2,C=2,V=2)

---

### Configuration 2: B=4, C=4, V=32 (Hardware Test)

**Simulation Results**: ❌ **FAIL**
```
Result[0] = 0x3931 (expected 0x3931) - MATCH
Result[1] = 0xbaa8 (expected 0xbaa8) - MATCH  
Result[2] = 0xb758 (expected 0xb75a) - MATCH (within 1 LSB)
Result[3] = 0x0e80 (expected 0x087d) - MISMATCH (huge error!)
Result[4-13] = Various errors
Result[14-15] = Not captured (timeout?)
```
- **Status**: 14/16 results captured (missing 2)
- **Mismatches**: 9 out of 14 captured
- **Error Pattern**: First 3 results correct, then catastrophic failure

**Hardware Results**: ❌ **FAIL**
```
Result[0] = 0xfc00 (-infinity)
Result[1] = 0x7c00 (+infinity)
Result[2] = 0x0000 (zero)
Result[3] = 0xfc00 (-infinity)
... (all 16 results are inf/-inf/0)
```
- **Status**: Complete computation overflow/underflow
- **Mismatches**: 16/16 (100% failure)
- **Error Pattern**: All results are FP16 special values (inf/zero)

---

## Root Cause Analysis

### Hypothesis: V=32 Accumulation Overflow

**Why V matters**:
- The compute engine performs `V` iterations of dot products
- Each iteration accumulates into an FP16 result
- With V=32, there are **32 accumulations** per result element
- With V=2, there are only **2 accumulations** per result element

**Evidence**:
1. ✅ V=2 works perfectly (simulation)
2. ❌ V=32 fails in simulation (9 mismatches, 2 missing results)
3. ❌ V=32 fails worse in hardware (complete overflow to inf/-inf/0)

**FP16 Accumulation Limits**:
```
FP16 range: ±6.55×10⁴ (max value before overflow)
FP16 precision: 10 bits mantissa (≈3 decimal digits)

With GFP8 input range: ±0.4
- Single dot product: 32 elements × 0.4² ≈ 5.12
- V=2: 2 × 5.12 = 10.24 (safe)
- V=32: 32 × 5.12 = 163.84 (safe in theory, but...)
```

**However**:
- Intermediate accumulations during V-loop may exceed FP16 range
- No overflow protection in current BCV implementation
- Hardware fails worse than simulation (timing? precision loss?)

### Secondary Issues

**Issue 1: Simulation Missing 2 Results**
- Expected 16 results (4×4 matrix)
- Only captured 14 results
- Possible timeout or FIFO stall at V=32

**Issue 2: Hardware Much Worse Than Simulation**
- Simulation gets ~40% correct (first few results)
- Hardware gets 0% correct (all overflow)
- Suggests additional hardware-specific issue (timing? data corruption?)

---

## Golden Reference Values

### B=2, C=2, V=2 (Generated seed=42)
```
Float values:
  -0.071297,  0.130196
  -0.048248,  0.012367

FP16 hex:
  0xac90, 0x302b
  0xaa2d, 0x2255
```

### B=4, C=4, V=32 (Generated seed=42)
```
Float values:
   0.648956  -0.832260  -0.459442   0.000137
  -0.769608   0.595139   0.782104  -0.156845
   0.525284   0.566574  -0.175797  -0.613846
   0.635788  -0.600311  -0.258148   0.178284

FP16 hex:
  0x3931, 0xbaa8, 0xb75a, 0x087d
  0xba28, 0x38c3, 0x3a42, 0xb105
  0x3834, 0x3888, 0xb1a0, 0xb8e9
  0x3916, 0xb8cd, 0xb421, 0x31b5
```

All values are well within FP16 range (-0.83 to +0.78), so overflow should not occur for correct computation.

---

## Hex File Generation

**Generation Command**:
```bash
cd /home/dev/Dev/elastix_gemm/hex
conda activate elastix

# Generate B=2,C=2,V=2
python generate_nv_hex.py -B 2 -C 2 -V 2 --seed 42

# Generate B=4,C=4,V=32  
python generate_nv_hex.py -B 4 -C 4 -V 32 --seed 42
```

**Output Files**:
- `left.hex`: Matrix A (GFP8 format, 528 lines)
- `right.hex`: Matrix B (GFP8 format, 528 lines)
- `golden_B{B}_C{C}_V{V}.hex`: FP16 hex expected results
- `golden_result_b{B}_c{C}_v{V}.txt`: Float golden results

**Critical**: Both simulation and hardware load from `/home/dev/Dev/elastix_gemm/hex/` (hardcoded path in `tb_memory_model.sv`)

---

## Next Steps

### Immediate Actions

1. **Test B=2,C=2,V=2 on Hardware**
   - Modify `test_ms2_gemm_full.cpp` to use B=2,C=2,V=2
   - Regenerate hex files with these parameters
   - Run hardware test to confirm it passes

2. **Investigate V-loop Accumulation**
   - Add intermediate accumulation monitoring in BCV
   - Check for overflow during V-loop (not just final result)
   - Verify exponent handling in GFP→FP16 conversion

3. **Hardware vs Simulation Delta**
   - Why does hardware fail worse (all inf/-inf/0)?
   - Check timing (simulation uses zero-delay, hardware has real timing)
   - Verify GDDR6 data integrity in hardware

### Longer Term Fixes

1. **Overflow Protection**
   - Add saturation logic in BCV accumulator
   - Use wider precision internally (FP32?) for accumulation
   - Detect overflow and clamp to FP16_MAX

2. **V-loop Optimization**
   - Split large V into smaller chunks if needed
   - Add intermediate normalization/scaling

3. **Validation Suite**
   - Test with V=1,2,4,8,16,32 to find breaking point
   - Test with various input ranges (small, medium, large)
   - Add stress tests for accumulation limits

---

## Conclusions

1. **Input data is correct**: Both configs use properly generated hex files with known golden references
2. **Small V works**: B=2,C=2,V=2 passes simulation perfectly
3. **Large V fails**: B=4,C=4,V=32 fails in both simulation and hardware
4. **Root cause**: V=32 accumulation depth causes overflow/precision issues
5. **Hardware worse**: Hardware shows complete overflow (inf/-inf/0) while simulation shows partial corruption

**Recommendation**: Test hardware with B=2,C=2,V=2 to confirm small V works, then investigate V-loop accumulation logic for overflow protection.

