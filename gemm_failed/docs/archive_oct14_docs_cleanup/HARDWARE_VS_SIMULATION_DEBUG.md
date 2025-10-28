# Hardware vs Simulation Debug Analysis

**Date**: October 14, 2025  
**Status**: Simulation PASSES, Hardware FAILS (inf/-inf/0 results)

---

## Test Configuration Comparison

| Parameter | Simulation | Hardware |
|-----------|-----------|----------|
| Input Format | GFP8 (8-bit mantissa) | GFP8 (8-bit mantissa) |
| Matrix Dimensions | B=2, C=2, V=2 (2×2 output) | B=4, C=4, V=32 (4×4 output) |
| Mantissa Mode | `man_4b = 0` (8-bit) | `man_4b_8b_n = 0` (8-bit) |
| Data Files | `vector_system_test/left.hex`, `right.hex` | `/hex/left.hex`, `right.hex` |
| Result Format | FP16 | FP16 |

---

## Critical Findings

### 1. Input Data Mismatch (FIXED)
- **Issue**: Hardware was using **wrong `right.hex`** file (1059 lines different from simulation)
- **Fix**: Copied correct `right.hex` from `gemm/sim/vector_system_test/` to `/hex/`
- **Result**: Still getting inf/-inf/0 (so this wasn't the only issue)

### 2. Results Comparison

**Simulation (B=2, C=2, V=2) - PASS**:
```
result_0 = 0xb414 (FP16: valid)
result_1 = 0x2ecb (FP16: valid)
result_2 = 0x3344 (FP16: valid)  
result_3 = 0x326b (FP16: valid)
```

**Hardware (B=4, C=4, V=32) - FAIL**:
```
Result[0] = 0xfc00 (FP16: -infinity)
Result[1] = 0x7c00 (FP16: +infinity)
Result[2] = 0x0000 (FP16: zero)
Result[3] = 0xfc00 (FP16: -infinity)
```

**Golden Reference (Hardware)**:
```
golden[0] = 0.454346   (expected, within FP16 range)
golden[1] = 0.902344   (expected, within FP16 range)
golden[2] = -0.554688  (expected, within FP16 range)
golden[3] = -1.03906   (expected, within FP16 range)
```

---

## Root Cause Hypotheses

### Primary Suspect: Accumulation Overflow with V=32

**Theory**: The compute engine accumulates V=32 iterations, which could overflow FP16:
- Simulation uses V=2 (small accumulation) → Works
- Hardware uses V=32 (16× more accumulation) → Overflows to inf/-inf

**Evidence**:
1. Simulation passes with V=2
2. Hardware fails with V=32
3. All results are exactly inf/-inf/0 (typical overflow pattern)
4. Golden values are reasonable, but intermediate products might be large

**FP16 Limits**:
- Max value: ±65504
- Min normalized: ±6.10×10⁻⁵
- Overflow → ±infinity
- Underflow → 0

### Secondary Suspects

1. **Timing Issue**: Hardware might have setup/hold violations causing data corruption
   - Evidence: Simulation (zero-delay) works, hardware (real timing) fails
   - Mitigation: Check if clock speeds match expectations

2. **Initialization Issue**: GDDR6 or tile memory not properly initialized
   - Evidence: All results overflow (not just random wrong values)
   - Mitigation: Check FETCH/DISPATCH phases complete correctly

3. **Data Format Mismatch**: GFP8 → FP16 conversion issue
   - Evidence: inf/-inf suggests format problem, not just wrong data
   - Mitigation: Verify exponent/mantissa reconstruction logic

---

## Next Steps

### Immediate Actions

1. **Test with smaller V** (B=2, C=2, V=2 in hardware):
   - Modify `test_ms2_gemm_full.cpp` to use same dimensions as simulation
   - If this passes → confirms V=32 overflow issue
   - If this fails → indicates deeper problem

2. **Check intermediate debug signals**:
   - Monitor accumulation values during MATMUL
   - Check if overflow happens early or late in V-loop
   - Verify exponent reconstruction from GFP8

3. **Verify FETCH/DISPATCH phases**:
   - Confirm data is correctly transferred to tile memory
   - Check if GDDR6 read values match expected
   - Verify DISPATCH correctly unpacks GFP8 → internal format

### Hardware Debug Commands

```bash
# Run test with smaller dimensions (edit test to B=2,C=2,V=2)
cd /home/dev/Dev/elastix_gemm/gemm/sw_test
./test_ms2_gemm_full

# Check engine debug registers
./test_registers

# Verify GDDR6 data integrity
./test_mem_endpoints
```

### Simulation Verification

```bash
# Re-run simulation with B=4,C=4,V=32 to match hardware
cd /home/dev/Dev/elastix_gemm/gemm/sim/engine_gddr6_test
# Edit tb_engine_gddr6.sv: TEST_B=4, TEST_C=4, TEST_V=32
make clean && make run
```

---

## Files Modified

### Input Data (Fixed)
- `/home/dev/Dev/elastix_gemm/hex/right.hex` → Copied from simulation (was incorrect)
- `/home/dev/Dev/elastix_gemm/hex/left.hex` → Copied from simulation (for consistency)

### Test Programs
- `test_ms2_gemm_full.cpp` → Uses corrected hex files
- Simulation `tb_engine_gddr6.sv` → Passes with V=2

---

## Infrastructure Status ✓

**All infrastructure is working correctly:**
- ✅ Result BRAM DMA at NAP[3][5] (`0x4140000000`)
- ✅ GDDR6 DMA (256MB validated)
- ✅ Command processing (FETCH, DISPATCH, MATMUL all execute)
- ✅ Engine completion (no timeouts)
- ✅ PCIe/DMA stable (no device hangs)

**Only issue**: Computation produces inf/-inf/0 instead of correct FP16 values.

---

## Conclusion

The problem is **NOT infrastructure** - all datapath components work. The issue is likely:
1. **Accumulation overflow with V=32** (most likely)
2. **GFP8 format handling** at larger scales
3. **Timing-related data corruption** (less likely, since commands execute correctly)

**Recommendation**: Test with B=2,C=2,V=2 in hardware to isolate the V=32 overflow hypothesis.

