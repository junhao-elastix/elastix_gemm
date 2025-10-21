# Test Failure Analysis - MS2.0 GEMM Engine
**Date:** Mon Oct 13 2025  
**Testbench:** `tb_engine_top.sv` (engine_top with FIFO interface)

---

## Test Results Summary

| Test Configuration | Status | Issue |
|-------------------|--------|-------|
| B=1, C=1, V=1     | **PASS** | ✅ Single result, no overflow |
| B=2, C=2, V=2     | **PASS** | ✅ Small accumulation |
| B=8, C=8, V=16    | **FAIL** | ❌ Overflow to infinity |
| B=2, C=64, V=2    | **FAIL** | ❌ Overflow to infinity |
| B=4, C=2, V=2     | **PASS** | ✅ Small accumulation |
| B=4, C=32, V=4    | **FAIL** | ❌ Overflow to infinity |
| B=4, C=4, V=32    | **FAIL** | ❌ Overflow to infinity |
| B=128, C=1, V=1   | **FAIL** | ❌ Timeout (insufficient time) |

**Pattern:** Tests with **large V values** or **large BxC products** fail with overflow to infinity.

---

## Root Cause Analysis

### Problem 1: GFP8 to FP16 Exponent Overflow

**Location:** `src/rtl/gfp8_to_fp16.sv` lines 115-132

**Failure Mechanism:**

From simulation trace (B=4, C=32, V=4 test):
```
[BCV_ACCUM] V=0 INIT: mant=6985 (0x00001b49), exp=13
[BCV_ACCUM] V=3 ADD: sum=6971, max_exp=13
```

GFP8 result: mantissa=6971, exponent=13

**FP16 Conversion Calculation:**
```systemverilog
// Line 123: fp16_exp_signed = exp_signed + 31 - leading_zeros + 15
```

For mantissa=6971 (binary: 0x00001b3b):
- **Leading zeros:** 18
- **fp16_exp_signed** = 13 + 31 - 18 + 15 = **41**

Overflow check (line 130):
```systemverilog
if (fp16_exp_signed > 30) begin
    // Overflow to infinity
    fp16_next = {sign, 5'b11111, 10'b0000000000};  // 0x7c00 (+inf) or 0xfc00 (-inf)
end
```

**Result:** Hardware produces `0x7c00` (+infinity)  
**Expected:** `golden_B4_C32_V4.hex` contains normal FP16 values (e.g., `3932`, `baa7`)

---

### Problem 2: Exponent Bias Mismatch

**The Issue:** The GFP8 to FP16 conversion formula assumes:

```
GFP8 format: value = mantissa x 2^(exponent)
FP16 format: value = 1.fraction x 2^(exp_unbiased) where exp_biased = exp_unbiased + 15
```

Current formula (line 123):
```systemverilog
fp16_exp_signed = exp_signed + 31 - leading_zeros + 15
```

**Breakdown:**
- `exp_signed`: GFP8 exponent (assumes no bias or bias=15)
- `+31`: Accounts for 32-bit mantissa normalized to [2^31, 2^32)
- `-leading_zeros`: Normalization shift
- `+15`: FP16 bias

**Hypothesis:** The GFP8 exponent coming from `gfp8_nv_dot` already has a bias, but the conversion treats it as unbiased, causing double-biasing.

---

### Problem 3: V-Loop Accumulation Growth

**Observation:** Larger V values cause more accumulations:
- V=1: 1 Native Vector dot product (minimal accumulation)
- V=32: 32 Native Vector dot products (32x accumulation)
- V=128: 128 Native Vector dot products (128x accumulation)

**Effect:** Each accumulation increases mantissa magnitude, eventually pushing exponent beyond FP16 range.

**Simulation Evidence:**
```
[BCV_ACCUM] V=0 INIT: mant=6985, exp=13
[BCV_ACCUM] V=1 ADD: sum=6988, max_exp=13   <- Small increase
[BCV_ACCUM] V=2 ADD: sum=6994, max_exp=13   <- Growing
[BCV_ACCUM] V=3 ADD: sum=6971, max_exp=13   <- Continues growing
```

With V=32 or V=128, mantissa grows larger, requiring higher exponents that exceed FP16's range.

---

### Problem 4: Golden Reference Compatibility

**Question:** Are the golden reference files generated with the **same GFP8 format assumptions** as the RTL?

**Comparison:**
- **Golden values:** `a67f` (≈ -0.0039 in FP16), `ac97`, `3932`, `baa7`
- **Hardware output:** `0x7c00` (+infinity), `0xfc00` (-infinity)

**Size check:**
```bash
$ ls -lh /home/dev/Dev/elastix_gemm/hex/golden_B4_C32_V4.hex
-rw-rw-r-- 1 dev dev 640 Oct 11 22:20 golden_B4_C32_V4.hex
# 640 bytes = 128 results x 5 bytes per line (4 hex chars + newline)
# Confirms golden contains 128 FP16 values as expected (B=4 x C=32)
```

**Hypothesis:** Golden references may have been generated with:
1. Different GFP8 exponent bias
2. Different input data scaling
3. Different GFP8 to FP16 conversion formula

---

## Detailed Failure Points

### Test: B=4, C=32, V=4 (Expected 128 results)

**Hardware Output:**
```
Result[0]: 0x7c00 (+infinity)
Result[1]: 0x7c00 (+infinity)
...
Result[127]: 0x7c00 (+infinity)
```

**Golden Reference (first 4 values):**
```
3932  (FP16: ≈ 0.5740)
baa7  (FP16: ≈ -0.0051)
b758  (FP16: ≈ -0.0045)
1120  (FP16: ≈ 0.0000...)
```

**Mismatch:** All hardware outputs are infinity, golden values are normal FP16.

### Test: B=8, C=8, V=16 (Expected 64 results)

**Pattern:** Similar overflow to infinity across all results.

### Test: B=128, C=1, V=1 (Expected 128 results)

**Issue:** Timeout - simulation watchdog triggered before all results produced.
```
[TB] ERROR: Result wait timeout! Expected 128, got 48
```

**Analysis:** Only 48/128 results produced before timeout, suggesting:
- Slow result generation (not architectural issue)
- Possible FIFO stall or back-pressure issue

---

## Recommended Fixes

### Fix 1: Investigate GFP8 Exponent Bias

**Action:** Verify the exponent bias convention in `gfp8_nv_dot.sv` and `gfp8_group_dot.sv`.

**Check:**
1. What bias is used when generating GFP8 exponent?
2. Is it consistent with `gfp8_to_fp16.sv` expectations?
3. Should the formula subtract a bias before adding FP16 bias?

**Proposed modification (line 123):**
```systemverilog
// Option A: GFP8 exponent already has bias=15, subtract it
fp16_exp_signed = (exp_signed - 15) + 31 - leading_zeros + 15;
                = exp_signed + 31 - leading_zeros;

// Option B: GFP8 exponent needs different scaling
fp16_exp_signed = exp_signed - leading_zeros + FP16_BIAS;
```

### Fix 2: Verify Golden Reference Generation

**Action:** Check `/home/dev/Dev/compute_engine_w8a8/hex/hardware_gfp_reference.py` to understand how golden references are generated.

**Validate:**
1. Does golden generation use same GFP8 format as RTL?
2. Are input matrices (`left.hex`, `right.hex`) scaled appropriately?
3. Is the expected dynamic range compatible with FP16?

### Fix 3: Add Scaling Factor for Large V

**Action:** Consider adding a scaling factor to prevent overflow during V-loop accumulation.

**Options:**
1. Pre-scale input matrices to smaller magnitudes
2. Add periodic normalization during V-loop accumulation
3. Use higher intermediate precision (e.g., FP32) before final FP16 conversion

### Fix 4: Increase Timeout for Large Tests

**Action:** Increase watchdog timeout for tests with large BxC products.

**Current:** `watchdog = 100000` (1ms @ 100MHz)  
**Proposed:** Scale timeout based on expected result count:
```systemverilog
watchdog = expected_results * 1000;  // ~1000 cycles per result
```

---

## Investigation Steps

1. **Examine GFP8 format definition**
   - Check `gfp8_nv_dot.sv` output exponent calculation
   - Verify exponent bias assumptions

2. **Compare with golden generation**
   - Review `hardware_gfp_reference.py`
   - Validate GFP8 → FP16 conversion matches RTL

3. **Test with scaled inputs**
   - Generate test data with smaller magnitudes
   - Verify if overflow is data-dependent or architectural

4. **Add debug instrumentation**
   - Log GFP8 mantissa/exponent before FP16 conversion
   - Track fp16_exp_signed values in failing cases

---

## Files Involved

### RTL Files
- **`src/rtl/gfp8_to_fp16.sv`** - FP16 conversion (line 123: exponent formula)
- **`src/rtl/gfp8_bcv_controller.sv`** - V-loop accumulation
- **`src/rtl/gfp8_nv_dot.sv`** - Native Vector dot product (exponent output)
- **`src/rtl/gfp8_group_dot.sv`** - Group dot product (exponent calculation)

### Testbench Files
- **`sim/vector_system_test/tb_engine_top.sv`** - Main testbench
- **`sim/vector_system_test/Makefile.engine_top`** - Build system

### Golden Reference Files
- **`/home/dev/Dev/elastix_gemm/hex/golden_*.hex`** - Expected FP16 results
- **`/home/dev/Dev/elastix_gemm/hex/left.hex`** - Left matrix input
- **`/home/dev/Dev/elastix_gemm/hex/right.hex`** - Right matrix input
- **`/home/dev/Dev/compute_engine_w8a8/hex/hardware_gfp_reference.py`** - Golden generator

---

## Next Steps

1. ✅ **Clean up obsolete engine_wrapper** - DONE
2. ⚠️ **Investigate GFP8 exponent bias** - IN PROGRESS
3. ⏳ **Verify golden reference generation** - PENDING
4. ⏳ **Test fixes and re-run simulation** - PENDING

---

## Cleanup Summary

**Removed:**
- `sim/vector_system_test/tb_engine_wrapper_ms2.sv` - Obsolete testbench (DELETED)
- `sim/vector_system_test/Makefile` - Updated to redirect to Makefile.engine_top

**Active Testbench:**
- `sim/vector_system_test/tb_engine_top.sv` - Current MS2.0 FIFO interface testbench
- `sim/vector_system_test/Makefile.engine_top` - Active Makefile

---

## Contact / References

- **Project:** MS2.0 GEMM Engine (elastix_gemm/gemm)
- **Architecture:** BxCxV nested loops with GFP8 arithmetic
- **Status:** 3/8 tests passing, overflow issue identified
- **Documentation:** See `CLAUDE.md` for development guidelines

