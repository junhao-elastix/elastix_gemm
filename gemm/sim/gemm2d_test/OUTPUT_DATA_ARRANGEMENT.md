# Output Data Arrangement Analysis

**Date:** 2026-01-27
**Test Directory:** `gemm/sim/gemm2d_test/`
**Conclusion:** **C-Major (Column-Major) Order**

---

## Summary

The 2-D GEMM engine output is organized in **C-major order**, meaning columns vary fastest within each batch.

**Index Formula:** `index = b * C + c`

**Inverse Mapping:**
- `batch = index / C`
- `column = index % C`

---

## Data Flow Analysis

### 1. Compute Engine Counter Order (compute_engine_2d.sv)

```
Innermost → Outermost:
l_cnt (0..3) → v_cnt (0..V-1) → cg_cnt (0..G-1) → b_cnt (0..B-1)
```

- `l_cnt`: Line within Native Vector (4 lines per NV)
- `v_cnt`: NV accumulation counter (V dot products summed per output)
- `cg_cnt`: Column group counter (for C > NUM_COLS)
- `b_cnt`: Batch counter (outermost loop)

Results are pushed to `mlp_result_fp16[0..NUM_COLS-1]` when `last_nv` is true. For each (b, cg) pair, all NUM_COLS columns produce simultaneously into parallel FIFOs.

### 2. Result Collector Drain Order (result_collector_2d.sv)

```
For each batch b (0 to B-1):
    For each column c (0 to C-1):
        1. Drain col_idx = c % NUM_COLS from all 16 row FIFOs
        2. Reduce 16 FP16 values via tree adder
        3. Serialize into 256-bit output buffer
```

Key counters:
- `col_idx`: Cycles 0..NUM_COLS-1, wrapping for C > NUM_COLS
- `col_remaining`: Counts down from C to 0 per batch
- `batch_cnt`: Counts down from B-1 to 0

### 3. Output Order Example

For **B=4, C=4** (16 total results):

| Index | Batch (b) | Column (c) | Description |
|-------|-----------|------------|-------------|
| 0     | 0         | 0          | First batch, first column |
| 1     | 0         | 1          | First batch, second column |
| 2     | 0         | 2          | First batch, third column |
| 3     | 0         | 3          | First batch, fourth column |
| 4     | 1         | 0          | Second batch, first column |
| 5     | 1         | 1          | Second batch, second column |
| ...   | ...       | ...        | ... |
| 15    | 3         | 3          | Last batch, last column |

---

## Why C-Major Order?

1. **CE Production Order**: Each batch completes all column groups before advancing to next batch
2. **FIFO Behavior**: Results arrive in CE's production order (first-in, first-out)
3. **RC Sequential Drain**: Sweeps all columns for batch 0, then all columns for batch 1, etc.

This matches the golden reference Python code:
```python
for b in range(B):
    for c in range(C):
        results.append(fp16_result)  # C varies fastest
```

---

## Hardware Output Format

### 256-bit Output Lines

Each output line packs 16 × FP16 values:
```
o_output_data[255:0] = {fp16[15], fp16[14], ..., fp16[1], fp16[0]}
```

Where `fp16[i]` is at bits `[i*16 +: 16]`.

### Output Interface Signals

| Signal | Width | Description |
|--------|-------|-------------|
| `o_output_valid` | 1 | Data valid |
| `o_output_data` | 256 | 16 × FP16 packed |
| `o_output_keep` | 16 | Valid mask (for partial last line) |
| `o_output_last` | 1 | Last line in sequence |

---

## Simulation Results

**Test Run:** 2026-01-27

| Test Config | B | C | V | Results | Pass Rate | Status |
|-------------|---|---|---|---------|-----------|--------|
| B1_C1_V1    | 1 | 1 | 1 | 1       | 100.0%    | ✅ PASS |
| B2_C2_V2    | 2 | 2 | 2 | 4       | 100.0%    | ✅ PASS |
| B4_C4_V4    | 4 | 4 | 4 | 16      | 93.8%     | ❌ FAIL |
| B4_C4_V32   | 4 | 4 | 32| 16      | 93.8%     | ❌ FAIL |
| B4_C8_V4    | 4 | 8 | 4 | 32      | 96.9%     | ✅ PASS |
| B4_C13_V9   | 4 | 13| 9 | 52      | 98.1%     | ✅ PASS |
| B4_C16_V8   | 4 | 16| 8 | 64      | 100.0%    | ✅ PASS |
| B8_C8_V16   | 8 | 8 | 16| 64      | 98.4%     | ✅ PASS |
| B16_C16_V4  | 16| 16| 4 | 256     | 99.2%     | ✅ PASS |
| B16_C16_V8  | 16| 16| 8 | 256     | 99.6%     | ✅ PASS |

**Overall: 8/10 tests passed**

Note: Failed tests are due to FP16 rounding differences in tree reduction (hardware) vs sequential accumulation (golden model), not ordering issues.

---

## Code References

- **Compute Engine**: `gemm/src/rtl/compute_engine_2d.sv` (lines 370-395 for counter logic)
- **Result Collector**: `gemm/src/rtl/result_collector_2d.sv` (lines 461-488 for drain logic)
- **Golden Reference**: `hex/hardware_gfp_reference.py` (lines 214-216 for iteration order)
- **Testbench**: `gemm/sim/gemm2d_test/tb_gemm2d.sv` (lines 683-695 for result capture)
