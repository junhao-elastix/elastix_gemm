# MLP Column Mapping Reference

This document provides a concise reference for how `mlp_bram_col` maps weights, activations, and outputs to columns. This is partially extracted and clarified from ARCHITECTURE.md Section 18.

## 1. Architecture Summary

```
NUM_MLPS = 8
Columns per MLP = 2 (Bank 0 and Bank 1)
Total Columns = NUM_MLPS x 2 = 16
```

**Key Insight:** `mlp_bram_col` computes **16 independent dot products in parallel**, NOT one large dot product.

## 2. Hardware Structure

**Source:** `src/acx_mlp/rtl/mlp_bram_col.sv`

```
                     din (72-bit) - BROADCAST to all MLPs
                          |
        +-----------------+-----------------+
        |                 |                 |
        v                 v                 v
    +-------+         +-------+         +-------+
    | MLP 0 |   ...   | MLP 3 |   ...   | MLP 7 |
    +-------+         +-------+         +-------+
    |Bank 0 |         |Bank 0 |         |Bank 0 |  <-- Different weights per bank
    |Bank 1 |         |Bank 1 |         |Bank 1 |
    +---+---+         +---+---+         +---+---+
        |                 |                 |
        v                 v                 v
    dout[0]           dout[3]           dout[7]
    (72-bit)          (72-bit)          (72-bit)
```

- **ALL MLPs receive the SAME `din`** (activations are broadcast)
- **Each MLP has DIFFERENT weights** in its BRAM (via per-MLP `wren[i]` write enables)
- **Each MLP produces 2 results** (one per bank)

## 3. Column to MLP/Bank Mapping

For column index `c` (0 to 15):

| Column | MLP Index | Bank | Weight Source | Result Location |
|--------|-----------|------|---------------|-----------------|
| 0 | 0 | 1 (CD) | `weights[0,:,0]` | `dout[0][23:0]` |
| 1 | 0 | 0 (AB) | `weights[1,:,0]` | `dout[0][47:24]` |
| 2 | 1 | 1 (CD) | `weights[0,:,1]` | `dout[1][23:0]` |
| 3 | 1 | 0 (AB) | `weights[1,:,1]` | `dout[1][47:24]` |
| 4 | 2 | 1 (CD) | `weights[0,:,2]` | `dout[2][23:0]` |
| 5 | 2 | 0 (AB) | `weights[1,:,2]` | `dout[2][47:24]` |
| 6 | 3 | 1 (CD) | `weights[0,:,3]` | `dout[3][23:0]` |
| 7 | 3 | 0 (AB) | `weights[1,:,3]` | `dout[3][47:24]` |
| 8 | 4 | 1 (CD) | `weights[0,:,4]` | `dout[4][23:0]` |
| 9 | 4 | 0 (AB) | `weights[1,:,4]` | `dout[4][47:24]` |
| 10 | 5 | 1 (CD) | `weights[0,:,5]` | `dout[5][23:0]` |
| 11 | 5 | 0 (AB) | `weights[1,:,5]` | `dout[5][47:24]` |
| 12 | 6 | 1 (CD) | `weights[0,:,6]` | `dout[6][23:0]` |
| 13 | 6 | 0 (AB) | `weights[1,:,6]` | `dout[6][47:24]` |
| 14 | 7 | 1 (CD) | `weights[0,:,7]` | `dout[7][23:0]` |
| 15 | 7 | 0 (AB) | `weights[1,:,7]` | `dout[7][47:24]` |

### Formulas

```
MLP_index   = c // 2
Bank_index  = (c + 1) % 2      # Column 0 -> Bank 1, Column 1 -> Bank 0
Weight_idx  = c % 2            # weights[0] for even cols, weights[1] for odd cols

Result bits:
  if c % 2 == 0: dout[c//2][23:0]    # Even columns -> lower 24 bits
  if c % 2 == 1: dout[c//2][47:24]   # Odd columns -> upper 24 bits
```

## 4. Weight Loading via `write_bram_params()`

**Source:** `src/acx_mlp/tests/acx_mlp_tests.py` (lines 83-128)

The test function `write_bram_params(bram_offset, bank0_params, bank1_params, mlp_mask)` writes weights as follows:

```python
# From src/acx_mlp/tests/acx_mlp_tests.py lines 105-124
low_bank = pack_bytes(bank1_params)   # bank1 data
high_bank = pack_bytes(bank0_params)  # bank0 data

# Write to BRAM:
wraddr = bram_offset     -> low_bank (bank1_params)   # Even address
wraddr = bram_offset + 1 -> high_bank (bank0_params)  # Odd address
```

**BRAM Asymmetric Read:**
```
rdaddr N reads:
  - wraddr 2N   (even) -> BRAM_DOUT[71:0]   -> Bank 0 (AB) physically
  - wraddr 2N+1 (odd)  -> BRAM_DOUT[143:72] -> Bank 1 (CD) physically
```

**Result:**
- `bank0_params` (weights[0]) -> odd wraddr -> BRAM[143:72] -> Bank 1 (CD) -> `dout[23:0]`
- `bank1_params` (weights[1]) -> even wraddr -> BRAM[71:0] -> Bank 0 (AB) -> `dout[47:24]`

## 5. Output Extraction via `get_outputs()`

**Source:** `src/acx_mlp/tests/acx_mlp_tests.py` (lines 173-182)

```python
# From src/acx_mlp/tests/acx_mlp_tests.py lines 173-182
def get_outputs(self) -> list[tuple[float, float]]:
    results = []
    for mlp_index in range(self.NUM_MLPS):
        mlp_out = self.dut.dout[mlp_index].value
        ed0 = int_to_float24(mlp_out[23:0].to_signed())   # Column 2*mlp_index
        ed1 = int_to_float24(mlp_out[47:24].to_signed())  # Column 2*mlp_index + 1
        results.append((ed0, ed1))
    return results
```

**Output format per MLP:**

**Source:** `src/acx_mlp/rtl/mlp_dot16_bfp8.sv` (line 521, `outmode_sel=2'b11`)

```
dout[71:48] = {12'h0, fp_ab_status[3:0], fp_cd_status[3:0]}  (status)
dout[47:24] = accum_ab_reg[23:0]  (Bank 0/AB result = odd column)
dout[23:0]  = out_reg[23:0]       (Bank 1/CD result = even column)
```

## 6. Computation Model

For a vector-matrix multiplication `y = x * W`:

```
x: (1 x N) activation vector, streamed via din (8 elements/cycle, N/8 cycles)
W: (N x 16) weight matrix, stored across 8 MLPs x 2 banks
y: (1 x 16) output vector

y[c] = SUM x[i] * W[i, c]   for i = 0 to N-1
```

**Each column `c` computes independently:**
- Same activations `x` (broadcast)
- Different weights `W[:, c]` (stored in MLP[c//2], bank corresponding to c%2)

## 7. Cycle-by-Cycle Computation

**Source:** `src/acx_mlp/tests/acx_mlp_tests.py` (lines 236-279, `accumulate_dot_products()`)

For computing one row of `left` (activation) against all 16 columns of `right` (weight):

```
Cycle 0:
  din    = activations[0]      (8 elements, broadcast to all MLPs)
  rdaddr = 0
  For each column c:
    weight = weights[c][rdaddr] = weights[c][0:7]
    partial[c] = dot(din, weight)  (8-element dot product)

Cycle 1:
  din    = activations[1]
  rdaddr = 1
  For each column c:
    weight = weights[c][8:15]
    partial[c] += dot(din, weight)  (accumulate enabled)

...

Cycle n:
  din    = activations[n]
  rdaddr = n
  For each column c:
    weight = weights[c][8n : 8n+7]
    partial[c] += dot(din, weight)  (accumulate)
```

**After N/8 cycles:**
```
result[c] = SUM over n=0 to N/8-1 of dot(activations[n], weights[c][n])
          = full N-element dot product for column c
```

**Result:** 16 independent dot products computed in parallel, one per column.

### Control Signal Timing (from testbench)

**Source:** `src/acx_mlp/tests/acx_mlp_tests.py` lines 256-270

```python
for i in range(cycle_length):
    apply_input_vector(activations[i])   # din = activations[i]

    if i < cycle_length - 1:
        rdaddr = i + 1                    # Set rdaddr for NEXT cycle

    accumulate = 1 if (i > 0) else 0      # Enable after cycle 0
    load = 1 if (i == 2 and new_dot) else 0  # Load at cycle 2

    await RisingEdge(clk)
```

| Cycle | din | rdaddr | accumulate | load | Notes |
|-------|-----|--------|------------|------|-------|
| 0 | act[0] | 0 | 0 | 0 | First multiply |
| 1 | act[1] | 1 | 1 | 0 | Start accumulating |
| 2 | act[2] | 2 | 1 | 1 | Load first valid result |
| 3+ | act[n] | n | 1 | 0 | Continue accumulating |

### Control Signal Semantics

**Source:** `src/acx_mlp/rtl/mlp_dot16_bfp8.sv` (lines 425-442, 450-455)

| Signal | Parameter | Effect |
|--------|-----------|--------|
| `load=1` | Loads accumulator | Initialize accumulator with current FP_ADD result |
| `accumulate=1` | `fpadd_xx_dinb_sel=3'b000` | FP_ADD B input = ACCUM_REG (feedback loop) |
| `add_accum_xx_bypass=1` | Output bypass | Accumulator output bypassed (show running sum) |

### Pipeline Latency

**Source:** `src/acx_mlp/rtl/mlp_dot16_bfp8.sv` parameter defaults

- `del_multa_l/h = 1'b1`: Input register enabled (1 cycle)
- `del_add_00_07_reg = 1'b1`: Adder register enabled (1 cycle)
- Total: **2-cycle latency** from din to first valid FP result
- `load` at cycle 2: First valid result arrives, initialize accumulator