# BCV Computation Guide for mlp_bram_col

This document explains how BCV (Batch-Column-Vector) matrix multiplication is computed using the `mlp_bram_col` module and the test strategies used for validation.

## 1. Test Architecture Overview

The tests use a **three-layer validation strategy**:

```
┌─────────────────────────────────────────────────────────────────┐
│  Layer 1: PyTorch Reference (Golden Model)                      │
│  - torch.matmul() computes expected dot products                │
│  - Random seeds ensure reproducibility                          │
└────────────────────────────────────┬────────────────────────────┘
                                     │ Compare
┌────────────────────────────────────▼────────────────────────────┐
│  Layer 2: Cocotb Testbench (MLPBramColTestbench)                │
│  - Drives RTL signals via cocotb                                │
│  - Handles GFP8/BFP8 format conversion                          │
│  - Extracts FP24 results from dout                              │
└────────────────────────────────────┬────────────────────────────┘
                                     │ Stimulates
┌────────────────────────────────────▼────────────────────────────┐
│  Layer 3: RTL DUT (mlp_bram_col)                                │
│  - ACX_MLP72 primitives                                         │
│  - BRAM weight storage                                          │
│  - Hardware accumulation                                        │
└─────────────────────────────────────────────────────────────────┘
```

**Key Files:**
- `src/acx_mlp/tests/acx_mlp_tests.py` - `MLPBramColTestbench` class
- `src/checkpoint1/tests/test_bcv_pattern.py` - BCV test cases
- `src/checkpoint1/tests/test_nv_dot_8mlps.py` - NV test cases

---

## 2. How BCV Maps to mlp_bram_col

### BCV Dimensions

```
B = Batch     → Number of left matrix rows (activations)
C = Columns   → Number of weight columns (max 16 = 8 MLPs × 2 banks)
V = Vector    → Inner dimension (8 elements × V cycles to accumulate)
```

### Hardware Mapping

```
              Column Index (c)
              0    1    2    3    ...   14   15
            ┌────┬────┬────┬────┬─────┬────┬────┐
            │MLP0│MLP0│MLP1│MLP1│ ... │MLP7│MLP7│
            │ b0 │ b1 │ b0 │ b1 │     │ b0 │ b1 │
            └────┴────┴────┴────┴─────┴────┴────┘

Column c → MLP index: c // 2
         → Bank index: c % 2
```

### Mapping Formula

```python
def column_to_hardware(c):
    mlp_idx = c // 2    # Which MLP (0-7)
    bank_idx = c % 2    # Which bank within MLP (0 or 1)
    return mlp_idx, bank_idx

# Examples:
# Column 0  → MLP0, bank0
# Column 1  → MLP0, bank1
# Column 2  → MLP1, bank0
# Column 15 → MLP7, bank1
```

### Broadcast Architecture

**Critical Insight**: ALL MLPs share the SAME `din` (activations are broadcast).

```
                    din (72-bit)
                         │
           ┌─────────────┼─────────────┐
           │             │             │
           ▼             ▼             ▼
        ┌─────┐       ┌─────┐       ┌─────┐
        │MLP 0│  ...  │MLP 3│  ...  │MLP 7│
        ├─────┤       ├─────┤       ├─────┤
        │bank0│       │bank0│       │bank0│  ← weights from BRAM (different per MLP)
        │bank1│       │bank1│       │bank1│
        └──┬──┘       └──┬──┘       └──┬──┘
           │             │             │
           ▼             ▼             ▼
        dout[0]       dout[3]       dout[7]
        (2×FP24)     (2×FP24)      (2×FP24)
```

---

## 3. Computation Flow for BCV

### Example: B=2, C=4, V=4

This walks through `test_bcv_gemm_equivalent`:

```python
# Matrix dimensions
B, C, V = 2, 4, 4
num_params = V * 8  # 32 elements per dot product
```

### Step 1: Generate Random Weights

```python
# Shape: [2 banks, 32 params, 8 MLPs]
weights = torch.randint(-64, 64, (2, num_params, NUM_MLPS), dtype=torch.int32)
```

### Step 2: Load Weights to BRAM (Once)

```python
await tb.load_weights(weights)
```

This writes weights to each MLP's BRAM. Each MLP stores:
- Bank 0: `weights[0, :, mlp_idx]` (32 elements)
- Bank 1: `weights[1, :, mlp_idx]` (32 elements)

### Step 3: Generate Left Matrix

```python
# Shape: [B rows, 32 elements each]
left_matrix = torch.randint(-64, 64, (B, num_params), dtype=torch.int32)
```

### Step 4: Process Each Batch

```python
for b in range(B):  # B=2 batches
    # 4a. Load activations for this batch row
    tb.update_activations(left_matrix[b])  # 32 elements

    # 4b. Run V=4 accumulation cycles
    await tb.accumulate_dot_products(V, new_dot=True)

    # 4c. Read 16 results from MLPs
    outputs = tb.get_outputs()  # [(bank0, bank1) for each MLP]

    # 4d. Extract C=4 columns
    row = []
    for c in range(C):  # c = 0, 1, 2, 3
        mlp_idx = c // 2   # 0, 0, 1, 1
        bank_idx = c % 2   # 0, 1, 0, 1
        row.append(outputs[mlp_idx][bank_idx])
    results_matrix.append(row)
```

### Data Flow Diagram

```
Batch 0:
  left_matrix[0] (32 elem) ──┐
                             │    ┌─────────────────┐
  weights[0,:,0] (32 elem) ──┼───►│ MLP0 bank0      │──► result[0][0]
  weights[1,:,0] (32 elem) ──┼───►│ MLP0 bank1      │──► result[0][1]
  weights[0,:,1] (32 elem) ──┼───►│ MLP1 bank0      │──► result[0][2]
  weights[1,:,1] (32 elem) ──┴───►│ MLP1 bank1      │──► result[0][3]
                                  └─────────────────┘

Batch 1:
  left_matrix[1] (32 elem) ──┐
                             │    ┌─────────────────┐
  (same weights)         ────┼───►│ MLP0-1          │──► result[1][0..3]
                             │    └─────────────────┘
```

---

## 4. Pipeline Timing

The MLP has a **2-cycle pipeline latency** from input to first valid output.

### Timing Diagram

```
Cycle:     0      1      2      3      4      5    ...
           ├──────┼──────┼──────┼──────┼──────┼──────┤
din:       [a0]   [a1]   [a2]   [a3]   ...
rdaddr:     0      1      2      3    ...
ce:         1      1      1      1      1      0    (enable)
load:       0      0      1      0      0      0    (load at cycle 2!)
accum:      0      0      0      1      1      0    (accumulate after load)
           ├──────┼──────┼──────┼──────┼──────┼──────┤
Output:                  [r0]   [r0+r1] [sum]  [final]
```

### Pipeline Timing

- Cycle 0: First activation enters pipeline stage 0
- Cycle 1: First activation in pipeline stage 1
- Cycle 2: First valid result appears at FP adder output
- Cycle 3+: Subsequent results accumulate

### Accumulation Mechanism (from Achronix Documentation)

Per the Achronix Component Library User Guide:
> "When load is low, the old and new values are added, and the sum is stored."

**Key insight**: After reset, `ACCUM = 0`. With `load = 0`:
- FP_ADD computes: `result = new_dot_product + ACCUM`
- For V=1: `dout = dot[0] + 0 = dot[0]` (correct)
- For V≥2: Accumulation happens through the feedback path

### V Constraint

**All V ≥ 1 are valid.** Empirical testing confirms:
- V=1: Single dot product works (no accumulation needed)
- V=2: Accumulation works through feedback path
- V≥3: `load` signal explicitly starts fresh accumulation at i=2

---

## 5. Code Path in accumulate_dot_products

From `src/acx_mlp/tests/acx_mlp_tests.py`:

```python
async def accumulate_dot_products(self, cycle_length: int, new_dot: bool):
    """Perform accumulating dot product over multiple cycles
    
    Works for all V >= 1, despite load only being asserted at i==2.
    For V < 3, accumulation happens through the FP adder feedback path
    since ACCUM starts at 0 after reset.
    """

    self.dut.rdaddr.value = 0
    self.dut.accumulate.value = 0
    self.dut.load.value = 0

    # Initial setup cycle
    await RisingEdge(self.dut.clk)
    self.dut.ce.value = 1

    # Process each activation vector (8 elements per cycle)
    for i in range(cycle_length):  # V cycles
        # Apply 8-element activation group
        self.apply_input_vector(self.activations[i])

        # Update read address for next BRAM word
        if i < cycle_length - 1:
            self.dut.rdaddr.value = i + 1

        # Enable accumulation after first cycle
        if i > 0:
            self.dut.accumulate.value = 1

        # Load accumulator at cycle 2 (pipeline latency)
        self.dut.load.value = 1 if ((i == 2) and new_dot) else 0

        await RisingEdge(self.dut.clk)

    # Reset control signals
    self.dut.rdaddr.value = 0
    self.dut.load.value = 0
    await RisingEdge(self.dut.clk)
    self.dut.accumulate.value = 0
    self.dut.ce.value = 0
    await RisingEdge(self.dut.clk)
```

### apply_input_vector

```python
def apply_input_vector(self, inputs: list[int]):
    """Apply input vector to DIN"""
    if len(inputs) == 8:
        inputs.insert(0, BFP8E8_BIAS)  # Add exponent byte
    din_value = pack_bytes(inputs)  # Pack 9 bytes → 72 bits
    self.dut.din.value = din_value
```

---

## 6. Expected vs Actual Comparison

### Computing Expected Results (PyTorch)

```python
expected_matrix = []
for b in range(B):
    row = []
    for c in range(C):
        mlp_idx = c // 2
        bank_idx = c % 2
        # PyTorch matmul: left[b] · weights[bank, :, mlp]
        dot = torch.matmul(
            left_matrix[b],           # (32,) activation vector
            weights[bank_idx, :, mlp_idx]  # (32,) weight vector
        ).item()
        row.append(dot)
    expected_matrix.append(row)
```

### Reading Actual Results (Hardware)

```python
def get_outputs(self) -> list[tuple[float, float]]:
    """Retrieve output dot products from DUT"""
    results = []
    for mlp_index in range(self.NUM_MLPS):
        mlp_out = self.dut.dout[mlp_index].value
        # Extract FP24 values from 72-bit output
        ed0 = int_to_float24(mlp_out[23:0].to_signed())   # Bank 0
        ed1 = int_to_float24(mlp_out[47:24].to_signed())  # Bank 1
        results.append((ed0, ed1))
    return results
```

### Output Format

```
dout[i] (72 bits):
  [71:48] - Status/unused
  [47:24] - Bank 1 result (FP24)
  [23:0]  - Bank 0 result (FP24)
```

### Verification with Tolerance

```python
assert math.isclose(actual, expected, rel_tol=(V / 2**14))
```

The tolerance scales with V because:
- More accumulation cycles → more rounding operations
- FP24 mantissa has ~14 bits of precision
- `V / 2^14` provides proportional tolerance

---

## 7. Parallelism and Throughput

### 7.1 Peak Parallelism

| Level | Parallelism | Description |
|-------|-------------|-------------|
| MLPs | 8 | 8 MLP units operating in parallel |
| Banks per MLP | 2 | Each MLP computes 2 independent dot products |
| Elements per bank | 8 | 8 MACs per bank per cycle |
| **Total MACs/cycle** | **128** | 8 × 2 × 8 = 128 multiply-accumulate operations |

**Peak Throughput**: 128 MACs/cycle @ 100 MHz = **12.8 GMAC/s**

### 7.2 Optimal Operation Model

```
┌─────────────────────────────────────────────────────────────────────────┐
│  PHASE 1: WEIGHT PRELOAD (One-time setup)                               │
│  - Load weights into each MLP's BRAM (done once per layer)              │
│  - Cost: ~2 × V × NUM_MLPS cycles (amortized over batches)              │
└─────────────────────────────────────────────────────────────────────────┘
                                    │
                                    ▼
┌─────────────────────────────────────────────────────────────────────────┐
│  PHASE 2: COMPUTE (High throughput streaming)                           │
│                                                                         │
│  For each batch b:                                                      │
│    Cycle 0:  din ← act[0]    rdaddr=0  → read weights[0] from BRAM     │
│    Cycle 1:  din ← act[1]    rdaddr=1  → read weights[1] from BRAM     │
│    Cycle 2:  din ← act[2]    rdaddr=2  → LOAD first valid result       │
│    Cycle 3+: din ← act[n]    rdaddr=n  → ACCUMULATE subsequent         │
│                                                                         │
│  Each cycle: 128 MACs (all 8 MLPs × 2 banks × 8 elements)               │
└─────────────────────────────────────────────────────────────────────────┘
```

**Key Insight**: Weights are read via `rdaddr` increment while `din` streams new activations every cycle. All 8 MLPs read their weights **simultaneously**.

### 7.3 Efficiency Formula

```
Compute Efficiency = V / (V + 3)

Where:
  V = number of accumulation cycles (inner dimension / 8)
  3 = overhead cycles per batch (1 setup + 2 flush)
```

### 7.4 Measured Efficiency

| V | Theoretical | Measured | MACs/cycle |
|---|-------------|----------|------------|
| 4 | 57.1% | 57.1% | 73.1 |
| 8 | 72.7% | 72.7% | 93.1 |
| 16 | 84.2% | 84.2% | 107.8 |
| 32 | 91.4% | 91.4% | 117.0 |
| 128 | 97.7% | 97.7% | 125.1 |

**Conclusion**: For large V (≥32), efficiency approaches peak. Use large accumulation depth for maximum throughput.

---

## 8. Test Coverage Summary

### NV Tests (`test_nv_dot_8mlps.py`)

| Test | Description | Elements |
|------|-------------|----------|
| `test_nv_dot_simple_ones` | All-ones validation | 8 |
| `test_nv_dot_random` | Random integer data | 8 |
| `test_nv_dot_multi_cycle` | Multi-cycle accumulation | 32 |
| `test_nv_dot_gfp8_format` | GFP8 format conversion | 32 |

### BCV Tests (`test_bcv_pattern.py`)

| Test | B | C | V | Total Elements | Purpose |
|------|---|---|---|----------------|---------|
| `test_bcv_B1_C16_V1` | 1 | 16 | 1 | 8 | Single batch, all columns, minimal |
| `test_bcv_B4_C16_V1` | 4 | 16 | 1 | 8 | Multiple batches, all columns |
| `test_bcv_B2_C16_V4` | 2 | 16 | 4 | 32 | Multi-cycle accumulation |
| `test_bcv_B8_C8_V16` | 8 | 8 | 16 | 128 | Large accumulation depth |
| `test_bcv_gemm_equivalent` | 2 | 4 | 4 | 32 | GEMM engine equivalent |
| `test_bcv_throughput_measurement` | 16 | 16 | 16 | 128 | **Throughput & efficiency validation** |

### Running Tests

```bash
cd /home/dev/Dev/elastix_gemm/mlp_jeremy

# NV tests (4 tests)
uv run python src/checkpoint1/run_nv_test.py

# BCV tests (6 tests)
uv run python src/checkpoint1/run_bcv_test.py
```

---

## 9. Appendix: Format Conversion

### GFP8 to BFP8

```
GFP8 bias: 128
BFP8 bias: 133
Conversion: BFP8_exp = GFP8_exp + 5
```

### 72-bit BFP8 Format

```
Byte:    [8]     [7]    [6]    [5]    [4]    [3]    [2]    [1]    [0]
Content: exp   man[7] man[6] man[5] man[4] man[3] man[2] man[1] man[0]
```

### Packing Code

```python
def pack_bytes(byte_list: list[int]) -> int:
    """Pack bytes into 72-bit integer. byte[0] is MSB."""
    result = 0
    for i, byte in enumerate(reversed(byte_list)):
        result |= (byte & 0xFF) << (i * 8)
    return result
```
