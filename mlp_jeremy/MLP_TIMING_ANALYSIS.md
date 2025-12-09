# MLP Timing Analysis - ACX_MLP72 BFP8 Mode

## Critical Timing Parameters

### Pipeline Latency: **2 cycles to first valid result**

```
Cycle 0: Apply inputs (DIN + BRAM rdaddr)
Cycle 1: BRAM data → MLP multipliers → adders
Cycle 2: First valid result available → LOAD into accumulator
Cycle 3+: Subsequent results → ACCUMULATE
```

### Multi-Cycle Dot Product Protocol

From `acx_mlp_tests.py`:

```python
for i in range(num_cycles):
    apply_input_vector(activations[i])     # Cycle i: Apply activation group
    rdaddr = i + 1                         # Update BRAM address for next cycle
    if i > 0:
        accumulate = 1                     # Enable accumulation after cycle 0
    if i == 2 and new_dot:
        load = 1                          # Load first valid result at cycle 2
    await RisingEdge(clk)
```

**Key Insight**: The `load` signal at cycle 2 captures the first valid partial product into the accumulator. All subsequent cycles use `accumulate=1` to add new partials.

## Hardware Pipeline Stages

### Stage 0: Input Registers (Enabled)
From `mlp_dot16_bfp8.sv`:
- `del_multa_l = 1'b1` - Lower bank A input register
- `del_multa_h = 1'b1` - Upper bank A input register
- `del_multb_l = 1'b1` - Lower bank B input register (from BRAM)
- `del_multb_h = 1'b1` - Upper bank B input register (from BRAM)
- Clock enable: `cesel = 4'h2` → ce[1]

### Stage 1: Multiplier Registers (Disabled)
- All multiplier stage registers disabled (`del_mult00a = 1'b0`, etc.)
- Multipliers operate combinationally

### Stage 2: Adder Registers (Enabled)
- `del_add_00_07_reg = 1'b1` - Bank 0 adder tree register
- `del_add_08_15_reg = 1'b1` - Bank 1 adder tree register
- Clock enable: `cesel = 4'hD` → always enabled

### Stage 3: Accumulator (Floating-Point)
- Controlled by `load` and `accumulate` signals
- Outputs FP24 format by default

## BRAM Read Timing

From `weight_bram.sv`:
- **Configuration**: Asynchronous read mode
- `.outreg_enable(1'b0)` - No output register
- `.del_fwdi_ram_rd_addr(1'b0)` - No address register
- **Read latency**: ~1 cycle (BRAM internal)
- Direct connection to MLP via `mlpram_dout2mlp[143:0]`

**Read Width**: 144 bits = 2 BFP8 blocks
- Bits [71:0]   → Bank 0 (lower) parameters (8×8-bit mantissas + 8-bit exponent)
- Bits [143:72] → Bank 1 (upper) parameters (8×8-bit mantissas + 8-bit exponent)

## Dual-Bank Operation

### Configuration (from `mlp_dot16_bfp8.sv`)
- **Bank 0 (Lower)**: `bytesel_00_07 = 5'h05` - BFP Int8 ×2/×4 mode (8 multiplications)
- **Bank 1 (Upper)**: `bytesel_08_15 = 6'h25` - BFP Int8 ×4 mode (16 multiplications)

**Data Flow**:
```
DIN[71:0] (8 elements + exponent)
    ├─ duplicated to → Bank 0 lower (multa_l)
    └─ duplicated to → Bank 1 upper (multa_h)

BRAM_DOUT[143:0]
    ├─ [71:0]   → Bank 0 lower weights (multb_l)
    └─ [143:72] → Bank 1 upper weights (multb_h)

Outputs:
    ├─ dout[23:0]  → Bank 0 dot product (FP24)
    └─ dout[47:24] → Bank 1 dot product (FP24)
```

**Can banks have different exponents?**
- Hardware supports it via `expb[7:0]` signal
- Current implementation uses shared exponent for both banks
- For GFP8→BFP8 mapping with replicated exponents, this is correct

## Exponent Handling

From `mlp_bram.sv`:
```systemverilog
wire [7:0] expb = {lram_wraddr[5:0], lram_rdaddr[5:4]};
```

The exponent is encoded using virtual LRAM ports. In our use case:
- GFP8 exponent (5-bit) + bias adjustment
- Replicated 4 times per group (4 BFP8 blocks = 1 GFP8 group)

## Cascade Chain Timing

From `mlp_bram_col.sv`:

**Base MLP (mlp_col_base)**:
- `mux_sel_multa_l = 2'b00` → Select DIN directly
- `mux_sel_multa_h = 3'b000` → Select DIN directly
- `del_multa_l = 1'b1` → Input register enabled
- `del_multa_h = 1'b1` → Input register enabled

**Stacked MLPs (mlp_col_stack)**:
- `mux_sel_multa_l = 2'b11` → Select cascade input (FWDI_MULTA_L)
- `mux_sel_multa_h = 3'b111` → Select cascade input (FWDI_MULTA_H)
- `del_multa_l = 1'b0` → Bypass input register (data already registered in base)
- `del_multa_h = 1'b0` → Bypass input register

**Critical**: Cascade registers disabled for stacked MLPs to avoid double-registration.

## Mapping 2 MLPs to 1 GFP8 Group (32 elements)

Each MLP computes 16 elements using dual 8×8 banks:

**MLP 0**:
- Bank 0: Elements 0-7
- Bank 1: Elements 8-15

**MLP 1**:
- Bank 0: Elements 16-23
- Bank 1: Elements 24-31

**Protocol**:
1. Both MLPs receive same activations on DIN[71:0]
2. Each MLP reads different weights from its own BRAM
3. Each MLP produces 2 outputs (one per bank)
4. Final aggregation: Sum all 4 outputs

**Exponent Replication**:
- GFP8 group has 1 exponent for 32 elements
- This exponent is replicated to all 4 BFP8 blocks (2 MLPs × 2 banks)
- All banks use the same exponent value

## Timing Diagram: 2-MLP Single Group Operation

```
Cycle  | Action                           | load | accum | rdaddr | Notes
-------|----------------------------------|------|-------|--------|---------------------------
0      | Apply activation[0] (8 elements) |  0   |   0   |   0    | Pipeline fill starts
1      | Apply activation[1] (8 elements) |  0   |   0   |   1    | BRAM read for addr 1
2      | Apply activation[2] (8 elements) |  1   |   0   |   2    | LOAD first valid result
3      | Apply activation[3] (8 elements) |  0   |   1   |   3    | ACCUMULATE subsequent results
...    | ...                              |  0   |   1   |  ...   | Continue accumulation
N      | Final cycle                      |  0   |   1   |  N-1   | Last activation
N+1    | Pipeline flush                   |  0   |   0   |   0    | Reset control signals
N+2    | Results valid                    |  -   |   -   |   -    | Read dout[NUM_MLPS-1:0]
```

**For 1 GFP8 group (32 elements) = 4 cycles**:
- 4 BFP8 blocks × 8 elements = 32 elements
- Each cycle processes 8 elements across both MLPs
- Total: 4 cycles + 2 cycle latency = 6 cycles to completion

## Mapping 8 MLPs to 1 Native Vector (128 elements)

**Architecture**:
- 1 NV = 4 GFP8 groups × 32 elements = 128 elements
- 1 GFP8 group requires 2 MLPs
- 1 NV requires 8 MLPs (all operating in parallel)

**MLP Assignment**:
```
Group 0 (elements 0-31):   MLP0 + MLP1
Group 1 (elements 32-63):  MLP2 + MLP3
Group 2 (elements 64-95):  MLP4 + MLP5
Group 3 (elements 96-127): MLP6 + MLP7
```

**Parallel Operation**:
- All 8 MLPs receive same activations simultaneously
- Each MLP pair (0-1, 2-3, 4-5, 6-7) shares same exponent (GFP8 group exponent)
- Each MLP reads different weights (16 per MLP, 128 total per cycle)
- After 4 cycles: All 128×128 partial products computed

**Output Collection**:
1. Sum within each MLP pair → 4 group results
2. Apply NV aggregation (max-align-sum) → final NV result

## References

### RTL Files
- `mlp_dot16_bfp8.sv` - MLP primitive configuration (lines 331-336: adder registers)
- `weight_bram.sv` - BRAM timing configuration (line 56: outreg_enable)
- `mlp_bram.sv` - Combined MLP+BRAM tile (lines 76-78: exponent encoding)
- `mlp_bram_col.sv` - Column wrapper with cascade chain

### Test Files
- `acx_mlp_tests.py` - Load/accumulate protocol
  - Line 268: Load at cycle 2
  - Lines 256-279: accumulate_dot_products function

### Key Parameters
- Pipeline latency: 2 cycles
- BRAM read latency: 1 cycle
- Load timing: Cycle 2 (first valid result)
- Accumulate timing: Cycle 3+ (subsequent results)
