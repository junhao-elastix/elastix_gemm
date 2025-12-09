# Achronix ACX_MLP72 Primitive Reference

This document provides a detailed reference for the Achronix ACX_MLP72 Machine Learning Processor primitive, based on the Component Library User Guide (UG086) and implementation analysis.

## Overview

The ACX_MLP72 is a 72-bit Machine Learning Processor primitive that provides:
- 16 multipliers (configurable for INT8, INT16, BFP8, FP16, FP24, etc.)
- Adder tree for summing multiplication results
- Dual accumulators (AB and CD banks)
- Integrated LRAM (2KB) for local storage
- Cascade interfaces for vertical chaining

## Architecture Stages

### Stage 0: Input Stage
- Input mux selection (`mux_sel_multa_l`, `mux_sel_multa_h`, `mux_sel_multb_l`, `mux_sel_multb_h`)
- Optional input registers (`del_multa_l`, `del_multa_h`, `del_multb_l`, `del_multb_h`)
- Data sources: MLP_DIN, BRAM_DOUT, LRAM_DOUT, or forward cascade (FWDI)

### Stage 1: Multiplier Stage
- 16 multipliers organized as lower bank (00-07) and upper bank (08-15)
- Mode selection via `bytesel_00_07` and `bytesel_08_15`
- Operation mode via `multmode_00_07` and `multmode_08_15` (signed, unsigned, etc.)

### Stage 2: Adder Tree Stage
- Hierarchical adder tree: ADD03, ADD47 → ADD07 (lower bank)
- Hierarchical adder tree: ADD811, ADD1215 → ADD815 (upper bank)
- Optional combining: ADD015 = ADD07 + ADD815
- Pipeline registers (`del_add_00_07_reg`, `del_add_08_15_reg`)

### Stage 3: Floating-Point Processing Stage
- FPMULT_AB: Floating-point multiplier for A×B products (uses lower bank)
- FPMULT_CD: Floating-point multiplier for C×D products (uses upper bank)
- Block floating-point mode support (`fpmult_ab_blockfp`, `fpmult_cd_blockfp`)

### Stage 4: Output Stage (Accumulator)
This stage is critical for understanding dot product accumulation.

#### Accumulator Bypass Parameters

**`add_accum_ab_bypass`** (Default: `1'b1` in mlp_dot16_bfp8.sv)
- `1'b0`: Integer AB accumulator value is used for OUTPUT
- `1'b1`: **Bypass** accumulator in OUTPUT path (use FP_ADD result directly)

**`add_accum_cd_bypass`** (Default: `1'b1` in mlp_dot16_bfp8.sv)
- `1'b0`: CD accumulator value is used for OUTPUT
- `1'b1`: **Bypass** CD accumulator in OUTPUT path

**CRITICAL CLARIFICATION** (Validated Dec 5, 2025):
The "bypass" parameter only affects the **OUTPUT routing**, NOT the accumulation mechanism!

- With `fpadd_cd_dinb_sel = 3'b000`, the FP adder's B input is ALWAYS `ACCUM_CD_REG`
- The FP adder computes: `result = dot_product + ACCUM_CD_REG` regardless of bypass
- The `ACCUM_CD_REG` is still updated based on `load`/`accumulate` signals
- "Bypass=1" means: output shows FP_ADD result directly (the running sum)
- "Bypass=0" means: output shows latched accumulator value

**The `load` signal DOES have effect even with bypass=1!**

#### Load Signals

Per Achronix Component Library UG086:
- **`load=1`**: "Previous accumulator value IGNORED, new value stored" (fresh start)
- **`load=0`**: "Old and new values are ADDED, sum is stored" (accumulate)

**Empirically validated behavior** (Dec 5, 2025):

| Signal | ACCUM_REG Update | Use Case |
|--------|------------------|----------|
| `load=1` | `ACCUM ← current_dot_product` | Start fresh accumulation |
| `load=0` | `ACCUM ← FP_ADD output` | Continue accumulating |

**When `load=1` is REQUIRED:**
- Running multiple batches without reset between them
- Preventing cross-contamination between computations

**Test Proof:**
```
Batch 2 (with load=1): 32.0  ✓ Fresh result
Batch 3 (NO load):     64.0  ✗ Contaminated (32 + 32)!
```

**`load_ab`** signal behavior:
- `rndsubshare = 1'b0`: When the lower half ab_add_accum is enabled, load with add_00_15_sel output
- `rndsubshare = 1'b1`: Unused

#### Output Routing Parameters

**`out_reg_din_sel`** (3 bits):
- `3'b000`: Value from Mult8×4
- `3'b001`: I32×I32
- `3'b010`: FP_ADD_CD floating-point value
- `3'b011`: Output or bypass of integer CD accumulator
- `3'b100`: 8-wide A +/- B output
- `3'b110`: Value from Mult16×2

**`dout_mlp_sel`** (2 bits):
- `2'b00`: Value from OUT_REG[63:0]
- `2'b01`: Concatenated {24'h0, ACCUM_AB_REG[23:0], OUT_REG[23:0]} for FP24 output
- `2'b10`: ACCUM_AB_REG[47:0]
- `2'b11`: Concatenated {ACCUM_AB_REG[35:0], OUT_REG[35:0]}

**`outmode_sel`** (2 bits):
- `2'b00`: 72-bit output selected by `dout_mlp_sel`
- `2'b01`: LRAM_DOUT[71:0]
- `2'b10`: BRAM_DOUT[143:72]
- `2'b11`: FP format conversion with status bits

## Current Configuration in mlp_dot16_bfp8.sv

```systemverilog
// Key accumulator parameters (BYPASS MODE)
add_accum_ab_bypass           = 1'b1    // Bypass AB accumulator
add_accum_cd_bypass           = 1'b1    // Bypass CD accumulator
accum_ab_reg_din_sel          = 1'b1    // Select FP result

// Output routing
out_reg_din_sel               = 3'b010  // FP_ADD_CD value
dout_mlp_sel                  = 2'b01   // Concatenated FP24 outputs
outmode_sel                   = 2'b11   // FP format + status

// Block floating-point mode
fpmult_ab_blockfp             = 1'b1    // BFP mode enabled
fpmult_cd_blockfp             = 1'b1    // BFP mode enabled
bytesel_00_07                 = 5'h05   // BFP Int8 ×2/×4 mode
bytesel_08_15                 = 6'h25   // BFP Int8 ×4 mode
```

## Why V < 3 Tests Pass (Validated Dec 5, 2025)

**Previous understanding was INCORRECT.** Empirical testing proves:

### Actual Data Flow (with bypass=1)

```
                          ┌─────────────┐
  dot_product ──────────> │   FP_ADD    │ ──────> dout (running sum!)
                          │   A + B     │
                          │             │
  ACCUM_CD_REG ─────────> │  (B input)  │
       ▲                  └─────────────┘
       │                        │
       │                        v (when accumulate_ce=1)
       └────────────────────────┘
```

### Key Parameters Creating This Flow

- `fpadd_cd_dinb_sel = 3'b000`: FP adder B input = ACCUM_CD_REG (feedback!)
- `out_reg_din_sel = 3'b010`: Output = FP_ADD result
- `add_accum_cd_bypass = 1'b1`: Output shows FP_ADD directly (not latched value)

### Why V < 3 Works Without Load

1. **After reset**: `ACCUM_CD_REG = 0`
2. **FP_ADD computes**: `dot_product + ACCUM_REG = dot_product + 0`
3. **For V=1**: Output = dot[0] + 0 = dot[0] ✓
4. **For V=2**: Accumulation happens through FP_ADD feedback loop

### Empirical Test Results

| V | Expected | Actual | Status |
|---|----------|--------|--------|
| 1 | 8 | 8.0 | ✓ |
| 2 | 24 | 24.0 | ✓ (8+16 accumulated!) |
| 3 | 48 | 48.0 | ✓ |
| 4 | 80 | 80.0 | ✓ |

### Trace Test (V=3)

```
Cycle 2: dout=8     (first result, load=1)
Flush 1: dout=88    (8+80, load=0, accumulated!)
Flush 2: dout=888   (88+800, load=0, accumulated!)
```

**Conclusion**: Accumulation IS happening internally via the FP_ADD feedback loop. The "bypass" only affects output routing, not the accumulation mechanism.

## Understanding Multi-Cycle Accumulation

### Current Configuration (bypass=1) - WORKS!

Even with `add_accum_cd_bypass = 1'b1`, accumulation works because:

1. **FP_ADD feedback loop is active**: `fpadd_cd_dinb_sel = 3'b000` routes ACCUM_REG to FP_ADD
2. **ACCUM_REG is updated**: Controlled by `load` and `accumulate_ce` signals
3. **Output shows running sum**: `out_reg_din_sel = 3'b010` shows FP_ADD result

### Control Signal Timing

| Cycle | Input | load | accumulate | ACCUM_REG Action |
|-------|-------|------|------------|------------------|
| 0 | din[0] | 0 | 0 | (not yet updated) |
| 1 | din[1] | 0 | 1 | (not yet updated) |
| 2 | din[2] | **1** | 1 | ← dot[0] (fresh start) |
| 3+ | - | 0 | 1 | ← FP_ADD output (accumulate) |

### Testbench Implementation

```python
# From acx_mlp_tests.py accumulate_dot_products()
for i in range(cycle_length):
    if i > 0:
        dut.accumulate.value = 1
    dut.load.value = 1 if (i == 2 and new_dot) else 0
```

- `load=1` at i==2: Ensures fresh start when first result appears (after 2-cycle latency)
- `accumulate=1` for i>0: Enables ACCUM_REG updates
- `new_dot=True`: Start fresh accumulation (prevents cross-batch contamination)
- `new_dot=False`: Continue from previous ACCUM value (for chained operations)

## Data Flow Summary

### BFP8 Dual Dot Product (Current Mode)
```
Input:                     Weight BRAM:
DIN[71:0] (8×int8+exp)    BRAM[143:0] (2×8×int8+2×exp)
       |                        |
       v                        v
   [Duplicated]           [Bank0, Bank1]
       |                        |
       +--------+--------+------+
                |
                v
        16× Multipliers
        (8 lower, 8 upper)
                |
                v
          Adder Trees
       ADD07     ADD815
         |         |
         v         v
      FP Mult    FP Mult
        (AB)       (CD)
         |         |
         v         v
      FP_ADD     FP_ADD     <-- Adds current + ACCUM_REG
     (A + B)    (A + B)
         |         |
         v         v
    ACCUM_AB   ACCUM_CD     <-- Updated via load/accumulate
       ↑ │       ↑ │            (feedback loop ACTIVE!)
       │ │       │ │
       └─┘       └─┘
         │         │
         +----+----+
              │
              v (bypass=1: shows FP_ADD result directly)
         FP24 Output
    dout = {status, AB[23:0], CD[23:0]}
```

**Note**: "Bypass" only affects output routing. The accumulator feedback
loop (ACCUM → FP_ADD B input) remains active for multi-cycle accumulation.

## Clock Enable Mapping

The `ce[11:0]` signal has specific mappings:
- `ce[0]`: Used for `accumulate_ce` in current design
- `ce[1]`: General clock enable
- `ce[7]`: LRAM write enable
- `ce[8-11]`: LRAM read address bits

## Reset Signal Mapping

The `rstn[3:0]` signal:
- `rstn[0]`: LRAM register reset
- `rstn[1]`: Main pipeline reset (used for most stages)
- `rstn[2-3]`: Reserved

## Validation History

### Dec 5, 2025 - Major Corrections (Verified Against UG086-1)

**Previous document had incorrect claims about accumulator bypass behavior.**

#### Official Achronix Documentation (UG086-1) Confirms:

1. **fpadd_cd_dinb_sel[2:0]** (part204.htm):
   > "Select the addend, or subtrahend for the CD accumulator:
   >  3'b000 – 48-bit ACCUM_CD_REG input (registered)"
   
   ✓ With our setting (3'b000), FP_ADD B input IS the accumulator register

2. **add_accum_cd_bypass** (part204.htm):
   > "Select to bypass the CD accumulator **OUTPUT**"
   
   ✓ Bypass affects OUTPUT routing, NOT the feedback loop

3. **out_reg_din_sel[2:0]** (part204.htm):
   > "3'b010 – FP_ADD_CD floating-point value"
   
   ✓ We output FP_ADD result which includes ACCUM feedback

4. **Load Signal** (part246.htm, part302.htm):
   > "When load is high, the previous value of the internal accumulation 
   >  register is ignored, and the new value is stored."
   > "When load is low, the old and new values are added, and the sum is stored."
   
   ✓ Load controls fresh start vs accumulate

#### Empirical Testing Confirms:

- `test_v1_to_v4_sweep`: V=1,2,3,4 all accumulate correctly
- `test_accumulator_trace`: Cycle-by-cycle trace showing 8→88→888 accumulation
- `test_load_critical_multi_batch`: load=1 prevents cross-batch contamination

## References

- Achronix Component Library User Guide (UG086)
- `/home/dev/Dev/elastix_gemm/doc/Component_Library/` - Local copy
- mlp_dot16_bfp8.sv (local implementation)
- mlp_bram.sv (MLP+BRAM wrapper)
- mlp_bram_col.sv (column wrapper)
- test_bcv_pattern.py (empirical validation tests)
