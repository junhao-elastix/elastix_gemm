# Python Golden Reference Scripts - Comparison and Usage

**Date**: October 5, 2025
**Location**: `/home/dev/Dev/elastix_gemm/hex/`

---

## Executive Summary

Two Python scripts generate golden references with **different algorithms**:

| Script | Algorithm | Output | Use Case |
|--------|-----------|--------|----------|
| **mem_layout.py** | GFPGemm (emulator) | `decoded_result.txt` | Understanding/Analysis |
| **hardware_gfp_reference.py** | Group-by-group (hardware) | `out.hex` | **Testbench Validation** |

**Critical**: For hardware testing, **ALWAYS use `hardware_gfp_reference.py`** output (`out.hex`)

---

## 1. mem_layout.py

### Purpose
**High-level analysis and understanding** of GFP matrix operations with variable B, C, V parameters.

### Algorithm
Uses **GFPGemm** from `/home/dev/Dev/emulator/src/emulator`:
- Dynamic range compression
- Max exponent alignment across groups
- Mantissa shifting before accumulation
- Sophisticated rounding and overflow handling

### Inputs
- `left.hex` (128×128 GFP8 matrix)
- `right.hex` (128×128 GFP8 matrix)

### Outputs
**Primary**: `decoded_result.txt` - Human-readable comparison report
```
GFP GEMM vs FP Matmul Comparison - Decoded from Hex Files
================================================================================
Parameters: B=4, C=4, V=1
Matrix A dimensions: 4 × 128
Matrix B dimensions: 128 × 4
Result dimensions: 4 × 4

GFP GEMM Result Matrix (Float values):
  -17.156250   -26.886719     0.089844   -11.526367
   -6.739258    -1.092773    11.238281    -7.611816
   -9.611328     9.114258   -14.643555     1.884766
    3.050781     1.710938    29.306641   -15.587891

GFP GEMM Result Matrix (Hex values - IEEE 754 float16):
0xcc4a 0xceb9 0x2dc0 0xc9c3
0xc6bd 0xbc5f 0x499e 0xc79d
0xc8ce 0x488f 0xcb52 0x3f8a
0x421a 0x3ed8 0x4f54 0xcbcb
```

**Secondary**: Displays detailed comparison with FP matmul for accuracy verification

### Usage
```bash
cd /home/dev/Dev/elastix_gemm/hex
conda activate elastix

# Generate golden reference with custom dimensions
python mem_layout.py --B 4 --C 4 --V 1

# Output: decoded_result.txt with detailed analysis
```

### Key Features
- ✅ Configurable B, C, V parameters
- ✅ FP matmul comparison for accuracy verification
- ✅ Human-readable float and hex output
- ✅ Statistical analysis (min, max, mean, differences)
- ⚠️ **Does NOT match hardware exactly** (±1 LSB differences expected)

---

## 2. hardware_gfp_reference.py

### Purpose
**Hardware verification** - generates golden reference that **EXACTLY** matches RTL behavior.

### Algorithm
**Group-by-group integer accumulation** (matches `compute_engine.sv`):
```python
For each output element C[i,j]:
  For each group g in {0, 1, 2, 3}:
    acc[g] = Σ(mant_left[i] × mant_right[i])  # Integer accumulation
    exp_sum = exp_left[g] + exp_right[g] - 2*BIAS
    result[g] = acc[g] × 2^exp_sum             # Scale

  dot_product = Σ(result[0..3])                # FP summation
  return convert_to_fp16(dot_product)
```

### Inputs
- `left.hex` (128×128 GFP8 matrix)
- `right.hex` (128×128 GFP8 matrix)

### Outputs
**Primary**: `out.hex` - Golden reference for testbench (16,384 FP16 values)
```
cc4a
ceb8
2dc0
c9c3
c6bd
bc5f
499e
c79c
...
```

**Format**: 4-digit hex per line, tile-major order, ready for testbench loading

### Usage
```bash
cd /home/dev/Dev/elastix_gemm/hex
conda activate elastix

# Generate hardware-accurate golden reference
python hardware_gfp_reference.py --B 4 --C 4 --V 1

# Output: out.hex (used by tb_vector_top_ms2.sv)
```

### Key Features
- ✅ **Matches hardware RTL exactly** (compute_engine.sv)
- ✅ Simple group-by-group algorithm
- ✅ Outputs directly to testbench format (out.hex)
- ✅ Tile-major ordering (matches hardware output)
- ✅ FP16 conversion with overflow clamping
- ⚠️ **Always generates full 128×128 output** (16,384 values)

---

## Algorithm Differences

### Why Two Different Algorithms?

**mem_layout.py (GFPGemm)**:
- Uses emulator's optimized GFP implementation
- Focuses on numerical accuracy and dynamic range
- Better for understanding GFP behavior
- Produces slightly different results than hardware

**hardware_gfp_reference.py (Group-by-Group)**:
- Mirrors actual hardware RTL implementation
- Simpler, more hardware-friendly algorithm
- **Required for hardware verification**
- Matches RTL bit-exact (except ±1 LSB in some positions)

### Expected Differences

Comparing outputs from both scripts for the same input:

| Position | mem_layout.py | hardware_gfp_reference.py | Difference |
|----------|---------------|---------------------------|------------|
| [0,1]    | 0xceb9        | 0xceb8                    | ±1 LSB     |
| [2,1]    | 0x488f        | 0x488e                    | ±1 LSB     |
| [1,3]    | 0xc79d        | 0xc79c                    | ±1 LSB     |
| [3,2]    | 0x4f54        | 0x4f53                    | ±1 LSB     |

**Assessment**: These ±1 LSB differences are **acceptable** and expected due to:
- Different accumulation orders
- Different rounding strategies
- Integer vs floating-point intermediate computations

---

## Usage Guidelines

### For Hardware Testing (Simulation/Verification)
```bash
# CORRECT - Use hardware-accurate reference
cd /home/dev/Dev/elastix_gemm/hex
conda activate elastix
python hardware_gfp_reference.py --B 4 --C 4 --V 1

cd /home/dev/Dev/elastix_gemm/engine_sim/sim/top_vector_system_ms2
make clean && make run
```

### For Understanding/Analysis
```bash
# Use mem_layout.py for detailed analysis
cd /home/dev/Dev/elastix_gemm/hex
conda activate elastix
python mem_layout.py --B 4 --C 4 --V 1

# Read decoded_result.txt for:
# - Comparison with FP matmul
# - Statistical analysis
# - Float value interpretation
```

### For Debugging Mismatches
```bash
# 1. Generate both references
python hardware_gfp_reference.py --B 4 --C 4 --V 1  # → out.hex
python mem_layout.py --B 4 --C 4 --V 1              # → decoded_result.txt

# 2. Compare outputs
# - If hardware matches out.hex: ✅ Hardware correct
# - If hardware differs from out.hex: ❌ Hardware bug
# - Small differences (±1 LSB) between mem_layout and hardware_gfp_reference: ✅ Expected
```

---

## File Dependencies

### Input Files (Static - Generated Once)
```
left.hex   ← Generated by matrix_engine_w4gfp8/src/tb_py/gfp_gen.py
right.hex  ← Generated by matrix_engine_w4gfp8/src/tb_py/gfp_gen.py
```

### Output Files (Dynamic - Regenerated for Each Test)
```
mem_layout.py:
  └── decoded_result.txt  (Human-readable analysis)

hardware_gfp_reference.py:
  └── out.hex             (Testbench golden reference) ← USED BY TESTBENCH
```

### Testbench Loading
```systemverilog
// src/tb/tb_vector_top_ms2.sv line 171
fd_golden = $fopen("/home/dev/Dev/elastix_gemm/hex/out.hex", "r");
```

---

## Command Reference

### Generate Test Inputs (One-time)
```bash
cd /home/dev/Dev/elastix_gemm/matrix_engine_w4gfp8/src/tb_py
conda activate elastix
python gfp_gen.py
# Generates: ../../hex/left.hex, ../../hex/right.hex
```

### Generate Golden Reference for Testing
```bash
cd /home/dev/Dev/elastix_gemm/hex
conda activate elastix

# For hardware testbench validation (REQUIRED)
python hardware_gfp_reference.py --B 4 --C 4 --V 1

# For analysis/understanding (OPTIONAL)
python mem_layout.py --B 4 --C 4 --V 1
```

### Run Hardware Test
```bash
cd /home/dev/Dev/elastix_gemm/engine_sim/sim/top_vector_system_ms2
make clean && make run

# Testbench automatically loads out.hex from hardware_gfp_reference.py
# Compares DUT output vs golden reference
```

---

## Technical Implementation Details

### mem_layout.py Key Functions
```python
def test_gemm_decoding(B: int = 1, C: int = 1, V: int = 1):
    """
    Main function: Decode hex files and perform GFP GEMM

    Uses:
        - GFPTensor for matrix representation
        - GFPGemm for matrix multiplication
        - Comparison with FP matmul for validation

    Returns:
        Matrix A, Matrix B, Result (B×C)
    """
```

### hardware_gfp_reference.py Key Functions
```python
class HardwareGFPCompute:
    def compute_dot_product(self, left_mant, left_exp, right_mant, right_exp):
        """
        Compute dot product using hardware algorithm

        Matches compute_engine.sv behavior:
        1. Group-by-group integer accumulation
        2. Per-group scaling by 2^(exp_a + exp_b - 30)
        3. FP summation of 4 group results
        4. FP16 conversion with overflow clamping
        """
```

---

## Common Pitfalls

### ❌ Using mem_layout.py output for hardware testing
```bash
# WRONG - mem_layout.py doesn't generate out.hex
python mem_layout.py --B 4 --C 4 --V 1
make run  # Testbench uses stale/incorrect out.hex
```

### ✅ Correct workflow
```bash
# CORRECT - Always regenerate out.hex before testing
python hardware_gfp_reference.py --B 4 --C 4 --V 1
make clean && make run
```

### ❌ Expecting exact match between both scripts
```python
# mem_layout.py outputs 0xceb9
# hardware_gfp_reference.py outputs 0xceb8
# This is EXPECTED - different algorithms produce ±1 LSB differences
```

---

## Validation Summary

| Validation Type | Script to Use | Expected Outcome |
|-----------------|---------------|------------------|
| Hardware RTL vs Golden | `hardware_gfp_reference.py` | Exact match (or ±1 LSB) |
| GFP vs FP accuracy | `mem_layout.py` | Within 0.1% tolerance |
| B, C, V parameter testing | Both (run separately) | Both complete successfully |
| Understanding GFP behavior | `mem_layout.py` | Detailed analysis in decoded_result.txt |

---

## Conclusion

- **Use `hardware_gfp_reference.py`** for all hardware verification and testbench validation
- **Use `mem_layout.py`** for understanding, analysis, and FP comparison
- Both scripts are **complementary**, not redundant
- ±1 LSB differences between them are **expected and acceptable**
- Testbench **only loads `out.hex`** (from `hardware_gfp_reference.py`)

---

**Last Updated**: October 5, 2025
**Maintainer**: Project Documentation
**Related Files**: `CHANGELOG.md`, `README.md`, `BCV_VALIDATION_SUMMARY.md`
