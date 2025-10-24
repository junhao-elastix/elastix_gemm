# Group Floating Point (GFP) Format

## Overview

Group Floating Point (GFP) is a custom floating-point format designed for hardware efficiency in FPGA implementations. Unlike standard IEEE floating-point formats where each number has its own exponent, GFP uses **shared exponents across groups of numbers**, significantly reducing storage overhead and simplifying hardware logic.

## Core Concept: Shared Exponents

### Traditional Floating-Point
```
Number 1: [sign][exponent][mantissa]
Number 2: [sign][exponent][mantissa]
Number 3: [sign][exponent][mantissa]
Number 4: [sign][exponent][mantissa]
```

### Group Floating-Point
```
Group of 4 numbers: [shared_exponent] + [mantissa1][mantissa2][mantissa3][mantissa4]
```

## GFP Data Structure

### GFPDataType Configuration
- **mantissa_bits**: Width of mantissa (e.g., 8 bits)
- **exp_bits**: Width of exponent (e.g., 5 bits)
- **exp_bias**: Exponent bias (default: 2^(exp_bits-1))
- **mantissa_signed**: Whether mantissa includes sign bit or uses separate sign storage

### GFPTensor Organization
A GFP tensor reshapes the original tensor by grouping elements along a specified axis:

```python
# Original tensor: [batch, channels] = [4, 256]
# With group_size=32, group_axis=-1 becomes:
# Grouped: [batch, num_groups, group_size] = [4, 8, 32]
```

**Storage Components:**
- **mantissa_data**: `[batch, num_groups, group_size]` - quantized values
- **exp_data**: `[batch, num_groups, 1]` - shared exponent per group
- **sign_data**: `[batch, num_groups, group_size]` - signs (if mantissa unsigned)

## Quantization Process

### 1. Grouping and Padding
```python
# Transpose group dimension to last position
x = x.transpose(-1, group_axis)
# Pad to make divisible by group_size
x = F.pad(x, (0, pad_size))
# Reshape into groups
x = x.unflatten(-1, (num_groups, group_size))
```

### 2. Shared Exponent Calculation
```python
# Find maximum absolute value in each group
x_max = x.abs().max(-1, keepdim=True)[0]
# Calculate shared exponent for the group
e = (x_max * scale).log2().ceil() - effective_mantissa_bits + exp_bias
```

### 3. Mantissa Quantization
```python
# Scale all values in group by shared exponent
scales = 2.0 ** (e - exp_bias)
mantissa = (x / scales).round()
```

## Hardware Benefits

### Storage Efficiency
- **Standard FP32**: 32 bits per number
- **GFP (8m/5e, group=32)**: 8 + 5/32 ≈ 8.16 bits per number (4× reduction)

### Computation Simplification
1. **Alignment**: All numbers in group already aligned to same exponent
2. **Addition**: Simple integer addition of mantissas (no exponent comparison)
3. **Multiplication**: Mantissa multiply + exponent add (groups handled independently)

### GEMM Operation Example
```python
# LHS: [batch, groups, group_size] with exponents [batch, groups, 1]
# RHS: [rows, groups, group_size] with exponents [rows, groups, 1]

# Dot product within each group
mantissa_product = einsum("bng, rng -> brn", lhs_mantissa, rhs_mantissa)

# Add exponents
exponent_sum = lhs_exp + rhs_exp  # Broadcasting: [batch,1,groups] + [1,rows,groups]

# Find max exponent across groups for alignment
shared_exp = exponent_sum.max(-1, keepdim=True)[0]
exp_diff = shared_exp - exponent_sum

# Align and accumulate
aligned_product = mantissa_product >> exp_diff
result_mantissa = aligned_product.sum(-1)  # Sum across groups
```

## Trade-offs

### Advantages
- **Memory Efficient**: Significant storage reduction
- **Hardware Friendly**: Simple integer operations, reduced exponent logic
- **Bandwidth Efficient**: Less data movement in memory hierarchy

### Limitations
- **Precision Loss**: Quantization error from shared exponents
- **Group Constraints**: Values with very different magnitudes in same group lose precision
- **Alignment Overhead**: Worst-case group member determines precision for entire group

## FPGA Implementation Benefits

### Reduced Resource Usage
- Fewer exponent processing units needed
- Simplified floating-point ALUs
- Reduced memory bandwidth requirements

### Pipeline Efficiency
- Groups can be processed in parallel
- Reduced dependency chains in computation
- Better utilization of FPGA DSP blocks

### Memory Hierarchy Optimization
- Better cache utilization due to data locality
- Reduced off-chip memory accesses
- Efficient burst transfers aligned to group boundaries

## Palettized Extension

For further compression, GFP supports palettized mantissas:
- **Palette**: Shared set of common mantissa values
- **Indices**: Each mantissa position stores an index into palette
- **Additional Compression**: Especially effective for sparse or quantized networks

This format is particularly suitable for neural network inference where slight precision loss is acceptable in exchange for significant hardware efficiency gains.