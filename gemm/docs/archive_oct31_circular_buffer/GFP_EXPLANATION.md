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
In our case, we use a group of 32 numbers.

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
