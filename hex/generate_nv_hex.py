#!/usr/bin/env python3
"""
Generate 528-line Native Vector (NV) format hex files for GFP GEMM testing

Memory Layout (Fixed):
- Total 528 lines per tensor
- Lines 0-15: Exponent data (512 exponents, 32 per line)
- Lines 16-527: Mantissa data (16,384 mantissas, 32 per line)
- Each NV = 128 elements = 4 groups of 32 elements each
- Block size = 128 NVs always

For B, C, V parameters:
- Matrix A uses BxV Native Vectors
- Matrix B uses CxV Native Vectors
- Constraint: BxV ≤ 128 and CxV ≤ 128
"""

import numpy as np
import torch
import sys
import argparse

# Add emulator path for GFP classes
sys.path.append('../emulator/src/emulator')
from group_floating_point import GFPTensor, GFPDataType


def generate_nv_block(B, V, is_matrix_a=True, seed=42, std=1.0):
    """
    Generate one 528-line block for either Matrix A or Matrix B

    Args:
        B: Batch size (for Matrix A) or column count (for Matrix B)
        V: Number of Native Vectors in inner dimension
        is_matrix_a: True for Matrix A, False for Matrix B
        seed: Random seed
        std: Standard deviation for random data generation

    Returns:
        tuple: (exponent_lines, mantissa_lines, gfp_tensor)
            - exponent_lines: List of 16 arrays (32 bytes each)
            - mantissa_lines: List of 512 arrays (32 bytes each)
            - gfp_tensor: GFPTensor object for dequantization
    """
    np.random.seed(seed)
    torch.manual_seed(seed)

    NUM_NVS = B * V  # Total Native Vectors needed
    if NUM_NVS > 128:
        raise ValueError(f"BxV = {B}x{V} = {NUM_NVS} exceeds maximum 128 NVs")

    NV_SIZE = 128  # Elements per Native Vector
    GROUP_SIZE = 32  # Elements per group
    GROUPS_PER_NV = 4  # 128 / 32 = 4

    # GFP data type (5-bit exponent, 8-bit mantissa)
    gfp_dtype = GFPDataType(
        mantissa_bits=8,
        exp_bits=5,
        exp_bias=15,
        mantissa_signed=True
    )

    # Generate matrix dimensions based on type
    if is_matrix_a:
        # Matrix A: B x (128xV)
        rows = B
        cols = NV_SIZE * V
        print(f"Generating Matrix A: {rows} x {cols} ({NUM_NVS} NVs)")
    else:
        # Matrix B: (128xV) x B (stored transposed)
        rows = NV_SIZE * V
        cols = B
        print(f"Generating Matrix B: {rows} x {cols} ({NUM_NVS} NVs, stored transposed)")

    # Generate random float data with specified standard deviation
    float_data = torch.randn(rows, cols) * std

    # Create GFP tensor
    # For Matrix A: group along columns (axis=1)
    # For Matrix B: group along rows (axis=0) for transposed storage
    group_axis = 1 if is_matrix_a else 0

    gfp_tensor = GFPTensor(
        original_shape=torch.Size([rows, cols]),
        group_axis=group_axis,
        group_size=GROUP_SIZE,
        dtype=gfp_dtype,
        original_data=float_data
    )

    # Extract exponents and mantissas
    exp_data = gfp_tensor.exp_data.numpy()  # Shape varies by group_axis
    mant_data = gfp_tensor.mantissa_data_signed.numpy()

    # Prepare 528 lines
    exponent_lines = []  # 16 lines
    mantissa_lines = []  # 512 lines

    # === Pack Exponents (Lines 0-15) ===
    # Need 512 exponents total (128 NVs x 4 groups = 512)
    # Pack into 16 lines x 32 bytes = 512 bytes

    # Flatten and extract exponents for each NV
    exponents_flat = np.zeros(512, dtype=np.uint8)

    if is_matrix_a:
        # Matrix A: group_axis=1, exp_data shape is [rows, num_groups, 1]
        # For each row (which becomes NVs when concatenated across V)
        for b in range(B):
            for v in range(V):
                nv_idx = b * V + v
                # Each NV has 4 groups
                for g in range(GROUPS_PER_NV):
                    exp_idx = nv_idx * GROUPS_PER_NV + g
                    # Get exponent from row b, group (v*4 + g) - offset by NV index
                    group_offset = v * GROUPS_PER_NV
                    exp_val = exp_data[b, group_offset + g, 0]
                    exponents_flat[exp_idx] = exp_val & 0x1F  # Mask to 5 bits
    else:
        # Matrix B: group_axis=0, exp_data shape is [cols, num_groups, 1]
        # Columns are groups of NVs
        for c in range(B):
            for v in range(V):
                nv_idx = c * V + v
                # Each NV has 4 groups (along rows)
                for g in range(GROUPS_PER_NV):
                    exp_idx = nv_idx * GROUPS_PER_NV + g
                    # Get exponent from column c, group (v*4 + g) - offset by NV index
                    group_offset = v * GROUPS_PER_NV
                    exp_val = exp_data[c, group_offset + g, 0]
                    exponents_flat[exp_idx] = exp_val & 0x1F

    # Pack exponents into 16 lines
    for line_idx in range(16):
        line_data = exponents_flat[line_idx*32:(line_idx+1)*32]
        exponent_lines.append(line_data)

    # === Pack Mantissas (Lines 16-527) ===
    # Need 16,384 mantissas (128 NVs x 128 elements)
    # Pack into 512 lines x 32 bytes = 16,384 bytes
    # Each NV occupies 4 consecutive lines

    mantissas_flat = np.zeros(16384, dtype=np.int8)

    if is_matrix_a:
        # Matrix A: mant_data shape is [rows, num_groups, group_size]
        for b in range(B):
            for v in range(V):
                nv_idx = b * V + v
                # Each NV has 128 elements = 4 groups x 32 elements
                group_offset = v * GROUPS_PER_NV  # Offset by NV index
                for g in range(GROUPS_PER_NV):
                    for elem in range(GROUP_SIZE):
                        mant_idx = nv_idx * NV_SIZE + g * GROUP_SIZE + elem
                        mant_val = mant_data[b, group_offset + g, elem]
                        mantissas_flat[mant_idx] = mant_val
    else:
        # Matrix B: mant_data shape is [cols, num_groups, group_size]
        # Stored transposed (group_axis=0)
        for c in range(B):
            for v in range(V):
                nv_idx = c * V + v
                group_offset = v * GROUPS_PER_NV  # Offset by NV index
                for g in range(GROUPS_PER_NV):
                    for elem in range(GROUP_SIZE):
                        mant_idx = nv_idx * NV_SIZE + g * GROUP_SIZE + elem
                        # Index into mant_data: [col, group, elem]
                        mant_val = mant_data[c, group_offset + g, elem]
                        mantissas_flat[mant_idx] = mant_val

    # Pack mantissas into 512 lines
    for line_idx in range(512):
        line_start = line_idx * 32
        line_data = mantissas_flat[line_start:line_start+32].astype(np.uint8)
        mantissa_lines.append(line_data)

    return exponent_lines, mantissa_lines, gfp_tensor


def write_hex_file(filename, exponent_lines, mantissa_lines):
    """
    Write 528-line hex file

    Args:
        filename: Output filename
        exponent_lines: List of 16 exponent line arrays (32 bytes each)
        mantissa_lines: List of 512 mantissa line arrays (32 bytes each)
    """
    with open(filename, 'w') as f:
        # Write exponent lines (0-15)
        for line_data in exponent_lines:
            hex_bytes = ' '.join(f'{b:02x}' for b in line_data)
            f.write(hex_bytes + '\n')

        # Write mantissa lines (16-527)
        for line_data in mantissa_lines:
            hex_bytes = ' '.join(f'{b:02x}' for b in line_data)
            f.write(hex_bytes + '\n')

    print(f"  Written: {filename} (528 lines)")


def main():
    parser = argparse.ArgumentParser(description="Generate NV-format hex files for GFP matrices")
    parser.add_argument('--B', type=int, default=128, help='Batch size (Matrix A rows)')
    parser.add_argument('--C', type=int, default=128, help='Column count (Matrix B columns)')
    parser.add_argument('--V', type=int, default=1, help='Native Vectors in inner dimension')
    parser.add_argument('--seed', type=int, default=42, help='Random seed')
    parser.add_argument('--std', type=float, default=1.0, help='Standard deviation for random data')
    parser.add_argument('--output-dir', default='.', help='Output directory')
    args = parser.parse_args()

    B = args.B
    C = args.C
    V = args.V

    print(f"\n{'='*70}")
    print(f"NV-Format Hex File Generator")
    print(f"{'='*70}")
    print(f"Parameters: B={B}, C={C}, V={V}")
    print(f"Matrix A: {B} x {128*V} (uses {B*V} NVs)")
    print(f"Matrix B: {128*V} x {C} (uses {C*V} NVs, stored transposed)")
    print(f"Result:   {B} x {C}")
    print(f"{'='*70}\n")

    # Generate Matrix A
    def write_float_matrix(filename, float_matrix, matrix_name="Matrix"):
        with open(filename, "w") as f:
            f.write(f"Float {matrix_name} ({float_matrix.shape[0]}x{float_matrix.shape[1]}):\n")
            for row in float_matrix:
                f.write(' '.join(f"{val:12.6f}" for val in row) + "\n")

    print("Generating Matrix A (left.hex)...")
    exp_a, mant_a, gfp_a = generate_nv_block(B, V, is_matrix_a=True, seed=args.seed, std=args.std)
    write_hex_file(f"{args.output_dir}/left.hex", exp_a, mant_a)

    # Also generate float for left from the original float
    float_a = gfp_a.dequantize()
    float_left_file = f"{args.output_dir}/left_float.txt"
    write_float_matrix(float_left_file, float_a, matrix_name="Matrix A")
    print(f"  Written float matrix: {float_left_file}")

    # Generate Matrix B
    print("\nGenerating Matrix B (right.hex)...")
    exp_b, mant_b, gfp_b = generate_nv_block(C, V, is_matrix_a=False, seed=args.seed+1, std=args.std)
    write_hex_file(f"{args.output_dir}/right.hex", exp_b, mant_b)

    # Also generate float for right from the original float
    float_b = gfp_b.dequantize()
    float_right_file = f"{args.output_dir}/right_float.txt"
    write_float_matrix(float_right_file, float_b, matrix_name="Matrix B")
    print(f"  Written float matrix: {float_right_file}")

    # ========================================================================
    # NOTE: Golden reference generation has been moved to hardware_gfp_reference.py
    #
    # To generate golden references (hardware-accurate and emulator-based):
    #   python hardware_gfp_reference.py --B {B} --C {C} --V {V}
    # ========================================================================

    print(f"\n{'='*70}")
    print(f"Matrix Generation Complete!")
    print(f"  left.hex:  Matrix A ({B}x{128*V}, {B*V} NVs)")
    print(f"  right.hex: Matrix B ({128*V}x{C}, {C*V} NVs)")
    print(f"  left_float.txt, right_float.txt: Dequantized matrices")
    print(f"\nTo generate golden references, run:")
    print(f"  python hardware_gfp_reference.py --B {B} --C {C} --V {V}")
    print(f"{'='*70}\n")


if __name__ == "__main__":
    main()
