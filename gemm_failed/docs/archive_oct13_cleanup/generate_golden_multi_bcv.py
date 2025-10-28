#!/usr/bin/env python3
"""
Generate golden references for multiple (B, C, V) test cases
Uses existing left.hex and right.hex (128 NVs each)
"""

import numpy as np
import torch
import sys

sys.path.append('/home/dev/Dev/emulator/src/emulator')
from group_floating_point import GFPTensor, GFPDataType, GFPGemm

# Use validated hex parser from mem_layout.py
sys.path.append('/home/dev/Dev/elastix_gemm/hex')
from mem_layout import load_hex_file, decode_exponents, decode_mantissas

# Test cases: (B, C, V, description)
TEST_CASES = [
    (1, 1, 128, "Maximum V"),
    (128, 1, 1, "Maximum B"),
    (1, 128, 1, "Maximum C"),
    (128, 128, 1, "Maximum output size"),
    (2, 64, 2, "C×V boundary"),
    (4, 32, 4, "C×V boundary balanced"),
    (8, 8, 16, "Balanced both at limit"),
    (4, 4, 32, "Current validated test"),
    (1, 1, 1, "Absolute minimum"),
    (2, 2, 2, "Small with V-loop"),
]

def load_nv_from_hex(filename, num_nvs):
    """Load Native Vectors from hex file using validated parser"""
    # Use validated mem_layout parser
    exp_data, mant_data = load_hex_file(filename)

    # Decode using validated functions
    exponents_full = decode_exponents(exp_data)  # [128, 4]
    mantissas_full = decode_mantissas(mant_data)  # [128, 128]

    # Extract only needed NVs
    exponents = []
    mantissas = []

    for nv_idx in range(num_nvs):
        # Get exponents for this NV (4 groups)
        nv_exps = exponents_full[nv_idx].tolist()
        exponents.append(nv_exps)

        # Get mantissas for this NV (128 elements)
        nv_mants = mantissas_full[nv_idx].tolist()
        mantissas.append(nv_mants)

    return exponents, mantissas

def reconstruct_gfp_tensor(exponents, mantissas, shape, group_axis):
    """Reconstruct GFPTensor from exponents and mantissas"""
    gfp_dtype = GFPDataType(
        mantissa_bits=8,
        exp_bits=5,
        exp_bias=15,
        mantissa_signed=True
    )

    # Dequantize to float
    num_nvs = len(exponents)
    nv_size = 128

    if group_axis == 1:  # Matrix A
        rows, cols = shape
        float_data = torch.zeros(rows, cols)
        for nv_idx in range(num_nvs):
            row = nv_idx
            if row >= rows:
                break
            for g in range(4):
                exp = exponents[nv_idx][g]
                scale = 2.0 ** (exp - 15)
                for elem in range(32):
                    col = g * 32 + elem
                    if col < cols:
                        mant = mantissas[nv_idx][g * 32 + elem]
                        float_data[row, col] = mant * scale
    else:  # Matrix B (group_axis == 0)
        rows, cols = shape
        float_data = torch.zeros(rows, cols)
        for nv_idx in range(num_nvs):
            col = nv_idx
            if col >= cols:
                break
            for g in range(4):
                exp = exponents[nv_idx][g]
                scale = 2.0 ** (exp - 15)
                for elem in range(32):
                    row = g * 32 + elem
                    if row < rows:
                        mant = mantissas[nv_idx][g * 32 + elem]
                        float_data[row, col] = mant * scale

    # Create GFP tensor from float data
    gfp_tensor = GFPTensor(
        original_shape=torch.Size(shape),
        group_axis=group_axis,
        group_size=32,
        dtype=gfp_dtype,
        original_data=float_data
    )

    return gfp_tensor

def compute_golden_for_bcv(B, C, V, left_exp, left_mant, right_exp, right_mant):
    """Compute golden reference for specific (B, C, V)"""
    # Extract the needed NVs
    num_left_nvs = B * V
    num_right_nvs = C * V

    left_exp_subset = left_exp[:num_left_nvs]
    left_mant_subset = left_mant[:num_left_nvs]
    right_exp_subset = right_exp[:num_right_nvs]
    right_mant_subset = right_mant[:num_right_nvs]

    # Reconstruct as matrices
    # Matrix A: B × (128×V)
    mat_a_shape = (B, 128 * V)
    # Matrix B: (128×V) × C
    mat_b_shape = (128 * V, C)

    # For Matrix A: each row is one "batch", V NVs concatenated
    # Need to reshape: B rows, each containing V NVs of 128 elements
    gfp_a_exp = []
    gfp_a_mant = []
    for b in range(B):
        row_exp = []
        row_mant = []
        for v in range(V):
            nv_idx = b * V + v
            if nv_idx < len(left_exp_subset):
                row_exp.extend(left_exp_subset[nv_idx])
                row_mant.extend(left_mant_subset[nv_idx])
        gfp_a_exp.append(row_exp)
        gfp_a_mant.append(row_mant)

    # For Matrix B: each column is one output column, V NVs concatenated
    gfp_b_exp = []
    gfp_b_mant = []
    for c in range(C):
        col_exp = []
        col_mant = []
        for v in range(V):
            nv_idx = c * V + v
            if nv_idx < len(right_exp_subset):
                col_exp.extend(right_exp_subset[nv_idx])
                col_mant.extend(right_mant_subset[nv_idx])
        gfp_b_exp.append(col_exp)
        gfp_b_mant.append(col_mant)

    # Dequantize to float
    float_a = torch.zeros(B, 128 * V)
    for b in range(B):
        for g_idx, exp in enumerate(gfp_a_exp[b]):
            scale = 2.0 ** (exp - 15)
            start_elem = g_idx * 32
            for i in range(32):
                elem_idx = start_elem + i
                if elem_idx < 128 * V:
                    mant = gfp_a_mant[b][elem_idx]
                    float_a[b, elem_idx] = mant * scale

    float_b = torch.zeros(128 * V, C)
    for c in range(C):
        for g_idx, exp in enumerate(gfp_b_exp[c]):
            scale = 2.0 ** (exp - 15)
            start_elem = g_idx * 32
            for i in range(32):
                elem_idx = start_elem + i
                if elem_idx < 128 * V:
                    mant = gfp_b_mant[c][elem_idx]
                    float_b[elem_idx, c] = mant * scale

    # Create GFP tensors
    gfp_dtype = GFPDataType(
        mantissa_bits=8,
        exp_bits=5,
        exp_bias=15,
        mantissa_signed=True
    )

    gfp_a = GFPTensor(
        original_shape=torch.Size([B, 128 * V]),
        group_axis=1,
        group_size=32,
        dtype=gfp_dtype,
        original_data=float_a
    )

    gfp_b = GFPTensor(
        original_shape=torch.Size([128 * V, C]),
        group_axis=0,
        group_size=32,
        dtype=gfp_dtype,
        original_data=float_b
    )

    # Compute GEMM
    product_dtype = GFPDataType(mantissa_bits=19, exp_bits=8, mantissa_signed=True)
    accum_dtype = GFPDataType(mantissa_bits=20, exp_bits=9, mantissa_signed=True)
    gemm = GFPGemm(accum_dtype=accum_dtype, product_dtype=product_dtype)

    gfp_result = gemm(gfp_a, gfp_b)
    result = gfp_result.dequantize()

    return result

def main():
    print("="*70)
    print("Generating Golden References for Multiple (B, C, V) Test Cases")
    print("="*70)

    # Load hex files (128 NVs each)
    print("\nLoading left.hex (128 NVs)...")
    left_exp, left_mant = load_nv_from_hex("left.hex", 128)
    print(f"  Loaded {len(left_exp)} NVs")

    print("Loading right.hex (128 NVs)...")
    right_exp, right_mant = load_nv_from_hex("right.hex", 128)
    print(f"  Loaded {len(right_exp)} NVs")

    # Generate golden references
    print("\n" + "="*70)
    for idx, (B, C, V, desc) in enumerate(TEST_CASES):
        print(f"\nTest {idx}: B={B}, C={C}, V={V} - {desc}")
        print(f"  Matrix A: {B} × {128*V}, uses {B*V} NVs")
        print(f"  Matrix B: {128*V} × {C}, uses {C*V} NVs")
        print(f"  Output:   {B} × {C}")

        result = compute_golden_for_bcv(B, C, V, left_exp, left_mant, right_exp, right_mant)

        # Save to file
        filename = f"golden_B{B}_C{C}_V{V}.txt"
        with open(filename, 'w') as f:
            f.write(f"Golden Reference: B={B}, C={C}, V={V}\n")
            f.write(f"Result shape: {result.shape}\n")
            f.write(f"Min: {result.min():.6f}, Max: {result.max():.6f}\n")
            f.write(f"Mean: {result.mean():.6f}\n\n")

            # Write matrix values
            for r in range(B):
                for c in range(C):
                    f.write(f"{result[r, c]:.6f} ")
                f.write("\n")

        print(f"  Range: [{result.min():.6f}, {result.max():.6f}]")
        print(f"  Written: {filename}")

    print("\n" + "="*70)
    print("All golden references generated!")
    print("="*70)

if __name__ == "__main__":
    main()
