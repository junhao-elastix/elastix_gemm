#!/usr/bin/env python3
"""
Generate golden references for multi-tile test cases
Uses existing left.hex and right.hex (128 NVs each)

Multi-tile concept:
- Single FETCH+DISP loads 528 lines (16 exp + 512 mantissa)
- Multiple TILE commands process different regions
- Each TILE has its own left_addr, right_addr, B, C, V

Memory Layout:
- Lines 0-15: Exponent region (32 group exponents per line, 8-bit each)
- Lines 16-527: Mantissa region (1 group per line = 32 mantissas)
- left_addr in TILE command = mantissa line reference (0-511)
"""

import numpy as np
import torch
import sys
import os

sys.path.append('/home/dev/Dev/emulator/src/emulator')
from group_floating_point import GFPTensor, GFPDataType, GFPGemm

# Use validated hex parser from mem_layout.py
sys.path.append('/home/dev/Dev/elastix_gemm/hex')
from mem_layout import load_hex_file, decode_exponents, decode_mantissas

# Multi-tile test cases
# Format: list of tiles, each tile = (left_addr, right_addr, B, C, V, description)
MULTI_TILE_TESTS = [
    {
        "name": "two_tiles_simple",
        "description": "2 tiles with different addresses",
        "tiles": [
            (0, 0, 2, 2, 2, "First tile at addr 0"),
            (32, 32, 2, 2, 2, "Second tile at addr 32"),
        ]
    },
    {
        "name": "four_tiles_sequential",
        "description": "4 tiles processing sequential regions",
        "tiles": [
            (0, 0, 4, 4, 4, "Tile 0"),
            (64, 64, 4, 4, 4, "Tile 1"),
            (128, 128, 4, 4, 4, "Tile 2"),
            (192, 192, 4, 4, 4, "Tile 3"),
        ]
    },
    {
        "name": "eight_tiles_medium",
        "description": "8 tiles B=2, C=1, V=32",
        "tiles": [
            (0, 0, 2, 1, 32, "Tile 0"),
            (256, 64, 2, 1, 32, "Tile 1"),
            (0, 128, 2, 1, 32, "Tile 2"),
            (256, 192, 2, 1, 32, "Tile 3"),
            (0, 256, 2, 1, 32, "Tile 4"),
            (256, 320, 2, 1, 32, "Tile 5"),
            (0, 384, 2, 1, 32, "Tile 6"),
            (256, 448, 2, 1, 32, "Tile 7"),
        ]
    },
]

def load_nv_from_hex(filename, num_nvs):
    """Load Native Vectors from hex file using validated parser"""
    exp_data, mant_data = load_hex_file(filename)
    exponents_full = decode_exponents(exp_data)  # [128, 4]
    mantissas_full = decode_mantissas(mant_data)  # [128, 128]

    exponents = []
    mantissas = []

    for nv_idx in range(num_nvs):
        nv_exps = exponents_full[nv_idx].tolist()
        exponents.append(nv_exps)
        nv_mants = mantissas_full[nv_idx].tolist()
        mantissas.append(nv_mants)

    return exponents, mantissas

def extract_tile_data(all_exponents, all_mantissas, base_addr, B, C, V, matrix_type):
    """
    Extract data for one tile from full NV dataset
    
    Args:
        all_exponents: Full list of NV exponents [128 NVs, 4 groups each]
        all_mantissas: Full list of NV mantissas [128 NVs, 128 elements each]
        base_addr: Mantissa line reference (0-511) from TILE command
        B, C, V: Tile dimensions
        matrix_type: 'left' or 'right'
    
    Returns:
        Extracted exponents and mantissas for this tile
    """
    if matrix_type == 'left':
        num_nvs_needed = B * V
    else:  # right
        num_nvs_needed = C * V
    
    # Calculate starting NV index from base_addr
    # base_addr is mantissa line reference
    # Each NV occupies 4 mantissa lines (4 groups)
    start_nv = base_addr // 4
    
    tile_exponents = []
    tile_mantissas = []
    
    for i in range(num_nvs_needed):
        nv_idx = start_nv + i
        if nv_idx < len(all_exponents):
            tile_exponents.append(all_exponents[nv_idx])
            tile_mantissas.append(all_mantissas[nv_idx])
        else:
            print(f"  WARNING: NV {nv_idx} out of bounds, using zeros")
            tile_exponents.append([0, 0, 0, 0])
            tile_mantissas.append([0] * 128)
    
    return tile_exponents, tile_mantissas

def compute_golden_for_tile(left_addr, right_addr, B, C, V, 
                            all_left_exp, all_left_mant, 
                            all_right_exp, all_right_mant):
    """
    Compute golden reference for a single tile
    
    Args:
        left_addr, right_addr: Mantissa line references from TILE command
        B, C, V: Tile dimensions
        all_left_exp, all_left_mant: Full left matrix data (128 NVs)
        all_right_exp, all_right_mant: Full right matrix data (128 NVs)
    
    Returns:
        result: B x C torch tensor with FP32 golden reference
    """
    # Extract data for this specific tile
    left_exp, left_mant = extract_tile_data(all_left_exp, all_left_mant, 
                                            left_addr, B, C, V, 'left')
    right_exp, right_mant = extract_tile_data(all_right_exp, all_right_mant, 
                                              right_addr, B, C, V, 'right')
    
    # Dequantize to float
    # Matrix A: B x (128*V)
    float_a = torch.zeros(B, 128 * V)
    for b in range(B):
        for v in range(V):
            nv_idx = b * V + v
            if nv_idx < len(left_exp):
                for g in range(4):
                    exp = left_exp[nv_idx][g]
                    scale = 2.0 ** (exp - 15)
                    for elem in range(32):
                        col = v * 128 + g * 32 + elem
                        if col < 128 * V:
                            mant = left_mant[nv_idx][g * 32 + elem]
                            float_a[b, col] = mant * scale
    
    # Matrix B: (128*V) x C
    float_b = torch.zeros(128 * V, C)
    for c in range(C):
        for v in range(V):
            nv_idx = c * V + v
            if nv_idx < len(right_exp):
                for g in range(4):
                    exp = right_exp[nv_idx][g]
                    scale = 2.0 ** (exp - 15)
                    for elem in range(32):
                        row = v * 128 + g * 32 + elem
                        if row < 128 * V:
                            mant = right_mant[nv_idx][g * 32 + elem]
                            float_b[row, c] = mant * scale
    
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
    print("Generating Golden References for Multi-Tile Test Cases")
    print("="*70)
    
    # Load hex files (128 NVs each)
    print("\nLoading left.hex (128 NVs)...")
    left_exp, left_mant = load_nv_from_hex("left.hex", 128)
    print(f"  Loaded {len(left_exp)} NVs")
    
    print("Loading right.hex (128 NVs)...")
    right_exp, right_mant = load_nv_from_hex("right.hex", 128)
    print(f"  Loaded {len(right_exp)} NVs")
    
    # Process each multi-tile test
    for test_config in MULTI_TILE_TESTS:
        test_name = test_config["name"]
        test_desc = test_config["description"]
        tiles = test_config["tiles"]
        
        print("\n" + "="*70)
        print(f"Test: {test_name}")
        print(f"Description: {test_desc}")
        print(f"Number of tiles: {len(tiles)}")
        print("="*70)
        
        # Create output file for this test
        output_filename = f"golden_multi_tile_{test_name}.txt"
        
        with open(output_filename, 'w') as f:
            f.write(f"Multi-Tile Golden Reference: {test_name}\n")
            f.write(f"Description: {test_desc}\n")
            f.write(f"Number of tiles: {len(tiles)}\n\n")
            
            # Process each tile
            for tile_idx, tile_spec in enumerate(tiles):
                left_addr, right_addr, B, C, V, tile_desc = tile_spec
                
                print(f"\nTile {tile_idx}: {tile_desc}")
                print(f"  left_addr={left_addr}, right_addr={right_addr}")
                print(f"  B={B}, C={C}, V={V}")
                print(f"  Matrix A: {B} x {128*V}, uses {B*V} NVs starting at NV {left_addr//4}")
                print(f"  Matrix B: {128*V} x {C}, uses {C*V} NVs starting at NV {right_addr//4}")
                print(f"  Output:   {B} x {C} = {B*C} results")
                
                # Compute golden reference for this tile
                result = compute_golden_for_tile(
                    left_addr, right_addr, B, C, V,
                    left_exp, left_mant, right_exp, right_mant
                )
                
                # Write tile results
                f.write(f"--- Tile {tile_idx} ---\n")
                f.write(f"Description: {tile_desc}\n")
                f.write(f"left_addr={left_addr}, right_addr={right_addr}, B={B}, C={C}, V={V}\n")
                f.write(f"Result shape: {result.shape}\n")
                f.write(f"Min: {result.min():.6f}, Max: {result.max():.6f}\n")
                f.write(f"Mean: {result.mean():.6f}\n")
                f.write("Results:\n")
                
                for r in range(B):
                    for c in range(C):
                        f.write(f"{result[r, c]:.6f} ")
                    f.write("\n")
                f.write("\n")
                
                print(f"  Range: [{result.min():.6f}, {result.max():.6f}]")
        
        print(f"\nWritten: {output_filename}")
    
    print("\n" + "="*70)
    print("All multi-tile golden references generated!")
    print("="*70)

if __name__ == "__main__":
    main()









