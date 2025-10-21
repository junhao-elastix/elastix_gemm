#!/usr/bin/env python3
"""
Multi-Tile Golden Reference Generator

Uses validated GFP emulator library to generate golden references for multi-tile tests.
Correctly handles address-based tile extraction from left.hex and right.hex.

Key Features:
- Uses official GFP emulator library (validated against hardware)
- Extracts tiles based on left_addr and right_addr
- Generates per-tile golden references
- Supports arbitrary B, C, V configurations

Address Translation:
- Each tile specifies left_addr and right_addr in BRAM address units
- Address 0 = NV 0 (lines 16-19 for mantissas)
- Address 32 = NV 32 (lines 144-147 for mantissas)
- Formula: NV_index = left_addr (since mantissas start at line 16, addr 0 = line 16)

Author: Claude Code
Date: Fri Oct 10 2025
"""

import numpy as np
import torch
import sys
import struct

# Add validated GFP emulator library
sys.path.append('/home/dev/Dev/emulator/src/emulator')
from group_floating_point import GFPTensor, GFPDataType, GFPGemm

# Add hex utilities
sys.path.append('/home/dev/Dev/elastix_gemm/hex')
from mem_layout import load_hex_file, decode_exponents, decode_mantissas


def load_gfp_data(hex_file, start_nv, num_nvs):
    """
    Load Native Vectors from hex file starting at specific NV index.
    
    Args:
        hex_file: Path to hex file (left.hex or right.hex)
        start_nv: Starting Native Vector index (derived from address)
        num_nvs: Number of Native Vectors to load
    
    Returns:
        exponents: List of [4] exponent arrays (one per NV)
        mantissas: List of [128] mantissa arrays (one per NV)
    """
    # Load full file using validated parser
    exp_data, mant_data = load_hex_file(hex_file)
    
    # Decode using validated functions
    exponents_full = decode_exponents(exp_data)  # [128, 4]
    mantissas_full = decode_mantissas(mant_data)  # [128, 128]
    
    # Extract requested NV range
    exponents = []
    mantissas = []
    
    for nv_idx in range(start_nv, min(start_nv + num_nvs, 128)):
        # Get exponents for this NV (4 groups of 32 elements each)
        nv_exps = exponents_full[nv_idx].tolist()
        exponents.append(nv_exps)
        
        # Get mantissas for this NV (128 elements)
        nv_mants = mantissas_full[nv_idx].tolist()
        mantissas.append(nv_mants)
    
    return exponents, mantissas


def reconstruct_gfp_tensor(exponents, mantissas, shape, group_axis):
    """
    Reconstruct GFPTensor from exponents and mantissas.
    
    Args:
        exponents: List of [4] exponent arrays
        mantissas: List of [128] mantissa arrays
        shape: (rows, cols) for the reconstructed tensor
        group_axis: 1 for left matrix (rows), 0 for right matrix (cols)
    
    Returns:
        GFPTensor ready for computation
    """
    gfp_dtype = GFPDataType(
        mantissa_bits=8,
        exp_bits=5,
        exp_bias=15,
        mantissa_signed=True
    )
    
    num_nvs = len(exponents)
    rows, cols = shape
    float_data = torch.zeros(rows, cols, dtype=torch.float32)
    
    if group_axis == 1:  # Left matrix (B rows × 128V columns)
        # Each row consists of V NVs concatenated
        # Example: B=2, V=2: Row 0 = NV[0,1], Row 1 = NV[2,3]
        for b in range(rows):  # For each output row (batch)
            for v in range(num_nvs // rows):  # For each NV in this row
                nv_idx = b * (num_nvs // rows) + v
                if nv_idx >= num_nvs:
                    break
                for g in range(4):  # 4 groups per NV
                    exp = exponents[nv_idx][g]
                    scale = 2.0 ** (exp - 15)
                    for elem in range(32):  # 32 elements per group
                        # Column offset: v*128 + g*32 + elem
                        col = v * 128 + g * 32 + elem
                        if col < cols:
                            mant = mantissas[nv_idx][g * 32 + elem]
                            # Handle signed mantissa
                            if mant > 127:
                                mant = mant - 256
                            float_data[b, col] = mant * scale
    else:  # Right matrix (128V rows × C columns), group_axis == 0
        # Each column consists of V NVs concatenated
        # Example: C=2, V=2: Col 0 = NV[0,1], Col 1 = NV[2,3]
        for c in range(cols):  # For each output column
            for v in range(num_nvs // cols):  # For each NV in this column
                nv_idx = c * (num_nvs // cols) + v
                if nv_idx >= num_nvs:
                    break
                for g in range(4):  # 4 groups per NV
                    exp = exponents[nv_idx][g]
                    scale = 2.0 ** (exp - 15)
                    for elem in range(32):  # 32 elements per group
                        # Row offset: v*128 + g*32 + elem
                        row = v * 128 + g * 32 + elem
                        if row < rows:
                            mant = mantissas[nv_idx][g * 32 + elem]
                            # Handle signed mantissa
                            if mant > 127:
                                mant = mant - 256
                            float_data[row, c] = mant * scale
    
    # Create GFP tensor from float data
    return GFPTensor(
        original_shape=torch.Size(shape),
        group_axis=group_axis,
        group_size=32,
        dtype=gfp_dtype,
        original_data=float_data
    )


def float_to_fp16_hex(value):
    """Convert float32 to FP16 hex string (4 digits)"""
    # Convert to FP16
    fp16_value = np.float16(value)
    # Pack as uint16 and format as 4-digit hex
    bytes_val = struct.pack('<e', fp16_value)
    uint16_val = struct.unpack('<H', bytes_val)[0]
    return f"{uint16_val:04x}"


def generate_tile_golden(left_addr, right_addr, B, C, V, left_file, right_file):
    """
    Generate golden reference for a single tile.
    
    Args:
        left_addr: BRAM address for left matrix (NV start index)
        right_addr: BRAM address for right matrix (NV start index)
        B: Batch dimension (output rows)
        C: Column dimension (output columns)
        V: Vector dimension (inner dimension = 128*V)
        left_file: Path to left.hex
        right_file: Path to right.hex
    
    Returns:
        results_fp16: List of FP16 values (B×C results)
        results_hex: List of 4-digit hex strings
    """
    # Address to NV index: Each NV occupies 4 mantissa lines
    # Both left_addr and right_addr are relative offsets (mantissa line units)
    # NV index = address / 4
    # Example: addr=0 -> NV 0, addr=32 -> NV 8
    left_start_nv = left_addr // 4
    right_start_nv = right_addr // 4
    
    # Load tile data
    print(f"  Loading left NVs {left_start_nv} to {left_start_nv + B*V - 1} (B={B}, V={V})")
    left_exp, left_mant = load_gfp_data(left_file, left_start_nv, B * V)
    print(f"    DEBUG: Loaded {len(left_exp)} NVs, first NV exp={left_exp[0] if left_exp else 'none'}")
    
    print(f"  Loading right NVs {right_start_nv} to {right_start_nv + C*V - 1} (C={C}, V={V})")
    right_exp, right_mant = load_gfp_data(right_file, right_start_nv, C * V)
    print(f"    DEBUG: Loaded {len(right_exp)} NVs, first NV exp={right_exp[0] if right_exp else 'none'}")
    
    # Reconstruct GFP tensors
    # Left matrix: B rows × (128*V) columns, group_axis=1
    # Right matrix: (128*V) rows × C columns, group_axis=0
    left_tensor = reconstruct_gfp_tensor(left_exp, left_mant, (B, 128*V), group_axis=1)
    right_tensor = reconstruct_gfp_tensor(right_exp, right_mant, (128*V, C), group_axis=0)
    
    # Perform GFP GEMM using validated emulator
    # Define intermediate data types for accumulation and products
    product_dtype = GFPDataType(mantissa_bits=19, exp_bits=8, mantissa_signed=True)
    accum_dtype = GFPDataType(mantissa_bits=20, exp_bits=9, mantissa_signed=True)
    gemm = GFPGemm(accum_dtype=accum_dtype, product_dtype=product_dtype)
    
    # Compute matmul
    result_tensor = gemm(left_tensor, right_tensor)
    
    # Convert to FP16
    result_float = result_tensor.dequantize().flatten().numpy()
    results_fp16 = [np.float16(val) for val in result_float]
    results_hex = [float_to_fp16_hex(val) for val in result_float]
    
    return results_fp16, results_hex


def main():
    """Generate golden references for multi-tile test"""
    
    # Paths
    left_file = "/home/dev/Dev/elastix_gemm/hex/left.hex"
    right_file = "/home/dev/Dev/elastix_gemm/hex/right.hex"
    output_dir = "/home/dev/Dev/compute_engine_w8a8/hex"
    
    # Multi-tile test configuration: 2 tiles × (B=2, C=2, V=2)
    # Addresses match hardware testbench:
    # - Left matrix: BRAM[0-527], right matrix: BRAM[528-1055]
    # - Tile 0: left=0 (NV 0), right=528 (right matrix base)
    # - Tile 1: left=32 (NV 8), right=560 (right matrix base + 32)
    # Tiles with relative addresses (mantissa line units)
    # Tile 0: NV 0 (mantissa line 0)
    # Tile 1: NV 8 (mantissa line 32, since 8 NVs × 4 lines/NV = 32)
    tiles = [
        {"id": 0, "left_addr": 0, "right_addr": 0, "B": 2, "C": 2, "V": 2},
        {"id": 1, "left_addr": 32, "right_addr": 32, "B": 2, "C": 2, "V": 2},
    ]
    
    print("=" * 60)
    print("Multi-Tile Golden Reference Generation")
    print("Using Validated GFP Emulator Library")
    print("=" * 60)
    
    all_results_fp16 = []
    all_results_hex = []
    
    for tile in tiles:
        tile_id = tile["id"]
        left_addr = tile["left_addr"]
        right_addr = tile["right_addr"]
        B = tile["B"]
        C = tile["C"]
        V = tile["V"]
        
        print(f"\nTile {tile_id}:")
        print(f"  left_addr={left_addr}, right_addr={right_addr}")
        print(f"  B={B}, C={C}, V={V} -> {B*C} results expected")
        
        # Generate golden reference for this tile
        results_fp16, results_hex = generate_tile_golden(
            left_addr, right_addr, B, C, V, left_file, right_file
        )
        
        # Display results
        print(f"  Results (FP16): {[f'{val:.6f}' for val in results_fp16]}")
        print(f"  Results (hex):  {results_hex}")
        
        # Accumulate
        all_results_fp16.extend(results_fp16)
        all_results_hex.extend(results_hex)
    
    # Save combined golden reference
    output_file = f"{output_dir}/golden_multi_tile_2x_B2_C2_V2.txt"
    with open(output_file, 'w') as f:
        f.write("# Multi-Tile Golden Reference\n")
        f.write("# Test: 2 tiles × (B=2, C=2, V=2) = 8 total results\n")
        f.write("# Generated using validated GFP emulator library\n")
        f.write(f"# Total results: {len(all_results_hex)}\n")
        f.write("#\n")
        for i, (hex_val, fp16_val) in enumerate(zip(all_results_hex, all_results_fp16)):
            tile_id = i // 4  # Each tile produces 4 results
            local_idx = i % 4
            f.write(f"{hex_val}  # Result[{i}]: Tile {tile_id}, local index {local_idx}, value={fp16_val:.6f}\n")
    
    print(f"\n{'=' * 60}")
    print(f"Golden reference saved to: {output_file}")
    print(f"Total results generated: {len(all_results_hex)}")
    print(f"{'=' * 60}")


if __name__ == "__main__":
    main()

