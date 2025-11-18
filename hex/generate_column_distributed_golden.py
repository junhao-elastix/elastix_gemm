#!/usr/bin/env python3
"""
Generate golden reference files for column-distributed multi-tile GEMM.

This generator matches the actual hardware behavior where multiple tiles
operate in parallel on the SAME input matrices, with each tile computing
a subset of columns.

This is different from the sequential tiling approach in hardware_gfp_reference.py
which assumes tiles process different regions of the input matrices sequentially.
"""

import numpy as np
import os
import sys
import struct
import argparse

# Add parent directory to path to import hardware_gfp_reference
script_dir = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, script_dir)

from hardware_gfp_reference import (
    HardwareGFPCompute,
    load_hex_file,
    decode_exponents,
    decode_mantissas
)


def generate_column_distributed_golden(B, C, V, num_tiles, output_prefix="golden"):
    """
    Generate golden reference for column-distributed multi-tile execution.

    In this mode:
    - All tiles operate on the SAME input matrices
    - Each tile computes a subset of columns
    - Results are collected round-robin by the arbiter

    Args:
        B: Output rows (batch size)
        C: Output columns (total across all tiles)
        V: Inner dimension multiplier (V Native Vectors per output)
        num_tiles: Number of tiles to distribute columns across
        output_prefix: Prefix for output files

    Returns:
        tuple: (ordered_results, tile_results_dict)
    """
    print(f"Column-Distributed Multi-Tile Configuration:")
    print(f"  B={B}, C={C}, V={V}")
    print(f"  Number of tiles: {num_tiles}")

    # Load matrices from hex files
    left_hex_path = os.path.join(script_dir, 'left.hex')
    right_hex_path = os.path.join(script_dir, 'right.hex')

    exp_left_raw, man_left_raw = load_hex_file(left_hex_path)
    left_exp = decode_exponents(exp_left_raw).numpy()
    left_mant = decode_mantissas(man_left_raw)

    exp_right_raw, man_right_raw = load_hex_file(right_hex_path)
    right_exp = decode_exponents(exp_right_raw).numpy()
    right_mant = decode_mantissas(man_right_raw)

    print(f"  Left matrix: {left_mant.shape}, Right matrix: {right_mant.shape}")

    # Initialize hardware-accurate compute engine
    hw_compute = HardwareGFPCompute(exp_bits=5, exp_bias=15, group_size=32)

    # Calculate column distribution - ROUND-ROBIN pattern matching dispatcher behavior
    # With ugd_vec_size = V (one column worth of data), columns are distributed round-robin

    print(f"\nColumn distribution (round-robin):")

    # Build list of which tile gets which columns
    tile_columns = {}
    for tile_idx in range(num_tiles):
        tile_columns[tile_idx] = []

    # Distribute columns in round-robin fashion
    for col_idx in range(C):
        tile_idx = col_idx % num_tiles
        tile_columns[tile_idx].append(col_idx)

    # Print distribution
    for tile_idx in range(num_tiles):
        cols = tile_columns[tile_idx]
        print(f"  Tile {tile_idx}: columns {cols} ({len(cols)} columns)")

    # Store results for each tile
    tile_results = {}

    # Compute results for each tile
    for tile_idx in range(num_tiles):
        # Get the columns this tile computes
        cols_to_compute = tile_columns[tile_idx]

        print(f"  Tile {tile_idx}: computing columns {cols_to_compute}")

        # For each tile, compute B rows × selected columns
        # We'll compute the full B×C matrix and extract this tile's columns
        full_results = hw_compute.compute_gemm_with_bcv(
            left_mant, left_exp, right_mant, right_exp, B, C, V
        )

        # Extract this tile's results (only the round-robin columns)
        tile_results[tile_idx] = []
        for b_idx in range(B):
            for c_idx in cols_to_compute:
                # Results are in row-major order: index = b_idx * C + c_idx
                result_idx = b_idx * C + c_idx
                tile_results[tile_idx].append(full_results[result_idx])

        print(f"    Computed {len(tile_results[tile_idx])} results for tile {tile_idx}")

    # Now simulate the round-robin arbiter collection
    # The arbiter collects one result at a time from each tile in round-robin fashion
    ordered_results = []

    # Track position in each tile's result list
    tile_positions = [0] * num_tiles
    total_results = B * C
    current_tile = 0

    print(f"\nSimulating round-robin arbiter collection:")

    while len(ordered_results) < total_results:
        # Try to collect from current tile
        if tile_positions[current_tile] < len(tile_results[current_tile]):
            # Tile has data - collect it
            result = tile_results[current_tile][tile_positions[current_tile]]
            ordered_results.append(result)
            tile_positions[current_tile] += 1

        # Move to next tile (round-robin)
        current_tile = (current_tile + 1) % num_tiles

    print(f"  Collected {len(ordered_results)} total results")

    # Write output file
    hex_filename = f"{output_prefix}.hex"

    with open(hex_filename, 'w') as f:
        for val in ordered_results:
            f.write(f"{val:04x}\n")

    print(f"\nGenerated: {hex_filename} ({len(ordered_results)} FP16 results)")
    print(f"  First 8 values: {' '.join(f'0x{v:04x}' for v in ordered_results[:8])}")

    return ordered_results, tile_results


def main():
    parser = argparse.ArgumentParser(
        description='Generate column-distributed multi-tile golden reference')
    parser.add_argument('--B', type=int, required=True, help='Output rows')
    parser.add_argument('--C', type=int, required=True, help='Output columns')
    parser.add_argument('--V', type=int, required=True, help='Inner dimension multiplier')
    parser.add_argument('--tiles', type=int, default=2, help='Number of tiles')
    parser.add_argument('--output', type=str, default='golden',
                        help='Output file prefix')
    args = parser.parse_args()

    print("=" * 80)
    print("Column-Distributed Multi-Tile Golden Reference Generator")
    print("=" * 80)

    generate_column_distributed_golden(
        args.B, args.C, args.V, args.tiles, args.output
    )

    print("=" * 80)
    print("Generation complete!")
    print("=" * 80)


if __name__ == "__main__":
    main()