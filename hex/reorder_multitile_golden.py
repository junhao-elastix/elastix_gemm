#!/usr/bin/env python3
"""
Reorder multi-tile golden reference files from row-major to tile-by-tile order.

For a B×C matrix with N tiles, where each tile computes B×(C/N):
- Input (row-major): [0,0], [0,1], [0,2], ..., [1,0], [1,1], [1,2], ...
- Output (tile-by-tile): [tile0 results], [tile1 results], ...
  where tile0 = [0,0], [0,1], [1,0], [1,1]
        tile1 = [0,2], [0,3], [1,2], [1,3]
"""

import sys

def reorder_2tile_results(B, C, input_hex_path, output_hex_path):
    """
    Reorder results for 2-tile configuration.

    Args:
        B: Number of rows
        C: Number of columns (must be even for 2 tiles)
        input_hex_path: Input golden file in row-major order
        output_hex_path: Output golden file in tile-by-tile order
    """
    if C % 2 != 0:
        raise ValueError(f"C={C} must be even for 2-tile configuration")

    C_per_tile = C // 2

    # Read input file
    with open(input_hex_path, 'r') as f:
        results = [line.strip() for line in f if line.strip()]

    expected_count = B * C
    if len(results) != expected_count:
        raise ValueError(f"Expected {expected_count} results, got {len(results)}")

    # Convert to 2D array (row-major)
    matrix = []
    for row in range(B):
        matrix.append(results[row*C : (row+1)*C])

    # Reorder: tile-by-tile
    reordered = []

    # Tile 0: columns [0, C_per_tile)
    for row in range(B):
        for col in range(C_per_tile):
            reordered.append(matrix[row][col])

    # Tile 1: columns [C_per_tile, C)
    for row in range(B):
        for col in range(C_per_tile, C):
            reordered.append(matrix[row][col])

    # Write output file
    with open(output_hex_path, 'w') as f:
        for val in reordered:
            f.write(f"{val}\n")

    print(f"Reordered {B}x{C} matrix from row-major to 2-tile order")
    print(f"  Input:  {input_hex_path}")
    print(f"  Output: {output_hex_path}")
    print(f"  Results per tile: {B * C_per_tile}")
    print(f"\nTile 0 results (columns 0-{C_per_tile-1}):")
    print(f"  " + " ".join(reordered[:min(8, B*C_per_tile)]))
    print(f"\nTile 1 results (columns {C_per_tile}-{C-1}):")
    print(f"  " + " ".join(reordered[B*C_per_tile:B*C_per_tile+min(8, B*C_per_tile)]))

if __name__ == '__main__':
    # Reorder all 2-tile golden files
    configs = [
        (2, 4, 16),   # B2_C4_V16_2T
        (4, 8, 8),    # B4_C8_V8_2T
        (8, 32, 2),   # B8_C32_V2_2T
        (16, 16, 4),  # B16_C16_V4_2T
    ]

    for B, C, V in configs:
        test_name = f"B{B}_C{C}_V{V}_2T"
        input_path = f"golden_{test_name}.hex"
        output_path = f"golden_{test_name}_reordered.hex"

        print("\n" + "="*80)
        print(f"Processing {test_name}")
        print("="*80)
        try:
            reorder_2tile_results(B, C, input_path, output_path)
        except Exception as e:
            print(f"ERROR: {e}")

    print("\n" + "="*80)
    print("Done! Replace original golden files with *_reordered.hex versions")
    print("="*80)
