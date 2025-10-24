#!/usr/bin/env python3
"""
External Memory Layout Calculator for GFP Tensors

This script calculates and displays the external memory layout for GFP tensors
based on the configuration described in CLAUDE.md:
- GFP group size: 32 elements
- Native vector size: 128 elements (4 groups)
- Block size: 128 native vectors
- Mantissa bits: 8, Exponent bits: 8
- Channel bytes: 32 (memory burst alignment)
"""

import math
from typing import Tuple


def calculate_memory_layout(tensor_rows: int, tensor_cols: int) -> dict:
    """
    Calculate external memory layout for a 2D tensor.

    Args:
        tensor_rows: First dimension (ungrouped dimension)
        tensor_cols: Second dimension (grouped dimension, must be divisible by 128)

    Returns:
        Dictionary with memory layout information
    """
    # Configuration constants
    GFP_GROUP_SIZE = 32
    NATIVE_VECTOR_SIZE = 128  # 4 groups of 32 elements
    BLOCK_SIZE = 128  # Native vectors per block
    MANTISSA_BITS = 8
    EXPONENT_BITS = 8
    CHANNEL_BYTES = 32  # Memory burst alignment

    # Validate input
    if tensor_cols % NATIVE_VECTOR_SIZE != 0:
        raise ValueError(f"tensor_cols ({tensor_cols}) must be divisible by native vector size ({NATIVE_VECTOR_SIZE})")

    # Calculate basic dimensions
    native_vectors_per_row = tensor_cols // NATIVE_VECTOR_SIZE
    total_native_vectors = tensor_rows * native_vectors_per_row
    total_blocks = math.ceil(total_native_vectors / BLOCK_SIZE)

    # Calculate memory requirements per block
    groups_per_native_vector = NATIVE_VECTOR_SIZE // GFP_GROUP_SIZE  # 4 groups
    exponents_per_native_vector = groups_per_native_vector  # 4 exponents
    mantissa_bytes_per_native_vector = NATIVE_VECTOR_SIZE  # 128 bytes (1 byte per element)

    # Block memory layout
    exponents_per_block = BLOCK_SIZE * exponents_per_native_vector  # 128 * 4 = 512 exponents
    exponent_bytes_per_block = exponents_per_block  # 1 byte per exponent = 512 bytes
    exponent_entries_per_block = math.ceil(exponent_bytes_per_block / CHANNEL_BYTES)  # 512/32 = 16 entries

    mantissa_bytes_per_block = BLOCK_SIZE * mantissa_bytes_per_native_vector  # 128 * 128 = 16,384 bytes
    mantissa_entries_per_block = mantissa_bytes_per_block // CHANNEL_BYTES  # 16,384/32 = 512 entries

    total_entries_per_block = exponent_entries_per_block + mantissa_entries_per_block
    total_memory_entries = total_blocks * total_entries_per_block
    total_memory_bytes = total_memory_entries * CHANNEL_BYTES

    # Calculate compression ratio vs FP32
    fp32_bytes = tensor_rows * tensor_cols * 4  # 4 bytes per FP32
    compression_ratio = fp32_bytes / total_memory_bytes

    return {
        'tensor_shape': (tensor_rows, tensor_cols),
        'native_vectors_per_row': native_vectors_per_row,
        'total_native_vectors': total_native_vectors,
        'total_blocks': total_blocks,
        'block_layout': {
            'exponent_section': {
                'bytes': exponent_bytes_per_block,
                'entries': exponent_entries_per_block,
                'address_range': '0 to 15'
            },
            'mantissa_section': {
                'bytes': mantissa_bytes_per_block,
                'entries': mantissa_entries_per_block,
                'address_range': f'16 to {15 + mantissa_entries_per_block}'
            },
            'total_entries_per_block': total_entries_per_block,
            'bytes_per_block': total_entries_per_block * CHANNEL_BYTES
        },
        'memory_totals': {
            'total_entries': total_memory_entries,
            'total_bytes': total_memory_bytes,
            'total_mb': total_memory_bytes / (1024 * 1024)
        },
        'compression': {
            'fp32_bytes': fp32_bytes,
            'gfp_bytes': total_memory_bytes,
            'ratio': compression_ratio,
            'savings_percent': (1 - 1/compression_ratio) * 100
        }
    }


def print_memory_layout(layout: dict):
    """Print formatted memory layout information."""
    print("=" * 70)
    print("EXTERNAL MEMORY LAYOUT ANALYSIS")
    print("=" * 70)

    print(f"\nTensor Configuration:")
    print(f"  Shape: {layout['tensor_shape'][0]} × {layout['tensor_shape'][1]}")
    print(f"  Native vectors per row: {layout['native_vectors_per_row']}")
    print(f"  Total native vectors: {layout['total_native_vectors']:,}")
    print(f"  Total blocks: {layout['total_blocks']:,}")

    block = layout['block_layout']
    print(f"\nBlock Memory Organization:")
    print(f"  Block size: {layout['total_blocks']:,} blocks × {block['total_entries_per_block']} entries = {block['bytes_per_block']:,} bytes per block")
    print(f"  ┌─────────────────────────────────────────────────────────────┐")
    print(f"  │ EXPONENT SECTION (entries {block['exponent_section']['address_range']})              │")
    print(f"  │   - {block['exponent_section']['bytes']:,} bytes in {block['exponent_section']['entries']} entries                           │")
    print(f"  │   - 128 native vectors × 4 exponents per vector            │")
    print(f"  ├─────────────────────────────────────────────────────────────┤")
    print(f"  │ MANTISSA SECTION (entries {block['mantissa_section']['address_range']})            │")
    print(f"  │   - {block['mantissa_section']['bytes']:,} bytes in {block['mantissa_section']['entries']} entries                         │")
    print(f"  │   - 128 native vectors × 128 bytes per vector              │")
    print(f"  └─────────────────────────────────────────────────────────────┘")

    mem = layout['memory_totals']
    print(f"\nTotal Memory Requirements:")
    print(f"  Total entries: {mem['total_entries']:,}")
    print(f"  Total bytes: {mem['total_bytes']:,} ({mem['total_mb']:.1f} MB)")

    comp = layout['compression']
    print(f"\nCompression Analysis:")
    print(f"  FP32 storage: {comp['fp32_bytes']:,} bytes")
    print(f"  GFP storage:  {comp['gfp_bytes']:,} bytes")
    print(f"  Compression ratio: {comp['ratio']:.1f}× smaller")
    print(f"  Storage savings: {comp['savings_percent']:.1f}%")


def calculate_block_addresses(layout: dict, block_id: int) -> Tuple[int, int]:
    """Calculate start and end addresses for a specific block."""
    entries_per_block = layout['block_layout']['total_entries_per_block']
    start_addr = block_id * entries_per_block
    end_addr = start_addr + entries_per_block - 1
    return start_addr, end_addr


def main():
    """Interactive memory layout calculator."""
    print("GFP External Memory Layout Calculator")
    print("Configuration: 32-element groups, 128-element native vectors, 128 native vectors per block")
    print()

    while True:
        try:
            print("Enter tensor dimensions (or 'quit' to exit):")
            user_input = input("Rows: ").strip()
            if user_input.lower() == 'quit':
                break
            rows = int(user_input)

            user_input = input("Cols: ").strip()
            if user_input.lower() == 'quit':
                break
            cols = int(user_input)

            layout = calculate_memory_layout(rows, cols)
            print_memory_layout(layout)

            # Show example block addresses
            print(f"\nExample Block Addresses:")
            total_blocks = layout['total_blocks']
            example_blocks = min(3, total_blocks)
            for i in range(example_blocks):
                start, end = calculate_block_addresses(layout, i)
                print(f"  Block {i}: entries {start:,} to {end:,}")

            if total_blocks > 3:
                # Show last block
                start, end = calculate_block_addresses(layout, total_blocks - 1)
                print(f"  ...")
                print(f"  Block {total_blocks-1}: entries {start:,} to {end:,}")

            print("\n" + "=" * 70 + "\n")

        except ValueError as e:
            print(f"Error: {e}")
            print("Please enter valid integers for dimensions.\n")
        except KeyboardInterrupt:
            break

    print("Goodbye!")


if __name__ == "__main__":
    # Example calculations for common tensor sizes
    example_sizes = [
        (4096, 4096),    # Large square matrix
        (1024, 2048),    # Rectangular matrix
        (512, 512),      # Medium square matrix
        (128, 128),      # Small matrix
    ]

    print("Example Memory Layouts for Common Tensor Sizes:")
    print("=" * 70)

    for rows, cols in example_sizes:
        try:
            layout = calculate_memory_layout(rows, cols)
            print(f"\nTensor {rows}×{cols}:")
            print(f"  Blocks: {layout['total_blocks']:,}")
            print(f"  Memory: {layout['memory_totals']['total_mb']:.1f} MB")
            print(f"  Compression: {layout['compression']['ratio']:.1f}× vs FP32")
        except ValueError as e:
            print(f"  Error: {e}")

    # Show detailed layout for one example
    print("\n" + "=" * 70)
    print("DETAILED ANALYSIS FOR 4096×4096 TENSOR:")
    layout = calculate_memory_layout(4096, 4096)
    print_memory_layout(layout)

    print("\n" + "=" * 70)
    print("\nTo run interactive mode, uncomment the main() call below")
    # main()  # Uncomment for interactive mode