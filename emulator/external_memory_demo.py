#!/usr/bin/env python3
"""
ExternalMem Class Demonstration

This script demonstrates how to use the actual ExternalMem class from api.py
to store GFP tensors in external memory with realistic hardware constraints.
Uses seed 42 for reproducible random data generation.
"""

import torch
import sys
import os

# Add the src/emulator directory to Python path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), 'src', 'emulator'))

from api import ExternalMem, GemmTileConfig, ExtMemTensorDescriptor
from group_floating_point import GFPTensor, GFPDataType


def create_gfp_data_type():
    """Create a standard 8-bit mantissa, 8-bit exponent GFP data type."""
    return GFPDataType(
        mantissa_bits=8,
        exp_bits=8,
        exp_bias=127,
        mantissa_signed=True
    )


def create_tile_config(dtype):
    """Create a tile configuration for the GEMM hardware."""
    return GemmTileConfig(
        left_dtype=dtype,
        right_dtype=dtype,
        output_dtype=dtype,
        group_size=32,      # 32 elements per group
        tile_groups=4,      # 4 groups per tile (128 elements total)
        left_mem_depth=128,
        right_mem_depth=128
    )


def create_external_memory(tile_config):
    """Create external memory with realistic FPGA constraints."""
    return ExternalMem(
        tile_config=tile_config,
        memory_channels=8,      # 8 memory channels (typical for GDDR6)
        channel_depth=1024*1024,  # 1M entries per channel
        channel_bytes=32        # 32-byte burst alignment
    )


def create_test_tensor(rows, cols, dtype, seed=42):
    """Create a test tensor with reproducible random data."""
    torch.manual_seed(seed)

    # Create random data scaled to reasonable range
    original_data = torch.randn(rows, cols) * 0.1

    # Convert to GFP tensor
    gfp_tensor = GFPTensor(
        original_shape=torch.Size([rows, cols]),
        group_axis=-1,  # Group along columns
        group_size=32,  # 32 elements per group
        dtype=dtype,
        original_data=original_data
    )

    return gfp_tensor, original_data


def analyze_memory_layout(ext_mem, tensor_desc):
    """Analyze and display the memory layout after writing tensor."""
    print(f"\nMemory Layout Analysis:")
    print(f"=" * 60)
    print(f"Tensor shape: {tensor_desc.gfp_shape}")
    print(f"Memory channels used: {tensor_desc.memory_channels}")
    print(f"Memory address range: {tensor_desc.memory_start_addr} to {tensor_desc.memory_end_addr}")
    print(f"Total memory entries used: {tensor_desc.memory_end_addr - tensor_desc.memory_start_addr + 1}")
    print(f"Number of blocks: {tensor_desc.block_cnt}")
    print(f"Native vectors per block: {tensor_desc.block_vectors}")
    print(f"Block depth (entries): {tensor_desc.block_depth}")
    print(f"Mantissa offset in block: {tensor_desc.block_mantissa_offset}")
    print(f"UGD native vectors: {tensor_desc.ugd_native_vectors}")

    # Calculate memory usage
    total_entries = tensor_desc.memory_end_addr - tensor_desc.memory_start_addr + 1
    total_bytes = total_entries * ext_mem.channel_bytes
    print(f"\nMemory Usage:")
    print(f"Total entries: {total_entries:,}")
    print(f"Total bytes: {total_bytes:,} ({total_bytes / (1024*1024):.2f} MB)")

    # Show block structure
    print(f"\nBlock Structure:")
    print(f"Each block contains {tensor_desc.block_vectors} native vectors")
    exp_entries = tensor_desc.block_mantissa_offset
    mantissa_entries = tensor_desc.block_depth - tensor_desc.block_mantissa_offset
    print(f"  Exponent section: {exp_entries} entries")
    print(f"  Mantissa section: {mantissa_entries} entries")
    print(f"  Total per block: {tensor_desc.block_depth} entries")


def inspect_memory_data(ext_mem, tensor_desc, channel=0, block=0):
    """Inspect actual memory data for verification."""
    print(f"\nMemory Data Inspection (Channel {channel}, Block {block}):")
    print(f"=" * 60)

    # Calculate block start address
    block_start = tensor_desc.memory_start_addr + (block * tensor_desc.block_depth)
    block_end = block_start + tensor_desc.block_depth

    print(f"Block {block} address range: {block_start} to {block_end-1}")

    # Get exponent section
    exp_end = block_start + tensor_desc.block_mantissa_offset
    exp_data = ext_mem.mem[channel, block_start:exp_end, :]
    print(f"\nExponent section ({block_start} to {exp_end-1}):")
    print(f"Shape: {exp_data.shape}")
    print(f"First few entries: {exp_data[:min(3, exp_data.shape[0]), :8]}")

    # Get mantissa section
    mantissa_start = exp_end
    mantissa_data = ext_mem.mem[channel, mantissa_start:block_end, :]
    print(f"\nMantissa section ({mantissa_start} to {block_end-1}):")
    print(f"Shape: {mantissa_data.shape}")
    print(f"First few entries: {mantissa_data[:min(3, mantissa_data.shape[0]), :16]}")

    # Show some statistics
    exp_nonzero = (exp_data != 0).sum().item()
    mantissa_nonzero = (mantissa_data != 0).sum().item()
    print(f"\nData Statistics:")
    print(f"Non-zero exponent elements: {exp_nonzero}")
    print(f"Non-zero mantissa elements: {mantissa_nonzero}")


def demonstrate_external_memory():
    """Main demonstration of ExternalMem functionality."""
    print("ExternalMem Class Demonstration")
    print("=" * 60)

    # Create GFP data type and tile configuration
    dtype = create_gfp_data_type()
    tile_config = create_tile_config(dtype)

    print(f"GFP Data Type: {dtype}")
    print(f"Tile Configuration:")
    print(f"  Group size: {tile_config.group_size}")
    print(f"  Tile groups: {tile_config.tile_groups}")
    print(f"  Native size: {tile_config.native_size}")

    # Create external memory
    ext_mem = create_external_memory(tile_config)
    print(f"\nExternal Memory Configuration:")
    print(f"  Memory channels: {ext_mem.memory_channels}")
    print(f"  Channel depth: {ext_mem.channel_depth:,}")
    print(f"  Channel bytes: {ext_mem.channel_bytes}")
    print(f"  Total memory: {ext_mem.memory_channels * ext_mem.channel_depth * ext_mem.channel_bytes / (1024*1024*1024):.1f} GB")

    # Test different tensor sizes
    test_cases = [
        (128, 256, "Small tensor"),
        (512, 512, "Medium tensor"),
        (1024, 2048, "Large tensor")
    ]

    for rows, cols, description in test_cases:
        print(f"\n{'='*60}")
        print(f"Testing {description}: {rows} × {cols}")
        print(f"{'='*60}")

        try:
            # Create test tensor with seed 42
            gfp_tensor, original_data = create_test_tensor(rows, cols, dtype, seed=42)

            print(f"Original tensor stats:")
            print(f"  Shape: {original_data.shape}")
            print(f"  Range: [{original_data.min():.4f}, {original_data.max():.4f}]")
            print(f"  Mean: {original_data.mean():.4f}")

            print(f"GFP tensor stats:")
            print(f"  Mantissa shape: {gfp_tensor.mantissa_shape}")
            print(f"  Exponent shape: {gfp_tensor.exp_shape}")

            # Write tensor to external memory
            target_address = 1000  # Start at address 1000
            block_size = 128       # 128 native vectors per block

            tensor_desc = ext_mem.write_tensor(
                tensor=gfp_tensor,
                target_address=target_address,
                row=None,  # Distribute across all channels
                block_vectors=block_size,
                inline_exp_storage=False
            )

            # Analyze the memory layout
            analyze_memory_layout(ext_mem, tensor_desc)

            # Inspect memory data for the first block
            if tensor_desc.block_cnt > 0:
                inspect_memory_data(ext_mem, tensor_desc, channel=0, block=0)

            # Verify data integrity by checking reconstruction
            reconstructed = gfp_tensor.dequantize()
            rmse = (reconstructed - original_data).pow(2).mean().sqrt()
            print(f"\nData Integrity Check:")
            print(f"Reconstruction RMSE: {rmse:.6f}")

        except Exception as e:
            print(f"Error processing {description}: {e}")
            import traceback
            traceback.print_exc()


if __name__ == "__main__":
    demonstrate_external_memory()