#!/usr/bin/env python3
"""
FP to GFP Conversion using Elastix Emulator (1D Tensor Only)

This module provides floating point to GFP (Group Floating Point) conversion
for 1D tensors by wrapping the emulator's GFPTensor class.
"""

import sys
from pathlib import Path

# Add emulator to path
emulator_path = Path(__file__).resolve().parents[3] / "emulator" / "src"
sys.path.insert(0, str(emulator_path))

import torch
from emulator.group_floating_point import GFPDataType, GFPTensor


def fp_to_gfp_1d(
    data: torch.Tensor,
    mantissa_bits: int = 8,
    exp_bits: int = 8,
    exp_bias: int | None = None,
    group_size: int = 32,
) -> tuple[torch.Tensor, torch.Tensor]:
    """
    Convert 1D floating point tensor to GFP format.

    Args:
        data: 1D input floating point tensor
        mantissa_bits: Number of bits for mantissa (default 8)
        exp_bits: Number of bits for exponent (default 8)
        exp_bias: Exponent bias (default: 2^(exp_bits-1))
        group_size: Number of elements sharing an exponent (default 32)

    Returns:
        Tuple of (mantissa, exponent):
        - mantissa: Quantized mantissa values, shape [num_groups, group_size]
        - exponent: Shared exponent per group, shape [num_groups, 1]
    """
    if data.ndim != 1:
        raise ValueError(f"Expected 1D tensor, got {data.ndim}D")

    dtype = GFPDataType(
        mantissa_bits=mantissa_bits,
        exp_bits=exp_bits,
        exp_bias=exp_bias,
        mantissa_signed=True,
    )

    gfp_tensor = GFPTensor(
        original_shape=data.shape,
        group_axis=-1,
        group_size=group_size,
        dtype=dtype,
        original_data=data,
    )

    return gfp_tensor.mantissa_data, gfp_tensor.exp_data


def gfp_to_fp_1d(
    mantissa: torch.Tensor,
    exponent: torch.Tensor,
    original_len: int,
    mantissa_bits: int = 8,
    exp_bits: int = 8,
    exp_bias: int | None = None,
    group_size: int = 32,
) -> torch.Tensor:
    """
    Convert GFP format back to 1D floating point tensor.

    Args:
        mantissa: GFP mantissa data, shape [num_groups, group_size]
        exponent: GFP exponent data, shape [num_groups, 1]
        original_len: Original 1D tensor length
        mantissa_bits: Number of bits for mantissa
        exp_bits: Number of bits for exponent
        exp_bias: Exponent bias
        group_size: Number of elements per group

    Returns:
        Dequantized 1D floating point tensor
    """
    dtype = GFPDataType(
        mantissa_bits=mantissa_bits,
        exp_bits=exp_bits,
        exp_bias=exp_bias,
        mantissa_signed=True,
    )

    gfp_tensor = GFPTensor(
        original_shape=torch.Size([original_len]),
        group_axis=-1,
        group_size=group_size,
        dtype=dtype,
        mantissa_data=mantissa,
        exp_data=exponent,
        sign_data=None,
    )

    return gfp_tensor.dequantize()


# =============================================================================
# Test / Demo
# =============================================================================
if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description="FP to GFP 1D Conversion Test")
    parser.add_argument("-m", "--mantissa-bits", type=int, default=8,
                        help="GFP mantissa bits (default: 8)")
    parser.add_argument("-e", "--exp-bits", type=int, default=8,
                        help="GFP exponent bits (default: 8)")
    parser.add_argument("-g", "--group-size", type=int, default=32,
                        help="GFP group size (default: 4)")
    parser.add_argument("-s", "--std", type=float, default=1.0,
                        help="Standard deviation for random data (default: 1.0)")
    parser.add_argument("-n", "--num-elements", type=int, default=128,
                        help="Number of elements in test tensor (default: 8)")
    parser.add_argument("-d", "--dtype", type=str, default="fp32",
                        choices=["fp32", "fp16", "bf16"],
                        help="Input floating point dtype (default: fp32)")
    parser.add_argument("--seed", type=int, default=42,
                        help="Random seed (default: 42)")
    args = parser.parse_args()

    # Set random seed
    torch.manual_seed(args.seed)

    # Map dtype string to torch dtype
    dtype_map = {
        "fp32": torch.float32,
        "fp16": torch.float16,
        "bf16": torch.bfloat16,
    }
    torch_dtype = dtype_map[args.dtype]

    m_bits = args.mantissa_bits
    e_bits = args.exp_bits
    g_size = args.group_size
    bias = 2 ** (e_bits - 1)

    print("=" * 70)
    print("FP to GFP 1D Conversion Test (using Elastix Emulator)")
    print(f"  mantissa_bits={m_bits}, exp_bits={e_bits}, group_size={g_size}, bias={bias}")
    print(f"  std={args.std}, num_elements={args.num_elements}, dtype={args.dtype}")
    print("=" * 70)

    data = (torch.randn(args.num_elements) * args.std).to(torch_dtype)
    print(f"\nInput: {data.tolist()}")

    m, e = fp_to_gfp_1d(data, mantissa_bits=m_bits, exp_bits=e_bits, group_size=g_size)
    print(f"\nMantissa shape: {m.shape}  (num_groups x group_size)")
    print(f"Exponent shape: {e.shape}  (num_groups x 1)")
    print(f"Mantissa:\n  {m.tolist()}")
    print(f"Exponent:\n  {e.tolist()}")

    # Dequantize and verify
    recon = gfp_to_fp_1d(m, e, len(data), mantissa_bits=m_bits, exp_bits=e_bits, group_size=g_size)
    print(f"\nReconstructed: {recon.tolist()}")

    # Error metrics
    err = data - recon
    max_err = err.abs().max().item()
    rmse = (err ** 2).mean().sqrt().item()
    print(f"\nMax error: {max_err:.6e}")
    print(f"RMSE:      {rmse:.6e}")

    print("\n" + "=" * 70)
    print("PASS" if max_err < 0.1 else "FAIL")
    print("=" * 70)
