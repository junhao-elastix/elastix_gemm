import logging

import torch

from emulator import group_floating_point as gfp


def max_error(x: gfp.GFPTensor, y: torch.Tensor):
    return (x.dequantize() - y).abs().max()


def rmse(x: gfp.GFPTensor, y: torch.Tensor):
    return (x.dequantize() - y).pow(2).mean().sqrt()


def test_gemm():
    # Configure logging for the test
    logging.basicConfig(level=logging.INFO, format="%(levelname)s: %(message)s")

    # Test parameters
    batch_size = 16  # B
    input_channels = 4096  # C
    output_channels = 4096  # R

    group_size = 128  # G
    lhs_mantissa_bits = 9
    rhs_mantissa_bits = 9
    product_mantissa_bits = 20
    accum_mantissa_bits = 23
    output_mantissa_bits = 9
    exp_bits = 5

    # GFP configurations
    lhs_dtype = gfp.GFPDataType(
        mantissa_bits=lhs_mantissa_bits,
        exp_bits=exp_bits,
    )
    rhs_dtype = gfp.GFPDataType(
        mantissa_bits=rhs_mantissa_bits,
        exp_bits=exp_bits,
    )
    product_dtype = gfp.GFPDataType(
        mantissa_bits=product_mantissa_bits,
        exp_bits=exp_bits,
    )
    accum_dtype = gfp.GFPDataType(
        mantissa_bits=accum_mantissa_bits,
        exp_bits=exp_bits + 1,
    )
    output_dtype = gfp.GFPDataType(
        mantissa_bits=output_mantissa_bits,
        exp_bits=exp_bits,
    )

    # LHS: activations with standard distribution
    lhs_tensor = torch.randn(batch_size, input_channels)

    # RHS: weight parameters with scaled distribution
    weight_std = (1.0 / (input_channels + output_channels)) ** 0.5
    rhs_tensor = torch.randn(input_channels, output_channels) * weight_std

    gfp_lhs = gfp.GFPTensor(
        lhs_tensor.shape,
        group_axis=1,
        group_size=group_size,
        dtype=lhs_dtype,
        original_data=lhs_tensor,
    )

    print(f"\nLHS GFP: {gfp_lhs}")
    print(f"LHS Max Error: {max_error(gfp_lhs, lhs_tensor):.6f}")
    print(f"LHS RMSE: {rmse(gfp_lhs, lhs_tensor):.6f}")

    gfp_rhs = gfp.GFPTensor(
        rhs_tensor.shape,
        group_axis=0,
        group_size=group_size,
        dtype=rhs_dtype,
        original_data=rhs_tensor,
    )

    print(f"\nRHS GFP: {gfp_rhs}")
    print(f"RHS Max Error: {max_error(gfp_rhs, rhs_tensor):.6f}")
    print(f"RHS RMSE: {rmse(gfp_rhs, rhs_tensor):.6f}")

    gemm = gfp.GFPGemmTiled(
        accum_dtype=accum_dtype,
        product_dtype=product_dtype,
        batch_buffer_size=batch_size // 2,
        col_buffer_size=input_channels // 2,
        row_buffer_size=output_channels // 2,
        batch_num_tiles=1,
        col_num_tiles=16,
        row_num_tiles=16,
    )

    # Test GFP GEMM
    gfp_result = gemm(gfp_lhs, gfp_rhs)
    original_result = torch.matmul(lhs_tensor, rhs_tensor)

    print(f"\nGEMM Results: {gfp_result}")
    print(f"Max error: {max_error(gfp_result, original_result):.6f}")
    print(f"RMSE: {rmse(gfp_result, original_result):.6f}")

    # Element-wise add
    accum_tensor = torch.randn(batch_size, output_channels) * 0.5
    gfp_accum = gfp.GFPTensor(
        accum_tensor.shape,
        group_axis=-1,
        group_size=1,
        dtype=accum_dtype,
        original_data=accum_tensor,
    )

    elmwise_add = gfp.GFPElmwiseAdd(accum_dtype)
    gfp_accum = elmwise_add(gfp_accum, gfp_result)
    original_accum = accum_tensor + original_result

    print(f"\nAccum GFP: {gfp_accum}")
    print(f"Accum Max Error: {max_error(gfp_accum, original_accum):.6f}")
    print(f"Accum RMSE: {rmse(gfp_accum, original_accum):.6f}")

    # Normalize the result
    gfp_accum_norm = gfp.GFPTensor(
        gfp_result.original_shape,
        group_axis=-1,
        group_size=group_size,
        dtype=output_dtype,
        gfp_data=gfp_accum,
    )

    print(f"\nNormalized GEMM Result: {gfp_accum_norm}")
    print(f"Max error: {max_error(gfp_accum_norm, original_accum):.6f}")
    print(f"RMSE: {rmse(gfp_accum_norm, original_accum):.6f}")


if __name__ == "__main__":
    test_gemm()
