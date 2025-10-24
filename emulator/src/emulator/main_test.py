import torch

from emulator import group_floating_point as gfp


def rmse(x: gfp.GFPTensor, y: torch.Tensor):
    return (x.dequantize() - y).pow(2).mean().sqrt()


def test_quantize_dequantize():
    """Test GFP tensor quantize and dequantize operations"""
    dtype = gfp.GFPDataType(
        mantissa_bits=8,
        exp_bits=5,
    )

    # Test 1: Random vector
    torch.manual_seed(42)
    random_data = torch.randn(2, 256)
    gfp_random = gfp.GFPTensor(
        random_data.shape,
        group_axis=-1,
        group_size=32,
        dtype=dtype,
        original_data=random_data,
    )
    gfp_random_rmse = rmse(gfp_random, random_data)
    assert gfp_random_rmse < 0.01, f"Random data RMSE too large: {gfp_random_rmse}"

    # Test 2: Extreme values - zeros
    zero_data = torch.zeros(2, 256)
    gfp_zero = gfp.GFPTensor(
        zero_data.shape,
        group_axis=-1,
        group_size=32,
        dtype=dtype,
        original_data=zero_data,
    )
    gfp_zero_rmse = rmse(gfp_zero, zero_data)
    assert gfp_zero_rmse == 0, f"Zero data RMSE too large: {gfp_zero_rmse}"

    # Test 3: Extreme values - large numbers
    max_val = dtype.top_val * 0.9
    large_data = torch.full((2, 256), max_val)
    gfp_large = gfp.GFPTensor(
        large_data.shape,
        group_axis=-1,
        group_size=32,
        dtype=dtype,
        original_data=large_data,
    )
    gfp_large_rmse = rmse(gfp_large, large_data)
    relative_rmse = gfp_large_rmse / max_val
    assert relative_rmse < 0.01, f"Large data relative RMSE too large: {relative_rmse}"

    # Test 4: Extreme values - small positive numbers
    min_val = dtype.bottom_val * 2
    small_data = torch.full((2, 256), min_val)
    gfp_small = gfp.GFPTensor(
        small_data.shape,
        group_axis=-1,
        group_size=32,
        dtype=dtype,
        original_data=small_data,
    )
    gfp_small_rmse = rmse(gfp_small, small_data)
    relative_rmse = gfp_small_rmse / min_val
    assert relative_rmse < 0.01, f"Small data relative RMSE too large: {relative_rmse}"


def test_gfp_gemm():
    """Test GFP GEMM operations with and without accumulation"""
    batch_size = 2
    input_channels = 256
    output_channels = 256

    lhs_dtype = gfp.GFPDataType(
        mantissa_bits=8,
        exp_bits=5,
    )
    rhs_dtype = gfp.GFPDataType(
        mantissa_bits=8,
        exp_bits=5,
    )
    product_dtype = gfp.GFPDataType(
        mantissa_bits=19,
        exp_bits=5,
    )
    accum_dtype = gfp.GFPDataType(
        mantissa_bits=20,
        exp_bits=6,
    )

    torch.manual_seed(123)
    weight_std = (1.0 / (input_channels + output_channels)) ** 0.5
    lhs_data = torch.randn(batch_size, input_channels)
    rhs_data = torch.randn(input_channels, output_channels) * weight_std
    gfp_lhs = gfp.GFPTensor(
        lhs_data.shape,
        group_axis=1,
        group_size=32,
        dtype=lhs_dtype,
        original_data=lhs_data,
    )
    gfp_rhs = gfp.GFPTensor(
        rhs_data.shape,
        group_axis=0,
        group_size=32,
        dtype=rhs_dtype,
        original_data=rhs_data,
    )

    gemm = gfp.GFPGemm(
        accum_dtype=accum_dtype,
        product_dtype=product_dtype,
    )
    gfp_result = gemm(gfp_lhs, gfp_rhs)
    original_result = torch.matmul(lhs_data, rhs_data)
    gfp_result_rmse = rmse(gfp_result, original_result)
    assert gfp_result_rmse < 0.01, f"GEMM RMSE too large: {gfp_result_rmse}"


def test_gfp_normalization():
    dtype = gfp.GFPDataType(
        mantissa_bits=20,
        exp_bits=6,
    )

    accum_data = torch.randn(2, 256) * 0.5
    gfp_accum = gfp.GFPTensor(
        accum_data.shape,
        group_axis=-1,
        group_size=1,
        dtype=dtype,
        original_data=accum_data,
    )

    gfp_accum_normalized = gfp.GFPTensor(
        accum_data.shape, group_axis=-1, group_size=32, dtype=dtype, gfp_data=gfp_accum
    )
    gfp_accum_normalized_rmse = rmse(gfp_accum_normalized, accum_data)
    assert (
        gfp_accum_normalized_rmse < 0.01
    ), f"Normalized accum RMSE too large: {gfp_accum_normalized_rmse}"


def test_gfp_elmwise_add():
    dtype = gfp.GFPDataType(
        mantissa_bits=8,
        exp_bits=5,
    )
    output_dtype = gfp.GFPDataType(
        mantissa_bits=9,
        exp_bits=5,
    )

    # Test 1: Group size = 32
    lhs_data = torch.randn(2, 256) * 0.5
    rhs_data = torch.randn(2, 256) * 0.5
    gfp_lhs = gfp.GFPTensor(
        lhs_data.shape,
        group_axis=-1,
        group_size=32,
        dtype=dtype,
        original_data=lhs_data,
    )
    gfp_rhs = gfp.GFPTensor(
        rhs_data.shape,
        group_axis=-1,
        group_size=32,
        dtype=dtype,
        original_data=rhs_data,
    )
    elmwise_add = gfp.GFPElmwiseAdd(output_dtype)
    gfp_result = elmwise_add(gfp_lhs, gfp_rhs)
    original_result = lhs_data + rhs_data
    gfp_result_rmse = rmse(gfp_result, original_result)
    assert gfp_result_rmse < 0.01, f"Element-wise add RMSE too large: {gfp_result_rmse}"

    # Test 2: Group size = 1
    gfp_lhs = gfp.GFPTensor(
        lhs_data.shape,
        group_axis=-1,
        group_size=1,
        dtype=dtype,
        original_data=lhs_data,
    )
    gfp_rhs = gfp.GFPTensor(
        rhs_data.shape,
        group_axis=-1,
        group_size=1,
        dtype=dtype,
        original_data=rhs_data,
    )
    elmwise_add = gfp.GFPElmwiseAdd(output_dtype)
    gfp_result = elmwise_add(gfp_lhs, gfp_rhs)
    original_result = lhs_data + rhs_data
    gfp_result_rmse = rmse(gfp_result, original_result)
    assert gfp_result_rmse < 0.01, f"Element-wise add RMSE too large: {gfp_result_rmse}"
