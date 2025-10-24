import torch
from src.emulator import group_floating_point as gfp

def test_gfp_dot_product():
    """Example: Create two 128-element GFP vectors and compute their dot product"""

    # Configure GFP data type: 8-bit mantissa, 8-bit exponent
    dtype = gfp.GFPDataType(
        mantissa_bits=8,
        exp_bits=8,
        exp_bias=127,  # Standard bias for 8-bit exponent (2^(8-1) - 1)
        mantissa_signed=True
    )

    print(f"GFP Data Type: {dtype}")
    print(f"Value range: [{dtype.bottom_val:.2e}, {dtype.top_val:.2e}]")

    # Create two random 128-element vectors
    torch.manual_seed(42)  # For reproducible results
    vector_a = torch.randn(128) * 0.1  # Scale to reasonable range
    vector_b = torch.randn(128) * 0.1

    print(f"\nOriginal vectors:")
    print(f"Vector A range: [{vector_a.min():.4f}, {vector_a.max():.4f}]")
    print(f"Vector B range: [{vector_b.min():.4f}, {vector_b.max():.4f}]")

    # Convert to GFP tensors
    # For dot product, we'll treat these as [1, 128] matrices
    gfp_a = gfp.GFPTensor(
        original_shape=torch.Size([1, 128]),
        group_axis=1,  # Group along the 128-element dimension
        group_size=32,  # Use groups of 32 elements (4 groups total)
        dtype=dtype,
        original_data=vector_a.unsqueeze(0)  # Make it [1, 128]
    )

    gfp_b = gfp.GFPTensor(
        original_shape=torch.Size([128, 1]),
        group_axis=0,  # Group along the 128-element dimension
        group_size=32,  # Use groups of 32 elements
        dtype=dtype,
        original_data=vector_b.unsqueeze(1)  # Make it [128, 1]
    )

    print(f"\nGFP Tensors created:")
    print(f"GFP A: {gfp_a}")
    print(f"GFP B: {gfp_b}")

    # Check quantization accuracy
    def rmse(gfp_tensor, original):
        return (gfp_tensor.dequantize() - original).pow(2).mean().sqrt()

    rmse_a = rmse(gfp_a, vector_a.unsqueeze(0))
    rmse_b = rmse(gfp_b, vector_b.unsqueeze(1))
    print(f"\nQuantization RMSE:")
    print(f"Vector A RMSE: {rmse_a:.6f}")
    print(f"Vector B RMSE: {rmse_b:.6f}")

    # Define GEMM operation for dot product
    # We need intermediate and accumulator data types
    product_dtype = gfp.GFPDataType(
        mantissa_bits=16,  # Wider for intermediate products
        exp_bits=8,
        mantissa_signed=True
    )

    accum_dtype = gfp.GFPDataType(
        mantissa_bits=20,  # Even wider for accumulation
        exp_bits=9,        # Extra exponent bit for larger range
        mantissa_signed=True
    )

    # Create GEMM operator
    gemm = gfp.GFPGemm(
        accum_dtype=accum_dtype,
        product_dtype=product_dtype
    )

    # Compute dot product: [1, 128] @ [128, 1] = [1, 1]
    gfp_result = gemm(gfp_a, gfp_b)
    print(f"\nGFP Result tensor: {gfp_result}")

    # Extract the scalar result
    gfp_dot_product = gfp_result.dequantize().item()

    # Compute reference dot product
    reference_dot_product = torch.dot(vector_a, vector_b).item()

    # Compare results
    print(f"\nDot Product Results:")
    print(f"Reference (float32): {reference_dot_product:.8f}")
    print(f"GFP result:          {gfp_dot_product:.8f}")
    print(f"Absolute error:      {abs(gfp_dot_product - reference_dot_product):.8f}")
    print(f"Relative error:      {abs(gfp_dot_product - reference_dot_product) / abs(reference_dot_product) * 100:.4f}%")

    # Test with different group sizes
    print(f"\n" + "="*60)
    print("Testing different group sizes:")

    for group_size in [1, 4, 16, 32, 64, 128]:
        if 128 % group_size == 0:  # Only test valid group sizes
            # Recreate tensors with different group size
            gfp_a_test = gfp.GFPTensor(
                original_shape=torch.Size([1, 128]),
                group_axis=1,
                group_size=group_size,
                dtype=dtype,
                original_data=vector_a.unsqueeze(0)
            )

            gfp_b_test = gfp.GFPTensor(
                original_shape=torch.Size([128, 1]),
                group_axis=0,
                group_size=group_size,
                dtype=dtype,
                original_data=vector_b.unsqueeze(1)
            )

            # Compute dot product
            gfp_result_test = gemm(gfp_a_test, gfp_b_test)
            gfp_dot_test = gfp_result_test.dequantize().item()

            # Calculate error
            error = abs(gfp_dot_test - reference_dot_product)
            rel_error = error / abs(reference_dot_product) * 100

            print(f"Group size {group_size:3d}: {gfp_dot_test:.8f} (error: {error:.8f}, {rel_error:.4f}%)")

if __name__ == "__main__":
    test_gfp_dot_product()