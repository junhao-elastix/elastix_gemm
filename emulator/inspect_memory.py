import torch
import numpy as np
from src.emulator import group_floating_point as gfp

def inspect_gfp_memory_layout(vector_a, vector_b, dtype, group_size):
    """Inspect the actual memory layout of GFP tensors"""

    print("="*60)
    print("GFP Memory Layout Inspection")
    print("="*60)

    print(f"Vector A range: [{vector_a.min():.4f}, {vector_a.max():.4f}]")
    print(f"Vector B range: [{vector_b.min():.4f}, {vector_b.max():.4f}]")

    # Convert to GFP
    gfp_tensor_a = gfp.GFPTensor(
        original_shape=vector_a.shape,
        group_axis=0,
        group_size=group_size,
        dtype=dtype,
        original_data=vector_a
    )

    gfp_tensor_b = gfp.GFPTensor(
        original_shape=vector_b.shape,
        group_axis=0,
        group_size=group_size,
        dtype=dtype,
        original_data=vector_b
    )

    print(f"\nGFP Tensor A Configuration:")
    print(f"  Original shape: {gfp_tensor_a.original_shape}")
    print(f"  Grouped shape: {gfp_tensor_a.grouped_shape}")
    print(f"  Group axis: {gfp_tensor_a.group_axis}")
    print(f"  Group size: {gfp_tensor_a.group_size}")
    print(f"  Num groups: {gfp_tensor_a.num_groups}")

    print(f"\n" + "-"*50)
    print("VECTOR A MEMORY LAYOUT:")
    print("-"*50)

    # Mantissa data layout
    print(f"\n1. MANTISSA DATA (shape: {gfp_tensor_a.mantissa_data.shape}):")
    mantissa_a = gfp_tensor_a.mantissa_data
    for group_idx in range(mantissa_a.shape[0]):
        print(f"   Group {group_idx}: {mantissa_a[group_idx].tolist()} (signed integers)")

    # Exponent data layout
    print(f"\n2. EXPONENT DATA (shape: {gfp_tensor_a.exp_data.shape}):")
    exponent_a = gfp_tensor_a.exp_data
    for group_idx in range(exponent_a.shape[0]):
        exp_val = exponent_a[group_idx].item()
        exp_biased = exp_val - dtype.exp_bias
        print(f"   Group {group_idx}: {exp_val} (raw) = 2^{exp_biased} (biased)")

    # Sign data (if applicable)
    if gfp_tensor_a.sign_data is not None:
        print(f"\n3. SIGN DATA (shape: {gfp_tensor_a.sign_data.shape}):")
        sign_a = gfp_tensor_a.sign_data
        for group_idx in range(sign_a.shape[0]):
            print(f"   Group {group_idx}: {sign_a[group_idx].tolist()}")
    else:
        print(f"\n3. SIGN DATA: Integrated into mantissa (signed mantissa mode)")

    # Show reconstruction
    print(f"\n" + "-"*50)
    print("VECTOR A RECONSTRUCTION:")
    print("-"*50)

    reconstructed_a = gfp_tensor_a.dequantize()
    error_a = vector_a - reconstructed_a
    print(f"Original (first 8):      {vector_a[:8].tolist()}")
    print(f"Reconstructed (first 8): {reconstructed_a[:8].tolist()}")
    print(f"Error (first 8):         {error_a[:8].tolist()}")
    print(f"RMSE across all elements: {error_a.pow(2).mean().sqrt():.8f}")
    print(f"Max absolute error:      {error_a.abs().max():.8f}")

    # Show bit-level representation for ALL groups
    print(f"\n" + "-"*50)
    print("VECTOR A BIT-LEVEL MEMORY LAYOUT (ALL GROUPS):")
    print("-"*50)

    for group_idx in range(mantissa_a.shape[0]):
        print(f"\nGroup {group_idx}:")
        exp_bits = format(exponent_a[group_idx].item(), f'0{dtype.exp_bits}b')
        exp_val = exponent_a[group_idx].item()
        exp_biased = exp_val - dtype.exp_bias
        print(f"  Shared Exponent: {exp_bits} (raw={exp_val}, biased=2^{exp_biased})")

        # Show all elements in each group
        for elem_idx in range(mantissa_a.shape[1]):
            mant_val = mantissa_a[group_idx, elem_idx].item()
            # Handle negative values for signed mantissa
            if mant_val < 0:
                # Two's complement representation
                mant_bits = format(mant_val & ((1 << dtype.mantissa_bits) - 1), f'0{dtype.mantissa_bits}b')
            else:
                mant_bits = format(mant_val, f'0{dtype.mantissa_bits}b')

            orig_val = vector_a[group_idx * gfp_tensor_a.group_size + elem_idx]
            recon_val = reconstructed_a[group_idx * gfp_tensor_a.group_size + elem_idx]
            print(f"    Element {elem_idx}: {mant_bits} (dec={mant_val:4d}) -> orig={orig_val:.6f} ≈ recon={recon_val:.6f}")

    return gfp_tensor_a, gfp_tensor_b

def inspect_dot_product_memory(vector_a, vector_b, dtype, group_size):
    """Show memory layout for the dot product example"""

    print("\n" + "="*60)
    print("DOT PRODUCT MEMORY LAYOUT")
    print("="*60)

    print(f"Vector A (first 8): {vector_a[:8].tolist()}")
    print(f"Vector B (first 8): {vector_b[:8].tolist()}")

    # Convert to GFP matrices for GEMM
    gfp_a = gfp.GFPTensor(
        original_shape=torch.Size([1, len(vector_a)]),
        group_axis=1,
        group_size=group_size,
        dtype=dtype,
        original_data=vector_a.unsqueeze(0)
    )

    gfp_b = gfp.GFPTensor(
        original_shape=torch.Size([len(vector_b), 1]),
        group_axis=0,
        group_size=group_size,
        dtype=dtype,
        original_data=vector_b.unsqueeze(1)
    )

    num_groups = len(vector_a) // group_size
    print(f"\nGFP A Memory Layout (LHS: [1, {len(vector_a)}] -> [1, {num_groups}, {group_size}]):")
    print(f"  Mantissa shape: {gfp_a.mantissa_data.shape}")
    print(f"  Exponent shape: {gfp_a.exp_data.shape}")
    print(f"  Group 0 mantissa: {gfp_a.mantissa_data[0, 0, :].tolist()}")
    print(f"  Group 0 exponent: {gfp_a.exp_data[0, 0].item()}")

    print(f"\nGFP B Memory Layout (RHS: [{len(vector_b)}, 1] -> [{num_groups}, {group_size}, 1]):")
    print(f"  Mantissa shape: {gfp_b.mantissa_data.shape}")
    print(f"  Exponent shape: {gfp_b.exp_data.shape}")
    print(f"  Group 0 mantissa: {gfp_b.mantissa_data[0, :, 0].tolist()}")
    print(f"  Group 0 exponent: {gfp_b.exp_data[0, 0].item()}")

    # Show how GEMM processes this
    product_dtype = gfp.GFPDataType(mantissa_bits=16, exp_bits=dtype.exp_bits, mantissa_signed=True)
    accum_dtype = gfp.GFPDataType(mantissa_bits=20, exp_bits=dtype.exp_bits+1, mantissa_signed=True)

    gemm = gfp.GFPGemm(
        accum_dtype=accum_dtype,
        product_dtype=product_dtype
    )
    result = gemm(gfp_a, gfp_b)

    print(f"\nGEMM Result Memory Layout:")
    print(f"  Shape: {result.mantissa_data.shape}")
    print(f"  Mantissa: {result.mantissa_data}")
    print(f"  Exponent: {result.exp_data}")
    print(f"  Final value: {result.dequantize().item():.8f}")
    print(f"  Reference: {torch.dot(vector_a, vector_b).item():.8f}")

    return result

def show_hardware_memory_format(vector_a, vector_b, dtype, group_size):
    """Show how vectors would be laid out in actual FPGA memory"""

    print("\n" + "="*60)
    print(f"FPGA MEMORY FORMAT ({len(vector_a)} elements)")
    print("="*60)

    gfp_tensor = gfp.GFPTensor(
        original_shape=vector_a.shape,
        group_axis=0,
        group_size=group_size,
        dtype=dtype,
        original_data=vector_a
    )

    print("FPGA Memory Layout Overview:")
    print(f"  Total elements: {vector_a.shape[0]}")
    print(f"  Groups: {gfp_tensor.num_groups}")
    print(f"  Elements per group: {gfp_tensor.group_size}")
    print(f"  Memory per group: {dtype.exp_bits + dtype.mantissa_bits * gfp_tensor.group_size} bits")
    print(f"  Total GFP memory: {gfp_tensor.num_groups * (dtype.exp_bits + dtype.mantissa_bits * gfp_tensor.group_size)} bits")
    print(f"  vs IEEE FP32: {32 * vector_a.shape[0]} bits")
    print(f"  Compression ratio: {32 * vector_a.shape[0] / (gfp_tensor.num_groups * (dtype.exp_bits + dtype.mantissa_bits * gfp_tensor.group_size)):.1f}x")

    print(f"\nDetailed Layout (showing first 3 groups):")

    for group_idx in range(min(3, gfp_tensor.num_groups)):
        print(f"\n┌─────────────────────────────── Group {group_idx} ──────────────────────────────┐")

        # Show exponent storage
        exp_val = gfp_tensor.exp_data[group_idx].item()
        exp_bits = format(exp_val, f'0{dtype.exp_bits}b')
        exp_biased = exp_val - dtype.exp_bias
        print(f"│ Shared Exponent: {exp_bits} (raw={exp_val}, 2^{exp_biased})")
        print("├───────────────────────────────────────────────────────────────────────")

        # Show mantissa storage
        print(f"│ Mantissas ({gfp_tensor.group_size} x {dtype.mantissa_bits} bits):")
        for i in range(gfp_tensor.group_size):
            mant_val = gfp_tensor.mantissa_data[group_idx, i].item()
            if mant_val < 0:
                mant_bits = format(mant_val & ((1 << dtype.mantissa_bits) - 1), f'0{dtype.mantissa_bits}b')
            else:
                mant_bits = format(mant_val, f'0{dtype.mantissa_bits}b')

            orig_val = vector_a[group_idx * gfp_tensor.group_size + i]
            recon_val = gfp_tensor.dequantize()[group_idx * gfp_tensor.group_size + i]
            print(f"│   Elem {i}: {mant_bits} (dec={mant_val:3d}) -> {orig_val:.3f} ≈ {recon_val:.3f}")
        print("└───────────────────────────────────────────────────────────────────────┘")

    if gfp_tensor.num_groups > 3:
        print(f"\n... ({gfp_tensor.num_groups - 3} more groups with same structure)")

def main(vector_length=128, mantissa_bits=8, exp_bits=8, group_size=8):
    """Main function to demonstrate GFP memory layout with configurable parameters"""

    print(f"Parameters: vector_length={vector_length}, mantissa_bits={mantissa_bits}, exp_bits={exp_bits}, group_size={group_size}")
    print(f"Exp bias: {2**(exp_bits-1) - 1}")

    # Create GFP data type
    dtype = gfp.GFPDataType(
        mantissa_bits=mantissa_bits,
        exp_bits=exp_bits,
        exp_bias=2**(exp_bits-1) - 1,  # Standard bias
        mantissa_signed=True
    )

    print(f"GFP Data Type: {dtype}")

    # Create two random vectors with values < 4 (seed=42 for reproducibility)
    torch.manual_seed(42)
    vector_a = torch.rand(vector_length) * 3.0  # Random values between 0 and 3
    vector_b = torch.rand(vector_length) * 3.0  # Random values between 0 and 3

    # 1. Inspect memory layout
    gfp_a, gfp_b = inspect_gfp_memory_layout(vector_a, vector_b, dtype, group_size)

    # 2. Compute and inspect dot product
    dot_result = inspect_dot_product_memory(vector_a, vector_b, dtype, group_size)

    # 3. Show hardware memory format
    show_hardware_memory_format(vector_a, vector_b, dtype, group_size)

if __name__ == "__main__":
    # Run with default parameters: 128 elements, 8-bit mantissa, 8-bit exponent, group size 8
    main()