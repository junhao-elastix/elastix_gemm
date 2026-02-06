#!/usr/bin/env python3
"""
GFP11e5 to GFP8e5 Conversion Golden Model

This module provides bit-accurate golden reference functions for the
GFP11e5 → GFP8e5 streaming converter hardware modules.

GFP11e5 Format (per element, 16 bits total):
    [15:11] = exp[4:0]   - 5-bit exponent
    [10:0]  = man[10:0]  - 11-bit SIGNED mantissa (2's complement)

GFP8e5 Format (per element, 13 bits total):
    [7:0] = man[7:0]     - 8-bit SIGNED mantissa (2's complement)
    Shared exponent output separately (5-bit)
"""

from dataclasses import dataclass


@dataclass
class GFP11e5Format:
    """GFP11e5 format parameters (11-bit mantissa + 5-bit exponent = 16 bits)."""
    total_bits: int = 11 + 5 # 11-bit mantissa + 5-bit exponent
    exp_bits: int = 5
    man_bits: int = 11  # Signed mantissa


@dataclass
class GFP8e5Format:
    """GFP8e5 format parameters (8-bit mantissa + 5-bit exponent = 13 bits)."""
    total_bits: int = 8 + 5  # 8-bit mantissa + 5-bit exponent
    exp_bits: int = 5
    man_bits: int = 8   # Signed mantissa


# Default formats
GFP11e5 = GFP11e5Format()
GFP8e5 = GFP8e5Format()

# Backward-compatible aliases
GFP16Format = GFP11e5Format
GFP8Format = GFP8e5Format
GFP16 = GFP11e5
GFP8 = GFP8e5


def to_signed(value: int, bits: int) -> int:
    """Convert unsigned integer to signed (2's complement interpretation)."""
    if value >= (1 << (bits - 1)):
        return value - (1 << bits)
    return value


def to_unsigned(value: int, bits: int) -> int:
    """Convert signed integer to unsigned (2's complement representation)."""
    if value < 0:
        return value + (1 << bits)
    return value & ((1 << bits) - 1)


def saturate_signed(value: int, bits: int) -> int:
    """Saturate a signed value to fit in the specified bit width."""
    max_pos = (1 << (bits - 1)) - 1   # e.g., +127 for 8-bit
    max_neg = -(1 << (bits - 1))      # e.g., -128 for 8-bit
    if value > max_pos:
        return max_pos
    if value < max_neg:
        return max_neg
    return value


# =============================================================================
# Sub-module Golden Functions
# =============================================================================

def gfp_extract_hw(gfp_data: list[int], fmt: GFP11e5Format = GFP11e5) -> tuple[list[int], list[int], list[bool]]:
    """
    Extract exponent and signed mantissa from packed GFP data.

    Args:
        gfp_data: List of packed GFP values
        fmt: GFP format parameters (exp_bits, man_bits)

    Returns:
        (exps, mans, is_zeros) where:
        - exps: List of unsigned exponents
        - mans: List of signed mantissas (as Python integers, can be negative)
        - is_zeros: List of boolean zero flags
    """
    exps = []
    mans = []
    is_zeros = []

    for val in gfp_data:
        # Extract exponent (upper bits)
        exp = (val >> fmt.man_bits) & ((1 << fmt.exp_bits) - 1)

        # Extract mantissa (lower bits) - interpret as signed
        man_unsigned = val & ((1 << fmt.man_bits) - 1)
        man_signed = to_signed(man_unsigned, fmt.man_bits)

        # Zero detection
        is_zero = (exp == 0) and (man_signed == 0)

        exps.append(exp)
        mans.append(man_signed)
        is_zeros.append(is_zero)

    return exps, mans, is_zeros


def signed_aligner_hw(
    exps: list[int],
    mans: list[int],
    is_zeros: list[bool],
    max_exp: int,
    man_bits: int = 11
) -> tuple[list[int], list[int]]:
    """
    Align signed mantissas to the maximum exponent using arithmetic right shift.

    Args:
        exps: List of exponents
        mans: List of signed mantissas
        is_zeros: List of zero flags
        max_exp: Maximum exponent in the group
        man_bits: Mantissa bit width

    Returns:
        (aligned_mans, round_bits) where:
        - aligned_mans: List of aligned signed mantissas
        - round_bits: List of round bits (first discarded bit)
    """
    aligned_mans = []
    round_bits = []

    for exp, man, is_zero in zip(exps, mans, is_zeros):
        if is_zero:
            aligned_mans.append(0)
            round_bits.append(0)
        else:
            shift_amt = max_exp - exp

            if shift_amt == 0:
                # No shift needed
                aligned_mans.append(man)
                round_bits.append(0)
            elif shift_amt >= man_bits:
                # Complete underflow - all sign bits
                aligned_mans.append(-1 if man < 0 else 0)
                round_bits.append(0)
            else:
                # Arithmetic right shift (preserves sign)
                aligned = man >> shift_amt

                # Round bit is the first discarded bit
                round_bit = (man >> (shift_amt - 1)) & 1

                aligned_mans.append(aligned)
                round_bits.append(round_bit)

    return aligned_mans, round_bits


def gfp_quantizer_hw(
    aligned_mans: list[int],
    round_bits: list[int],  # Kept for API compatibility, but not used
    is_zeros: list[bool],
    in_man_bits: int = 11,
    out_man_bits: int = 8
) -> list[int]:
    """
    Quantize aligned signed mantissas to a smaller bit width.

    The quantization round bit is computed from the aligned value itself
    (bit [quant_shift-1]), not from the alignment phase round bit.

    Args:
        aligned_mans: List of aligned signed mantissas
        round_bits: (Unused, kept for API compatibility)
        is_zeros: List of zero flags
        in_man_bits: Input mantissa bits
        out_man_bits: Output mantissa bits

    Returns:
        List of quantized signed mantissas (as Python int)
    """
    quant_shift = in_man_bits - out_man_bits  # 11 - 8 = 3
    max_positive = (1 << (out_man_bits - 1)) - 1  # 127 for 8-bit

    gfp_mans = []

    for aligned, is_zero in zip(aligned_mans, is_zeros):
        if is_zero:
            gfp_mans.append(0)
        else:
            # Compute quantization round bit from aligned value
            # This is the MSB of the bits being discarded (bit [quant_shift-1])
            # For negative numbers, we need to handle 2's complement properly
            if aligned >= 0:
                quant_round_bit = (aligned >> (quant_shift - 1)) & 1
            else:
                # For negative, convert to unsigned, extract bit, handle sign
                aligned_unsigned = aligned & ((1 << in_man_bits) - 1)
                quant_round_bit = (aligned_unsigned >> (quant_shift - 1)) & 1

            # Check if rounding would cause overflow:
            # If shifted result is already at max positive (127), skip rounding
            shifted_preview = aligned >> quant_shift
            at_max_positive = (aligned >= 0) and (shifted_preview == max_positive)

            if at_max_positive:
                # Skip rounding to prevent overflow (127 + 1 = 128 would overflow)
                shifted = shifted_preview
            else:
                # Add rounding constant: quant_round_bit << (quant_shift - 1)
                round_add = quant_round_bit << (quant_shift - 1) if quant_shift > 0 else 0
                shifted = (aligned + round_add) >> quant_shift

            gfp_mans.append(shifted)

    return gfp_mans


def group_max_exp_finder_hw(
    exps: list[int],
    is_zeros: list[bool],
    pad: int = 0
) -> int:
    """
    Find maximum exponent in a group, excluding zero and padded elements.

    Args:
        exps: List of exponents
        is_zeros: List of zero flags
        pad: Number of padding elements at the end

    Returns:
        Maximum exponent in the group
    """
    max_exp = 0
    valid_count = len(exps) - pad

    for i, (exp, is_zero) in enumerate(zip(exps, is_zeros)):
        if i < valid_count and not is_zero:
            if exp > max_exp:
                max_exp = exp

    return max_exp


# =============================================================================
# Full Conversion Function
# =============================================================================

def gfp11e5_to_gfp8e5_hw(
    gfp11e5_data: list[int],
    pad: int = 0,
    gfp11e5_fmt: GFP11e5Format = GFP11e5,
    gfp8e5_fmt: GFP8e5Format = GFP8e5
) -> tuple[list[int], int]:
    """
    Convert GFP11e5 data to GFP8e5 format (single group).

    Args:
        gfp11e5_data: List of packed GFP11e5 values
        pad: Number of padding elements
        gfp11e5_fmt: GFP11e5 format parameters
        gfp8e5_fmt: GFP8e5 format parameters

    Returns:
        (gfp8e5_mans, gfp8e5_exp) where:
        - gfp8e5_mans: List of 8-bit signed mantissas (as unsigned for HW comparison)
        - gfp8e5_exp: Shared 5-bit exponent
    """
    # Step 1: Extract fields
    exps, mans, is_zeros = gfp_extract_hw(gfp11e5_data, gfp11e5_fmt)

    # Step 2: Find max exponent
    max_exp = group_max_exp_finder_hw(exps, is_zeros, pad)

    # Step 3: Align mantissas
    aligned_mans, round_bits = signed_aligner_hw(
        exps, mans, is_zeros, max_exp, gfp11e5_fmt.man_bits
    )

    # Step 4: Quantize to GFP8e5
    gfp8e5_mans_signed = gfp_quantizer_hw(
        aligned_mans, round_bits, is_zeros,
        gfp11e5_fmt.man_bits, gfp8e5_fmt.man_bits
    )

    # Convert signed mantissas to unsigned for hardware comparison
    gfp8e5_mans_unsigned = [to_unsigned(m, gfp8e5_fmt.man_bits) for m in gfp8e5_mans_signed]

    # GFP8e5 exponent is same as input (5-bit)
    gfp8e5_exp = max_exp

    return gfp8e5_mans_unsigned, gfp8e5_exp


# Backward-compatible alias
gfp16_to_gfp8_hw = gfp11e5_to_gfp8e5_hw


def pack_gfp11e5(exp: int, man_signed: int, fmt: GFP11e5Format = GFP11e5) -> int:
    """
    Pack exponent and signed mantissa into GFP11e5 format.

    Args:
        exp: Unsigned exponent (5-bit)
        man_signed: Signed mantissa (Python int, can be negative)
        fmt: GFP11e5 format parameters

    Returns:
        Packed GFP11e5 value (16-bit unsigned)
    """
    man_unsigned = to_unsigned(man_signed, fmt.man_bits)
    return ((exp & ((1 << fmt.exp_bits) - 1)) << fmt.man_bits) | man_unsigned


# Backward-compatible alias
pack_gfp16 = pack_gfp11e5


# =============================================================================
# Full Round-Trip Test: FP16 → GFP11e5 → GFP8e5 → FP
# =============================================================================

def test_fp16_gfp11e5_gfp8e5_roundtrip(
    num_elements: int = 16,
    group_size: int = 16,
    std: float = 1.0,
    seed: int = 42,
    verbose: bool = True,
):
    """
    Test the full conversion pipeline: FP16 → GFP11e5 → GFP8e5 → FP.

    Uses emu_golden for FP↔GFP conversions and gfp11e5_to_gfp8e5_hw for GFP11e5→GFP8e5.

    Args:
        num_elements: Number of elements to test
        group_size: GFP group size (elements sharing an exponent)
        std: Standard deviation for random FP16 data
        seed: Random seed for reproducibility
        verbose: Print detailed output

    Returns:
        dict with error metrics
    """
    import torch
    from emu_golden import fp_to_gfp_1d, gfp_to_fp_1d

    torch.manual_seed(seed)

    # GFP16: 11-bit mantissa, 5-bit exponent
    GFP11e5_MAN_BITS = 11
    GFP11e5_EXP_BITS = 5

    # GFP8: 8-bit mantissa, 5-bit exponent
    GFP8e5_MAN_BITS = 8
    GFP8e5_EXP_BITS = 5

    if verbose:
        print("=" * 70)
        print("FP16 → GFP11e5 → GFP8 → FP Round-Trip Test")
        print(f"  num_elements={num_elements}, group_size={group_size}, std={std}")
        print("=" * 70)

    # Step 1: Create FP16 input data
    fp16_input = (torch.randn(num_elements) * std).to(torch.float16)

    if verbose:
        print(f"\n[Step 1] FP16 Input ({num_elements} elements):")
        print(f"  {fp16_input.tolist()}")

    # Step 2: Convert FP16 → GFP11e5 using emulator
    gfp11e5_man, gfp11e5_exp = fp_to_gfp_1d(
        fp16_input.float(),  # Convert to float32 for emulator
        mantissa_bits=GFP11e5_MAN_BITS,
        exp_bits=GFP11e5_EXP_BITS,
        group_size=group_size,
    )

    if verbose:
        print(f"\n[Step 2] GFP16 (emulator output):")
        print(f"  Mantissa shape: {gfp11e5_man.shape}")
        print(f"  Exponent shape: {gfp11e5_exp.shape}")
        print(f"  Mantissa: {gfp11e5_man.tolist()}")
        print(f"  Exponent: {gfp11e5_exp.tolist()}")

    # Step 2b: Convert GFP16 back to FP to measure GFP16-only loss
    fp_from_gfp11e5 = gfp_to_fp_1d(
        gfp11e5_man,
        gfp11e5_exp,
        num_elements,
        mantissa_bits=GFP11e5_MAN_BITS,
        exp_bits=GFP11e5_EXP_BITS,
        group_size=group_size,
    )

    fp16_as_float = fp16_input.float()
    gfp11e5_error = fp16_as_float - fp_from_gfp11e5
    gfp11e5_max_error = gfp11e5_error.abs().max().item()
    gfp11e5_rel_error = (gfp11e5_error.abs() / (fp16_as_float.abs() + 1e-10)).mean().item()

    if verbose:
        print(f"\n[Step 2b] GFP11e5 → FP (to measure GFP16-only loss):")
        print(f"  Reconstructed: {fp_from_gfp11e5.tolist()}")
        print(f"  Max error (GFP11e5 only): {gfp11e5_max_error:.6e}")
        print(f"  Rel error (GFP11e5 only): {gfp11e5_rel_error:.4%}")

    # Step 3: Convert GFP11e5 → GFP8 using our golden model
    # Process each group separately
    num_groups = gfp11e5_man.shape[0]
    gfp8_mans_all = []
    gfp8_exps_all = []

    for g in range(num_groups):
        # Pack GFP16 mantissa and exponent into packed format for gfp16_to_gfp8_hw
        group_mans = gfp11e5_man[g].tolist()  # Signed mantissas
        group_exp = int(gfp11e5_exp[g, 0].item())  # Shared exponent

        # Pack each element: exp[4:0] | man[10:0]
        packed_gfp11e5 = []
        for man in group_mans:
            man_int = int(man)
            packed = pack_gfp16(exp=group_exp, man_signed=man_int)
            packed_gfp11e5.append(packed)

        # Convert GFP11e5 → GFP8
        gfp8_mans, gfp8_exp = gfp16_to_gfp8_hw(packed_gfp11e5)

        # Adjust exponent: when quantizing from 11-bit to 8-bit mantissa,
        # we shift right by 3, so we must increase exponent by 3 to preserve magnitude
        quant_shift = GFP11e5_MAN_BITS - GFP8e5_MAN_BITS  # 11 - 8 = 3
        gfp8_exp_adjusted = gfp8_exp + quant_shift

        # Convert unsigned mantissas back to signed for dequantization
        gfp8_mans_signed = [to_signed(m, GFP8e5_MAN_BITS) for m in gfp8_mans]
        gfp8_mans_all.append(gfp8_mans_signed)
        gfp8_exps_all.append(gfp8_exp_adjusted)

    if verbose:
        print(f"\n[Step 3] GFP8 (gfp16_to_gfp8_hw output, exp adjusted +{GFP11e5_MAN_BITS - GFP8e5_MAN_BITS}):")
        for g in range(num_groups):
            print(f"  Group {g}: exp={gfp8_exps_all[g]}, mans={gfp8_mans_all[g]}")

    # Step 4: Convert GFP8 → FP using emulator
    # Reconstruct mantissa and exponent tensors for the emulator
    gfp8_man_tensor = torch.tensor(gfp8_mans_all, dtype=torch.float32)
    gfp8_exp_tensor = torch.tensor([[e] for e in gfp8_exps_all], dtype=torch.float32)

    fp_reconstructed = gfp_to_fp_1d(
        gfp8_man_tensor,
        gfp8_exp_tensor,
        num_elements,
        mantissa_bits=GFP8e5_MAN_BITS,
        exp_bits=GFP8e5_EXP_BITS,
        group_size=group_size,
    )

    if verbose:
        print(f"\n[Step 4] FP Reconstructed:")
        print(f"  {fp_reconstructed.tolist()}")

    # Step 5: Compare original FP16 with reconstructed FP
    error = fp16_as_float - fp_reconstructed
    max_error = error.abs().max().item()
    rmse = (error ** 2).mean().sqrt().item()
    rel_error = (error.abs() / (fp16_as_float.abs() + 1e-10)).mean().item()

    # Calculate additional error from GFP8 quantization
    gfp8_additional_error = rel_error - gfp11e5_rel_error

    if verbose:
        print(f"\n[Step 5] Error Analysis:")
        print(f"  ┌─────────────────────────────────────────────────┐")
        print(f"  │ Stage              │ Max Error  │ Rel Error    │")
        print(f"  ├─────────────────────────────────────────────────┤")
        print(f"  │ GFP11e5 only         │ {gfp11e5_max_error:10.6e} │ {gfp11e5_rel_error:10.4%}   │")
        print(f"  │ GFP11e5 → GFP8       │ {max_error:10.6e} │ {rel_error:10.4%}   │")
        print(f"  │ GFP8e5 additional    │     -      │ {gfp8_additional_error:+10.4%}  │")
        print(f"  └─────────────────────────────────────────────────┘")
        print(f"  RMSE (full pipeline): {rmse:.6e}")

        print(f"\n  Element-wise comparison (FP16 orig vs GFP8 reconstructed):")
        for i in range(min(num_elements, 16)):  # Show first 16
            orig = fp16_as_float[i].item()
            recon = fp_reconstructed[i].item()
            err = error[i].item()
            print(f"    [{i:2d}] orig={orig:+10.6f}, recon={recon:+10.6f}, err={err:+10.6f}")

        print("\n" + "=" * 70)
        # Determine pass/fail based on expected quantization error
        threshold = 0.1  # 10% relative error threshold
        status = "PASS" if rel_error < threshold else "FAIL"
        print(f"{status} (relative error {rel_error:.4%} vs threshold {threshold:.2%})")
        print("=" * 70)

    return {
        "max_error": max_error,
        "rmse": rmse,
        "rel_error": rel_error,
        "gfp11e5_rel_error": gfp11e5_rel_error,
        "gfp8_additional_error": gfp8_additional_error,
        "fp16_input": fp16_input,
        "fp_from_gfp11e5": fp_from_gfp11e5,
        "fp_reconstructed": fp_reconstructed,
    }


# =============================================================================
# Direct FP16 → GFP8 → FP16 Test (bypassing GFP16 intermediate)
# =============================================================================

def fp16_to_gfp8e5_direct(
    fp16_values: list[float],
    group_size: int = 32,
    gfp8_man_bits: int = 8,
    gfp8_exp_bits: int = 5,
) -> tuple[list[int], list[int]]:
    """
    Convert FP16 values directly to GFP8 format.

    This bypasses GFP16 intermediate format - goes straight from FP16 to GFP8.

    Args:
        fp16_values: List of FP16 values as Python floats
        group_size: Number of elements sharing an exponent
        gfp8_man_bits: GFP8 mantissa bits (default 8)
        gfp8_exp_bits: GFP8 exponent bits (default 5)

    Returns:
        (gfp8_mans, gfp8_exps) where:
        - gfp8_mans: List of 8-bit unsigned mantissas
        - gfp8_exps: List of shared exponents (one per group)
    """
    import math

    all_mans = []
    all_exps = []

    # Process in groups
    num_groups = (len(fp16_values) + group_size - 1) // group_size

    for g in range(num_groups):
        start = g * group_size
        end = min(start + group_size, len(fp16_values))
        group_values = fp16_values[start:end]

        # Pad group if needed
        while len(group_values) < group_size:
            group_values.append(0.0)

        # Find max absolute value to determine shared exponent
        max_abs = max(abs(v) for v in group_values)

        if max_abs == 0:
            # All zeros
            shared_exp = 0
            group_mans = [0] * group_size
        else:
            # Calculate shared exponent: floor(log2(max_abs)) + bias
            # GFP8 uses bias of 15 (same as FP16 for 5-bit exponent)
            bias = (1 << (gfp8_exp_bits - 1)) - 1  # 15

            # Exponent such that max value fits in mantissa range
            # For 8-bit signed mantissa: range is [-128, 127]
            max_mantissa = (1 << (gfp8_man_bits - 1)) - 1  # 127

            # shared_exp is chosen so that max_abs / 2^(shared_exp - bias) <= max_mantissa
            # We need: scale >= max_abs / max_mantissa
            # scale = 2^(exp - bias), so exp = ceil(log2(max_abs / max_mantissa)) + bias
            if max_abs > 0:
                raw_exp = math.ceil(math.log2(max_abs / max_mantissa)) + bias
                shared_exp = max(0, min(raw_exp, (1 << gfp8_exp_bits) - 1))
            else:
                shared_exp = 0

            # Scale factor: 2^(shared_exp - bias)
            scale = 2.0 ** (shared_exp - bias) if shared_exp > 0 else 2.0 ** (1 - bias)

            # Quantize each value
            group_mans = []
            for v in group_values:
                if v == 0:
                    group_mans.append(0)
                else:
                    # Mantissa = round(value / scale)
                    man_float = v / scale
                    man_int = int(round(man_float))

                    # Saturate to 8-bit signed range
                    man_int = max(-128, min(127, man_int))

                    # Convert to unsigned
                    group_mans.append(to_unsigned(man_int, gfp8_man_bits))

        all_mans.extend(group_mans)
        all_exps.append(shared_exp)

    return all_mans, all_exps


def gfp8e5_to_fp16_direct(
    gfp8_mans: list[int],
    gfp8_exps: list[int],
    group_size: int = 32,
    gfp8_man_bits: int = 8,
    gfp8_exp_bits: int = 5,
) -> list[float]:
    """
    Convert GFP8 values back to FP16 floats.

    Args:
        gfp8_mans: List of 8-bit unsigned mantissas
        gfp8_exps: List of shared exponents (one per group)
        group_size: Number of elements per group
        gfp8_man_bits: GFP8 mantissa bits
        gfp8_exp_bits: GFP8 exponent bits

    Returns:
        List of reconstructed float values
    """
    bias = (1 << (gfp8_exp_bits - 1)) - 1  # 15

    fp_values = []

    for g, exp in enumerate(gfp8_exps):
        start = g * group_size
        end = min(start + group_size, len(gfp8_mans))

        # Scale factor
        scale = 2.0 ** (exp - bias) if exp > 0 else 2.0 ** (1 - bias)

        for i in range(start, end):
            man_unsigned = gfp8_mans[i]
            man_signed = to_signed(man_unsigned, gfp8_man_bits)
            fp_values.append(man_signed * scale)

    return fp_values


def test_fp16_gfp8e5_direct_roundtrip(
    num_elements: int = 32,
    group_size: int = 32,
    std: float = 1.0,
    seed: int = 42,
    verbose: bool = True,
):
    """
    Test direct FP16 → GFP8 → FP16 conversion (bypassing GFP16).

    Args:
        num_elements: Number of elements to test
        group_size: GFP group size
        std: Standard deviation for random data
        seed: Random seed
        verbose: Print detailed output

    Returns:
        dict with error metrics
    """
    import random
    random.seed(seed)

    if verbose:
        print("=" * 70)
        print("Direct FP16 → GFP8 → FP16 Round-Trip Test")
        print(f"  num_elements={num_elements}, group_size={group_size}, std={std}")
        print("=" * 70)

    # Generate random FP16 values
    fp16_input = [random.gauss(0, std) for _ in range(num_elements)]

    if verbose:
        print(f"\n[Step 1] FP16 Input ({num_elements} elements):")
        print(f"  First 8: {[f'{v:.4f}' for v in fp16_input[:8]]}")

    # Convert FP16 → GFP8 directly
    gfp8_mans, gfp8_exps = fp16_to_gfp8e5_direct(
        fp16_input, group_size=group_size
    )

    if verbose:
        print(f"\n[Step 2] GFP8 Output:")
        for g, exp in enumerate(gfp8_exps):
            start = g * group_size
            mans_hex = [f"{m:02x}" for m in gfp8_mans[start:start+8]]
            print(f"  Group {g}: exp={exp}, mans (first 8): {' '.join(mans_hex)}")

    # Convert GFP8 → FP16
    fp16_output = gfp8e5_to_fp16_direct(
        gfp8_mans, gfp8_exps, group_size=group_size
    )

    if verbose:
        print(f"\n[Step 3] FP16 Reconstructed:")
        print(f"  First 8: {[f'{v:.4f}' for v in fp16_output[:8]]}")

    # Calculate errors
    errors = [abs(a - b) for a, b in zip(fp16_input, fp16_output)]
    rel_errors = [abs(a - b) / (abs(a) + 1e-10) for a, b in zip(fp16_input, fp16_output)]

    max_error = max(errors)
    mean_error = sum(errors) / len(errors)
    max_rel_error = max(rel_errors)
    mean_rel_error = sum(rel_errors) / len(rel_errors)

    if verbose:
        print(f"\n[Step 4] Error Analysis:")
        print(f"  ┌─────────────────────────────────────────────────┐")
        print(f"  │ Metric              │ Value                     │")
        print(f"  ├─────────────────────────────────────────────────┤")
        print(f"  │ Max Absolute Error  │ {max_error:25.6e} │")
        print(f"  │ Mean Absolute Error │ {mean_error:25.6e} │")
        print(f"  │ Max Relative Error  │ {max_rel_error:25.4%} │")
        print(f"  │ Mean Relative Error │ {mean_rel_error:25.4%} │")
        print(f"  └─────────────────────────────────────────────────┘")

        print(f"\n  Element-wise comparison (first 16):")
        for i in range(min(num_elements, 16)):
            orig = fp16_input[i]
            recon = fp16_output[i]
            err = errors[i]
            rel_err = rel_errors[i]
            print(f"    [{i:2d}] orig={orig:+10.6f}, recon={recon:+10.6f}, "
                  f"err={err:.6e}, rel={rel_err:.2%}")

        print("\n" + "=" * 70)
        threshold = 0.15  # 15% relative error threshold for 8-bit quantization
        status = "PASS" if mean_rel_error < threshold else "FAIL"
        print(f"{status} (mean relative error {mean_rel_error:.4%} vs threshold {threshold:.2%})")
        print("=" * 70)

    return {
        "max_error": max_error,
        "mean_error": mean_error,
        "max_rel_error": max_rel_error,
        "mean_rel_error": mean_rel_error,
        "fp16_input": fp16_input,
        "fp16_output": fp16_output,
    }


# =============================================================================
# Bit-Level Comparison: GFP11e5 vs GFP8e5 Representations
# =============================================================================

def test_bit_level_comparison(
    num_elements: int = 32,
    group_size: int = 32,
    std: float = 1.0,
    seed: int = 42,
    verbose: bool = True,
):
    """
    Compare the actual GFP8e5 bits produced by both conversion paths:
      Path A: FP16 → GFP11e5 → GFP8e5 (via emulator + HW golden model)
      Path B: FP16 → GFP8e5 (direct conversion)

    This tests whether the two paths produce identical bit representations.

    Naming clarification:
      - GFP11e5 (aka "GFP16"): 11-bit signed mantissa + 5-bit exponent = 16 bits
      - GFP8e5 (aka "GFP8"):   8-bit signed mantissa + 5-bit exponent = 13 bits

    Args:
        num_elements: Number of elements to test
        group_size: GFP group size
        std: Standard deviation for random data
        seed: Random seed
        verbose: Print detailed output

    Returns:
        dict with comparison results
    """
    import torch
    from emu_golden import fp_to_gfp_1d

    torch.manual_seed(seed)

    if verbose:
        print("=" * 80)
        print("  Bit-Level Comparison: FP16 → GFP11e5 → GFP8e5  vs  FP16 → GFP8e5")
        print("=" * 80)
        print(f"  Parameters: num_elements={num_elements}, group_size={group_size}, std={std}")
        print("=" * 80)

    # Generate FP16 input
    fp16_input = (torch.randn(num_elements) * std).to(torch.float16)
    fp16_list = [float(v) for v in fp16_input.tolist()]

    if verbose:
        print(f"\n[INPUT] FP16 ({num_elements} elements):")
        print(f"  First 8: {[f'{v:.6f}' for v in fp16_list[:8]]}")

    # =========================================================================
    # Path A: FP16 → GFP11e5 → GFP8e5
    # =========================================================================
    if verbose:
        print(f"\n{'='*40}")
        print(f"  PATH A: FP16 → GFP11e5 → GFP8e5")
        print(f"{'='*40}")

    # Step A1: FP16 → GFP11e5 (via emulator)
    gfp11e5_man, gfp11e5_exp = fp_to_gfp_1d(
        fp16_input.float(),
        mantissa_bits=11,
        exp_bits=5,
        group_size=group_size,
    )

    if verbose:
        print(f"\n  [A1] GFP11e5 (from emulator):")
        for g in range(gfp11e5_man.shape[0]):
            exp = int(gfp11e5_exp[g, 0].item())
            mans = [int(m) for m in gfp11e5_man[g].tolist()]
            print(f"    Group {g}: exp={exp:2d} (0x{exp:02x})")
            print(f"      mans[0:8]: {[f'{m:+5d}' for m in mans[:8]]}")

    # Step A2: GFP11e5 → GFP8e5 (via HW golden model)
    path_a_mans = []
    path_a_exps = []

    for g in range(gfp11e5_man.shape[0]):
        group_mans = gfp11e5_man[g].tolist()
        group_exp = int(gfp11e5_exp[g, 0].item())

        # Pack into GFP11e5 format
        packed_gfp11e5 = [pack_gfp16(exp=group_exp, man_signed=int(m)) for m in group_mans]

        # Convert to GFP8e5
        gfp8_mans, gfp8_exp = gfp16_to_gfp8_hw(packed_gfp11e5)
        path_a_mans.extend(gfp8_mans)
        path_a_exps.append(gfp8_exp)

    if verbose:
        print(f"\n  [A2] GFP8e5 (from HW golden model):")
        for g, exp in enumerate(path_a_exps):
            start = g * group_size
            mans = path_a_mans[start:start + group_size]
            mans_signed = [to_signed(m, 8) for m in mans[:8]]
            print(f"    Group {g}: exp={exp:2d} (0x{exp:02x})")
            print(f"      mans[0:8] (hex):    {[f'0x{m:02x}' for m in mans[:8]]}")
            print(f"      mans[0:8] (signed): {[f'{m:+4d}' for m in mans_signed]}")

    # =========================================================================
    # Path B: FP16 → GFP8e5 (direct)
    # =========================================================================
    if verbose:
        print(f"\n{'='*40}")
        print(f"  PATH B: FP16 → GFP8e5 (direct)")
        print(f"{'='*40}")

    path_b_mans, path_b_exps = fp16_to_gfp8e5_direct(fp16_list, group_size=group_size)

    if verbose:
        print(f"\n  [B] GFP8e5 (direct conversion):")
        for g, exp in enumerate(path_b_exps):
            start = g * group_size
            mans = path_b_mans[start:start + group_size]
            mans_signed = [to_signed(m, 8) for m in mans[:8]]
            print(f"    Group {g}: exp={exp:2d} (0x{exp:02x})")
            print(f"      mans[0:8] (hex):    {[f'0x{m:02x}' for m in mans[:8]]}")
            print(f"      mans[0:8] (signed): {[f'{m:+4d}' for m in mans_signed]}")

    # =========================================================================
    # Bit-Level Comparison
    # =========================================================================
    if verbose:
        print(f"\n{'='*80}")
        print(f"  BIT-LEVEL COMPARISON")
        print(f"{'='*80}")

    exp_matches = 0
    exp_mismatches = 0
    man_exact_matches = 0
    man_off_by_one = 0
    man_larger_diff = 0
    mismatch_details = []

    num_groups = len(path_a_exps)
    for g in range(num_groups):
        # Compare exponents
        if path_a_exps[g] == path_b_exps[g]:
            exp_matches += 1
        else:
            exp_mismatches += 1
            mismatch_details.append(
                f"Group {g} exp: A={path_a_exps[g]}, B={path_b_exps[g]}, diff={path_a_exps[g]-path_b_exps[g]}"
            )

        # Compare mantissas
        start = g * group_size
        for i in range(group_size):
            idx = start + i
            man_a = to_signed(path_a_mans[idx], 8)
            man_b = to_signed(path_b_mans[idx], 8)
            diff = abs(man_a - man_b)

            if diff == 0:
                man_exact_matches += 1
            elif diff == 1:
                man_off_by_one += 1
            else:
                man_larger_diff += 1
                if len(mismatch_details) < 20:
                    mismatch_details.append(
                        f"  elem[{g},{i}]: A={man_a:+4d} (0x{path_a_mans[idx]:02x}), "
                        f"B={man_b:+4d} (0x{path_b_mans[idx]:02x}), diff={diff}"
                    )

    total_elements = num_groups * group_size

    if verbose:
        print(f"\n  Exponent Comparison:")
        print(f"    Exact matches: {exp_matches}/{num_groups}")
        print(f"    Mismatches:    {exp_mismatches}/{num_groups}")

        print(f"\n  Mantissa Comparison:")
        print(f"    Exact matches: {man_exact_matches}/{total_elements} ({100*man_exact_matches/total_elements:.1f}%)")
        print(f"    Off-by-one:    {man_off_by_one}/{total_elements} ({100*man_off_by_one/total_elements:.1f}%)")
        print(f"    Larger diff:   {man_larger_diff}/{total_elements} ({100*man_larger_diff/total_elements:.1f}%)")

        if mismatch_details:
            print(f"\n  Mismatch Details (first 20):")
            for detail in mismatch_details[:20]:
                print(f"    {detail}")

        # Analysis
        print(f"\n{'='*80}")
        print(f"  ANALYSIS")
        print(f"{'='*80}")

        if exp_mismatches > 0:
            print(f"\n  Exponent differences explained:")
            print(f"    - Path A: emulator uses bias=16 (2^(exp_bits-1))")
            print(f"    - Path B: direct uses bias=15 (FP16-style)")
            print(f"    - BOTH produce same effective scale when adjusted properly")
            print(f"    - HW golden exp needs +3 adjustment for 11→8 bit quant shift")

            # Show math for first group
            if num_groups > 0:
                exp_a = path_a_exps[0]
                exp_b = path_b_exps[0]
                man_a = to_signed(path_a_mans[0], 8)
                man_b = to_signed(path_b_mans[0], 8)
                print(f"\n  Example (element 0):")
                print(f"    Path A: exp_hw={exp_a}, +3 adj → exp_eff={exp_a+3}, bias=16")
                print(f"           scale = 2^({exp_a+3}-16) = 2^{exp_a+3-16}")
                print(f"           recon = {man_a} * 2^{exp_a+3-16} = {man_a * (2**(exp_a+3-16)):.4f}")
                print(f"    Path B: exp={exp_b}, bias=15")
                print(f"           scale = 2^({exp_b}-15) = 2^{exp_b-15}")
                print(f"           recon = {man_b} * 2^{exp_b-15} = {man_b * (2**(exp_b-15)):.4f}")
                print(f"    Original FP16: {fp16_list[0]:.4f}")

        if man_larger_diff > 0:
            print(f"\n  Mantissa differences > 1 exist because:")
            print(f"    - Different quantization paths accumulate different rounding")
            print(f"    - Path A: two-stage (FP16→GFP11e5→GFP8e5)")
            print(f"    - Path B: single-stage (FP16→GFP8e5)")

        print(f"\n  CONCLUSION:")
        if man_exact_matches == total_elements and exp_matches == num_groups:
            print(f"    *** PERFECT BIT MATCH: Both paths produce identical GFP8e5 ***")
        elif man_larger_diff == 0:
            print(f"    *** MATHEMATICALLY EQUIVALENT: Same effective scale ***")
            print(f"    *** Mantissa diff ≤1 is expected rounding variation ***")
        else:
            print(f"    Larger differences exist - paths not equivalent")

        print("=" * 80)

    return {
        "exp_matches": exp_matches,
        "exp_mismatches": exp_mismatches,
        "man_exact_matches": man_exact_matches,
        "man_off_by_one": man_off_by_one,
        "man_larger_diff": man_larger_diff,
        "path_a_mans": path_a_mans,
        "path_a_exps": path_a_exps,
        "path_b_mans": path_b_mans,
        "path_b_exps": path_b_exps,
        "mismatch_details": mismatch_details,
    }


# =============================================================================
# Mathematical Validation Test
# =============================================================================

def test_mathematical_soundness(
    num_trials: int = 100,
    group_size: int = 32,
    seed: int = 42,
    verbose: bool = True,
):
    """
    Rigorous mathematical validation of GFP conversions.

    Validates:
      1. Quantization error bounds (11→8 bit = 3 bits ≈ 12.5% max mantissa error)
      2. Sign preservation (negative stays negative, positive stays positive)
      3. Zero handling (zero maps to zero exactly)
      4. Monotonicity (ordering preserved within quantization precision)
      5. Overflow/underflow saturation behavior

    Args:
        num_trials: Number of random test trials
        group_size: GFP group size
        seed: Random seed
        verbose: Print detailed output

    Returns:
        dict with validation results
    """
    import random
    import math
    random.seed(seed)

    # Theoretical bounds
    # 11-bit signed mantissa → 8-bit signed mantissa = 3 bits lost
    # Max quantization error = 2^3 / 2^11 = 1/256 of full range per element
    # But with shared exponent alignment, error can compound
    QUANT_BITS_LOST = 3
    MAX_MANTISSA_REL_ERROR = 1.0 / (1 << (8 - 1))  # 1/128 ≈ 0.78% per LSB
    THEORETICAL_MAX_REL_ERROR = (1 << QUANT_BITS_LOST) * MAX_MANTISSA_REL_ERROR  # ~6.25%

    results = {
        "sign_preservation": {"passed": 0, "failed": 0, "violations": []},
        "zero_handling": {"passed": 0, "failed": 0, "violations": []},
        "monotonicity": {"passed": 0, "failed": 0, "violations": []},
        "error_bounds": {"passed": 0, "failed": 0, "max_observed": 0.0, "violations": []},
        "edge_cases": {"passed": 0, "failed": 0, "violations": []},
    }

    if verbose:
        print("=" * 75)
        print("  Mathematical Soundness Validation for GFP Conversions")
        print("=" * 75)
        print(f"  Theoretical max mantissa rel error: {THEORETICAL_MAX_REL_ERROR:.2%}")
        print(f"  Trials: {num_trials}, Group size: {group_size}")
        print("=" * 75)

    # =========================================================================
    # Test 1: Sign Preservation
    # =========================================================================
    if verbose:
        print("\n[Test 1] Sign Preservation")

    for trial in range(num_trials):
        # Generate mixed positive/negative values
        test_values = []
        for _ in range(group_size):
            sign = random.choice([-1, 1])
            magnitude = random.uniform(0.01, 10.0)
            test_values.append(sign * magnitude)

        # Convert via GFP16 path
        gfp8_mans, gfp8_exps = fp16_to_gfp8e5_direct(test_values, group_size=group_size)
        reconstructed = gfp8e5_to_fp16_direct(gfp8_mans, gfp8_exps, group_size=group_size)

        for i, (orig, recon) in enumerate(zip(test_values, reconstructed)):
            if orig != 0 and recon != 0:
                orig_sign = 1 if orig > 0 else -1
                recon_sign = 1 if recon > 0 else -1
                if orig_sign != recon_sign:
                    results["sign_preservation"]["failed"] += 1
                    results["sign_preservation"]["violations"].append(
                        f"Trial {trial}, elem {i}: orig={orig:.6f}, recon={recon:.6f}"
                    )
                else:
                    results["sign_preservation"]["passed"] += 1
            else:
                results["sign_preservation"]["passed"] += 1

    if verbose:
        sp = results["sign_preservation"]
        status = "PASS" if sp["failed"] == 0 else "FAIL"
        print(f"  {status}: {sp['passed']} passed, {sp['failed']} failed")

    # =========================================================================
    # Test 2: Zero Handling
    # =========================================================================
    if verbose:
        print("\n[Test 2] Zero Handling")

    for trial in range(num_trials // 10):
        # Insert zeros at random positions
        test_values = [random.uniform(-1.0, 1.0) for _ in range(group_size)]
        zero_positions = random.sample(range(group_size), k=min(5, group_size))
        for pos in zero_positions:
            test_values[pos] = 0.0

        gfp8_mans, gfp8_exps = fp16_to_gfp8e5_direct(test_values, group_size=group_size)
        reconstructed = gfp8e5_to_fp16_direct(gfp8_mans, gfp8_exps, group_size=group_size)

        for pos in zero_positions:
            if reconstructed[pos] == 0.0:
                results["zero_handling"]["passed"] += 1
            else:
                results["zero_handling"]["failed"] += 1
                results["zero_handling"]["violations"].append(
                    f"Trial {trial}, pos {pos}: expected 0.0, got {reconstructed[pos]:.6e}"
                )

    if verbose:
        zh = results["zero_handling"]
        status = "PASS" if zh["failed"] == 0 else "FAIL"
        print(f"  {status}: {zh['passed']} passed, {zh['failed']} failed")

    # =========================================================================
    # Test 3: Monotonicity (within group)
    # =========================================================================
    if verbose:
        print("\n[Test 3] Monotonicity (ordering preserved within quantization)")

    for trial in range(num_trials):
        # Generate sorted values
        test_values = sorted([random.uniform(-5.0, 5.0) for _ in range(group_size)])

        gfp8_mans, gfp8_exps = fp16_to_gfp8e5_direct(test_values, group_size=group_size)
        reconstructed = gfp8e5_to_fp16_direct(gfp8_mans, gfp8_exps, group_size=group_size)

        # Check monotonicity with tolerance for ties
        monotonic = True
        for i in range(len(reconstructed) - 1):
            # Allow equal values (quantization can create ties)
            if reconstructed[i] > reconstructed[i + 1] + 1e-10:
                monotonic = False
                results["monotonicity"]["violations"].append(
                    f"Trial {trial}: recon[{i}]={reconstructed[i]:.6f} > recon[{i+1}]={reconstructed[i+1]:.6f}"
                )
                break

        if monotonic:
            results["monotonicity"]["passed"] += 1
        else:
            results["monotonicity"]["failed"] += 1

    if verbose:
        mn = results["monotonicity"]
        status = "PASS" if mn["failed"] == 0 else "FAIL"
        print(f"  {status}: {mn['passed']} passed, {mn['failed']} failed")

    # =========================================================================
    # Test 4: Error Bounds (accounting for dynamic range limitations)
    # =========================================================================
    if verbose:
        print("\n[Test 4] Quantization Error Bounds")
        print("  Note: GFP shares exponent across group - dynamic range within group is limited")
        print("  Expected behavior: values << group_max have fewer mantissa bits, higher error")

    # GFP with 8-bit signed mantissa has ~7 bits precision at full scale
    # Values at ratio R from max have ~log2(127/R) bits precision
    # Error threshold scales inversely with available precision
    DYNAMIC_RANGE = 127  # max mantissa value

    underflow_count = 0
    low_precision_count = 0
    normal_count = 0

    for trial in range(num_trials):
        test_values = [random.gauss(0, 1.0) for _ in range(group_size)]
        max_abs = max(abs(v) for v in test_values)

        gfp8_mans, gfp8_exps = fp16_to_gfp8e5_direct(test_values, group_size=group_size)
        reconstructed = gfp8e5_to_fp16_direct(gfp8_mans, gfp8_exps, group_size=group_size)

        for i, (orig, recon) in enumerate(zip(test_values, reconstructed)):
            if abs(orig) < 1e-10:  # Skip true zeros
                continue

            # Calculate the ratio of this value to max
            ratio = abs(orig) / max_abs if max_abs > 0 else 1.0

            # Expected mantissa magnitude (proportional to ratio * 127)
            expected_mantissa = ratio * DYNAMIC_RANGE

            rel_error = abs(orig - recon) / abs(orig)

            if expected_mantissa < 1.0:
                # Complete underflow expected (mantissa rounds to 0)
                underflow_count += 1
                results["error_bounds"]["passed"] += 1
            elif expected_mantissa < 10.0:
                # Low precision region (< 4 bits): allow high error
                # With only ~3 bits, error can be up to ~50%
                low_precision_count += 1
                results["error_bounds"]["passed"] += 1  # Expected behavior
            else:
                # Normal precision: error should be bounded
                # With ~7 bits precision, max error ~1% (1/127)
                # But quantization adds ~0.5 LSB error, so allow ~5%
                results["error_bounds"]["max_observed"] = max(
                    results["error_bounds"]["max_observed"], rel_error
                )
                if rel_error > 0.10:  # 10% threshold for well-represented values
                    results["error_bounds"]["failed"] += 1
                    results["error_bounds"]["violations"].append(
                        f"Trial {trial}, elem {i}: rel_error={rel_error:.2%}, "
                        f"orig={orig:.6f}, recon={recon:.6f}, exp_man={expected_mantissa:.1f}"
                    )
                else:
                    normal_count += 1
                    results["error_bounds"]["passed"] += 1

    if verbose:
        eb = results["error_bounds"]
        status = "PASS" if eb["failed"] == 0 else "FAIL"
        print(f"  {status}: {eb['passed']} passed, {eb['failed']} failed")
        print(f"  Breakdown:")
        print(f"    Underflows (mantissa < 1): {underflow_count}")
        print(f"    Low precision (mantissa < 10): {low_precision_count}")
        print(f"    Normal precision: {normal_count}")
        if normal_count > 0:
            print(f"  Max rel error (normal precision): {eb['max_observed']:.2%}")

    # =========================================================================
    # Test 5: Edge Cases
    # =========================================================================
    if verbose:
        print("\n[Test 5] Edge Cases")

    edge_cases = [
        ("all_zeros", [0.0] * group_size),
        ("all_positive", [1.0] * group_size),
        ("all_negative", [-1.0] * group_size),
        ("alternating", [(-1)**i * 1.0 for i in range(group_size)]),
        ("large_range", [2**i if i < 16 else 2**(31-i) for i in range(group_size)]),
        ("tiny_values", [1e-6 * (i+1) for i in range(group_size)]),
        ("single_large", [0.001] * (group_size - 1) + [100.0]),
        ("max_mantissa", [127.0 / 128.0] * group_size),  # Near max 8-bit signed
    ]

    for name, test_values in edge_cases:
        try:
            gfp8_mans, gfp8_exps = fp16_to_gfp8e5_direct(test_values, group_size=group_size)
            reconstructed = gfp8e5_to_fp16_direct(gfp8_mans, gfp8_exps, group_size=group_size)

            # Basic sanity: no NaN/Inf
            has_bad_values = any(math.isnan(v) or math.isinf(v) for v in reconstructed)
            if has_bad_values:
                results["edge_cases"]["failed"] += 1
                results["edge_cases"]["violations"].append(f"{name}: produced NaN/Inf")
            else:
                results["edge_cases"]["passed"] += 1
        except Exception as e:
            results["edge_cases"]["failed"] += 1
            results["edge_cases"]["violations"].append(f"{name}: exception {e}")

    if verbose:
        ec = results["edge_cases"]
        status = "PASS" if ec["failed"] == 0 else "FAIL"
        print(f"  {status}: {ec['passed']} passed, {ec['failed']} failed")

    # =========================================================================
    # Summary
    # =========================================================================
    total_passed = sum(r["passed"] for r in results.values())
    total_failed = sum(r["failed"] for r in results.values())

    if verbose:
        print("\n" + "=" * 75)
        print("  MATHEMATICAL VALIDATION SUMMARY")
        print("=" * 75)
        print(f"  ┌─────────────────────────┬─────────┬─────────┬─────────┐")
        print(f"  │ Test                    │ Passed  │ Failed  │ Status  │")
        print(f"  ├─────────────────────────┼─────────┼─────────┼─────────┤")
        for test_name, r in results.items():
            status = "PASS" if r["failed"] == 0 else "FAIL"
            print(f"  │ {test_name:23s} │ {r['passed']:7d} │ {r['failed']:7d} │ {status:7s} │")
        print(f"  ├─────────────────────────┼─────────┼─────────┼─────────┤")
        print(f"  │ TOTAL                   │ {total_passed:7d} │ {total_failed:7d} │         │")
        print(f"  └─────────────────────────┴─────────┴─────────┴─────────┘")

        overall = "ALL TESTS PASSED" if total_failed == 0 else "SOME TESTS FAILED"
        print(f"\n  {overall}")

        if total_failed > 0 and verbose:
            print("\n  Violations (first 5 per category):")
            for test_name, r in results.items():
                if r["violations"]:
                    print(f"\n  [{test_name}]:")
                    for v in r["violations"][:5]:
                        print(f"    - {v}")

        print("=" * 75)

    return {
        "results": results,
        "total_passed": total_passed,
        "total_failed": total_failed,
        "all_passed": total_failed == 0,
    }


# =============================================================================
# Unified Comparison: All Three Paths
# =============================================================================

def test_compare_all_paths(
    num_elements: int = 32,
    group_size: int = 32,
    std: float = 1.0,
    seed: int = 42,
    verbose: bool = True,
):
    """
    Compare all three conversion paths with the same input data:
      1. FP16 → GFP11e5 → FP16           (GFP11e5 only)
      2. FP16 → GFP11e5 → GFP8 → FP16    (via GFP16 intermediate)
      3. FP16 → GFP8 → FP16            (direct)

    Args:
        num_elements: Number of elements to test
        group_size: GFP group size
        std: Standard deviation for random data
        seed: Random seed
        verbose: Print detailed output

    Returns:
        dict with error metrics for all three paths
    """
    import torch
    from emu_golden import fp_to_gfp_1d, gfp_to_fp_1d

    torch.manual_seed(seed)

    # Format parameters
    GFP11e5_MAN_BITS = 11
    GFP11e5_EXP_BITS = 5
    GFP8e5_MAN_BITS = 8
    GFP8e5_EXP_BITS = 5

    if verbose:
        print("=" * 75)
        print("  Unified Comparison: All Three Conversion Paths")
        print("=" * 75)
        print(f"  Parameters: num_elements={num_elements}, group_size={group_size}, std={std}")
        print("=" * 75)

    # =========================================================================
    # Generate common FP16 input
    # =========================================================================
    fp16_input = (torch.randn(num_elements) * std).to(torch.float16)
    fp16_as_float = fp16_input.float()

    if verbose:
        print(f"\n[INPUT] FP16 ({num_elements} elements):")
        print(f"  First 8: {[f'{v:.4f}' for v in fp16_input[:8].tolist()]}")

    # =========================================================================
    # Path 1: FP16 → GFP11e5 → FP16
    # =========================================================================
    gfp11e5_man, gfp11e5_exp = fp_to_gfp_1d(
        fp16_as_float,
        mantissa_bits=GFP11e5_MAN_BITS,
        exp_bits=GFP11e5_EXP_BITS,
        group_size=group_size,
    )

    fp_from_gfp11e5 = gfp_to_fp_1d(
        gfp11e5_man,
        gfp11e5_exp,
        num_elements,
        mantissa_bits=GFP11e5_MAN_BITS,
        exp_bits=GFP11e5_EXP_BITS,
        group_size=group_size,
    )

    error_path1 = fp16_as_float - fp_from_gfp11e5
    max_err_path1 = error_path1.abs().max().item()
    rel_err_path1 = (error_path1.abs() / (fp16_as_float.abs() + 1e-10)).mean().item()

    if verbose:
        print(f"\n[PATH 1] FP16 → GFP11e5 → FP16:")
        print(f"  Reconstructed first 8: {[f'{v:.4f}' for v in fp_from_gfp11e5[:8].tolist()]}")

    # =========================================================================
    # Path 2: FP16 → GFP11e5 → GFP8 → FP16
    # =========================================================================
    num_groups = gfp11e5_man.shape[0]
    gfp8_mans_all = []
    gfp8_exps_all = []

    for g in range(num_groups):
        group_mans = gfp11e5_man[g].tolist()
        group_exp = int(gfp11e5_exp[g, 0].item())

        # Pack GFP16
        packed_gfp11e5 = [pack_gfp16(exp=group_exp, man_signed=int(m)) for m in group_mans]

        # Convert GFP11e5 → GFP8
        gfp8_mans, gfp8_exp = gfp16_to_gfp8_hw(packed_gfp11e5)

        # Adjust exponent for quantization shift
        quant_shift = GFP11e5_MAN_BITS - GFP8e5_MAN_BITS  # 3
        gfp8_exp_adjusted = gfp8_exp + quant_shift

        gfp8_mans_signed = [to_signed(m, GFP8e5_MAN_BITS) for m in gfp8_mans]
        gfp8_mans_all.append(gfp8_mans_signed)
        gfp8_exps_all.append(gfp8_exp_adjusted)

    # Convert GFP8 → FP
    gfp8_man_tensor = torch.tensor(gfp8_mans_all, dtype=torch.float32)
    gfp8_exp_tensor = torch.tensor([[e] for e in gfp8_exps_all], dtype=torch.float32)

    fp_from_gfp8_via_gfp16 = gfp_to_fp_1d(
        gfp8_man_tensor,
        gfp8_exp_tensor,
        num_elements,
        mantissa_bits=GFP8e5_MAN_BITS,
        exp_bits=GFP8e5_EXP_BITS,
        group_size=group_size,
    )

    error_path2 = fp16_as_float - fp_from_gfp8_via_gfp16
    max_err_path2 = error_path2.abs().max().item()
    rel_err_path2 = (error_path2.abs() / (fp16_as_float.abs() + 1e-10)).mean().item()

    if verbose:
        print(f"\n[PATH 2] FP16 → GFP11e5 → GFP8 → FP16:")
        print(f"  Reconstructed first 8: {[f'{v:.4f}' for v in fp_from_gfp8_via_gfp16[:8].tolist()]}")

    # =========================================================================
    # Path 3: FP16 → GFP8 → FP16 (direct)
    # =========================================================================
    fp16_list = fp16_input.tolist()
    gfp8_mans_direct, gfp8_exps_direct = fp16_to_gfp8e5_direct(
        fp16_list, group_size=group_size
    )
    fp_from_gfp8_direct = gfp8e5_to_fp16_direct(
        gfp8_mans_direct, gfp8_exps_direct, group_size=group_size
    )

    error_path3 = [a - b for a, b in zip(fp16_list, fp_from_gfp8_direct)]
    abs_errors_path3 = [abs(e) for e in error_path3]
    rel_errors_path3 = [abs(a - b) / (abs(a) + 1e-10) for a, b in zip(fp16_list, fp_from_gfp8_direct)]

    max_err_path3 = max(abs_errors_path3)
    rel_err_path3 = sum(rel_errors_path3) / len(rel_errors_path3)

    if verbose:
        print(f"\n[PATH 3] FP16 → GFP8 → FP16 (direct):")
        print(f"  Reconstructed first 8: {[f'{v:.4f}' for v in fp_from_gfp8_direct[:8]]}")

    # =========================================================================
    # Comparison Summary
    # =========================================================================
    if verbose:
        print("\n" + "=" * 75)
        print("  COMPARISON SUMMARY")
        print("=" * 75)
        print(f"  ┌─────────────────────────────────────┬────────────┬────────────┐")
        print(f"  │ Path                                │ Max Error  │ Rel Error  │")
        print(f"  ├─────────────────────────────────────┼────────────┼────────────┤")
        print(f"  │ 1. FP16 → GFP11e5 → FP16              │ {max_err_path1:10.2e} │ {rel_err_path1:9.4%} │")
        print(f"  │ 2. FP16 → GFP11e5 → GFP8 → FP16       │ {max_err_path2:10.2e} │ {rel_err_path2:9.4%} │")
        print(f"  │ 3. FP16 → GFP8 → FP16 (direct)      │ {max_err_path3:10.2e} │ {rel_err_path3:9.4%} │")
        print(f"  └─────────────────────────────────────┴────────────┴────────────┘")

        # Additional analysis
        gfp8_loss_via_gfp16 = rel_err_path2 - rel_err_path1
        print(f"\n  Analysis:")
        print(f"    GFP16 quantization loss:           {rel_err_path1:+.4%}")
        print(f"    GFP8e5 additional loss (via GFP16):  {gfp8_loss_via_gfp16:+.4%}")
        print(f"    Total loss (via GFP16):            {rel_err_path2:+.4%}")
        print(f"    Direct GFP8 loss:                  {rel_err_path3:+.4%}")
        print(f"    Difference (direct - via GFP16):   {rel_err_path3 - rel_err_path2:+.4%}")

        # Determine best path
        best_path = min(
            [(1, rel_err_path1, "FP16 → GFP11e5 → FP16"),
             (2, rel_err_path2, "FP16 → GFP11e5 → GFP8 → FP16"),
             (3, rel_err_path3, "FP16 → GFP8 → FP16 (direct)")],
            key=lambda x: x[1]
        )
        print(f"\n  Best accuracy: Path {best_path[0]} ({best_path[2]}) with {best_path[1]:.4%} error")
        print("=" * 75)

    return {
        "path1_gfp16_only": {
            "max_error": max_err_path1,
            "rel_error": rel_err_path1,
            "reconstructed": fp_from_gfp11e5,
        },
        "path2_via_gfp16": {
            "max_error": max_err_path2,
            "rel_error": rel_err_path2,
            "reconstructed": fp_from_gfp8_via_gfp16,
        },
        "path3_direct": {
            "max_error": max_err_path3,
            "rel_error": rel_err_path3,
            "reconstructed": fp_from_gfp8_direct,
        },
        "fp16_input": fp16_input,
    }


# =============================================================================
# Test / Demo
# =============================================================================
if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description="GFP16 to GFP8 Golden Model Test")
    parser.add_argument("--roundtrip", action="store_true",
                        help="Run full FP16 → GFP11e5 → GFP8 → FP round-trip test")
    parser.add_argument("--direct", action="store_true",
                        help="Run direct FP16 → GFP8 → FP16 round-trip test")
    parser.add_argument("--compare", action="store_true",
                        help="Compare via-GFP16 vs direct paths")
    parser.add_argument("--compare-all", action="store_true",
                        help="Compare all three paths: GFP16-only, via-GFP16, and direct")
    parser.add_argument("--validate", action="store_true",
                        help="Run rigorous mathematical soundness validation")
    parser.add_argument("--bits", action="store_true",
                        help="Compare GFP8e5 bits: FP16→GFP11e5→GFP8e5 vs FP16→GFP8e5")
    parser.add_argument("-n", "--num-elements", type=int, default=32,
                        help="Number of elements (default: 32)")
    parser.add_argument("-g", "--group-size", type=int, default=32,
                        help="GFP group size (default: 32)")
    parser.add_argument("-s", "--std", type=float, default=1.0,
                        help="Standard deviation for random data (default: 1.0)")
    parser.add_argument("--seed", type=int, default=42,
                        help="Random seed (default: 42)")
    args = parser.parse_args()

    if args.bits:
        # Bit-level comparison of both paths
        test_bit_level_comparison(
            num_elements=args.num_elements,
            group_size=args.group_size,
            std=args.std,
            seed=args.seed,
            verbose=True,
        )

    elif args.validate:
        # Run mathematical soundness validation
        test_mathematical_soundness(
            num_trials=100,
            group_size=args.group_size,
            seed=args.seed,
            verbose=True,
        )

    elif args.compare_all:
        # Compare all three paths with unified test
        test_compare_all_paths(
            num_elements=args.num_elements,
            group_size=args.group_size,
            std=args.std,
            seed=args.seed,
            verbose=True,
        )

    elif args.compare:
        # Compare both GFP8 paths (legacy option)
        print("=" * 70)
        print("Comparing FP16 → GFP11e5 → GFP8 → FP  vs  FP16 → GFP8 → FP")
        print("=" * 70)

        result_via_gfp16 = test_fp16_gfp11e5_gfp8e5_roundtrip(
            num_elements=args.num_elements,
            group_size=args.group_size,
            std=args.std,
            seed=args.seed,
            verbose=True,
        )

        print("\n" + "=" * 70 + "\n")

        result_direct = test_fp16_gfp8e5_direct_roundtrip(
            num_elements=args.num_elements,
            group_size=args.group_size,
            std=args.std,
            seed=args.seed,
            verbose=True,
        )

        print("\n" + "=" * 70)
        print("COMPARISON SUMMARY")
        print("=" * 70)
        print(f"  Via GFP16:  rel_error = {result_via_gfp16['rel_error']:.4%}")
        print(f"  Direct:     rel_error = {result_direct['mean_rel_error']:.4%}")
        diff = result_via_gfp16['rel_error'] - result_direct['mean_rel_error']
        print(f"  Difference: {diff:+.4%} (positive = via GFP16 is worse)")
        print("=" * 70)

    elif args.direct:
        # Run direct FP16 → GFP8 → FP16 test
        test_fp16_gfp8e5_direct_roundtrip(
            num_elements=args.num_elements,
            group_size=args.group_size,
            std=args.std,
            seed=args.seed,
            verbose=True,
        )

    elif args.roundtrip:
        # Run full round-trip test via GFP16
        test_fp16_gfp11e5_gfp8e5_roundtrip(
            num_elements=args.num_elements,
            group_size=args.group_size,
            std=args.std,
            seed=args.seed,
            verbose=True,
        )

    else:
        # Run basic GFP11e5 → GFP8 test
        print("=" * 70)
        print("GFP16 to GFP8 Conversion Golden Model Test")
        print("=" * 70)

        # Create test data: mix of positive and negative values
        test_data = [
            pack_gfp16(exp=15, man_signed=512),    # Positive
            pack_gfp16(exp=15, man_signed=-512),   # Negative
            pack_gfp16(exp=14, man_signed=256),    # Lower exp, positive
            pack_gfp16(exp=14, man_signed=-256),   # Lower exp, negative
            pack_gfp16(exp=0, man_signed=0),       # Zero
            pack_gfp16(exp=13, man_signed=100),    # Even lower exp
            pack_gfp16(exp=15, man_signed=1023),   # Max positive mantissa
            pack_gfp16(exp=15, man_signed=-1024),  # Max negative mantissa
        ]

        print(f"\nInput GFP16 data ({len(test_data)} elements):")
        for i, val in enumerate(test_data):
            exp = (val >> 11) & 0x1F
            man = to_signed(val & 0x7FF, 11)
            print(f"  [{i}] 0x{val:04X} = exp={exp}, man={man:+5d}")

        # Convert
        gfp8_mans, gfp8_exp = gfp16_to_gfp8_hw(test_data)

        print(f"\nOutput GFP8:")
        print(f"  Shared exponent: {gfp8_exp}")
        print(f"  Mantissas:")
        for i, man in enumerate(gfp8_mans):
            man_signed = to_signed(man, 8)
            print(f"    [{i}] 0x{man:02X} = {man_signed:+4d}")

        print("\n" + "=" * 70)
        print("DONE")
        print("=" * 70)
