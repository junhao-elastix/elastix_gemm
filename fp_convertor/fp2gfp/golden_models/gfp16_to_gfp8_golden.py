#!/usr/bin/env python3
"""
GFP16 to GFP8 Conversion Golden Model

This module provides bit-accurate golden reference functions for the
GFP16 → GFP8 streaming converter hardware modules.

GFP16 Format (per element):
    [15:11] = exp[4:0]   - 5-bit exponent
    [10:0]  = man[10:0]  - 11-bit SIGNED mantissa (2's complement)

GFP8 Format (per element):
    [7:0] = man[7:0]     - 8-bit SIGNED mantissa (2's complement)
    Shared exponent output separately (8-bit)
"""

from dataclasses import dataclass


@dataclass
class GFP16Format:
    """GFP16 format parameters."""
    total_bits: int = 11 + 5 # 11-bit mantissa + 5-bit exponent
    exp_bits: int = 5
    man_bits: int = 11  # Signed mantissa


@dataclass
class GFP8Format:
    """GFP8 format parameters."""
    total_bits: int = 8 + 5  # 8-bit mantissa + 5-bit exponent
    exp_bits: int = 5
    man_bits: int = 8   # Signed mantissa


# Default formats
GFP16 = GFP16Format()
GFP8 = GFP8Format()


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

def gfp16_extract_hw(gfp16_data: list[int], fmt: GFP16Format = GFP16) -> tuple[list[int], list[int], list[bool]]:
    """
    Extract exponent and signed mantissa from GFP16 packed data.

    Args:
        gfp16_data: List of packed GFP16 values (16-bit each)
        fmt: GFP16 format parameters

    Returns:
        (exps, mans, is_zeros) where:
        - exps: List of unsigned exponents
        - mans: List of signed mantissas (as Python integers, can be negative)
        - is_zeros: List of boolean zero flags
    """
    exps = []
    mans = []
    is_zeros = []

    for val in gfp16_data:
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


def gfp8_quantizer_hw(
    aligned_mans: list[int],
    round_bits: list[int],
    is_zeros: list[bool],
    in_man_bits: int = 11,
    out_man_bits: int = 8
) -> list[int]:
    """
    Quantize aligned signed mantissas from GFP16 to GFP8.

    Args:
        aligned_mans: List of aligned signed mantissas (11-bit)
        round_bits: List of round bits
        is_zeros: List of zero flags
        in_man_bits: Input mantissa bits (11)
        out_man_bits: Output mantissa bits (8)

    Returns:
        List of quantized signed mantissas (8-bit signed, as Python int)
    """
    quant_shift = in_man_bits - out_man_bits  # 11 - 8 = 3

    gfp8_mans = []

    for aligned, rnd, is_zero in zip(aligned_mans, round_bits, is_zeros):
        if is_zero:
            gfp8_mans.append(0)
        else:
            # Add rounding constant
            # For shift of 3, rounding constant is 1 << 2 = 4
            # But we use the round_bit from aligner for finer control
            round_add = rnd << (quant_shift - 1) if quant_shift > 0 else 0
            rounded = aligned + round_add

            # Arithmetic right shift to quantize
            shifted = rounded >> quant_shift

            # Saturate to 8-bit signed range [-128, 127]
            saturated = saturate_signed(shifted, out_man_bits)

            gfp8_mans.append(saturated)

    return gfp8_mans


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

def gfp16_to_gfp8_hw(
    gfp16_data: list[int],
    pad: int = 0,
    gfp16_fmt: GFP16Format = GFP16,
    gfp8_fmt: GFP8Format = GFP8
) -> tuple[list[int], int]:
    """
    Convert GFP16 data to GFP8 format (single group).

    Args:
        gfp16_data: List of packed GFP16 values
        pad: Number of padding elements
        gfp16_fmt: GFP16 format parameters
        gfp8_fmt: GFP8 format parameters

    Returns:
        (gfp8_mans, gfp8_exp) where:
        - gfp8_mans: List of 8-bit signed mantissas (as unsigned for HW comparison)
        - gfp8_exp: Shared 8-bit exponent
    """
    # Step 1: Extract fields
    exps, mans, is_zeros = gfp16_extract_hw(gfp16_data, gfp16_fmt)

    # Step 2: Find max exponent
    max_exp = group_max_exp_finder_hw(exps, is_zeros, pad)

    # Step 3: Align mantissas
    aligned_mans, round_bits = signed_aligner_hw(
        exps, mans, is_zeros, max_exp, gfp16_fmt.man_bits
    )

    # Step 4: Quantize to GFP8
    gfp8_mans_signed = gfp8_quantizer_hw(
        aligned_mans, round_bits, is_zeros,
        gfp16_fmt.man_bits, gfp8_fmt.man_bits
    )

    # Convert signed mantissas to unsigned for hardware comparison
    gfp8_mans_unsigned = [to_unsigned(m, gfp8_fmt.man_bits) for m in gfp8_mans_signed]

    # GFP8 exponent is just zero-extended from 5-bit to 8-bit
    gfp8_exp = max_exp

    return gfp8_mans_unsigned, gfp8_exp


def pack_gfp16(exp: int, man_signed: int, fmt: GFP16Format = GFP16) -> int:
    """
    Pack exponent and signed mantissa into GFP16 format.

    Args:
        exp: Unsigned exponent (5-bit)
        man_signed: Signed mantissa (Python int, can be negative)
        fmt: GFP16 format parameters

    Returns:
        Packed GFP16 value (16-bit unsigned)
    """
    man_unsigned = to_unsigned(man_signed, fmt.man_bits)
    return ((exp & ((1 << fmt.exp_bits) - 1)) << fmt.man_bits) | man_unsigned


# =============================================================================
# Test / Demo
# =============================================================================
if __name__ == "__main__":
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
