#!/usr/bin/env python3
"""
Golden Test Vector Generator for gfp_norm_quant module.

Generates input and output hex files for RTL simulation:
- Input:  8 lines, each with 32 space-separated 16-bit hex values (GFP11e5)
- Output: 8 lines, each with 33 space-separated 8-bit hex values (1 exp + 32 mantissas)

Usage:
    python golden_gen.py
"""

import random
from pathlib import Path
from gfp11e5_to_gfp8e5_golden import gfp11e5_to_gfp8e5_hw, pack_gfp11e5, to_unsigned, GFP8e5


def generate_test_vectors(
    num_vectors: int = 8,
    in_elements: int = 32,
    seed: int = 42
) -> tuple[list[list[int]], list[list[int]], list[int]]:
    """
    Generate test vectors matching the cocotb E2E test.

    Args:
        num_vectors: Number of test vectors
        in_elements: Elements per vector
        seed: Random seed for reproducibility

    Returns:
        (input_data, output_mantissas, output_exponents)
        - input_data: List of vectors, each vector is list of packed GFP11e5 values
        - output_mantissas: List of vectors, each vector is list of 8-bit unsigned mantissas
        - output_exponents: List of shared exponents (one per vector)
    """
    random.seed(seed)

    all_input_data = []
    all_output_mans = []
    all_output_exps = []

    for vec_idx in range(num_vectors):
        input_vec = []
        for elem_idx in range(in_elements):
            # Varied exponent
            exp = random.randint(10, 13)
            # Random signed mantissa: -500 to +500
            man = random.randint(-100, 100)
            packed = pack_gfp11e5(exp=exp, man_signed=man)
            input_vec.append(packed)

        all_input_data.append(input_vec)

        # Get expected output from golden model
        output_mans, output_exp = gfp11e5_to_gfp8e5_hw(input_vec)
        # Convert signed mantissas to unsigned 8-bit representation
        output_mans_unsigned = [to_unsigned(m, GFP8e5.man_bits) for m in output_mans]

        all_output_mans.append(output_mans_unsigned)
        all_output_exps.append(output_exp)

    return all_input_data, all_output_mans, all_output_exps


def write_input_hex(
    filepath: Path,
    input_data: list[list[int]]
) -> None:
    """
    Write input data to hex file.

    Format: Each line has 32 space-separated 16-bit hex values (4 chars each)
    Example: "7e00 7c80 7b00 ..."
    """
    with open(filepath, 'w') as f:
        for vec in input_data:
            hex_values = [f"{val:04x}" for val in vec]
            f.write(" ".join(hex_values) + "\n")


def write_output_hex(
    filepath: Path,
    output_mantissas: list[list[int]],
    output_exponents: list[int]
) -> None:
    """
    Write output data to hex file.

    Format: Each line has 33 space-separated 8-bit hex values (2 chars each)
            First byte is shared exponent, remaining 32 bytes are mantissas
    Example: "19 40 20 10 08 ..."
    """
    with open(filepath, 'w') as f:
        for exp, mans in zip(output_exponents, output_mantissas):
            hex_values = [f"{exp:02x}"] + [f"{m:02x}" for m in mans]
            f.write(" ".join(hex_values) + "\n")


def main():
    """Generate golden test vectors and write to files."""
    # Configuration
    num_vectors = 8
    in_elements = 32
    seed = 42

    # Output directory (same as this script)
    out_dir = Path(__file__).parent

    # Generate test vectors
    print(f"Generating {num_vectors} vectors of {in_elements} GFP11e5 elements...")
    input_data, output_mans, output_exps = generate_test_vectors(
        num_vectors=num_vectors,
        in_elements=in_elements,
        seed=seed
    )

    # Write input file
    input_file = out_dir / "golden_input.txt"
    write_input_hex(input_file, input_data)
    print(f"Written: {input_file}")

    # Write output file
    output_file = out_dir / "golden_output.txt"
    write_output_hex(output_file, output_mans, output_exps)
    print(f"Written: {output_file}")

    # Print summary
    print(f"\nSummary:")
    print(f"  Input:  {num_vectors} lines x {in_elements} x 16-bit values")
    print(f"  Output: {num_vectors} lines x (1 exp + {in_elements} mantissas) x 8-bit values")

    # Print first vector as example
    print(f"\nExample (vector 0):")
    print(f"  Input (first 4):  {' '.join(f'{v:04x}' for v in input_data[0][:4])} ...")
    print(f"  Output exp: {output_exps[0]:02x}")
    print(f"  Output mans (first 4): {' '.join(f'{m:02x}' for m in output_mans[0][:4])} ...")


if __name__ == "__main__":
    main()
