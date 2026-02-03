#!/usr/bin/env python3
"""
Common Utilities for GFP Hex File Generation and Validation

This module provides the canonical implementations of common utilities used across
the hex file generation and validation scripts. All other modules should import
from this file to avoid code duplication.

Functions:
    - parse_hex_line(): Parse a single hex line to tensor
    - load_hex_file(): Load complete 528-line hex file
    - decode_exponents(): Decode exponent data to 128x4 matrix
    - decode_mantissas(): Decode mantissa data to 128x128 matrix
    - parse_golden_filename(): Extract B, C, V from golden filename
    - load_golden_file(): Load golden hex file with FP16 results
    - create_bcv_parser(): Create argparse parser for B, C, V parameters
    - get_emulator_path(): Get path to GFP emulator library

Memory Layout (Fixed):
    - Total 528 lines per tensor
    - Lines 0-15: Exponent data (512 exponents, 32 per line)
    - Lines 16-527: Mantissa data (16,384 mantissas, 32 per line)
    - Each NV = 128 elements = 4 groups of 32 elements each
    - Block size = 128 NVs always
"""

import torch
import re
import os
import sys
import numpy as np
import argparse


# =============================================================================
# Path Utilities
# =============================================================================

def get_script_dir():
    """Get the directory containing this script."""
    if '__file__' in globals():
        return os.path.dirname(os.path.abspath(__file__))
    return os.getcwd()


def get_emulator_path():
    """
    Get path to GFP emulator library.

    Returns:
        str: Path to emulator directory
    """
    script_dir = get_script_dir()
    return os.path.join(script_dir, '..', 'emulator', 'src', 'emulator')


def setup_emulator_import():
    """
    Add emulator path to sys.path for importing GFP classes.

    Returns:
        bool: True if emulator path was added, False if already present
    """
    emulator_path = get_emulator_path()
    if emulator_path not in sys.path:
        sys.path.insert(0, emulator_path)
        return True
    return False


# =============================================================================
# Hex File Parsing
# =============================================================================

def parse_hex_line(hex_line: str) -> torch.Tensor:
    """
    Parse a single hex line and convert to tensor of bytes.

    Hex file byte ordering: [byte_31] [byte_30] ... [byte_1] [byte_0]
    Display order (L->R): MSB/Left -> LSB/Right
    Element order: byte_0 is rightmost, corresponds to element [0]

    Args:
        hex_line: String containing space-separated hex bytes (e.g., "0a 0a 09...")

    Returns:
        torch.Tensor: Tensor of raw byte values as uint8, reversed to match element order
    """
    hex_line = hex_line.strip()
    if not hex_line:
        return torch.zeros(32, dtype=torch.uint8)

    byte_values = []
    for hex_byte in hex_line.split():
        byte_values.append(int(hex_byte, 16))

    if len(byte_values) < 32:
        byte_values.extend([0] * (32 - len(byte_values)))

    # Hex file already shows bytes in correct order [0->31]
    # No reversal needed - hardware reads bytes in forward order
    byte_values_truncated = byte_values[:32]

    return torch.tensor(byte_values_truncated, dtype=torch.uint8)


def load_hex_file(file_path: str) -> tuple[torch.Tensor, torch.Tensor]:
    """
    Load a complete hex file and separate into exponent and mantissa data.

    Args:
        file_path: Path to the hex file

    Returns:
        tuple: (exponent_data, mantissa_data) where:
               - exponent_data: [16, 32] uint8 tensor
               - mantissa_data: [512, 32] uint8 tensor
    """
    with open(file_path, 'r') as f:
        lines = f.readlines()

    if len(lines) != 528:
        raise ValueError(f"Expected 528 lines, got {len(lines)}")

    # Parse all lines to tensors
    parsed_lines = [parse_hex_line(line) for line in lines]

    # Separate exponent data (lines 0-15)
    exp_data = torch.stack(parsed_lines[:16])  # [16, 32]

    # Separate mantissa data (lines 16-527)
    man_data = torch.stack(parsed_lines[16:528])  # [512, 32]

    return exp_data, man_data


# =============================================================================
# GFP Data Decoding
# =============================================================================

def decode_exponents(exponent_data: torch.Tensor) -> torch.Tensor:
    """
    Decode exponent data from memory format into a 128x4 exponent matrix.

    The exponent layout is simple: mantissa line N uses exponent index N (1:1 mapping).
    Each mantissa line (group of 32 elements) has one shared exponent.
    - 512 mantissa lines -> 512 exponents
    - 512 exponents = 128 NVs x 4 groups per NV

    Args:
        exponent_data: [16, 32] tensor of raw exponent bytes (uint8)

    Returns:
        torch.Tensor: [128, 4] tensor of exponents (uint8, one per group per NV)
    """
    # Flatten and ensure we have the right number of exponents
    flat_exps = exponent_data.reshape(-1)  # Keep as torch tensor, shape [512]
    if flat_exps.shape[0] != 128 * 4:
        raise ValueError(f"Unexpected exponent count: {flat_exps.shape[0]}")

    # Simple 1:1 mapping: reshape flat exponents into [128 NVs, 4 groups per NV]
    # Exponent index i corresponds to mantissa line i
    # Ensure dtype is uint8 (5-bit exponents padded to 8-bit)
    exponents = flat_exps.reshape(128, 4)

    # Mask to 5 bits (exponents are only 5-bit, padded to 8-bit)
    exponents = exponents & 0x1F  # Keep only the 5 LSBs
    exponents = exponents.to(torch.uint8)

    return exponents


def decode_mantissas(mantissa_data: torch.Tensor) -> np.ndarray:
    """
    Decode mantissa data from memory format into a 128x128 mantissa matrix.

    Mantissa layout: Each row uses 4 lines (one per group of 32 elements).
    Each line contains 32 bytes representing 32 mantissa values.
    Raw bytes are 8-bit two's complement signed integers.

    Args:
        mantissa_data: [512, 32] tensor of raw mantissa bytes

    Returns:
        np.ndarray: [128, 128] array of signed 8-bit mantissa values in range [-128, 127]
    """
    mantissa_matrix = np.zeros((128, 128), dtype=np.int16)

    for row_idx in range(128):
        line_start = row_idx * 4  # Each row uses 4 lines

        for group_idx in range(4):
            line_idx = line_start + group_idx
            line = mantissa_data[line_idx].numpy()

            # Convert each byte from 8-bit two's complement to signed int
            signed = np.array(line, dtype=np.int16)
            signed[signed >= 128] -= 256  # Convert to signed range [-128, 127]

            # Use full 8-bit mantissa (no shifting needed)
            mantissas = signed

            # Store in correct column range
            col_start = group_idx * 32
            col_end = col_start + 32
            mantissa_matrix[row_idx, col_start:col_end] = mantissas

    return mantissa_matrix


# =============================================================================
# Golden File Utilities
# =============================================================================

def parse_golden_filename(filename: str) -> tuple[int, int, int]:
    """
    Extract B, C, V parameters from golden filename.

    Args:
        filename: Path to golden file (e.g., "golden_B16_C16_V8.hex")

    Returns:
        tuple: (B, C, V) as integers

    Raises:
        ValueError: If filename doesn't match expected pattern
    """
    # Extract just the basename
    basename = os.path.basename(filename)

    # Match pattern: golden_B(\d+)_C(\d+)_V(\d+)(_\d+)?\.hex
    # Supports both: golden_B4_C4_V32.hex and golden_B4_C4_V32_0.hex
    pattern = r'golden_B(\d+)_C(\d+)_V(\d+)(?:_(\d+))?\.hex'
    match = re.match(pattern, basename)

    if not match:
        raise ValueError(f"Golden filename '{basename}' doesn't match expected pattern 'golden_B<num>_C<num>_V<num>.hex' or 'golden_B<num>_C<num>_V<num>_<tile>.hex'")

    B = int(match.group(1))
    C = int(match.group(2))
    V = int(match.group(3))

    return B, C, V


def load_golden_file(filepath: str) -> np.ndarray:
    """
    Load golden hex file containing FP16 results.

    Each line contains one 4-digit hex value (16-bit FP16).

    Args:
        filepath: Path to golden hex file

    Returns:
        np.ndarray: Array of uint16 FP16 values
    """
    results = []

    with open(filepath, 'r') as f:
        for line_num, line in enumerate(f, 1):
            line = line.strip()
            if not line:
                continue  # Skip empty lines

            try:
                # Parse 4-digit hex value
                value = int(line, 16)
                if value > 0xFFFF:
                    raise ValueError(f"Value 0x{value:x} exceeds 16-bit range")
                results.append(value)
            except ValueError as e:
                raise ValueError(f"Error parsing line {line_num} in {filepath}: {e}")

    return np.array(results, dtype=np.uint16)


# =============================================================================
# Argument Parsing Utilities
# =============================================================================

def create_bcv_parser(description: str = "GFP Matrix utility with configurable dimensions") -> argparse.ArgumentParser:
    """
    Create an argparse parser for B, C, V parameters.

    Args:
        description: Description for the parser

    Returns:
        argparse.ArgumentParser: Configured parser with B, C, V arguments
    """
    parser = argparse.ArgumentParser(
        description=description,
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python <script>.py --B 2 --C 4 --V 1  # Matrix A: 2x128, Matrix B: 128x4, Result: 2x4
  python <script>.py --B 1 --C 1 --V 2  # Matrix A: 1x256, Matrix B: 256x1, Result: 1x1

Constraints:
  - BxV <= 128 (Matrix A constraint)
  - CxV <= 128 (Matrix B constraint)
  - Hex files always contain full 128x128 block (528 lines)
        """
    )

    parser.add_argument('--B', type=int, default=1,
                       help='Number of rows in Matrix A (default: 1)')
    parser.add_argument('--C', type=int, default=1,
                       help='Number of columns in Matrix B (default: 1)')
    parser.add_argument('--V', type=int, default=1,
                       help='Inner dimension multiplier 128xV (default: 1)')

    return parser


def validate_bcv_constraints(B: int, C: int, V: int) -> bool:
    """
    Validate B, C, V constraints for GFP matrices.

    Args:
        B: Number of rows in Matrix A
        C: Number of columns in Matrix B
        V: Inner dimension multiplier

    Returns:
        bool: True if constraints are satisfied

    Raises:
        ValueError: If constraints are violated
    """
    if B * V > 128:
        raise ValueError(f"Matrix A constraint violated: BxV = {B}x{V} = {B*V} > 128")
    if C * V > 128:
        raise ValueError(f"Matrix B constraint violated: CxV = {C}x{V} = {C*V} > 128")
    return True


# =============================================================================
# GFP-to-Float Conversion
# =============================================================================

def convert_gfp_to_float(mantissa_data: np.ndarray, exp_data: np.ndarray,
                         exp_bias: int = 15, group_size: int = 32) -> np.ndarray:
    """
    Convert GFP matrix (mantissas + exponents) to floating point matrix.

    Each element is converted using: value = mantissa * 2^(exponent - bias)

    Args:
        mantissa_data: [128, 128] array of signed mantissa values (8-bit)
        exp_data: [128, 4] array of exponents (5-bit, one per group per row)
        exp_bias: Exponent bias (default: 15 for 5-bit exponent)
        group_size: Elements per group (default: 32)

    Returns:
        np.ndarray: [128, 128] float matrix
    """
    float_matrix = np.zeros((128, 128), dtype=np.float64)

    for r in range(128):
        for c in range(128):
            mantissa_val = int(mantissa_data[r, c])

            # Get exponent for this element's group
            group_idx = c // group_size
            exp_val = int(exp_data[r, group_idx])

            # Convert to float using GFP formula
            if exp_val == 0:
                float_matrix[r, c] = 0.0
            else:
                exponent = exp_val - exp_bias
                scale_factor = 2.0 ** exponent
                float_matrix[r, c] = mantissa_val * scale_factor

    return float_matrix
