#!/usr/bin/env python3
"""
Validation Script for GFP GEMM Golden Files

This script validates whether a golden hex file is correctly produced from
a given left.hex and right.hex pair using the HARDWARE-ACCURATE GFP computation.

The hardware-accurate algorithm matches the RTL implementation in compute_engine.sv
and gfp8_nv_dot.sv, including:
- Group-by-group integer accumulation
- Exponent-aligned integer summation
- V-loop incremental accumulation
- FP16 conversion with overflow clamping

Usage:
    python validate_new.py left.hex right.hex golden_B16_C16_V8.hex
"""

import sys
import os
import struct
import numpy as np

# Import common utilities from hex_utils (canonical source)
from hex_utils import (
    load_hex_file,
    decode_exponents,
    decode_mantissas,
    parse_golden_filename,
    load_golden_file,
)

# Import hardware-accurate compute engine
# Note: We import from the _new version if available, otherwise original
try:
    from hex.hardware_gfp_reference import HardwareGFPCompute
except ImportError:
    from hardware_gfp_reference import HardwareGFPCompute


def validate_golden(left_hex, right_hex, golden_hex):
    """
    Main validation function using HARDWARE-ACCURATE algorithm.

    Args:
        left_hex: Path to left.hex file
        right_hex: Path to right.hex file
        golden_hex: Path to golden_*.hex file

    Returns:
        int: Exit code (0=success, 1=mismatch, 2=error)
    """
    try:
        # Step 1: Parse B, C, V from golden filename
        print("=" * 80)
        print("GFP GEMM Golden File Validation (HARDWARE-ACCURATE)")
        print("=" * 80)
        print(f"\n1. Parsing golden filename...")
        B, C, V = parse_golden_filename(golden_hex)
        print(f"   Extracted parameters: B={B}, C={C}, V={V}")

        # Validate constraints
        if B * V > 128:
            print(f"   ERROR: B x V = {B} x {V} = {B*V} > 128 (constraint violated)")
            return 2
        if C * V > 128:
            print(f"   ERROR: C x V = {C} x {V} = {C*V} > 128 (constraint violated)")
            return 2
        print(f"   [OK] Constraints satisfied (B x V={B*V} <= 128, C x V={C*V} <= 128)")

        # Step 2: Load input matrices
        print(f"\n2. Loading input matrices...")
        if not os.path.exists(left_hex):
            print(f"   ERROR: File not found: {left_hex}")
            return 2
        if not os.path.exists(right_hex):
            print(f"   ERROR: File not found: {right_hex}")
            return 2

        print(f"   Loading {left_hex}...")
        exp_left_raw, man_left_raw = load_hex_file(left_hex)
        left_exp_torch = decode_exponents(exp_left_raw)
        left_exp = left_exp_torch.numpy()
        left_mant = decode_mantissas(man_left_raw)

        print(f"   Loading {right_hex}...")
        exp_right_raw, man_right_raw = load_hex_file(right_hex)
        right_exp_torch = decode_exponents(exp_right_raw)
        right_exp = right_exp_torch.numpy()
        right_mant = decode_mantissas(man_right_raw)

        print(f"   [OK] Left matrix: mantissa {left_mant.shape}, exponents {left_exp.shape}")
        print(f"   [OK] Right matrix: mantissa {right_mant.shape}, exponents {right_exp.shape}")

        # Step 3: Compute expected results using HARDWARE-ACCURATE algorithm
        print(f"\n3. Computing expected results using HARDWARE-ACCURATE algorithm...")
        print(f"   Configuration: B={B}, C={C}, V={V} -> {B*C} output elements")
        hw_compute = HardwareGFPCompute(exp_bits=5, exp_bias=15, group_size=32)
        expected_results = hw_compute.compute_gemm_with_bcv(
            left_mant, left_exp, right_mant, right_exp, B, C, V
        )
        print(f"   [OK] Computed {len(expected_results)} expected results")

        # Step 4: Load golden file
        print(f"\n4. Loading golden file...")
        if not os.path.exists(golden_hex):
            print(f"   ERROR: File not found: {golden_hex}")
            return 2

        golden_results = load_golden_file(golden_hex)
        print(f"   [OK] Loaded {len(golden_results)} golden results")

        # Step 5: Compare results
        print(f"\n5. Comparing results...")
        print("=" * 80)

        if len(expected_results) != len(golden_results):
            print(f"   ERROR: Length mismatch!")
            print(f"   Expected: {len(expected_results)} results (B x C = {B} x {C} = {B*C})")
            print(f"   Golden:   {len(golden_results)} results")
            return 2

        # Element-wise comparison
        matches = (expected_results == golden_results)
        num_matches = np.sum(matches)
        num_mismatches = len(expected_results) - num_matches
        match_rate = 100.0 * num_matches / len(expected_results)

        print(f"   Total results: {len(expected_results)} (B x C = {B} x {C})")
        print(f"   Exact matches: {num_matches}/{len(expected_results)} ({match_rate:.1f}%)")

        if num_mismatches == 0:
            print(f"\n   [PASS] VALIDATION PASSED: All {len(expected_results)} values match!")
            print("=" * 80)
            return 0
        else:
            print(f"\n   [FAIL] VALIDATION FAILED: {num_mismatches} mismatches found")
            print("\n   First 10 mismatches:")
            print("   " + "-" * 76)
            print(f"   {'Index':<6} {'Row':<4} {'Col':<4} {'Expected (hex)':<14} {'Expected (float)':<16} {'Golden (hex)':<14} {'Golden (float)':<16} {'Diff':<10}")
            print("   " + "-" * 76)

            mismatch_count = 0
            for i in range(len(expected_results)):
                if not matches[i]:
                    row = i // C
                    col = i % C

                    # Convert to float for display
                    expected_fp16 = np.frombuffer(struct.pack('<H', expected_results[i]), dtype=np.float16)[0]
                    golden_fp16 = np.frombuffer(struct.pack('<H', golden_results[i]), dtype=np.float16)[0]
                    diff = abs(expected_fp16 - golden_fp16)

                    print(f"   {i:<6} {row:<4} {col:<4} 0x{expected_results[i]:04x}      {expected_fp16:14.6e}  0x{golden_results[i]:04x}      {golden_fp16:14.6e}  {diff:.6e}")

                    mismatch_count += 1
                    if mismatch_count >= 10:
                        break

            if num_mismatches > 10:
                print(f"   ... and {num_mismatches - 10} more mismatches")

            print("=" * 80)
            return 1

    except Exception as e:
        print(f"\n   ERROR: {type(e).__name__}: {e}")
        import traceback
        traceback.print_exc()
        return 2


def main():
    """Command-line interface."""
    if len(sys.argv) != 4:
        print("Usage: python validate_new.py <left.hex> <right.hex> <golden_B*_C*_V*.hex>")
        print("\nThis script validates golden files using the HARDWARE-ACCURATE algorithm.")
        print("The hardware-accurate algorithm matches the RTL implementation.")
        print("\nExample:")
        print("  python validate_new.py hex/left.hex hex/right.hex hex/golden_B16_C16_V8.hex")
        sys.exit(2)

    left_hex = sys.argv[1]
    right_hex = sys.argv[2]
    golden_hex = sys.argv[3]

    exit_code = validate_golden(left_hex, right_hex, golden_hex)
    sys.exit(exit_code)


if __name__ == '__main__':
    main()
