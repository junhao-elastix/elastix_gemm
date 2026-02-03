#!/usr/bin/env python3
"""
Generate hex files for all compute_engine_2d test configurations.

This script generates test matrices and HARDWARE-ACCURATE golden references
for various B, C, V configurations. 

Per config, per row (r): one left_r.hex, four right_r_b.hex (b=0..3),
and four golden files golden_B{B}_C{C}_V{V}_{r}_{b}.hex.

Configurations from tb_compute_engine_2d.sv:
- B1_C1_V1   - Minimal smoke test
- B2_C2_V2   - Multi-batch, multi-column
- B4_C4_V4   - 4x4 test
- B4_C8_V4   - 8 columns
- B4_C13_V9  - Non-power-of-2 C and V (already exists)
- B4_C16_V8  - Full 16 columns
- B8_C8_V16  - 8 batches
- B16_C16_V4 - 16 batches, 16 cols
- B16_C16_V8 - Large: 16 batches, full cols

"""

import os
import sys
import subprocess
import argparse

# Add paths for imports
script_dir = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, script_dir)

# Test configurations from tb_compute_engine_2d.sv
TEST_CONFIGS = [
    {'B': 1,  'C': 1,  'V': 1,  'name': 'B1_C1_V1'},
    {'B': 2,  'C': 2,  'V': 2,  'name': 'B2_C2_V2'},
    {'B': 4,  'C': 4,  'V': 4,  'name': 'B4_C4_V4'},
    {'B': 4,  'C': 8,  'V': 4,  'name': 'B4_C8_V4'},
    {'B': 4,  'C': 13, 'V': 9,  'name': 'B4_C13_V9'},
    {'B': 4,  'C': 16, 'V': 8,  'name': 'B4_C16_V8'},
    {'B': 8,  'C': 8,  'V': 16, 'name': 'B8_C8_V16'},
    {'B': 16, 'C': 16, 'V': 4,  'name': 'B16_C16_V4'},
    {'B': 16, 'C': 16, 'V': 8,  'name': 'B16_C16_V8'},
    {'B': 1, 'C': 64, 'V': 2,  'name': 'B1_C64_V2'},
    {'B': 8, 'C': 64, 'V': 2, 'name': 'B8_C64_V2'},
    {'B': 1, 'C': 32, 'V': 4, 'name': 'B1_C32_V4'},
]

NUM_ROWS = 16   # 16 parallel rows in 2D GEMM
NUM_RIGHT = 4   # 4 right matrices per row (b=0..3)


def generate_config(B, C, V, name, force=False):
    """
    Generate hex files for a single configuration.

    Per row r (0..15):
    - One left: left_{r}.hex
    - Four right: right_{r}_0.hex .. right_{r}_3.hex
    - Four golden: golden_B{B}_C{C}_V{V}_{r}_0.hex .. golden_B{B}_C{C}_V{V}_{r}_3.hex
    Also creates regenerate_golden.sh.

    """
    config_dir = os.path.join(script_dir, f"{name}")

    # Check if directory exists
    if os.path.exists(config_dir) and not force:
        print(f"[SKIP] {name} already exists (use --force to regenerate)")
        return True

    # Create directory
    os.makedirs(config_dir, exist_ok=True)
    print(f"\n{'='*60}")
    print(f"Generating {name}: B={B}, C={C}, V={V}")
    print(f"{'='*60}")

    # Validate parameters
    if B * V > 128:
        print(f"  ERROR: B*V = {B*V} exceeds 128")
        return False
    if C * V > 128:
        print(f"  ERROR: C*V = {C*V} exceeds 128")
        return False

    print(f"  Directory: {config_dir}")
    print(f"  Matrix A: {B} x {128*V} (uses {B*V} NVs)")
    print(f"  Matrix B: {128*V} x {C} (uses {C*V} NVs)")
    print(f"  Output:   {B} x {C} = {B*C} results per row")

    # Generate per-row hex files using generate_nv_hex.py
    # NOTE: generate_nv_hex.py doesn't have duplicates, so we use the original
    gen_script = os.path.join(script_dir, 'generate_nv_hex.py')
    ref_script = os.path.join(script_dir, 'hardware_gfp_reference.py')

    for row in range(NUM_ROWS):
        # Base seed for this row; vary per right block
        seed_base = 42 + row * 1000
        print(f"\n  Row {row}: seeds {seed_base}..{seed_base + (NUM_RIGHT - 1) * 100}")

        # First run: left_{row}.hex and right_{row}_0.hex
        cmd = [
            'python', gen_script,
            '--B', str(B),
            '--C', str(C),
            '--V', str(V),
            '--seed', str(seed_base),
            '--output-dir', config_dir
        ]
        result = subprocess.run(cmd, capture_output=True, text=True)
        if result.returncode != 0:
            print(f"    ERROR generating matrices: {result.stderr}")
            return False

        left_dst = os.path.join(config_dir, f'left_{row}.hex')
        right_0_dst = os.path.join(config_dir, f'right_{row}_0.hex')
        left_src = os.path.join(config_dir, 'left.hex')
        right_src = os.path.join(config_dir, 'right.hex')
        if os.path.exists(left_src):
            os.rename(left_src, left_dst)
        if os.path.exists(right_src):
            os.rename(right_src, right_0_dst)
        for f in ['left_float.txt', 'right_float.txt']:
            fpath = os.path.join(config_dir, f)
            if os.path.exists(fpath):
                os.remove(fpath)

        # Runs 2..NUM_RIGHT: only keep right -> right_{row}_1.hex .. right_{row}_3.hex
        for b in range(1, NUM_RIGHT):
            seed = seed_base + b * 100
            cmd = [
                'python', gen_script,
                '--B', str(B),
                '--C', str(C),
                '--V', str(V),
                '--seed', str(seed),
                '--output-dir', config_dir
            ]
            result = subprocess.run(cmd, capture_output=True, text=True)
            if result.returncode != 0:
                print(f"    ERROR generating right_{row}_{b}: {result.stderr}")
                return False
            right_b_dst = os.path.join(config_dir, f'right_{row}_{b}.hex')
            if os.path.exists(right_src):
                os.rename(right_src, right_b_dst)
            if os.path.exists(left_src):
                os.remove(left_src)
            for f in ['left_float.txt', 'right_float.txt']:
                fpath = os.path.join(config_dir, f)
                if os.path.exists(fpath):
                    os.remove(fpath)

        # Golden for each (row, b): left_{row}.hex x right_{row}_{b}.hex
        # NOTE: Using HARDWARE-ACCURATE algorithm via hardware_gfp_reference.py
        for b in range(NUM_RIGHT):
            right_b_path = os.path.join(config_dir, f'right_{row}_{b}.hex')
            golden_dst = os.path.join(config_dir, f'golden_B{B}_C{C}_V{V}_{row}_{b}.hex')
            cmd = [
                'python', ref_script,
                '--B', str(B),
                '--C', str(C),
                '--V', str(V),
                '--left', left_dst,
                '--right', right_b_path,
                '--output', golden_dst
            ]
            result = subprocess.run(cmd, capture_output=True, text=True)
            if result.returncode != 0:
                print(f"    ERROR generating golden_{row}_{b}: {result.stderr}")
            else:
                print(f"    Golden {row}_{b}: {os.path.basename(golden_dst)}")

    # Create regenerate_golden.sh script (per row r: left_r.hex x right_r_b.hex -> golden_*_r_b.hex)
    regen_script = os.path.join(config_dir, 'regenerate_golden.sh')
    with open(regen_script, 'w') as f:
        f.write(f'''#!/bin/bash
# Regenerate all golden files: for each row r and b in 0..3,
# golden_B{B}_C{C}_V{V}_r_b.hex from left_r.hex and right_r_b.hex
#
# NOTE: This uses the HARDWARE-ACCURATE algorithm via hardware_gfp_reference.py

SCRIPT_DIR="$(cd "$(dirname "${{BASH_SOURCE[0]}}")" && pwd)"
HEX_DIR="$SCRIPT_DIR"
REF_SCRIPT="$SCRIPT_DIR/../hardware_gfp_reference.py"
# Check if reference script exists
if [ ! -f "$REF_SCRIPT" ]; then
    echo "ERROR: hardware_gfp_reference.py not found at $REF_SCRIPT"
    exit 1
fi

# Activate conda environment
eval "$(conda shell.bash hook)"
conda activate elastix

echo "Regenerating golden files for B={B}, C={C}, V={V} (16 rows x 4 right blocks)"
echo "Using HARDWARE-ACCURATE algorithm (hardware_gfp_reference.py)"
echo "=============================================="
echo ""

for i in {{0..15}}; do
    LEFT_FILE="$HEX_DIR/left_${{i}}.hex"
    if [ ! -f "$LEFT_FILE" ]; then
        echo "ERROR: $LEFT_FILE not found, skipping row $i"
        continue
    fi
    for b in {{0..3}}; do
        RIGHT_FILE="$HEX_DIR/right_${{i}}_${{b}}.hex"
        GOLDEN_FILE="$HEX_DIR/golden_B{B}_C{C}_V{V}_${{i}}_${{b}}.hex"
        if [ ! -f "$RIGHT_FILE" ]; then
            echo "ERROR: $RIGHT_FILE not found, skipping row $i block $b"
            continue
        fi
        echo "Generating row $i block $b: $GOLDEN_FILE"
        python "$REF_SCRIPT" \\
            --B {B} --C {C} --V {V} \\
            --left "$LEFT_FILE" \\
            --right "$RIGHT_FILE" \\
            --output "$GOLDEN_FILE" \\
            2>&1 | grep -E "(Writing|Wrote|ERROR|Configuration)" || true
        if [ $? -eq 0 ]; then
            echo "  [OK] golden_${{i}}_${{b}}.hex"
        else
            echo "  [FAIL] golden_${{i}}_${{b}}.hex"
        fi
    done
    echo ""
done

echo "=============================================="
echo "Regeneration complete!"
echo ""
''')
    os.chmod(regen_script, 0o755)

    print(f"\n  Created: {regen_script}")
    print(f"  [OK] Configuration {name} complete!") 

    return True


def main():
    parser = argparse.ArgumentParser(description='Generate hex files for all test configurations')
    parser.add_argument('--force', action='store_true', help='Regenerate existing configurations')
    parser.add_argument('--config', type=str, default=None, help='Generate only specific config (e.g., B4_C4_V4)')
    args = parser.parse_args()

    print("="*60)
    print("Hex File Generator for compute_engine_2d Tests")
    print("="*60)
    print(f"Script directory: {script_dir}")
    print(f"Number of configurations: {len(TEST_CONFIGS)}")
    print(f"Rows per configuration: {NUM_ROWS}")

    # Activate conda environment
    print("\nActivating elastix conda environment...")

    success_count = 0
    fail_count = 0
    skip_count = 0

    for config in TEST_CONFIGS:
        if args.config and config['name'] != args.config:
            continue

        result = generate_config(
            config['B'], config['C'], config['V'], config['name'],
            force=args.force
        )

        if result is True:
            success_count += 1
        elif result is False:
            fail_count += 1
        else:
            skip_count += 1

    print("\n" + "="*60)
    print("SUMMARY")
    print("="*60)
    print(f"  Success: {success_count}")
    print(f"  Failed:  {fail_count}")
    print(f"  Skipped: {skip_count}")
    print("="*60)

    return 0 if fail_count == 0 else 1


if __name__ == '__main__':
    sys.exit(main())
