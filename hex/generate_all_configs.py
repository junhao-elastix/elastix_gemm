#!/usr/bin/env python3
"""
Generate hex files for all compute_engine_2d test configurations.

Creates per-row hex files (left_r.hex, right_r.hex) and golden files
for each configuration needed by tb_compute_engine_2d.sv.

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
emulator_path = os.path.join(script_dir, '..', 'emulator', 'src', 'emulator')
sys.path.insert(0, emulator_path)

# Test configurations from tb_compute_engine_2d.sv
TEST_CONFIGS = [
    {'B': 1,  'C': 1,  'V': 1,  'name': 'B1_C1_V1'},
    {'B': 2,  'C': 2,  'V': 2,  'name': 'B2_C2_V2'},
    {'B': 4,  'C': 4,  'V': 4,  'name': 'B4_C4_V4'},
    {'B': 4,  'C': 8,  'V': 4,  'name': 'B4_C8_V4'},
    # {'B': 4,  'C': 13, 'V': 9,  'name': 'B4_C13_V9'},  # Already exists
    {'B': 4,  'C': 16, 'V': 8,  'name': 'B4_C16_V8'},
    {'B': 8,  'C': 8,  'V': 16, 'name': 'B8_C8_V16'},
    {'B': 16, 'C': 16, 'V': 4,  'name': 'B16_C16_V4'},
    {'B': 16, 'C': 16, 'V': 8,  'name': 'B16_C16_V8'},
]

NUM_ROWS = 16  # 16 parallel rows in 2D GEMM


def generate_config(B, C, V, name, force=False):
    """
    Generate hex files for a single configuration.
    
    Creates directory and generates:
    - 16 per-row files: left_r.hex, right_r.hex (r=0..15)
    - 16 golden files: golden_B{B}_C{C}_V{V}_{r}.hex
    - regenerate_golden.sh script
    """
    config_dir = os.path.join(script_dir, name)
    
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
    gen_script = os.path.join(script_dir, 'generate_nv_hex.py')
    ref_script = os.path.join(script_dir, 'hardware_gfp_reference.py')
    
    for row in range(NUM_ROWS):
        # Use different seed for each row to get different data
        seed = 42 + row * 1000
        
        print(f"\n  Row {row}: seed={seed}")
        
        # Generate left and right matrices
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
            print(f"    ERROR generating matrices: {result.stderr}")
            return False
        
        # Rename generated files to per-row names
        left_src = os.path.join(config_dir, 'left.hex')
        right_src = os.path.join(config_dir, 'right.hex')
        left_dst = os.path.join(config_dir, f'left_{row}.hex')
        right_dst = os.path.join(config_dir, f'right_{row}.hex')
        
        if os.path.exists(left_src):
            os.rename(left_src, left_dst)
        if os.path.exists(right_src):
            os.rename(right_src, right_dst)
        
        # Clean up float files
        for f in ['left_float.txt', 'right_float.txt']:
            fpath = os.path.join(config_dir, f)
            if os.path.exists(fpath):
                os.remove(fpath)
        
        # Generate golden reference for this row
        golden_dst = os.path.join(config_dir, f'golden_B{B}_C{C}_V{V}_{row}.hex')
        
        cmd = [
            'python', ref_script,
            '--B', str(B),
            '--C', str(C),
            '--V', str(V),
            '--left', left_dst,
            '--right', right_dst,
            '--output', golden_dst
        ]
        
        result = subprocess.run(cmd, capture_output=True, text=True)
        if result.returncode != 0:
            print(f"    ERROR generating golden: {result.stderr}")
            # Continue anyway - golden can be regenerated later
        else:
            print(f"    Generated: left_{row}.hex, right_{row}.hex, golden_{row}.hex")
    
    # Create regenerate_golden.sh script
    regen_script = os.path.join(config_dir, 'regenerate_golden.sh')
    with open(regen_script, 'w') as f:
        f.write(f'''#!/bin/bash
# Regenerate all golden files from corresponding left/right pairs

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

echo "Regenerating golden files for B={B}, C={C}, V={V}"
echo "=============================================="
echo ""

# Loop through all 16 tiles
for i in {{0..15}}; do
    LEFT_FILE="$HEX_DIR/left_${{i}}.hex"
    RIGHT_FILE="$HEX_DIR/right_${{i}}.hex"
    GOLDEN_FILE="$HEX_DIR/golden_B{B}_C{C}_V{V}_${{i}}.hex"

    # Check if input files exist
    if [ ! -f "$LEFT_FILE" ]; then
        echo "ERROR: $LEFT_FILE not found, skipping tile $i"
        continue
    fi
    if [ ! -f "$RIGHT_FILE" ]; then
        echo "ERROR: $RIGHT_FILE not found, skipping tile $i"
        continue
    fi

    echo "Generating tile $i: $GOLDEN_FILE"
    echo "  from $LEFT_FILE and $RIGHT_FILE"

    # Run the reference script
    python "$REF_SCRIPT" \\
        --B {B} --C {C} --V {V} \\
        --left "$LEFT_FILE" \\
        --right "$RIGHT_FILE" \\
        --output "$GOLDEN_FILE" \\
        2>&1 | grep -E "(Writing|Wrote|ERROR|Configuration)" || true

    if [ $? -eq 0 ]; then
        echo "  [OK] Successfully generated tile $i"
    else
        echo "  [FAIL] Failed to generate tile $i"
    fi
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
