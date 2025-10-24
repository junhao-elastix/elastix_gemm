#!/bin/bash

# Clean old files
rm *.hex *.txt

test_configs=(
    "1 1 1"
    "2 2 2"
    "4 4 4"
    "2 2 64"
    "4 4 32"
    "8 8 16"
    "16 16 8"
    "1 128 1"
    "128 1 1"
    "1 1 128"
)

# Generate reference matrices ONCE (full 128 NVs each)
echo "=========================================================================="
echo "Step 1: Generating reference matrices (left.hex, right.hex)"
echo "=========================================================================="
python generate_nv_hex.py --B 128 --C 128 --V 1 --seed 1234 --std 0.002

echo ""
echo "=========================================================================="
echo "Step 2: Generating golden references for all configurations"
echo "=========================================================================="

# Generate golden references for all configurations
for config in "${test_configs[@]}"; do
    IFS=' ' read -r B C V <<< "${config}"
    echo ""
    echo "Generating golden for config: B=${B}, C=${C}, V=${V}"
    python hardware_gfp_reference.py --B ${B} --C ${C} --V ${V}
done

echo ""
echo "=========================================================================="
echo "Generation complete!"
echo "  - Reference matrices: left.hex, right.hex (128 NVs each)"
echo "  - Golden files: golden_B*_C*_V*.hex (hardware-accurate)"
echo "  - Golden files: golden_B*_C*_V*_emu_NEW.hex (emulator-based)"
echo "=========================================================================="