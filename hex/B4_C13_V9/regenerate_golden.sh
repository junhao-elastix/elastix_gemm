#!/bin/bash
# Regenerate all golden files: for each row r and b in 0..3,
# golden_B4_C13_V9_r_b.hex from left_r.hex and right_r_b.hex

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
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

echo "Regenerating golden files for B=4, C=13, V=9 (16 rows x 4 right blocks)"
echo "=============================================="
echo ""

for i in {0..15}; do
    LEFT_FILE="$HEX_DIR/left_${i}.hex"
    if [ ! -f "$LEFT_FILE" ]; then
        echo "ERROR: $LEFT_FILE not found, skipping row $i"
        continue
    fi
    for b in {0..3}; do
        RIGHT_FILE="$HEX_DIR/right_${i}_${b}.hex"
        GOLDEN_FILE="$HEX_DIR/golden_B4_C13_V9_${i}_${b}.hex"
        if [ ! -f "$RIGHT_FILE" ]; then
            echo "ERROR: $RIGHT_FILE not found, skipping row $i block $b"
            continue
        fi
        echo "Generating row $i block $b: $GOLDEN_FILE"
        python "$REF_SCRIPT" \
            --B 4 --C 13 --V 9 \
            --left "$LEFT_FILE" \
            --right "$RIGHT_FILE" \
            --output "$GOLDEN_FILE" \
            2>&1 | grep -E "(Writing|Wrote|ERROR|Configuration)" || true
        if [ $? -eq 0 ]; then
            echo "  [OK] golden_${i}_${b}.hex"
        else
            echo "  [FAIL] golden_${i}_${b}.hex"
        fi
    done
    echo ""
done

echo "=============================================="
echo "Regeneration complete!"
echo ""
