#!/bin/bash
# Regenerate all golden files from corresponding left/right pairs

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

echo "Regenerating golden files for B=8, C=8, V=16"
echo "=============================================="
echo ""

# Loop through all 16 tiles
for i in {0..15}; do
    LEFT_FILE="$HEX_DIR/left_${i}.hex"
    RIGHT_FILE="$HEX_DIR/right_${i}.hex"
    GOLDEN_FILE="$HEX_DIR/golden_B8_C8_V16_${i}.hex"

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
    python "$REF_SCRIPT" \
        --B 8 --C 8 --V 16 \
        --left "$LEFT_FILE" \
        --right "$RIGHT_FILE" \
        --output "$GOLDEN_FILE" \
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
