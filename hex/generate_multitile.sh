#!/bin/bash
#
# Generate golden reference files for multi-tile tests
# Multi-tile execution is transparent to the host - results are identical to single-tile
# The _2T suffix indicates col_en=0x000003 (2 tiles enabled for parallel execution)

echo "========================================================================"
echo "Generating Multi-Tile Golden References"
echo "========================================================================"
echo ""
echo "Note: Multi-tile execution produces identical results to single-tile."
echo "The _2T suffix indicates parallel execution on 2 tiles (col_en=0x000003)"
echo ""

# Multi-tile test configurations (from tb_engine_top.sv lines 211-214)
multi_tile_configs=(
    "2 4 16"    # B2_C4_V16_2T
    "4 8 8"     # B4_C8_V8_2T
    "8 32 2"    # B8_C32_V2_2T
    "16 16 4"   # B16_C16_V4_2T
)

# Generate golden references
for config in "${multi_tile_configs[@]}"; do
    IFS=' ' read -r B C V <<< "${config}"
    echo "Generating golden for B${B}_C${C}_V${V}_2T..."

    # Generate using hardware_gfp_reference.py (single-tile computation)
    python hardware_gfp_reference.py --B ${B} --C ${C} --V ${V}

    # Rename to _2T suffix
    mv golden_B${B}_C${C}_V${V}.hex golden_B${B}_C${C}_V${V}_2T.hex
    mv golden_B${B}_C${C}_V${V}_emu_NEW.hex golden_B${B}_C${C}_V${V}_2T_emu_NEW.hex

    echo "  ✓ Created golden_B${B}_C${C}_V${V}_2T.hex"
    echo ""
done

echo "========================================================================"
echo "Multi-tile golden generation complete!"
echo "========================================================================"
echo ""
echo "Generated files:"
ls -lh golden_*_2T.hex
echo ""
echo "These files represent the expected results for 2-tile parallel execution."
echo "Results are identical to single-tile computation - multi-tile is transparent."
