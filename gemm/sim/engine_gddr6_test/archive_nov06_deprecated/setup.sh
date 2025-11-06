#!/bin/bash
# Setup script for GEMM Engine GDDR6 simulation
# Verifies dependencies and environment

GDDR_REF_DIR="../../../gddr_ref_design"
GDDR_INC_DIR="${GDDR_REF_DIR}/src/include"
GDDR_MODEL_DIR="${GDDR_REF_DIR}/src/tb/gddr_model"

echo "=========================================="
echo "GEMM Engine GDDR6 Simulation Setup"
echo "=========================================="

# Check if GDDR reference design exists
if [ ! -d "$GDDR_INC_DIR" ]; then
    echo "ERROR: GDDR6 reference design includes not found at $GDDR_INC_DIR"
    exit 1
fi

if [ ! -d "$GDDR_MODEL_DIR" ]; then
    echo "ERROR: GDDR6 models not found at $GDDR_MODEL_DIR"
    exit 1
fi

echo ""
echo "Verifying GDDR6 dependencies..."
echo "  [OK] Include directory: $GDDR_INC_DIR"
echo "  [OK] Model directory: $GDDR_MODEL_DIR"

# Verify test data exists
echo ""
echo "Checking test data..."
if [ -f "/home/dev/Dev/elastix_gemm/hex/left.hex" ]; then
    echo "  ✓ left.hex found"
else
    echo "  ✗ left.hex NOT found"
fi

if [ -f "/home/dev/Dev/elastix_gemm/hex/right.hex" ]; then
    echo "  ✓ right.hex found"
else
    echo "  ✗ right.hex NOT found"
fi

if [ -f "/home/dev/Dev/elastix_gemm/hex/golden_B2_C2_V2.hex" ]; then
    echo "  ✓ golden_B2_C2_V2.hex found"
else
    echo "  ✗ golden_B2_C2_V2.hex NOT found"
fi

# Check environment
echo ""
echo "Checking environment..."
if [ -z "$ACE_INSTALL_DIR" ]; then
    echo "  ✗ ACE_INSTALL_DIR not set"
    echo "    Run: source /tools/Achronix/Acex/ACE-9.2/Achronix_ac7t1500_fpga_only/setup.bash"
else
    echo "  ✓ ACE_INSTALL_DIR = $ACE_INSTALL_DIR"
fi

if [ -n "$LD_LIBRARY_PATH" ]; then
    echo "  ✗ LD_LIBRARY_PATH is set (Riviera requires it to be unset)"
    echo "    Run: unset LD_LIBRARY_PATH"
else
    echo "  ✓ LD_LIBRARY_PATH is not set"
fi

echo ""
echo "=========================================="
echo "Setup complete!"
echo "=========================================="
echo ""
echo "Next steps:"
echo "  1. Source ACE tools if not already done"
echo "  2. Unset LD_LIBRARY_PATH if set"
echo "  3. Run: make clean && make run"
echo ""

