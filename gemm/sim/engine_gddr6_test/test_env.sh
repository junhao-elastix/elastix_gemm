#!/bin/bash
# Test environment for GDDR6 simulation

echo "========================================"
echo "Checking GDDR6 Simulation Environment"
echo "========================================"
echo ""

# Check ACE_INSTALL_DIR
if [ -z "$ACE_INSTALL_DIR" ]; then
    echo "❌ ACE_INSTALL_DIR not set"
    echo "   Please run: source /opt/achronix/ace/10.3.1/Achronix/ace/scripts/setup.bash"
    exit 1
else
    echo "✓ ACE_INSTALL_DIR = $ACE_INSTALL_DIR"
fi

# Check LD_LIBRARY_PATH
if [ -n "$LD_LIBRARY_PATH" ]; then
    echo "⚠️  LD_LIBRARY_PATH is set (may cause issues with Riviera)"
    echo "   Consider: unset LD_LIBRARY_PATH"
else
    echo "✓ LD_LIBRARY_PATH is not set"
fi

# Check ACX libraries exist
ACX_LIB_S7T="$ACE_INSTALL_DIR/libraries/speedster7t"
if [ -f "$ACX_LIB_S7T/common/acx_floating_point.sv" ]; then
    echo "✓ ACX floating point library found"
else
    echo "❌ ACX floating point library NOT found at $ACX_LIB_S7T/common/"
fi

if [ -f "$ACX_LIB_S7T/common/acx_integer.sv" ]; then
    echo "✓ ACX integer library found"
else
    echo "❌ ACX integer library NOT found at $ACX_LIB_S7T/common/"
fi

# Check GDDR reference design
GDDR_REF_DIR="../../../gddr_ref_design"
if [ -d "$GDDR_REF_DIR/src/include" ]; then
    echo "✓ GDDR6 includes found"
else
    echo "❌ GDDR6 includes NOT found"
fi

if [ -d "$GDDR_REF_DIR/src/tb/gddr_model" ]; then
    echo "✓ GDDR6 models found"
else
    echo "❌ GDDR6 models NOT found"
fi

# Check hex test files
if [ -f "/home/workstation/elastix_gemm/hex/left.hex" ]; then
    echo "✓ left.hex test data found"
else
    echo "❌ left.hex test data NOT found"
fi

if [ -f "/home/workstation/elastix_gemm/hex/right.hex" ]; then
    echo "✓ right.hex test data found"
else
    echo "❌ right.hex test data NOT found"
fi

echo ""
echo "========================================"
echo "Environment check complete!"
echo "========================================"