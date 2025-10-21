#!/bin/bash
# GEMM Engine GDDR6 Simulation - Quick Run Script

set -e  # Exit on error

echo "========================================================================"
echo "GEMM Engine GDDR6 Simulation"
echo "========================================================================"
echo ""

# Check current directory
if [ ! -f "tb_engine_gddr6.sv" ]; then
    echo "ERROR: Must run from engine_gddr6_test directory"
    exit 1
fi

# Setup ACE environment
echo "Step 1: Setting up ACE environment..."
if [ -z "$ACE_INSTALL_DIR" ]; then
    echo "  Sourcing ACE setup..."
    source /tools/Achronix/Acex/ACE-9.2/Achronix_ac7t1500_fpga_only/setup.bash
    echo "  ACE_INSTALL_DIR = $ACE_INSTALL_DIR"
else
    echo "  ACE_INSTALL_DIR already set: $ACE_INSTALL_DIR"
fi

# Unset LD_LIBRARY_PATH (Riviera requirement)
echo ""
echo "Step 2: Unsetting LD_LIBRARY_PATH..."
if [ -n "$LD_LIBRARY_PATH" ]; then
    echo "  Unsetting LD_LIBRARY_PATH"
    unset LD_LIBRARY_PATH
else
    echo "  LD_LIBRARY_PATH not set (OK)"
fi

# Verify dependencies
echo ""
echo "Step 3: Verifying dependencies..."

GDDR_REF_DIR="../../../gddr_ref_design"
GDDR_INC_DIR="${GDDR_REF_DIR}/src/include"
GDDR_MODEL_DIR="${GDDR_REF_DIR}/src/tb/gddr_model"

if [ ! -d "$GDDR_INC_DIR" ]; then
    echo "  ERROR: GDDR6 includes not found at $GDDR_INC_DIR"
    exit 1
fi
echo "  [OK] Include directory: $GDDR_INC_DIR"

if [ ! -d "$GDDR_MODEL_DIR" ]; then
    echo "  ERROR: GDDR6 models not found at $GDDR_MODEL_DIR"
    exit 1
fi
echo "  [OK] Model directory: $GDDR_MODEL_DIR"

# Check test data
if [ ! -f "/home/dev/Dev/elastix_gemm/hex/left.hex" ]; then
    echo "  WARNING: left.hex not found"
else
    echo "  [OK] left.hex found"
fi

if [ ! -f "/home/dev/Dev/elastix_gemm/hex/right.hex" ]; then
    echo "  WARNING: right.hex not found"
else
    echo "  [OK] right.hex found"
fi

# Clean previous build
echo ""
echo "Step 4: Cleaning previous build..."
make clean
echo "  [OK] Clean complete"

# Compile
echo ""
echo "Step 5: Compiling simulation..."
echo "  (This will take 3-5 minutes...)"
echo ""

if make run_compile; then
    echo ""
    echo "========================================================================"
    echo "COMPILATION SUCCESS"
    echo "========================================================================"
else
    echo ""
    echo "========================================================================"
    echo "COMPILATION FAILED"
    echo "========================================================================"
    echo ""
    echo "Check logs/FULLCHIP_BFM_simulation.log for details"
    exit 1
fi

# Run simulation
echo ""
echo "Step 6: Running simulation..."
echo "  (This will take 5-15 minutes...)"
echo ""

if make run_vsim; then
    echo ""
    echo "========================================================================"
    echo "SIMULATION COMPLETE"
    echo "========================================================================"
    echo ""
    echo "Results:"
    tail -50 logs/FULLCHIP_BFM_simulation.log
else
    echo ""
    echo "========================================================================"
    echo "SIMULATION FAILED"
    echo "========================================================================"
    echo ""
    echo "Last 50 lines of log:"
    tail -50 logs/FULLCHIP_BFM_simulation.log
    exit 1
fi

echo ""
echo "========================================================================"
echo "See logs/FULLCHIP_BFM_simulation.log for full output"
echo "========================================================================"


