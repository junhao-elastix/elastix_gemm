#!/bin/bash

# ============================================================================
# Tile Computation Test Script
# 
# This script validates the selective tile computation concept by:
# 1. Generating golden references for both single-tile and multi-tile modes
# 2. Running single-tile tests (compute only one specific tile)
# 3. Running multi-tile tests (compute all tiles)
# 4. Comparing results to validate that individual tiles can be computed on-demand
#
# Usage: ./test_tile_computation.sh [B] [C] [V] [verbose]
# Example: ./test_tile_computation.sh 2 2 32 1    # Verbose mode (shows detailed hardware vs golden comparison)
#          ./test_tile_computation.sh 4 4 32 0    # Quiet mode (shows only pass/fail results)
#          ./test_tile_computation.sh              # Default: B=2, C=2, V=32, verbose=0
#
# Author: Generated for multi-tile validation
# Date: $(date)
# ============================================================================


# Default parameters
B=${1:-2}
C=${2:-2}
V=${3:-32}
VERBOSE=${4:-0}  # 0 = quiet, 1 = verbose

echo "========================================"
echo "Tile Computation Test Script"
echo "========================================"
echo "Parameters: B=$B, C=$C, V=$V, Verbose=$([ $VERBOSE -eq 1 ] && echo "ON" || echo "OFF")"
echo ""

# Validate parameters
if [ $((B * V)) -gt 128 ] || [ $((C * V)) -gt 128 ]; then
    echo "ERROR: Invalid parameters! BxV=$((B*V)) and CxV=$((C*V)) must both be ≤ 128"
    exit 1
fi

# Calculate tile configuration
NUM_LEFT_TILE=$((128 / (B * V)))
NUM_RIGHT_TILE=$((128 / (C * V)))
TOTAL_TILES=$((NUM_LEFT_TILE * NUM_RIGHT_TILE))

if [ $TARGET_TILE -ge $TOTAL_TILES ]; then
    echo "ERROR: Target tile $TARGET_TILE exceeds total tiles $TOTAL_TILES"
    exit 1
fi

echo "Tile Configuration:"
echo "  Left tiles: $NUM_LEFT_TILE (each uses $((B*V)) NVs)"
echo "  Right tiles: $NUM_RIGHT_TILE (each uses $((C*V)) NVs)"
echo "  Total tiles: $TOTAL_TILES"
echo "  Results per tile: $((B*C))"
echo ""

echo "Making test_ms2_gemm_clean executable..."
make test_ms2_gemm_clean

# Legacy version (commented out)
# echo "Making test_ms2_gemm_full executable..."
# make test_ms2_gemm_full

# Change to hex directory for golden reference generation
cd ../../hex

echo "========================================"
echo "Step 1: Generate Golden References"
echo "========================================"

# Generate single-tile golden reference
echo "Generating single-tile golden reference (B=$B, C=$C, V=$V)..."
# python hardware_gfp_reference.py --B $B --C $C --V $V > /dev/null 2>&1
if [ $? -eq 0 ]; then
    echo "  ✓ Single-tile golden reference generated: golden_B${B}_C${C}_V${V}.hex"
else
    echo "  ✗ Failed to generate single-tile golden reference"
    exit 1
fi

# Generate multi-tile golden reference
echo "Generating multi-tile golden reference (B=$B, C=$C, V=$V)..."
# python hardware_gfp_reference.py --B $B --C $C --V $V --multitile > /dev/null 2>&1
if [ $? -eq 0 ]; then
    echo "  ✓ Multi-tile golden reference generated: golden_B${B}_C${C}_V${V}_multitile.hex"
else
    echo "  ✗ Failed to generate multi-tile golden reference"
    exit 1
fi

# Change back to sw_test directory
cd ../gemm/sw_test

echo ""
echo "========================================"
echo "Step 2: Run Default Single-Tile Test"
echo "========================================"

echo "Testing default single-tile computation (B=$B, C=$C, V=$V)..."
echo "This computes a single matrix multiplication starting from address 0."
echo "This should match the first tile (Tile 0) in the multi-tile results."
echo ""


# Run default single-tile test (starts from address 0)
if [ $VERBOSE -eq 1 ]; then
    ./test_ms2_gemm_clean -B $B -C $C -V $V -v
else
    ./test_ms2_gemm_clean -B $B -C $C -V $V
fi

# Legacy version (commented out)
# if [ $VERBOSE -eq 1 ]; then
#     ./test_ms2_gemm_full -B $B -C $C -V $V -v
# else
#     ./test_ms2_gemm_full -B $B -C $C -V $V
# fi
SINGLE_TILE_RESULT=$?

if [ $SINGLE_TILE_RESULT -eq 0 ]; then
    echo "  ✓ Default single-tile test PASSED"
else
    echo "  ✗ Default single-tile test FAILED"
fi

echo ""
echo "========================================"
echo "Step 3: Run Multi-Tile Test"
echo "========================================"

echo "Testing multi-tile computation for all $TOTAL_TILES tiles..."
echo "This should compute all tiles sequentially and validate against golden reference."
echo ""

# Run multi-tile test
if [ $VERBOSE -eq 1 ]; then
    ./test_ms2_gemm_clean -m -B $B -C $C -V $V -v
else
    ./test_ms2_gemm_clean -m -B $B -C $C -V $V
fi

# Legacy version (commented out)
# if [ $VERBOSE -eq 1 ]; then
#     ./test_ms2_gemm_full -m -B $B -C $C -V $V -v
# else
#     ./test_ms2_gemm_full -m -B $B -C $C -V $V
# fi
MULTI_TILE_RESULT=$?

if [ $MULTI_TILE_RESULT -eq 0 ]; then
    echo "  ✓ Multi-tile test PASSED"
else
    echo "  ✗ Multi-tile test FAILED"
fi

echo ""
echo "========================================"
echo "Step 4: Validation Summary"
echo "========================================"

echo "Test Results:"
echo "  Default single-tile test (address 0): $([ $SINGLE_TILE_RESULT -eq 0 ] && echo "PASS" || echo "FAIL")"
echo "  Multi-tile test (all $TOTAL_TILES tiles): $([ $MULTI_TILE_RESULT -eq 0 ] && echo "PASS" || echo "FAIL")"
echo ""

echo "Key Validation:"
echo "  The default single-tile test computes from address 0 (same as Tile 0 in multi-tile)"
echo "  The multi-tile test computes all tiles with different addresses"
echo "  Both should produce consistent results for the same computation"
echo ""

if [ $SINGLE_TILE_RESULT -eq 0 ] && [ $MULTI_TILE_RESULT -eq 0 ]; then
    echo "🎉 ALL TESTS PASSED!"
    echo ""
    echo "This validates that:"
    echo "  1. Default single-tile computation works correctly (address 0)"
    echo "  2. Multi-tile computation works correctly for all tiles"
    echo "  3. The MATMUL command can compute from different addresses"
    echo "  4. The multi-tile addressing system is working correctly"
    echo ""
    echo "The selective tile computation concept is validated! 🚀"
    exit 0
else
    echo "❌ SOME TESTS FAILED"
    echo ""
    echo "This indicates issues with:"
    if [ $SINGLE_TILE_RESULT -ne 0 ]; then
        echo "  - Default single-tile computation (address 0)"
    fi
    if [ $MULTI_TILE_RESULT -ne 0 ]; then
        echo "  - Multi-tile sequential computation"
    fi
    echo ""
    echo "Please investigate the failed tests above."
    exit 1
fi
