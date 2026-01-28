#!/bin/bash
# =============================================================================
# RTL Simulation Test Suite Runner
# 
# Runs all GEMM 2D test configurations in sequence, collecting results.
# Test configurations match those in the C++ test (test_gemm_2d.cpp).
#
# Usage:
#   ./run_all_tests.sh           # Run all tests
#   ./run_all_tests.sh -q        # Quiet mode (summary only)
#   ./run_all_tests.sh B4_C4_V4  # Run specific test only
# =============================================================================

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

# Test configurations: "B C V name"
TESTS=(
    "1 1 1 B1_C1_V1"
    "2 2 2 B2_C2_V2"
    "4 4 4 B4_C4_V4"
    "4 4 32 B4_C4_V32"
    "4 8 4 B4_C8_V4"
    "4 13 9 B4_C13_V9"
    "4 16 8 B4_C16_V8"
    "8 8 16 B8_C8_V16"
    "16 16 4 B16_C16_V4"
    "16 16 8 B16_C16_V8"
)

# Parse arguments
QUIET=0
SINGLE_TEST=""
for arg in "$@"; do
    case $arg in
        -q|--quiet) QUIET=1 ;;
        B*) SINGLE_TEST="$arg" ;;
    esac
done

# Results tracking
PASSED=0
FAILED=0
RESULTS_LOG="test_results_$(date +%Y%m%d_%H%M%S).log"

echo "=========================================="
echo "RTL Simulation Test Suite"
echo "=========================================="
echo "Date: $(date)"
echo "Log: $RESULTS_LOG"
echo "=========================================="
echo ""

# Function to run a single test
run_test() {
    local B=$1
    local C=$2
    local V=$3
    local NAME=$4
    
    echo "----------------------------------------"
    echo "Running: $NAME (B=$B, C=$C, V=$V)"
    echo "----------------------------------------"
    
    # Clean and run
    local LOG_FILE="sim_${NAME}.log"
    make clean > /dev/null 2>&1
    make run TEST_B=$B TEST_C=$C TEST_V=$V 2>&1 | tee "$LOG_FILE"
    
    # Check result
    if grep -q "ALL TESTS PASSED" "$LOG_FILE" || grep -q "PASS:" "$LOG_FILE"; then
        echo "[PASS] $NAME"
        echo "$NAME: PASS" >> "$RESULTS_LOG"
        return 0
    else
        echo "[FAIL] $NAME"
        echo "$NAME: FAIL" >> "$RESULTS_LOG"
        # Save failed log
        cp "$LOG_FILE" "FAILED_${NAME}.log"
        return 1
    fi
}

# Run tests
echo "" >> "$RESULTS_LOG"
echo "Test Results - $(date)" >> "$RESULTS_LOG"
echo "========================================" >> "$RESULTS_LOG"

for test_config in "${TESTS[@]}"; do
    read -r B C V NAME <<< "$test_config"
    
    # Skip if single test requested and this isn't it
    if [[ -n "$SINGLE_TEST" && "$NAME" != "$SINGLE_TEST" ]]; then
        continue
    fi
    
    if run_test "$B" "$C" "$V" "$NAME"; then
        ((PASSED++))
    else
        ((FAILED++))
    fi
    
    echo ""
done

# Summary
echo "=========================================="
echo "TEST SUMMARY"
echo "=========================================="
echo "Passed: $PASSED"
echo "Failed: $FAILED"
echo "Total:  $((PASSED + FAILED))"
echo "=========================================="

echo "" >> "$RESULTS_LOG"
echo "========================================" >> "$RESULTS_LOG"
echo "Summary: Passed=$PASSED, Failed=$FAILED" >> "$RESULTS_LOG"
echo "========================================" >> "$RESULTS_LOG"

if [[ $FAILED -eq 0 && $PASSED -gt 0 ]]; then
    echo "STATUS: ALL TESTS PASSED"
    exit 0
elif [[ $FAILED -gt 0 ]]; then
    echo "STATUS: SOME TESTS FAILED"
    echo "Check FAILED_*.log files for details"
    exit 1
else
    echo "STATUS: NO TESTS RUN"
    exit 1
fi
