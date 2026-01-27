#!/bin/bash
# Run all 9 test configurations for engine_gddr6_test

configs=(
    "1 1 1"
    "2 2 2"
    "4 4 4"
    "2 2 64"
    "4 4 32"
    "8 8 16"
    "1 128 1"
    "128 1 1"
    "1 1 128"
)

echo "========================================================================"
echo "Running engine_gddr6_test with 9 configurations"
echo "========================================================================"

pass_count=0
fail_count=0

for config in "${configs[@]}"; do
    read B C V <<< "$config"
    
    echo ""
    echo "========================================================================"
    echo "TEST: B=$B, C=$C, V=$V"
    echo "========================================================================"
    
    # Update testbench parameters
    sed -i "s/parameter TEST_B = [0-9]\+,/parameter TEST_B = $B,/" tb_engine_gddr6.sv
    sed -i "s/parameter TEST_C = [0-9]\+,/parameter TEST_C = $C,/" tb_engine_gddr6.sv
    sed -i "s/parameter TEST_V = [0-9]\+/parameter TEST_V = $V/" tb_engine_gddr6.sv
    
    # Run test
    make clean > /dev/null 2>&1
    timeout 120s make run 2>&1 | grep -E "Configuration|Results captured|Mismatches|STATUS|PASS" | tail -6
    
    # Check result
    if timeout 120s make run 2>&1 | grep -q "STATUS: \[PASS\]"; then
        ((pass_count++))
        echo "RESULT: PASS"
    else
        ((fail_count++))
        echo "RESULT: FAIL"
    fi
done

echo ""
echo "========================================================================"
echo "SUMMARY"
echo "========================================================================"
echo "Passed: $pass_count / 9"
echo "Failed: $fail_count / 9"
echo "========================================================================"

