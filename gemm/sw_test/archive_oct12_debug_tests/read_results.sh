#!/bin/bash
echo "=== Checking MS2.0 Engine Status ==="
echo ""
echo "Running test_registers to check engine state..."
./test_registers | grep -A 5 "ENGINE"
