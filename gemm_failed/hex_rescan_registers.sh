#!/bin/bash

if [ ! -f /home/dev/Dev/elastix_gemm/gemm/build/results/ace/impl_1/pnr/output/elastix_gemm_top.hex ]; then
    echo "ERROR:elastix_gemm_top.hex not found"
    exit 1
fi
# /home/dev/Dev/hex.sh
/home/dev/Dev/flash.sh
# CRITICAL SAFETY CHECK: Verify device is visible before any PCIe operations
# echo "=== Checking PCIe device visibility (MANDATORY safety check) ==="
# if ! sudo lspci -d 1b59: | grep -q "1b59"; then
#     echo "❌ ERROR: Device NOT visible on PCIe bus!"
#     echo "⚠️  DO NOT RUN RESCAN - this can crash the system!"
#     echo "⚠️  REBOOT REQUIRED: sudo reboot"
#     exit 1
# fi
# echo "✅ Device visible on PCIe bus - safe to proceed"
# echo ""

# Program FPGA with hex bitstream


# # ONLY rescan if device is still visible (should be after successful programming)
# echo "=== Checking device visibility before rescan ==="
# if ! sudo lspci -d 1b59: | grep -q "1b59"; then
#     echo "❌ ERROR: Device disappeared after programming!"
#     echo "⚠️  Skipping rescan to prevent system crash"
#     echo "⚠️  REBOOT REQUIRED: sudo reboot"
#     exit 1
# fi
# echo "✅ Device still visible - proceeding with rescan"

# sleep 10
# Safe to rescan now
# source /home/dev/rescan

# Test device status
# /home/dev/Dev/elastix_gemm/gemm/sw_test/test_registers