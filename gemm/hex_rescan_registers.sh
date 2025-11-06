#!/bin/bash
cd /home/dev/Dev/elastix_gemm/gemm/demo/11030039
# cd /home/dev/Dev/elastix_gemm/gemm/demo/bitstream/
echo "Copying flash.tcl to build directory"
pwd

if [ ! -f ./elastix_gemm_top.VP815.1.1.hex ]; then
    echo "ERROR:elastix_gemm_top.VP815.1.1.hex not found"
    exit 1
fi

cp /home/dev/Dev/elastix_gemm/gemm/hex.tcl .
/opt/achronix/ACE_10_3_1/Achronix-linux/ace -b -lab_mode -script_file hex.tcl

echo "=== Checking PCIe device visibility (MANDATORY safety check) ==="
if ! sudo lspci -d 1b59: | grep -q "1b59"; then
    echo "❌ ERROR: Device NOT visible on PCIe bus!"
    echo "⚠️  DO NOT RUN RESCAN - this can crash the system!"
    echo "⚠️  REBOOT REQUIRED: sudo reboot"
    exit 1
fi
echo "✅ Device visible on PCIe bus - safe to proceed"
echo ""

echo "=== Checking device visibility before rescan ==="
if ! sudo lspci -d 1b59: | grep -q "1b59"; then
    echo "❌ ERROR: Device disappeared after programming!"
    echo "⚠️  Skipping rescan to prevent system crash"
    echo "⚠️  REBOOT REQUIRED: sudo reboot"
    exit 1
fi
echo "✅ Device still visible - proceeding with rescan"

sleep 10
Safe to rescan now
source /home/dev/rescan

# Test device status
# /home/dev/Dev/elastix_gemm/gemm/sw_test/test_registers