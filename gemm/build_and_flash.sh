#!/bin/bash

cd /home/dev/Dev/elastix_gemm/gemm/build/
make clean && make all

if [ ! -f /home/dev/Dev/elastix_gemm/gemm/build/results/ace/impl_1/pnr/output/elastix_gemm_top.hex ]; then
    echo "ERROR:elastix_gemm_top.hex not found"
    exit 1
fi

/home/dev/Dev/flash.sh
# /home/dev/Dev/hex.sh

# if sudo lspci -d 1b59: -v | grep -q . && sudo lspci -d 12ba: -v | grep -q .; then
#     echo "PCIe devices enumerated."
# else
#     echo "ERROR: Required PCIe devices not found."
#     exit 1
# fi

# sleep 10
# source /home/dev/rescan
# /home/dev/Dev/test_registers.sh
# sudo reboot now
