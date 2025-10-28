#!/bin/bash

cd /home/dev/Dev/elastix_gemm/gemm_simple/build/
make clean && make all

if [ ! -f /home/dev/Dev/elastix_gemm/gemm_simple/build/results/ace/impl_1/pnr/output/elastix_gemm_top.hex ]; then
    echo "ERROR:elastix_gemm_top.hex not found"
    exit 1
fi

cd /home/dev/Dev/elastix_gemm/gemm_simple/build/results/ace/impl_1/pnr/output/
cp -f /home/dev/Dev/flash.tcl .
/opt/achronix/ACE_10_3_1/Achronix-linux/ace -lab_mode -b -script_file flash.tcl

sudo reboot