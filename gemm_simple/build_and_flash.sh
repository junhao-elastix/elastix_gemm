#!/bin/bash

gemm_root=$PWD
cd $gemm_root/gemm_simple/build/
make clean && make all

if [ ! -f $gemm_root/gemm_simple/build/results/ace/impl_1/pnr/output/elastix_gemm_top.hex ]; then
    echo "ERROR:elastix_gemm_top.hex not found"
    exit 1
fi

cd $gemm_root/gemm_simple/build/results/ace/impl_1/pnr/output/
cp -f $gemm_root/flash.tcl .
/opt/achronix/ACE_10_3_1/Achronix-linux/ace -lab_mode -b -script_file flash.tcl
