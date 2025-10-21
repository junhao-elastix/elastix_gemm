#!/bin/bash

cd /home/workstation/elastix_gemm/gemm/build/
make clean && make all

if [ ! -f /home/workstation/elastix_gemm/gemm/build/results/ace/impl_1/pnr/output/elastix_gemm_top.hex ]; then
    echo "ERROR:elastix_gemm_top.hex not found"
    exit 1
fi

/home/workstation/elastix_gemm/flash.sh

