# cd /home/workstation/elastix_gemm/gemm/build/results/ace/impl_1/pnr/output/
# cd /home/dev/Dev/elastix_gemm/matmul/build/results/ace/impl_1/pnr/output/]
# cd ./demo/11030039
cd ./bitstream/
echo "Copying flash.tcl to build directory"
pwd
cp -f ../../elastix_gemm/flash.tcl .
/opt/achronix/ACE_10_3_1/Achronix-linux/ace -lab_mode -b -script_file flash.tcl

sudo reboot