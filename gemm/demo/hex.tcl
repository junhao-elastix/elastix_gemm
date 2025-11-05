
set jtag_id [jtag::get_connected_devices]
# set bs ./mmio_test_top.hex
set bs ./11030039/elastix_gemm_top.VP815.1.1.hex
# set bs /home/dev/Demo/llm_vp_demo_pcie/src/ace/impl_1/pnr/output/tc_ref_design_top.hex

puts "###################################################"
puts "Bitstream = $bs IS THIS CORRECT??????????????? ####"
puts "###################################################"

jtag::open $jtag_id

jtag::configure_scan_chain $jtag_id AC7t1500ES1 0 0 0
after 500
jtag::ac7t1500_initialize_fcu $jtag_id -reset
after 500
jtag::ac7t1500_program_bitstream $jtag_id $bs
after 5000
#get_hex_version CSR_SPACE PCIE_1 SERDES_0
# APB address: 08198080000
##acx_stapl_player -q
after 5000
################dbiw 3d0 1ffff

jtag::close $jtag_id

puts "#####################################################"
puts "Bitstream = $bs has been programmed WITH FCU_RESET ##"
puts "#####################################################"
