set jtag_id [jtag::get_connected_devices]
set bs ./elastix_gemm_top.VP815.1.1.hex

puts "###################################################"
puts "Bitstream = $bs"
puts "Programming elastix_gemm_top with MS2.0 GEMM engine and GDDR6 support"
puts "###################################################"

jtag::open $jtag_id

jtag::configure_scan_chain $jtag_id AC7t1500ES1 0 0 0
after 500
jtag::ac7t1500_initialize_fcu $jtag_id -reset
after 500
jtag::ac7t1500_program_bitstream $jtag_id $bs
after 5000

jtag::close $jtag_id

puts "#####################################################"
puts "Bitstream = $bs has been programmed WITH FCU_RESET"
puts "#####################################################"
