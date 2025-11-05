
set jtag_id [jtag::get_connected_devices]
set flash0 ./elastix_gemm_top_page0.flash
set flash ./elastix_gemm_top.flash

spi::program_bitstream VectorPath $flash0 1 -offset 0 -device_id $jtag_id
spi::program_bitstream VectorPath $flash 4 -offset 4096 -device_id $jtag_id
