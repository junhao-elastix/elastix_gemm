# Load design
vsim -voptargs=+acc work.tb_back_to_back_test

# Add waves
add wave -radix hex /tb_back_to_back_test/clk
add wave -radix hex /tb_back_to_back_test/reset_n
add wave -radix hex /tb_back_to_back_test/result_fifo_rdata
add wave -radix hex /tb_back_to_back_test/result_fifo_ren
add wave -radix hex /tb_back_to_back_test/result_fifo_empty
add wave -radix hex /tb_back_to_back_test/u_packer/fifo_rd_valid
add wave -radix hex /tb_back_to_back_test/u_packer/wr_ptr
add wave -radix hex /tb_back_to_back_test/result_bram_wr_en
add wave -radix hex /tb_back_to_back_test/result_bram_wr_addr
add wave -radix hex /tb_back_to_back_test/result_bram_wr_data
add wave -radix hex /tb_back_to_back_test/result_bram_wr_strobe
add wave -radix hex /tb_back_to_back_test/result_bram_model[0]

# Run
run 2000
quit
