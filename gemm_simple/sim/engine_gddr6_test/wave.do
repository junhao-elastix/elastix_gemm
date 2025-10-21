# Basic waveform setup for GEMM Engine GDDR6 simulation

onerror {resume}
quietly WaveActivateNextPane {} 0

# Clock and Reset
add wave -noupdate -divider {Clock and Reset}
add wave -noupdate /tb_engine_gddr6/i_nap_clk
add wave -noupdate /tb_engine_gddr6/nap_rstn
add wave -noupdate /tb_engine_gddr6/test_start

# Engine Status
add wave -noupdate -divider {Engine Status}
add wave -noupdate /tb_engine_gddr6/engine_busy
add wave -noupdate -radix hexadecimal /tb_engine_gddr6/mc_state
add wave -noupdate -radix hexadecimal /tb_engine_gddr6/dc_state
add wave -noupdate -radix hexadecimal /tb_engine_gddr6/ce_state
add wave -noupdate -radix hexadecimal /tb_engine_gddr6/last_opcode

# Command Interface
add wave -noupdate -divider {Command Interface}
add wave -noupdate -radix hexadecimal /tb_engine_gddr6/user_regs_write[15]
add wave -noupdate -radix hexadecimal /tb_engine_gddr6/user_regs_write[16]
add wave -noupdate -radix hexadecimal /tb_engine_gddr6/user_regs_write[17]
add wave -noupdate -radix hexadecimal /tb_engine_gddr6/user_regs_write[18]
add wave -noupdate /tb_engine_gddr6/write_strobes[19]
add wave -noupdate /tb_engine_gddr6/cmd_fifo_wen
add wave -noupdate -radix hexadecimal /tb_engine_gddr6/cmd_fifo_wdata
add wave -noupdate -radix unsigned /tb_engine_gddr6/cmd_fifo_count

# AXI NAP Interface
add wave -noupdate -divider {AXI Read Address Channel}
add wave -noupdate /tb_engine_gddr6/nap/arvalid
add wave -noupdate /tb_engine_gddr6/nap/arready
add wave -noupdate -radix hexadecimal /tb_engine_gddr6/nap/araddr
add wave -noupdate -radix hexadecimal /tb_engine_gddr6/nap/arid
add wave -noupdate -radix unsigned /tb_engine_gddr6/nap/arlen

# AXI Read Data Channel
add wave -noupdate -divider {AXI Read Data Channel}
add wave -noupdate /tb_engine_gddr6/nap/rvalid
add wave -noupdate /tb_engine_gddr6/nap/rready
add wave -noupdate -radix hexadecimal /tb_engine_gddr6/nap/rdata
add wave -noupdate /tb_engine_gddr6/nap/rlast

# Dispatcher Control
add wave -noupdate -divider {Dispatcher Control}
add wave -noupdate /tb_engine_gddr6/i_engine_top/u_dispatcher_control/state_reg
add wave -noupdate /tb_engine_gddr6/i_engine_top/u_dispatcher_control/fetch_en_prev
add wave -noupdate -radix unsigned /tb_engine_gddr6/i_engine_top/u_dispatcher_control/current_line_reg
add wave -noupdate -radix unsigned /tb_engine_gddr6/i_engine_top/u_dispatcher_control/exp_lines_fetched_reg
add wave -noupdate -radix unsigned /tb_engine_gddr6/i_engine_top/u_dispatcher_control/man_lines_fetched_reg

# Dispatcher BRAM Writes
add wave -noupdate -divider {Dispatcher BRAM}
add wave -noupdate /tb_engine_gddr6/i_engine_top/u_dispatcher_control/bram_wr_en_reg
add wave -noupdate -radix unsigned /tb_engine_gddr6/i_engine_top/u_dispatcher_control/bram_wr_addr_reg
add wave -noupdate -radix hexadecimal /tb_engine_gddr6/i_engine_top/u_dispatcher_control/bram_wr_data_reg

# Compute Engine
add wave -noupdate -divider {Compute Engine}
add wave -noupdate /tb_engine_gddr6/i_engine_top/u_compute_engine/i_tile_en
add wave -noupdate -radix unsigned /tb_engine_gddr6/i_engine_top/u_compute_engine/i_dim_b
add wave -noupdate -radix unsigned /tb_engine_gddr6/i_engine_top/u_compute_engine/i_dim_c
add wave -noupdate -radix unsigned /tb_engine_gddr6/i_engine_top/u_compute_engine/i_dim_v

# BCV Controller
add wave -noupdate -divider {BCV Controller}
add wave -noupdate -radix unsigned /tb_engine_gddr6/i_engine_top/u_compute_engine/i_gfp_bcv_ctrl/b_idx_reg
add wave -noupdate -radix unsigned /tb_engine_gddr6/i_engine_top/u_compute_engine/i_gfp_bcv_ctrl/c_idx_reg
add wave -noupdate -radix unsigned /tb_engine_gddr6/i_engine_top/u_compute_engine/i_gfp_bcv_ctrl/v_idx_reg
add wave -noupdate /tb_engine_gddr6/i_engine_top/u_compute_engine/i_gfp_bcv_ctrl/state_reg

# Results
add wave -noupdate -divider {Results}
add wave -noupdate /tb_engine_gddr6/result_fifo_empty
add wave -noupdate -radix unsigned /tb_engine_gddr6/result_fifo_count
add wave -noupdate /tb_engine_gddr6/result_fifo_ren
add wave -noupdate -radix hexadecimal /tb_engine_gddr6/result_fifo_rdata
add wave -noupdate -radix unsigned /tb_engine_gddr6/result_idx

TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {0 ps} 0}
quietly wave cursor active 1
configure wave -namecolwidth 350
configure wave -valuecolwidth 100
configure wave -justifyvalue left
configure wave -signalnamewidth 0
configure wave -snapdistance 10
configure wave -datasetprefix 0
configure wave -rowmargin 4
configure wave -childrowmargin 2
configure wave -gridoffset 0
configure wave -gridperiod 1
configure wave -griddelta 40
configure wave -timeline 0
configure wave -timelineunits ps
update
WaveRestoreZoom {0 ps} {10000000 ps}


