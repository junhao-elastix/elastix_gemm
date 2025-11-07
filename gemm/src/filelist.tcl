set rtl_verilog_files {
# Package must be compiled first
../include/gemm_pkg.sv
# Top level
elastix_gemm_top.sv
# FLR responder block
flr_responder.sv
# MSI-X interrupt support
irq_gen.sv
msix_irq_handler.sv
# PCIe enumeration and memory training
acx_device_manager.sv
# Other shell modules
axi_bram_responder.sv
default_nettype.v
reg_control_block.sv
reset_processor_v2.sv
# NAP wrappers for BRAM bridges
nap_initiator_wrapper.sv
nap_responder_wrapper.sv
# Elastix GEMM Engine modules
cmd_fifo.sv
compute_engine_modular.sv
csr_to_fifo_bridge.sv
dispatcher_bram.sv
dispatcher.sv
dispatcher_control.sv
dma_bram_bridge.sv
engine_top.sv
fetcher.sv
gfp8_bcv_controller.sv
gfp8_nv_dot.sv
gfp8_to_fp16.sv
master_control.sv
result_arbiter.sv
result_bram.sv
result_fifo_to_simple_bram.sv
shift_reg.sv
tile_bram.sv
tile_result_fifo.sv
}

# WARNING: do not modify the files below this line unless you know what you are doing
# WARNING: do not modify the files below this line unless you know what you are doing
# WARNING: do not modify the files below this line unless you know what you are doing

# synthesis constraints
set synplify_constraints_files {
synplify_constraints.sdc
synplify_constraints.fdc
}

# ioring files must be first as they specify the clocks
set ace_constraints_files {
../ioring/elastix_gemm_top_ioring.sdc
../ioring/elastix_gemm_top_ioring.pdc
../ioring/elastix_gemm_top_ioring_delays_C1_900mV_0C_fast.sdc
../ioring/elastix_gemm_top_ioring_delays_C1_900mV_0C_slow.sdc
../ioring/elastix_gemm_top_ioring_delays_C1_900mV_n40C_fast.sdc
../ioring/elastix_gemm_top_ioring_delays_C1_900mV_n40C_slow.sdc
../ioring/elastix_gemm_top_ioring_delays_C1_900mV_125C_fast.sdc
../ioring/elastix_gemm_top_ioring_delays_C1_900mV_125C_slow.sdc
ace_constraints.sdc
ace_placements.pdc
../ioring/elastix_gemm_top_ioring_bitstream0.hex
../ioring/elastix_gemm_top_ioring_bitstream1.hex
../ioring/elastix_gemm_top_ioring_util.xml
../ioring/elastix_gemm_top_ioring_power.xml
}

set generate_ioring_path "../ioring"

set synplify_option_files {
synplify_options.tcl
}

set ace_options_files {
ace_options.tcl
}

set multi_acxip_files {
# acxip directory has the AC7t1500, (was ES1) files
../acxip/acx_device_manager.acxip
../acxip/ddr4.acxip
../acxip/pci_express_x16.acxip
../acxip/noc.acxip
../acxip/pll_ddr.acxip
../acxip/pll_pcie.acxip
../acxip/pll_noc.acxip
../acxip/gddr6_0.acxip
../acxip/gddr6_1.acxip
../acxip/gddr6_2.acxip
../acxip/gddr6_3.acxip
../acxip/gddr6_4.acxip
../acxip/gddr6_5.acxip
../acxip/gddr6_6.acxip
../acxip/gddr6_7.acxip
../acxip/pll_gddr_SE.acxip
../acxip/pll_gddr_SW.acxip
# VectorPath board files
../acxip/vp815_clkio_ne.acxip
../acxip/vp815_clkio_nw.acxip
../acxip/vp815_clkio_se.acxip
../acxip/vp815_clkio_sw.acxip
../acxip/vp815_gpio_n_b0.acxip
../acxip/vp815_gpio_n_b1.acxip
../acxip/vp815_gpio_n_b2.acxip
../acxip/vp815_gpio_s_b0.acxip
../acxip/vp815_gpio_s_b1.acxip
../acxip/vp815_gpio_s_b2.acxip
}

set tb_verilog_files {
tb_acx_sdk_vp_demo.sv
tb_pcie_bfm_dma.sv
}

set tb_vhdl_files {
}


