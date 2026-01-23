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
# Elastix GEMM Engine - Command/Control
cmd_fifo.sv
csr_to_fifo_bridge.sv
master_control.sv
# Elastix GEMM Engine - Memory Hierarchy
dispatcher_control.sv
dma_bram_bridge.sv
fetcher.sv
# Elastix GEMM Engine - Result Path
flex_fifo.sv
result_to_dma.sv
result_fifo_to_simple_bram.sv
shift_reg.sv
# Elastix GEMM Engine - MLP Compute (Single-Row Architecture - Legacy)
engine_top.sv
compute_engine_mlp.sv
# Elastix GEMM Engine - 2D Multi-Row Architecture (16 rows x 16 cols)
engine_top_2d.sv
master_control_2d.sv
dispatcher_control_2d.sv
dispatcher_2d.sv
fetcher_2d.sv
compute_engine_2d.sv
result_collector_2d.sv
comp_row_bram.sv
comp_bram_fill_ctrl.sv
comp_mlp_col_ctrl.sv
weight_bram.sv
comp_mlp_bram.sv
comp_mlp_bram_col.sv
comp_stack_fifo.sv
comp_mlp_bram_col_wrapper.sv
comp_mlp_dot16_bfp8.sv
comp_mlp_dot16_int8.sv
# FP Arithmetic
fp24_add.sv
fp24_to_fp16.sv
# Integer-Domain FP Adder Pipeline (for improved numerical accuracy)
fp_to_int.sv
int_to_fp.sv
int_adder_tree.sv
comp_fp_adder_pipeline.sv
}

# WARNING: do not modify the files below this line unless you know what you are doing
# WARNING: do not modify the files below this line unless you know what you are doing
# WARNING: do not modify the files below this line unless you know what you are doing

# synthesis constraints
set synplify_constraints_files {
synplify_constraints.sdc
synplify_constraints.fdc
}

# ioring files are auto-generated and auto-added by generate_ioring_design_files
# Do not list them here to avoid duplicates
set ace_constraints_files {
ace_constraints.sdc
ace_placements.pdc
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


