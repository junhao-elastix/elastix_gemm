set rtl_verilog_files {
default_nettype.v
# Package must be compiled first
../include/gemm_pkg.sv
reset_processor_v2.sv
shift_reg.sv
reg_control_block.sv
# BRAM DMA bridge (legacy +42 processing removed)
dma_bram_bridge.sv
# bram_vector_processor.sv - ARCHIVED (vector processor functionality removed from project)
# Original BRAM responder for ATU
axi_bram_responder.sv
# AXI packet generation and checking for GDDR6 testing - ARCHIVED (channels 1-7 disabled)
# axi_pkt_gen.sv - ARCHIVED (packet generator for GDDR6 validation, unused with GEMM focus)
# axi_pkt_chk.sv - ARCHIVED (packet checker for GDDR6 validation, unused with GEMM focus)
# axi_mem_pkt_gen_chk_channel.sv - ARCHIVED (memory channel test infrastructure, unused with GEMM focus)
# random_seq_engine.sv - ARCHIVED (random sequence generation for packet generators, unused)
# axi_performance_monitor.sv - ARCHIVED (performance monitoring for packet generators, unused)
# axi_latency_monitor.sv - ARCHIVED (latency monitoring for packet generators, unused)
# axi_bw_monitor.sv - ARCHIVED (bandwidth monitoring for packet generators, unused)
# axi_reg_layer.sv - ARCHIVED (Oct 14, 2025 - Achronix library component not used, referenced only in comments)
# NAP wrappers for BRAM bridges
nap_initiator_wrapper.sv
# nap_initiator_wrapper_fixed.sv - ARCHIVED (unused, interface direction fix not needed)
# nap_initiator_readonly_wrapper.sv - ARCHIVED (unused, read-only optimization not used)
nap_responder_wrapper.sv
# GDDR6-to-BRAM processor with configurable data processing
# g2b_data_processor.sv - ARCHIVED (legacy G2B functionality removed)
# gddr6_to_bram_processor.sv - ARCHIVED (replaced by MS2.0 GEMM engine)
# MS2.0 GEMM Engine modules
cmd_fifo.sv
# cmd_submit_pulser.sv - ARCHIVED (Oct 14, 2025 - replaced by reg_control_block write_strobes mechanism)
master_control.sv
# dispatcher_bram.sv - ARCHIVED (Oct 12, 2025 - single-read version, replaced by dispatcher_bram.sv)
dispatcher_bram.sv
tile_bram.sv
dispatcher_control.sv
# GFP8 hierarchical compute modules
gfp8_bcv_controller.sv
gfp8_nv_dot.sv
gfp8_group_dot_mlp.sv
gfp8_to_fp16.sv
# Compute engine (MS2.0 modular design with dual BRAM interface)
# compute_engine.sv - ARCHIVED (Oct 10, 2025 - replaced by compute_engine_modular.sv)
compute_engine_modular.sv
# csr_cmd_bridge.sv - ARCHIVED (Oct 6 23:20, replaced with direct CSR->FIFO in engine_wrapper.sv)
# result_bram_writer.sv - ARCHIVED (Oct 12, 2025 - functionality integrated into result_bram.sv)
result_bram.sv
csr_to_fifo_bridge.sv
result_fifo_to_simple_bram.sv
engine_top.sv
# engine_wrapper.sv - ARCHIVED (Oct 12, 2025 - complex CSR queue, replaced by engine_top.sv with csr_to_fifo_bridge.sv)
# MSI-X interrupt support
irq_gen.sv
msix_irq_handler.sv
# FLR responder block
flr_responder.sv
# PCIe enumeration and memory training
acx_device_manager.sv
# Top level
elastix_gemm_top.sv
}

# No VHDL files in project
# set rtl_vhdl_files {
# }

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


