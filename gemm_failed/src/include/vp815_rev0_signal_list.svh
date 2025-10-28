// ------------------------------------------------------------------
//
// Copyright (c) 2025 Achronix Semiconductor Corp.
// All Rights Reserved.
//
// This Software constitutes an unpublished work and contains
// valuable proprietary information and trade secrets belonging
// to Achronix Semiconductor Corp.
//
// Permission is hereby granted to use this Software including
// without limitation the right to copy, modify, merge or distribute
// copies of the software subject to the following condition:
//
// The above copyright notice and this permission notice shall
// be included in in all copies of the Software.
//
// The Software is provided “as is” without warranty of any kind
// expressed or implied, including  but not limited to the warranties
// of merchantability fitness for a particular purpose and non-infringement.
// In no event shall the copyright holder be liable for any claim,
// damages, or other liability for any damages or other liability,
// whether an action of contract, tort or otherwise, arising from, 
// out of, or in connection with the Software
//
// ------------------------------------------------------------------
// VectorPath 815 rev 0 Ports
//   Include this file in a design top level module instantiation in testbench
// ------------------------------------------------------------------
    // Ports for vp815_clkio_ne
    logic        pcie_perst_l;

    // Ports for vp815_gpio_n_b0
    // Core Data
    logic  [7:0] ext_gpio_fpga_in;
    logic  [7:0] ext_gpio_fpga_oe;
    logic  [7:0] ext_gpio_fpga_out;
    logic        ext_gpio_oe_l;
    logic        ext_gpio_oe_l_oe;
    logic        led_oe_l;
    logic        led_oe_l_oe;
    // Ports for vp815_gpio_n_b1
    // Core Data
    logic  [7:0] ext_gpio_dir;
    logic  [7:0] ext_gpio_dir_oe;
    logic  [7:0] led_l;
    logic  [7:0] led_l_oe;
    // Ports for vp815_gpio_n_b2
    // Core Data
    // Ports for vp815_gpio_s_b0
    // Core Data
    logic        fpga_avr_rxd;
    logic        fpga_ftdi_rxd;
    logic        fpga_i2c_mux_gnt;
    logic        fpga_rst_l;
    logic        qsfp_int_fpga_l;
    logic        fpga_avr_txd;
    logic        fpga_avr_txd_oe;
    logic        fpga_ftdi_txd;
    logic        fpga_ftdi_txd_oe;
    logic        fpga_i2c_req_l;
    logic        fpga_i2c_req_l_oe;
    logic        irq_to_avr;
    logic        irq_to_avr_oe;
    logic        recov_clk_0;
    logic        recov_clk_0_oe;
    // Ports for vp815_gpio_s_b1
    // Core Data
    logic        u1pps_1_in;
    logic        u1pps_2_in;
    logic        u1pps_in;
    logic        clk_gpio0;
    logic        clk_gpio0_oe;
    logic        clk_gpio1;
    logic        clk_gpio1_oe;
    logic        freq_dec;
    logic        freq_dec_oe;
    logic        freq_inc;
    logic        freq_inc_oe;
    logic        u1pps_1_dir;
    logic        u1pps_1_dir_oe;
    logic        u1pps_1_oe;
    logic        u1pps_1_out;
    logic        u1pps_2_dir;
    logic        u1pps_2_dir_oe;
    logic        u1pps_2_oe;
    logic        u1pps_2_out;
    logic        u1pps_en_l;
    logic        u1pps_en_l_oe;
    // Ports for vp815_gpio_s_b2
    // Core Data
    logic        fpga_sys_scl_in;
    logic        fpga_sys_sda_in;
    logic        fpga_sys_scl_oe;
    logic        fpga_sys_scl_out;
    logic        fpga_sys_sda_oe;
    logic        fpga_sys_sda_out;
    logic        recov_clk_1;
    logic        recov_clk_1_oe;
