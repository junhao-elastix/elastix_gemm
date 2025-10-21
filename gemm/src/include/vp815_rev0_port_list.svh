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
//   Include this file in a design top level module declaration
//   NOTE : This file should be the end of the port declarations,
//          If not, then add a "," after the include statement
// ------------------------------------------------------------------
    // Ports for vp815_clkio_ne
    input wire        pcie_perst_l,

    // Ports for vp815_gpio_n_b0
    // Core Data
    input wire [7:0] ext_gpio_fpga_in,
    output wire [7:0] ext_gpio_fpga_oe,
    output wire [7:0] ext_gpio_fpga_out,
    output wire       ext_gpio_oe_l,
    output wire       ext_gpio_oe_l_oe,
    output wire       led_oe_l,
    output wire       led_oe_l_oe,
    // Ports for vp815_gpio_n_b1
    // Core Data
    output wire [7:0] ext_gpio_dir,
    output wire [7:0] ext_gpio_dir_oe,
    output wire [7:0] led_l,
    output wire [7:0] led_l_oe,
    // Ports for vp815_gpio_n_b2
    // Core Data
    // Ports for vp815_gpio_s_b0
    // Core Data
    input wire        fpga_avr_rxd,
    input wire        fpga_ftdi_rxd,
    input wire        fpga_i2c_mux_gnt,
    input wire        fpga_rst_l,
    input wire        qsfp_int_fpga_l,
    output wire       fpga_avr_txd,
    output wire       fpga_avr_txd_oe,
    output wire       fpga_ftdi_txd,
    output wire       fpga_ftdi_txd_oe,
    output wire       fpga_i2c_req_l,
    output wire       fpga_i2c_req_l_oe,
    output wire       irq_to_avr,
    output wire       irq_to_avr_oe,
    output wire       recov_clk_0,
    output wire       recov_clk_0_oe,
    // Ports for vp815_gpio_s_b1
    // Core Data
    input wire        u1pps_1_in,
    input wire        u1pps_2_in,
    input wire        u1pps_in,
    output wire       clk_gpio0,
    output wire       clk_gpio0_oe,
    output wire       clk_gpio1,
    output wire       clk_gpio1_oe,
    output wire       freq_dec,
    output wire       freq_dec_oe,
    output wire       freq_inc,
    output wire       freq_inc_oe,
    output wire       u1pps_1_dir,
    output wire       u1pps_1_dir_oe,
    output wire       u1pps_1_oe,
    output wire       u1pps_1_out,
    output wire       u1pps_2_dir,
    output wire       u1pps_2_dir_oe,
    output wire       u1pps_2_oe,
    output wire       u1pps_2_out,
    output wire       u1pps_en_l,
    output wire       u1pps_en_l_oe,
    // Ports for vp815_gpio_s_b2
    // Core Data
    input wire        fpga_sys_scl_in,
    input wire        fpga_sys_sda_in,
    output wire       fpga_sys_scl_oe,
    output wire       fpga_sys_scl_out,
    output wire       fpga_sys_sda_oe,
    output wire       fpga_sys_sda_out,
    output wire       recov_clk_1,
    output wire       recov_clk_1_oe 

