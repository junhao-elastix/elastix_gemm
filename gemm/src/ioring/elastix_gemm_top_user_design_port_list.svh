//////////////////////////////////////
// ACE GENERATED VERILOG INCLUDE FILE
// Generated on: 2025.10.28 at 20:44:42 PDT
// By: ACE 10.3.1
// From project: elastix_gemm_top
//////////////////////////////////////
// User Design Port List Include File
//////////////////////////////////////

    // Ports for ddr4
    // Ports for gddr6_0
    // Ports for gddr6_1
    // Ports for gddr6_2
    // Ports for gddr6_3
    // Ports for gddr6_4
    // Ports for gddr6_5
    // Ports for gddr6_6
    // Ports for gddr6_7
    // Ports for noc
    // Ports for pci_express_x16
    // Status
    input wire  [3:0] pci_express_x16_status_flr_pf_active,
    input wire        pci_express_x16_status_flr_vf_active,
    input wire  [5:0] pci_express_x16_status_ltssm_state,
    // Ports for pll_ddr
    input wire        pll_ddr_lock,
    // Ports for pll_gddr_SE
    input wire        pll_gddr_SE_lock,
    // Ports for pll_gddr_SW
    input wire        pll_gddr_SW_lock,
    // Ports for pll_noc
    input wire        i_adm_clk,
    input wire        i_nap_clk,
    input wire        i_reg_clk,
    input wire        pll_noc_lock,
    // Ports for pll_pcie
    input wire        pll_pcie_lock,
    // Ports for vp815_clkio_ne
    input wire        pcie_perst_l,
    // Ports for vp815_clkio_nw
    // Ports for vp815_clkio_se
    // Ports for vp815_clkio_sw
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

//////////////////////////////////////
// End User Design Port List Include File
//////////////////////////////////////
