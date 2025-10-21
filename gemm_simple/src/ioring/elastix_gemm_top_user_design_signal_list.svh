//////////////////////////////////////
// ACE GENERATED VERILOG INCLUDE FILE
// Generated on: 2025.10.20 at 21:17:28 PDT
// By: ACE 10.3.1
// From project: elastix_gemm_top
//////////////////////////////////////
// User Design Signal List Include File
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
    logic  [3:0] pci_express_x16_status_flr_pf_active;
    logic        pci_express_x16_status_flr_vf_active;
    logic  [5:0] pci_express_x16_status_ltssm_state;
    // Ports for pll_ddr
    logic        pll_ddr_lock;
    // Ports for pll_gddr_SE
    logic        pll_gddr_SE_lock;
    // Ports for pll_gddr_SW
    logic        pll_gddr_SW_lock;
    // Ports for pll_noc
    logic        i_adm_clk;
    logic        i_nap_clk;
    logic        i_reg_clk;
    logic        pll_noc_lock;
    // Ports for pll_pcie
    logic        pll_pcie_lock;
    // Ports for vp815_clkio_ne
    logic        pcie_perst_l;
    // Ports for vp815_clkio_nw
    // Ports for vp815_clkio_se
    // Ports for vp815_clkio_sw
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

//////////////////////////////////////
// End User Design Signal List Include File
//////////////////////////////////////
