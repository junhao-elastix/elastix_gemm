//////////////////////////////////////
// ACE GENERATED VERILOG INCLUDE FILE
// Generated on: 2025.10.20 at 10:21:28 PDT
// By: ACE 10.3.1
// From project: elastix_gemm_top
//////////////////////////////////////
// User Design Port Binding Include File
//////////////////////////////////////

//////////////////////////////////////
// User Design Ports
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
`ACX_BIND_USER_DESIGN_PORT(pci_express_x16_status_flr_pf_active[0], i_user_10_09_mlp_00[10])
`ACX_BIND_USER_DESIGN_PORT(pci_express_x16_status_flr_pf_active[1], i_user_10_09_mlp_00[11])
`ACX_BIND_USER_DESIGN_PORT(pci_express_x16_status_flr_pf_active[2], i_user_10_09_mlp_00[12])
`ACX_BIND_USER_DESIGN_PORT(pci_express_x16_status_flr_pf_active[3], i_user_10_09_mlp_00[13])
`ACX_BIND_USER_DESIGN_PORT(pci_express_x16_status_flr_vf_active, i_user_10_09_mlp_00[9])
`ACX_BIND_USER_DESIGN_PORT(pci_express_x16_status_ltssm_state[0], i_user_10_09_lut_00[1])
`ACX_BIND_USER_DESIGN_PORT(pci_express_x16_status_ltssm_state[1], i_user_10_09_lut_00[2])
`ACX_BIND_USER_DESIGN_PORT(pci_express_x16_status_ltssm_state[2], i_user_10_09_lut_00[3])
`ACX_BIND_USER_DESIGN_PORT(pci_express_x16_status_ltssm_state[3], i_user_10_09_lut_00[4])
`ACX_BIND_USER_DESIGN_PORT(pci_express_x16_status_ltssm_state[4], i_user_10_09_lut_00[5])
`ACX_BIND_USER_DESIGN_PORT(pci_express_x16_status_ltssm_state[5], i_user_10_09_lut_00[6])
    // Ports for pll_ddr
`ifdef ACX_CLK_SW_FULL
`ACX_BIND_USER_DESIGN_PORT(pll_ddr_lock, i_user_00_01_lut_17[0])
`endif
    // Ports for pll_gddr_SE
`ifdef ACX_CLK_SE_FULL
`ACX_BIND_USER_DESIGN_PORT(pll_gddr_SE_lock, i_user_12_01_lut_17[0])
`endif
    // Ports for pll_gddr_SW
`ifdef ACX_CLK_SW_FULL
`ACX_BIND_USER_DESIGN_PORT(pll_gddr_SW_lock, i_user_00_01_lut_17[1])
`endif
    // Ports for pll_noc
`ifdef ACX_CLK_SW_FULL
`ACX_BIND_USER_DESIGN_PORT(i_adm_clk, i_user_06_00_trunk_00[2])
`ACX_BIND_USER_DESIGN_PORT(i_nap_clk, i_user_06_00_trunk_00[4])
`ACX_BIND_USER_DESIGN_PORT(i_reg_clk, i_user_06_00_trunk_00[3])
`ACX_BIND_USER_DESIGN_PORT(pll_noc_lock, i_user_00_01_lut_17[3])
`endif
    // Ports for pll_pcie
`ifdef ACX_CLK_NE_FULL
`ACX_BIND_USER_DESIGN_PORT(pll_pcie_lock, i_user_12_08_lut_17[2])
`endif
    // Ports for vp815_clkio_ne
`ACX_BIND_USER_DESIGN_PORT(pcie_perst_l, i_user_06_09_trunk_00[127])
    // Ports for vp815_clkio_nw
    // Ports for vp815_clkio_se
    // Ports for vp815_clkio_sw
    // Ports for vp815_gpio_n_b0
`ifdef ACX_GPIO_N_FULL
    // Core Data
`ACX_BIND_USER_DESIGN_PORT(ext_gpio_fpga_in[0], i_user_11_09_lut_13[15])
`ACX_BIND_USER_DESIGN_PORT(ext_gpio_fpga_in[1], i_user_11_09_lut_13[23])
`ACX_BIND_USER_DESIGN_PORT(ext_gpio_fpga_in[2], i_user_11_09_lut_14[3])
`ACX_BIND_USER_DESIGN_PORT(ext_gpio_fpga_in[3], i_user_11_09_lut_14[11])
`ACX_BIND_USER_DESIGN_PORT(ext_gpio_fpga_in[4], i_user_11_09_lut_14[19])
`ACX_BIND_USER_DESIGN_PORT(ext_gpio_fpga_in[5], i_user_11_09_lut_14[27])
`ACX_BIND_USER_DESIGN_PORT(ext_gpio_fpga_in[6], i_user_11_09_lut_15[7])
`ACX_BIND_USER_DESIGN_PORT(ext_gpio_fpga_in[7], i_user_11_09_lut_15[15])
`ACX_BIND_USER_DESIGN_PORT(ext_gpio_fpga_oe[0], o_user_11_09_lut_12[16])
`ACX_BIND_USER_DESIGN_PORT(ext_gpio_fpga_oe[1], o_user_11_09_lut_12[17])
`ACX_BIND_USER_DESIGN_PORT(ext_gpio_fpga_oe[2], o_user_11_09_lut_12[18])
`ACX_BIND_USER_DESIGN_PORT(ext_gpio_fpga_oe[3], o_user_11_09_lut_12[19])
`ACX_BIND_USER_DESIGN_PORT(ext_gpio_fpga_oe[4], o_user_11_09_lut_12[20])
`ACX_BIND_USER_DESIGN_PORT(ext_gpio_fpga_oe[5], o_user_11_09_lut_12[21])
`ACX_BIND_USER_DESIGN_PORT(ext_gpio_fpga_oe[6], o_user_11_09_lut_12[22])
`ACX_BIND_USER_DESIGN_PORT(ext_gpio_fpga_oe[7], o_user_11_09_lut_12[23])
`ACX_BIND_USER_DESIGN_PORT(ext_gpio_fpga_out[0], o_user_11_09_lut_13[12])
`ACX_BIND_USER_DESIGN_PORT(ext_gpio_fpga_out[1], o_user_11_09_lut_13[20])
`ACX_BIND_USER_DESIGN_PORT(ext_gpio_fpga_out[2], o_user_11_09_lut_14[0])
`ACX_BIND_USER_DESIGN_PORT(ext_gpio_fpga_out[3], o_user_11_09_lut_14[8])
`ACX_BIND_USER_DESIGN_PORT(ext_gpio_fpga_out[4], o_user_11_09_lut_14[16])
`ACX_BIND_USER_DESIGN_PORT(ext_gpio_fpga_out[5], o_user_11_09_lut_14[24])
`ACX_BIND_USER_DESIGN_PORT(ext_gpio_fpga_out[6], o_user_11_09_lut_15[4])
`ACX_BIND_USER_DESIGN_PORT(ext_gpio_fpga_out[7], o_user_11_09_lut_15[12])
`ACX_BIND_USER_DESIGN_PORT(ext_gpio_oe_l, o_user_11_09_lut_12[24])
`ACX_BIND_USER_DESIGN_PORT(ext_gpio_oe_l_oe, o_user_11_09_lut_12[14])
`ACX_BIND_USER_DESIGN_PORT(led_oe_l, o_user_11_09_lut_13[4])
`ACX_BIND_USER_DESIGN_PORT(led_oe_l_oe, o_user_11_09_lut_12[15])
`endif
    // Ports for vp815_gpio_n_b1
`ifdef ACX_GPIO_N_FULL
    // Core Data
`ACX_BIND_USER_DESIGN_PORT(ext_gpio_dir[0], o_user_11_09_lut_10[6])
`ACX_BIND_USER_DESIGN_PORT(ext_gpio_dir[1], o_user_11_09_lut_10[14])
`ACX_BIND_USER_DESIGN_PORT(ext_gpio_dir[2], o_user_11_09_lut_10[22])
`ACX_BIND_USER_DESIGN_PORT(ext_gpio_dir[3], o_user_11_09_lut_11[2])
`ACX_BIND_USER_DESIGN_PORT(ext_gpio_dir[4], o_user_11_09_lut_11[10])
`ACX_BIND_USER_DESIGN_PORT(ext_gpio_dir[5], o_user_11_09_lut_11[18])
`ACX_BIND_USER_DESIGN_PORT(ext_gpio_dir[6], o_user_11_09_lut_11[26])
`ACX_BIND_USER_DESIGN_PORT(ext_gpio_dir[7], o_user_11_09_lut_12[6])
`ACX_BIND_USER_DESIGN_PORT(ext_gpio_dir_oe[0], o_user_11_09_lut_09[10])
`ACX_BIND_USER_DESIGN_PORT(ext_gpio_dir_oe[1], o_user_11_09_lut_09[11])
`ACX_BIND_USER_DESIGN_PORT(ext_gpio_dir_oe[2], o_user_11_09_lut_09[12])
`ACX_BIND_USER_DESIGN_PORT(ext_gpio_dir_oe[3], o_user_11_09_lut_09[13])
`ACX_BIND_USER_DESIGN_PORT(ext_gpio_dir_oe[4], o_user_11_09_lut_09[14])
`ACX_BIND_USER_DESIGN_PORT(ext_gpio_dir_oe[5], o_user_11_09_lut_09[15])
`ACX_BIND_USER_DESIGN_PORT(ext_gpio_dir_oe[6], o_user_11_09_lut_09[16])
`ACX_BIND_USER_DESIGN_PORT(ext_gpio_dir_oe[7], o_user_11_09_lut_09[17])
`ACX_BIND_USER_DESIGN_PORT(led_l[4], o_user_11_09_lut_09[18])
`ACX_BIND_USER_DESIGN_PORT(led_l[5], o_user_11_09_lut_09[26])
`ACX_BIND_USER_DESIGN_PORT(led_l_oe[4], o_user_11_09_lut_09[8])
`ACX_BIND_USER_DESIGN_PORT(led_l_oe[5], o_user_11_09_lut_09[9])
`endif
    // Ports for vp815_gpio_n_b2
`ifdef ACX_GPIO_N_FULL
    // Core Data
`ACX_BIND_USER_DESIGN_PORT(led_l[0], o_user_11_09_lut_07[0])
`ACX_BIND_USER_DESIGN_PORT(led_l[1], o_user_11_09_lut_07[8])
`ACX_BIND_USER_DESIGN_PORT(led_l[2], o_user_11_09_lut_07[16])
`ACX_BIND_USER_DESIGN_PORT(led_l[3], o_user_11_09_lut_07[24])
`ACX_BIND_USER_DESIGN_PORT(led_l[6], o_user_11_09_lut_08[4])
`ACX_BIND_USER_DESIGN_PORT(led_l[7], o_user_11_09_lut_08[12])
`ACX_BIND_USER_DESIGN_PORT(led_l_oe[0], o_user_11_09_lut_06[4])
`ACX_BIND_USER_DESIGN_PORT(led_l_oe[1], o_user_11_09_lut_06[5])
`ACX_BIND_USER_DESIGN_PORT(led_l_oe[2], o_user_11_09_lut_06[6])
`ACX_BIND_USER_DESIGN_PORT(led_l_oe[3], o_user_11_09_lut_06[7])
`ACX_BIND_USER_DESIGN_PORT(led_l_oe[6], o_user_11_09_lut_06[8])
`ACX_BIND_USER_DESIGN_PORT(led_l_oe[7], o_user_11_09_lut_06[9])
`endif
    // Ports for vp815_gpio_s_b0
`ifdef ACX_GPIO_S_FULL
    // Core Data
`ACX_BIND_USER_DESIGN_PORT(fpga_avr_rxd, i_user_10_00_lut_07[7])
`ACX_BIND_USER_DESIGN_PORT(fpga_ftdi_rxd, i_user_10_00_lut_07[23])
`ACX_BIND_USER_DESIGN_PORT(fpga_i2c_mux_gnt, i_user_10_00_lut_06[11])
`ACX_BIND_USER_DESIGN_PORT(fpga_rst_l, i_user_10_00_lut_08[3])
`ACX_BIND_USER_DESIGN_PORT(qsfp_int_fpga_l, i_user_10_00_lut_06[3])
`ACX_BIND_USER_DESIGN_PORT(fpga_avr_txd, o_user_10_00_lut_07[26])
`ACX_BIND_USER_DESIGN_PORT(fpga_avr_txd_oe, o_user_10_00_lut_06[16])
`ACX_BIND_USER_DESIGN_PORT(fpga_ftdi_txd, o_user_10_00_lut_08[14])
`ACX_BIND_USER_DESIGN_PORT(fpga_ftdi_txd_oe, o_user_10_00_lut_06[18])
`ACX_BIND_USER_DESIGN_PORT(fpga_i2c_req_l, o_user_10_00_lut_07[18])
`ACX_BIND_USER_DESIGN_PORT(fpga_i2c_req_l_oe, o_user_10_00_lut_06[15])
`ACX_BIND_USER_DESIGN_PORT(irq_to_avr, o_user_10_00_lut_09[10])
`ACX_BIND_USER_DESIGN_PORT(irq_to_avr_oe, o_user_10_00_lut_06[21])
`ACX_BIND_USER_DESIGN_PORT(recov_clk_0, o_user_10_00_lut_06[22])
`ACX_BIND_USER_DESIGN_PORT(recov_clk_0_oe, o_user_10_00_lut_06[12])
`endif
    // Ports for vp815_gpio_s_b1
`ifdef ACX_GPIO_S_FULL
    // Core Data
`ACX_BIND_USER_DESIGN_PORT(u1pps_1_in, i_user_10_00_lut_03[22])
`ACX_BIND_USER_DESIGN_PORT(u1pps_2_in, i_user_10_00_lut_04[2])
`ACX_BIND_USER_DESIGN_PORT(u1pps_in, i_user_10_00_lut_03[14])
`ACX_BIND_USER_DESIGN_PORT(clk_gpio0, o_user_10_00_lut_03[16])
`ACX_BIND_USER_DESIGN_PORT(clk_gpio0_oe, o_user_10_00_lut_03[6])
`ACX_BIND_USER_DESIGN_PORT(clk_gpio1, o_user_10_00_lut_03[24])
`ACX_BIND_USER_DESIGN_PORT(clk_gpio1_oe, o_user_10_00_lut_03[7])
`ACX_BIND_USER_DESIGN_PORT(freq_dec, o_user_10_00_lut_05[24])
`ACX_BIND_USER_DESIGN_PORT(freq_dec_oe, o_user_10_00_lut_03[14])
`ACX_BIND_USER_DESIGN_PORT(freq_inc, o_user_10_00_lut_06[4])
`ACX_BIND_USER_DESIGN_PORT(freq_inc_oe, o_user_10_00_lut_03[15])
`ACX_BIND_USER_DESIGN_PORT(u1pps_1_dir, o_user_10_00_lut_05[0])
`ACX_BIND_USER_DESIGN_PORT(u1pps_1_dir_oe, o_user_10_00_lut_03[11])
`ACX_BIND_USER_DESIGN_PORT(u1pps_1_oe, o_user_10_00_lut_03[9])
`ACX_BIND_USER_DESIGN_PORT(u1pps_1_out, o_user_10_00_lut_04[12])
`ACX_BIND_USER_DESIGN_PORT(u1pps_2_dir, o_user_10_00_lut_05[8])
`ACX_BIND_USER_DESIGN_PORT(u1pps_2_dir_oe, o_user_10_00_lut_03[12])
`ACX_BIND_USER_DESIGN_PORT(u1pps_2_oe, o_user_10_00_lut_03[10])
`ACX_BIND_USER_DESIGN_PORT(u1pps_2_out, o_user_10_00_lut_04[20])
`ACX_BIND_USER_DESIGN_PORT(u1pps_en_l, o_user_10_00_lut_05[16])
`ACX_BIND_USER_DESIGN_PORT(u1pps_en_l_oe, o_user_10_00_lut_03[13])
`endif
    // Ports for vp815_gpio_s_b2
`ifdef ACX_GPIO_S_FULL
    // Core Data
`ACX_BIND_USER_DESIGN_PORT(fpga_sys_scl_in, i_user_10_00_lut_01[21])
`ACX_BIND_USER_DESIGN_PORT(fpga_sys_sda_in, i_user_10_00_lut_02[1])
`ACX_BIND_USER_DESIGN_PORT(fpga_sys_scl_oe, o_user_10_00_lut_00[6])
`ACX_BIND_USER_DESIGN_PORT(fpga_sys_scl_out, o_user_10_00_lut_02[2])
`ACX_BIND_USER_DESIGN_PORT(fpga_sys_sda_oe, o_user_10_00_lut_00[7])
`ACX_BIND_USER_DESIGN_PORT(fpga_sys_sda_out, o_user_10_00_lut_02[10])
`ACX_BIND_USER_DESIGN_PORT(recov_clk_1, o_user_10_00_lut_01[6])
`ACX_BIND_USER_DESIGN_PORT(recov_clk_1_oe, o_user_10_00_lut_00[3])
`endif

//////////////////////////////////////
// End IO Ring User Design Port Binding Include File
//////////////////////////////////////
