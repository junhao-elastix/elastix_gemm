#######################################
# ACE GENERATED SDC FILE
# Generated on: 2025.10.20 at 10:21:28 PDT
# By: ACE 10.3.1
# From project: elastix_gemm_top
#######################################
# IO Ring Boundary SDC File
#######################################

# Boundary clocks for ddr4

# Boundary clocks for gddr6_0

# Boundary clocks for gddr6_1

# Boundary clocks for gddr6_2

# Boundary clocks for gddr6_3

# Boundary clocks for gddr6_4

# Boundary clocks for gddr6_5

# Boundary clocks for gddr6_6

# Boundary clocks for gddr6_7

# Boundary clocks for noc

# Boundary clocks for pci_express_x16

# Boundary clocks for pll_ddr

# Boundary clocks for pll_gddr_SE

# Boundary clocks for pll_gddr_SW

# Boundary clocks for pll_noc
create_clock -period 10.0 {i_adm_clk}
# Frequency = 100.0 MHz
set_clock_uncertainty -setup 0.10770329614269007 [get_clocks {i_adm_clk}]

create_clock -period 5.0 {i_reg_clk}
# Frequency = 200.0 MHz
set_clock_uncertainty -setup 0.06403124237432849 [get_clocks {i_reg_clk}]

create_clock -period 10.0 {i_nap_clk}
# Frequency = 100.0 MHz
set_clock_uncertainty -setup 0.10770329614269007 [get_clocks {i_nap_clk}]


# Boundary clocks for pll_pcie

# Boundary clocks for vp815_clkio_ne

# Boundary clocks for vp815_clkio_nw

# Boundary clocks for vp815_clkio_se

# Boundary clocks for vp815_clkio_sw

# Boundary clocks for vp815_gpio_n_b0

# Boundary clocks for vp815_gpio_n_b1

# Boundary clocks for vp815_gpio_n_b2

# Boundary clocks for vp815_gpio_s_b0

# Boundary clocks for vp815_gpio_s_b1

# Boundary clocks for vp815_gpio_s_b2

# Virtual clocks for IO Ring IPs
create_clock -name v_acx_sc_PCIEX16_AXI_MASTER_CLK -period 1.0
create_clock -name v_acx_sc_PCIEX16_AXI_SLAVE_CLK -period 1.0

######################################
# End IO Ring Boundary SDC File
######################################
