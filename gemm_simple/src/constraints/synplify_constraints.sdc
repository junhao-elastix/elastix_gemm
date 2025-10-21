# -------------------------------------------------------------------------
# Synplify timing constaint file
# All clocks and clock relationships should be defined in this file for synthesis
# Note : There are small differences between Synplify Pro and ACE SDC syntax
# therefore it is not recommended to use the same file for both, instead to
# have two separate files.
# -------------------------------------------------------------------------

# -------------------------------------------------------------------------
# Primary clock timing constraints
# -------------------------------------------------------------------------
# Set 400MHz target for NAP clock
set NAP_CLK_PERIOD 2.500
create_clock -name nap_clk [get_ports i_nap_clk] -period $NAP_CLK_PERIOD

# Set 200MHz target for reg clock
set REG_CLK_PERIOD 5.000
create_clock -name reg_clk [get_ports i_reg_clk] -period $REG_CLK_PERIOD

# Set 100MHz target for ADM clock
set ADM_CLK_PERIOD 10.000
create_clock -name adm_clk [get_ports i_adm_clk] -period $ADM_CLK_PERIOD

# Set 10MHz target for tck
# This is bit[0] of the t_JTAG_INPUT type
set TCK_CLK_PERIOD 100.000
create_clock -name tck_clk [get_nets i_jtag_in\[0\]] -period $TCK_CLK_PERIOD

# -------------------------------------------------------------------------
# Example of defining a generated clock
# -------------------------------------------------------------------------
# create_generated_clock -name clk_gate [ get_pins {i_clkgate/clk_out} ] -source  [get_ports {i_clk} ] -divide_by 1

# Output clock from Snapshot
# As the SNAPHOT_UNIT is encrypted, Synplify reports that there is no path from tck_clk to tck_core.
# So create as a separate clock and place in the same clock group
create_clock -name tck_core \
          [get_pins x_acx_dev_mgr.x_dev_mgr.u.u.u.genblk2\.x_acx_jtap_interface.x_acx_jtap.clk_ipin_tck.dout ] \
          -period $TCK_CLK_PERIOD

# -------------------------------------------------------------------------
# Design has four input clocks.  reg_clk and adm_clk are synchronous from the same PLL
# The nap_clk is also synchronous to these two, but treat as async
# -------------------------------------------------------------------------
set_clock_groups -asynchronous -group {nap_clk} \
                               -group {reg_clk adm_clk} \
                               -group {tck_clk tck_core}

# -------------------------------------------------------------------------
# BUILD TIME OPTIMIZATIONS - Explicit timing constraints to prevent over-optimization
# -------------------------------------------------------------------------

# Set explicit clock uncertainties to give realistic timing targets
set_clock_uncertainty -setup 0.15 [get_clocks reg_clk]
set_clock_uncertainty -setup 0.10 [get_clocks adm_clk] 
set_clock_uncertainty -setup 0.20 [get_clocks nap_clk]

# Set max delay constraints between clock domains to prevent excessive optimization
set_max_delay 4.5 -from [get_clocks reg_clk] -to [get_clocks nap_clk]
set_max_delay 4.5 -from [get_clocks nap_clk] -to [get_clocks reg_clk]
set_max_delay 9.5 -from [get_clocks reg_clk] -to [get_clocks adm_clk]
set_max_delay 9.5 -from [get_clocks adm_clk] -to [get_clocks reg_clk]

# Set false paths for non-critical reset and configuration signals
set_false_path -from [get_ports i_rstn]
set_false_path -from [get_ports i_flr_reset]

# Set multicycle paths for slower control signals (reduce optimization effort)
set_multicycle_path -setup 2 -from [get_clocks reg_clk] -to [get_clocks reg_clk] -through [get_nets *control*]
set_multicycle_path -hold 1 -from [get_clocks reg_clk] -to [get_clocks reg_clk] -through [get_nets *control*]

# Input/Output delay constraints (prevent over-optimization of I/O paths)
set_input_delay -clock reg_clk -max 1.0 [all_inputs]
set_input_delay -clock reg_clk -min 0.5 [all_inputs]
set_output_delay -clock reg_clk -max 1.0 [all_outputs]
set_output_delay -clock reg_clk -min 0.5 [all_outputs]

