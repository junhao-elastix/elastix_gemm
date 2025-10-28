# -------------------------------------------------------------------------
# ACE timing constaint file
# Clocks, clock relationships, and IO timing constraints should be set
# in this file
# Clocks are set in the <design_name>_ioring.sdc file
# -------------------------------------------------------------------------

# -------------------------------------------------------------------------
# Example of adding new clocks, (in this example through a GPIO pin)
# -------------------------------------------------------------------------
# Set 250MHz target
# set INCLK_PERIOD 2.0
# create_clock -name gpio_clk [get_ports i_gpio_clk] -period $INCLK_PERIOD

# -------------------------------------------------------------------------
# Example of IO timing constraints
# -------------------------------------------------------------------------
# It is recommended that in_clk and out_clk are virtual clocks, based on the
# IO ports of their respective clocks.  This allows for the clock skew 
# into the device fabric.
# set_input_delay  -clock in_clk  -min  2   [get_ports din\[*\]]
# set_input_delay  -clock in_clk  -max  2.8 [get_ports din\[*\]]
# set_output_delay -clock out_clk -min -0.2 [get_ports dout\[*\]]
# set_output_delay -clock out_clk -max -0.6 [get_ports dout\[*\]]

# -------------------------------------------------------------------------
# Example of defining a generated clock
# -------------------------------------------------------------------------
# create_generated_clock -name clk_gate [ get_pins {i_clkgate/clk_out} ] -source  [get_ports {i_clk} ] -divide_by 1

# -------------------------------------------------------------------------
# Design has three PLL clocks. They have to all be treated as asynchronous
# and there should be CDC logic between any of the domain crossing paths
#
# Clock domains:
#   i_reg_clk (200 MHz): Register control block, PCIe register interface
#   i_nap_clk (300-400 MHz): NAP/NoC operations, GDDR6 access, BRAM operations
#   i_adm_clk (100 MHz): ADM/GDDR6 training
#
# CDC paths in design:
#   1. reg_control_block: Register read/write between i_reg_clk and i_nap_clk
#   2. Legacy gddr6_to_bram_processor: ARCHIVED - timing constraints removed
#      - Uses ACX_SYNCHRONIZER for all single-bit and multi-bit signals
#      - Control: enable, trigger, process_mode, process_param, addresses, length
#      - Status: busy, done, error
# -------------------------------------------------------------------------
set_clock_groups -asynchronous -group {i_nap_clk} \
                               -group {i_reg_clk} \
                               -group {i_adm_clk}
                               
# -------------------------------------------------------------------------
# Example of optionally creating clocks based on the build
# -------------------------------------------------------------------------
# Auto detect if snapshot is in the design
# if { [get_ports tck] != "" } { 
#     set use_snapshot 1
# } else {
#     set use_snapshot 0
# }
# if { $use_snapshot==1 } {
#     create_clock -period 100.0 -name tck   [get_ports tck]
#     set_clock_groups -asynchronous -group {tck}
# }

# JTAG clock: 10MHz
# Uncomment following if using snapshot or ADM
create_clock -period 40 [get_ports {i_jtag_in[0]}] -name tck
set_clock_groups -asynchronous -group {tck}

