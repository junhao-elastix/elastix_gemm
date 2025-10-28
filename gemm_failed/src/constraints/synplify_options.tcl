# -------------------------------------------------------------------------
# Synplify options file
# Any setting here will override the default settings when the Synplify Pro
# project is build using the script flow
# -------------------------------------------------------------------------

# -------------------------------------------------------------------------
# Define the top level
# -------------------------------------------------------------------------
set_option -top_module "elastix_gemm_top"

# -------------------------------------------------------------------------
# Set the following define if snapshot is to be included in the design
# -------------------------------------------------------------------------
set_option -hdl_define -set ACX_USE_SNAPSHOT=1

# -------------------------------------------------------------------------
# Set the default frequency for undefined clocks
# -------------------------------------------------------------------------
set_option -frequency 500

# -------------------------------------------------------------------------
# Example of how to set the maximum fanout
# -------------------------------------------------------------------------
# set_option -maxfan 100

# -------------------------------------------------------------------------
# Resolve mixed drivers (constant + logic on same net)
# Needed when multiple NAP instances have tie-offs to GND/VCC
# -------------------------------------------------------------------------
set_option -resolve_mixed_drivers 1

# -------------------------------------------------------------------------
# BUILD TIME OPTIMIZATIONS - Aggressive settings for faster synthesis
# -------------------------------------------------------------------------

# Enable high-effort optimization for faster convergence
set_option -hdl_param -set "OPTIMIZATION_GOAL=SPEED"

# Reduce synthesis effort for faster builds (compromise: speed vs. optimal results)
set_option -synthesis_effort "high"

# Enable resource sharing to reduce logic replication
set_option -resource_sharing 1

# Optimize FSM extraction for faster processing
set_option -auto_fsm_extract 1
set_option -fsm_explorer 1

# Reduce retiming iterations to speed up synthesis
set_option -retiming_iteration_limit 3

# Enable pipeline optimization for better timing closure
set_option -pipeline 1

# Set fanout limits to reduce optimization complexity
set_option -maxfan 50

# Enable arithmetic optimization for faster builds
set_option -arithmetic_optimization 1

# Optimize for speed rather than area (faster synthesis)
set_option -optimize_for_speed 1

