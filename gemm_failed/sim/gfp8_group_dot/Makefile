# ---------------------------------------------------------------------
# Makefile for GFP8 Group Dot Product Module Simulation with Achronix MLP
#
# Purpose: Validate 32-pair GFP8 dot product computation using actual ACX_INT_MULT_ADD primitive
# Date: Thu Oct 9 2025
# Based on: matrix_engine_w4gfp8 simulation pattern
# ---------------------------------------------------------------------

# Simulation settings
SIM_TOP := tb_gfp8_group_dot
DEVICE := AC7t1500
BASE_NAME := ac7t1500

# Achronix environment setup (following matrix_engine_w4gfp8 pattern)
export ACX_DEVICE_INSTALL_DIR := $(ACE_INSTALL_DIR)/system/data/$(DEVICE)
DSM_INCLUDE_FILE := $(ACX_DEVICE_INSTALL_DIR)/sim/$(BASE_NAME)_dsm_incdirs.f
DSM_COMPILE_FILE := $(ACX_DEVICE_INSTALL_DIR)/sim/$(BASE_NAME)_dsm_filelist.v
DEVICE_MODELS := $(ACE_INSTALL_DIR)/libraries/device_models/$(DEVICE)_simmodels.sv

# Achronix Speedster7t library paths
ACX_LIB_S7T := $(ACE_INSTALL_DIR)/libraries/speedster7t

# Compilation flags (following matrix_engine_w4gfp8 pattern)
VLOG_OPTIONS := +define+SIMULATION
VLOG_OPTIONS += -sv
VLOG_OPTIONS += -timescale "1ps/1ps"
VLOG_OPTIONS += +incdir+$(ACE_INSTALL_DIR)/libraries/
VLOG_OPTIONS += +incdir+$(ACX_DEVICE_INSTALL_DIR)/sim
VLOG_OPTIONS += +incdir+$(ACX_LIB_S7T)/common
VLOG_OPTIONS += -f $(DSM_INCLUDE_FILE)
VLOG_OPTIONS += -msg 0

# Default target
all: run

# Create work library
create_library :
	vlib work

# Compile the design
compile : create_library
	@echo "=== Compiling GFP8 Group Dot with Achronix MLP Primitive ==="
	@echo "Using ACE_INSTALL_DIR: $(ACE_INSTALL_DIR)"
	@echo "Using ACX_DEVICE_INSTALL_DIR: $(ACX_DEVICE_INSTALL_DIR)"
	@export LD_LIBRARY_PATH="" && \
	vlog $(VLOG_OPTIONS) \
		$(DSM_COMPILE_FILE) \
		$(DEVICE_MODELS) \
		$(ACX_LIB_S7T)/common/acx_integer.sv \
		../../src/rtl/gfp8_group_dot_mlp.sv \
		../../src/tb/tb_gfp8_group_dot.sv

# Run simulation
run_vsim : compile
	@echo "=== Running GFP8 Group Dot Simulation ==="
	@export LD_LIBRARY_PATH="" && \
	vsim -c -do "run -all; quit -force" work.$(SIM_TOP)

# Complete run (compile + simulate)
run : run_vsim

# Run with GUI for debugging
debug : compile
	@echo "=== Running GFP8 Group Dot Debug Simulation ==="
	@export LD_LIBRARY_PATH="" && \
	vsim -gui work.$(SIM_TOP)

# Clean up
clean :
	@echo "=== Cleaning Simulation Files ==="
	@rm -rf work/
	@rm -f transcript
	@rm -f *.wlf
	@rm -f *.log
	@rm -f *.vcd
	@rm -f *.asdb

.PHONY: all create_library compile run_vsim run debug clean
