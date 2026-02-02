# ---------------------------------------------------------------------
# Makefile for Engine Row Testbench
#
# Purpose: Test one complete row of the GEMM engine:
#   - dispatcher_control_2d: Fetches data from memory, dispatches to CE
#   - compute_engine_2d: Computes matrix multiplication
#   - Address conversion layer (from engine_top_2d)
#
# Author: Engine Row Testing
# Date: Jan 2026
# ---------------------------------------------------------------------

# Simulation settings
SIM_TOP := tb_engine_row
DEVICE := AC7t1500
BASE_NAME := ac7t1500
LOG_FILE := sim_engine_row.log

# Achronix environment setup
export ACX_DEVICE_INSTALL_DIR := $(ACE_INSTALL_DIR)/system/data/$(DEVICE)
DSM_INCLUDE_FILE := $(ACX_DEVICE_INSTALL_DIR)/sim/$(BASE_NAME)_dsm_incdirs.f
DSM_COMPILE_FILE := $(ACX_DEVICE_INSTALL_DIR)/sim/$(BASE_NAME)_dsm_filelist.v
DEVICE_MODELS := $(ACE_INSTALL_DIR)/libraries/device_models/$(DEVICE)_simmodels.sv

# Achronix Speedster7t library paths
ACX_LIB_S7T := $(ACE_INSTALL_DIR)/libraries/speedster7t

# Source directories
GEMM_RTL := ../../src/rtl
GEMM_INC := ../../src/include
GEMM_TB := ../../src/tb

# Configurable parameters
NUM_MLPS ?= 2
NUM_COLS ?= $(shell echo $$(($(NUM_MLPS) * 2)))

# Compilation flags
VLOG_OPTIONS := +define+SIMULATION +define+SPEEDSTER7T_SIMULATION +define+ACX_ENABLE_MLP_SIM +define+ACX_ENABLE_BRAM_SIM +define+ACX_ENABLE_PRIMITIVE_SIM +define+USE_BEHAVIORAL_BRAM
VLOG_OPTIONS += +define+NUM_MLPS=$(NUM_MLPS)
VLOG_OPTIONS += +define+NUM_COLS=$(NUM_COLS)
VLOG_OPTIONS += -sv
VLOG_OPTIONS += -timescale "1ps/1ps"

# =========================================================================
# Debug Macros - Uncomment to enable verbose output per module
# =========================================================================
# VLOG_OPTIONS += +define+DEBUG_MLPSTACK          # comp_MLPStack.sv, comp_MLPStack_oFIFO.sv
# VLOG_OPTIONS += +define+DEBUG_COMPUTE           # compute_engine_2d.sv
# VLOG_OPTIONS += +define+DEBUG_DISPATCHER_CTRL   # dispatcher_control_2d.sv
# VLOG_OPTIONS += +define+DEBUG_DISPATCHER        # dispatcher_2d.sv
# VLOG_OPTIONS += +define+DEBUG_FETCHER           # fetcher_2d.sv
VLOG_OPTIONS += +define+USE_BEHAVIORAL_BRAM      # Use behavioral BRAM model for simulation
# =========================================================================

VLOG_OPTIONS += -err VCP2675 W1   # Suppress warning: initial block + always_ff on same signal
VLOG_OPTIONS += +incdir+$(ACE_INSTALL_DIR)/libraries/
VLOG_OPTIONS += +incdir+$(ACX_DEVICE_INSTALL_DIR)/sim
VLOG_OPTIONS += +incdir+$(ACX_LIB_S7T)/common
VLOG_OPTIONS += +incdir+$(GEMM_INC)
VLOG_OPTIONS += -f $(DSM_INCLUDE_FILE)
VLOG_OPTIONS += -msg 0

.PHONY: all clean run compile debug view-log summary help

# Default target
all: run

# Create work library
create_library:
	@echo "Creating work library..." | tee $(LOG_FILE)
	@vlib work >> $(LOG_FILE) 2>&1

# Compile design
compile: create_library
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "  Engine Row Testbench Compilation Started: $$(date)" | tee -a $(LOG_FILE)
	@echo "  NUM_MLPS=$(NUM_MLPS), NUM_COLS=$(NUM_COLS)" | tee -a $(LOG_FILE)
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "Compiling Achronix primitives..." | tee -a $(LOG_FILE)
	@export LD_LIBRARY_PATH="" && \
	vlog $(VLOG_OPTIONS) \
		$(DSM_COMPILE_FILE) \
		$(DEVICE_MODELS) \
		$(ACX_LIB_S7T)/common/acx_integer.sv \
		$(ACX_LIB_S7T)/common/acx_floating_point.sv >> $(LOG_FILE) 2>&1 || \
		(echo "ERROR: ACX library compilation failed. See $(LOG_FILE)" && exit 1)
	@echo "Compiling all RTL modules..." | tee -a $(LOG_FILE)
	@export LD_LIBRARY_PATH="" && \
	vlog $(VLOG_OPTIONS) \
		$(GEMM_INC)/gemm_pkg.sv \
		$(GEMM_RTL)/nap_responder_wrapper.sv \
		$(GEMM_RTL)/flex_fifo.sv \
		$(GEMM_RTL)/comp_row_bram.sv \
		$(GEMM_RTL)/fetcher_2d.sv \
		$(GEMM_RTL)/dispatcher_2d.sv \
		$(GEMM_RTL)/dispatcher_control_2d.sv \
		$(GEMM_RTL)/comp_mlp_dot16_bfp8.sv \
		$(GEMM_RTL)/weight_bram.sv \
		$(GEMM_RTL)/comp_MLP.sv \
		$(GEMM_RTL)/comp_MLPRow.sv \
		$(GEMM_RTL)/comp_stack_fifo.sv \
		$(GEMM_RTL)/fp_to_int.sv \
		$(GEMM_RTL)/int_to_fp.sv \
		$(GEMM_RTL)/int_adder_tree.sv \
		$(GEMM_RTL)/comp_fp_adder_pipeline.sv \
		$(GEMM_RTL)/comp_MLPStack.sv \
		$(GEMM_RTL)/comp_MLPStack_oFIFO.sv \
		$(GEMM_RTL)/compute_engine_2d.sv >> $(LOG_FILE) 2>&1 || \
		(echo "ERROR: RTL compilation failed. See $(LOG_FILE)" && exit 1)
	@echo "Compiling memory models and testbench..." | tee -a $(LOG_FILE)
	@export LD_LIBRARY_PATH="" && \
	vlog $(VLOG_OPTIONS) \
		$(GEMM_TB)/tb_memory_model_realistic.sv \
		tb_engine_row.sv >> $(LOG_FILE) 2>&1 || \
		(echo "ERROR: Testbench compilation failed. See $(LOG_FILE)" && exit 1)
	@echo "Compilation complete!" | tee -a $(LOG_FILE)
	@echo "======================================================================" | tee -a $(LOG_FILE)

# Run simulation
run: compile
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "  Engine Row Simulation Started: $$(date)" | tee -a $(LOG_FILE)
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@export LD_LIBRARY_PATH="" && \
	vsim -c -asdb_skip -do "run -all; quit -force" work.$(SIM_TOP) >> $(LOG_FILE) 2>&1 || \
		(echo "ERROR: Simulation failed. See $(LOG_FILE)" && exit 1)
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "  Engine Row Simulation Complete: $$(date)" | tee -a $(LOG_FILE)
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo ""
	@make summary

# Debug with GUI
debug: compile
	@echo "Starting simulation with GUI..."
	@export LD_LIBRARY_PATH="" && \
	vsim work.$(SIM_TOP) &

# View simulation log
view-log:
	@less $(LOG_FILE)

# Extract and display summary
summary:
	@echo ""
	@echo "======================================================================="
	@echo "  ENGINE ROW TESTBENCH SUMMARY"
	@echo "======================================================================="
	@grep -E "\[TB\]|PASS|FAIL|TEST|MISMATCH|MATMUL|FETCH|DISPATCH|SUMMARY" $(LOG_FILE) | tail -80 || \
		echo "No summary found. Run 'make view-log' to see full output."
	@echo "======================================================================="
	@echo ""

# Clean
clean:
	@echo "=== Cleaning Simulation Files ==="
	@rm -rf work dataset.asdb $(LOG_FILE) transcript vsim.wlf *.vcd
	@echo "Clean complete"

# Help
help:
	@echo "Engine Row Testbench Makefile"
	@echo "============================="
	@echo ""
	@echo "Targets:"
	@echo "  make          - Compile and run simulation (default)"
	@echo "  make compile  - Compile only"
	@echo "  make run      - Compile and run simulation"
	@echo "  make debug    - Run with GUI"
	@echo "  make summary  - Display test summary"
	@echo "  make view-log - View simulation log"
	@echo "  make clean    - Remove generated files"
	@echo "  make help     - Show this help message"
	@echo ""
	@echo "Configuration:"
	@echo "  NUM_MLPS      - Number of MLPs (default: 2)"
	@echo "                  make run NUM_MLPS=4"
	@echo ""
	@echo "Output File: $(LOG_FILE)"
	@echo ""
