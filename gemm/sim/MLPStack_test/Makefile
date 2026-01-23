# ---------------------------------------------------------------------
# Makefile for comp_mlp_bram_col_wrapper Simulation
#
# Purpose: Validate the 4-stack MLP BRAM column wrapper module
# Features:
#   - 4 parallel MLP stacks (NUM_STACKS = 4)
#   - Integer-domain FP adder pipeline for accurate summation
#   - Weight loading via i_wt_valid interface
#   - Activation streaming via i_act_valid interface
#   - 16 columns × FP16 output
#
# Author: MLP Wrapper Testing
# Date: Jan 2026
# ---------------------------------------------------------------------

# Simulation settings
SIM_TOP := tb_mlp_wrapper
DEVICE := AC7t1500
BASE_NAME := ac7t1500
LOG_FILE := sim_mlp_wrapper.log

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
GEMM_TB := .

# MLP RTL is in main RTL directory
MLP_RTL := $(GEMM_RTL)

# Compilation flags
VLOG_OPTIONS := +define+SIMULATION +define+SPEEDSTER7T_SIMULATION +define+ACX_ENABLE_MLP_SIM +define+ACX_ENABLE_BRAM_SIM +define+ACX_ENABLE_PRIMITIVE_SIM
VLOG_OPTIONS += -sv
VLOG_OPTIONS += -timescale "1ps/1ps"
VLOG_OPTIONS += -err VCP2675 W1   # Suppress warning: initial block + always_ff on same signal
VLOG_OPTIONS += +incdir+$(ACE_INSTALL_DIR)/libraries/
VLOG_OPTIONS += +incdir+$(ACX_DEVICE_INSTALL_DIR)/sim
VLOG_OPTIONS += +incdir+$(ACX_LIB_S7T)/common
VLOG_OPTIONS += +incdir+$(GEMM_INC)
VLOG_OPTIONS += -f $(DSM_INCLUDE_FILE)
VLOG_OPTIONS += -msg 0

# =========================================================================
# Debug Macros - Enable verbose output per module
# =========================================================================
VLOG_OPTIONS += +define+DEBUG_MLPSTACK          # comp_MLPStack.sv
# =========================================================================

# Default target
all: run

# Create work library
create_library:
	@echo "Creating work library..." | tee $(LOG_FILE)
	@vlib work >> $(LOG_FILE) 2>&1

# Compile MLP wrapper design
compile: create_library
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "  MLP Wrapper Compilation Started: $$(date)" | tee -a $(LOG_FILE)
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "Compiling Achronix primitives..." | tee -a $(LOG_FILE)
	@export LD_LIBRARY_PATH="" && \
	vlog $(VLOG_OPTIONS) \
		$(DSM_COMPILE_FILE) \
		$(DEVICE_MODELS) \
		$(ACX_LIB_S7T)/common/acx_integer.sv \
		$(ACX_LIB_S7T)/common/acx_floating_point.sv >> $(LOG_FILE) 2>&1 || \
		(echo "ERROR: ACX library compilation failed. See $(LOG_FILE)" && exit 1)
	@echo "Compiling MLP RTL modules..." | tee -a $(LOG_FILE)
	@export LD_LIBRARY_PATH="" && \
	vlog $(VLOG_OPTIONS) \
		$(MLP_RTL)/comp_mlp_dot16_int8.sv \
		$(MLP_RTL)/comp_mlp_dot16_bfp8.sv \
		$(MLP_RTL)/weight_bram.sv \
		$(MLP_RTL)/comp_MLP.sv \
		$(MLP_RTL)/comp_MLPRow.sv \
		$(MLP_RTL)/comp_stack_fifo.sv \
		$(MLP_RTL)/fp_to_int.sv \
		$(MLP_RTL)/int_to_fp.sv \
		$(MLP_RTL)/int_adder_tree.sv \
		$(MLP_RTL)/comp_fp_adder_pipeline.sv \
		$(MLP_RTL)/comp_MLPStack.sv >> $(LOG_FILE) 2>&1 || \
		(echo "ERROR: MLP RTL compilation failed. See $(LOG_FILE)" && exit 1)
	@echo "Compiling testbench..." | tee -a $(LOG_FILE)
	@export LD_LIBRARY_PATH="" && \
	vlog $(VLOG_OPTIONS) \
		tb_mlp_wrapper.sv >> $(LOG_FILE) 2>&1 || \
		(echo "ERROR: Testbench compilation failed. See $(LOG_FILE)" && exit 1)
	@echo "MLP wrapper compilation completed successfully" | tee -a $(LOG_FILE)
	@echo ""

# Run MLP wrapper simulation
run_vsim: compile
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "  MLP Wrapper Simulation Started: $$(date)" | tee -a $(LOG_FILE)
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "Running comp_mlp_bram_col_wrapper simulation..." | tee -a $(LOG_FILE)
	@export LD_LIBRARY_PATH="" && \
	vsim -c -do "run -all; quit -force" work.$(SIM_TOP) >> $(LOG_FILE) 2>&1 || \
		(echo "ERROR: MLP wrapper simulation failed. See $(LOG_FILE)" && exit 1)
	@echo "" | tee -a $(LOG_FILE)
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "  MLP Wrapper Simulation Completed: $$(date)" | tee -a $(LOG_FILE)
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "" | tee -a $(LOG_FILE)
	@echo "Extracting test summary..." | tee -a $(LOG_FILE)
	@grep -E "PASS|FAIL|ALL TESTS|Test" $(LOG_FILE) | tail -20 || echo "Warning: Could not find test summary"
	@echo ""
	@echo "Full log available in: $(LOG_FILE)"

# Run tests
run: run_vsim

# Debug MLP wrapper with GUI
debug: compile
	@echo "=== Running comp_mlp_bram_col_wrapper Debug Simulation ==="
	@export LD_LIBRARY_PATH="" && \
	vsim -gui work.$(SIM_TOP) &

# View full simulation log
view-log:
	@if [ -f $(LOG_FILE) ]; then \
		less +G $(LOG_FILE); \
	else \
		echo "Error: $(LOG_FILE) not found. Run 'make run' first."; \
	fi

# Show test summary only
summary:
	@if [ -f $(LOG_FILE) ]; then \
		echo ""; \
		echo "Test Results from $(LOG_FILE):"; \
		echo "======================================"; \
		grep -E "PASS|FAIL|Test|SUMMARY" $(LOG_FILE) | tail -30; \
		echo ""; \
	else \
		echo "Error: $(LOG_FILE) not found. Run 'make run' first."; \
	fi

# Clean up
clean:
	@echo "=== Cleaning Simulation Files ==="
	@rm -rf work/
	@rm -f transcript
	@rm -f *.wlf
	@rm -f *.log
	@rm -f *.vcd
	@rm -f *.asdb
	@rm -f *.tmp
	@echo "Clean complete"

# Help
help:
	@echo "========================================================================"
	@echo "  Makefile for comp_mlp_bram_col_wrapper Simulation"
	@echo "========================================================================"
	@echo ""
	@echo "Purpose: Test comp_mlp_bram_col_wrapper.sv standalone"
	@echo "         Validates 4-stack MLP compute array before engine refactoring"
	@echo ""
	@echo "Targets:"
	@echo "  make             - Compile and run simulation (outputs to $(LOG_FILE))"
	@echo "  make run         - Compile and run simulation (same as make)"
	@echo "  make compile     - Compile only (no simulation)"
	@echo "  make debug       - Run with GUI for debugging"
	@echo "  make summary     - Show test results summary"
	@echo "  make view-log    - View full simulation log ($(LOG_FILE))"
	@echo "  make clean       - Remove all generated files"
	@echo "  make help        - Show this help message"
	@echo ""
	@echo "Test Suite:"
	@echo "  Test 1: Minimal smoke test (C=1, V=1, B=1)"
	@echo "  Test 2: Single column multi-NV accumulation (C=1, V=4, B=1)"
	@echo "  Test 3: Multi-column single NV (C=4, V=1, B=1)"
	@echo "  Test 4: Full 16-column test (C=16, V=1, B=1)"
	@echo "  Test 5: Multi-batch test (C=4, V=2, B=4)"
	@echo ""
	@echo "Architecture:"
	@echo "  - 4 parallel mlp_bram_col stacks"
	@echo "  - 8 MLPs per stack (16 columns total)"
	@echo "  - Integer-domain FP adder pipeline"
	@echo "  - FP24 -> Int -> Sum -> FP16 conversion"
	@echo ""
	@echo "========================================================================"

.PHONY: all create_library compile run_vsim run debug view-log summary clean help
