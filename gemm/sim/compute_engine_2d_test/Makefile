# ---------------------------------------------------------------------
# Makefile for compute_engine_2d Simulation
#
# Purpose: Validate the compute engine with:
#   - comp_row_bram for activations
#   - comp_MLPStack for computation
#   - comp_MLPStack_oFIFO for result buffering
#
# Author: Compute Engine 2D Testing
# Date: Jan 21, 2026
# ---------------------------------------------------------------------

# Simulation settings
SIM_TOP := tb_compute_engine_2d
DEVICE := AC7t1500
BASE_NAME := ac7t1500
LOG_FILE := sim_compute_engine_2d.log

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

# Configurable parameters (default: 8 MLPs, 16 columns)
# Override via: make run NUM_MLPS=2  (or NUM_MLPS=4, NUM_MLPS=8)
NUM_MLPS ?= 8
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
VLOG_OPTIONS += +define+DEBUG_MLPSTACK          # comp_MLPStack.sv, comp_MLPStack_oFIFO.sv
VLOG_OPTIONS += +define+DEBUG_COMPUTE           # compute_engine_2d.sv
# VLOG_OPTIONS += +define+DEBUG_WEIGHT_BRAM       # weight_bram.sv (very verbose)
# =========================================================================
VLOG_OPTIONS += -err VCP2675 W1   # Suppress warning: initial block + always_ff on same signal
VLOG_OPTIONS += +incdir+$(ACE_INSTALL_DIR)/libraries/
VLOG_OPTIONS += +incdir+$(ACX_DEVICE_INSTALL_DIR)/sim
VLOG_OPTIONS += +incdir+$(ACX_LIB_S7T)/common
VLOG_OPTIONS += +incdir+$(GEMM_INC)
VLOG_OPTIONS += -f $(DSM_INCLUDE_FILE)
VLOG_OPTIONS += -msg 0

# Default target
all: run

# Create work library
create_library:
	@echo "Creating work library..." | tee $(LOG_FILE)
	@vlib work >> $(LOG_FILE) 2>&1

# Compile design
compile: create_library
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "  Compute Engine 2D Compilation Started: $$(date)" | tee -a $(LOG_FILE)
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "Compiling Achronix primitives..." | tee -a $(LOG_FILE)
	@export LD_LIBRARY_PATH="" && \
	vlog $(VLOG_OPTIONS) \
		$(DSM_COMPILE_FILE) \
		$(DEVICE_MODELS) \
		$(ACX_LIB_S7T)/common/acx_integer.sv \
		$(ACX_LIB_S7T)/common/acx_floating_point.sv >> $(LOG_FILE) 2>&1 || \
		(echo "ERROR: ACX library compilation failed. See $(LOG_FILE)" && exit 1)
	@echo "Compiling RTL modules..." | tee -a $(LOG_FILE)
	@export LD_LIBRARY_PATH="" && \
	vlog $(VLOG_OPTIONS) \
		$(GEMM_INC)/gemm_pkg.sv \
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
		$(GEMM_RTL)/flex_fifo.sv \
		$(GEMM_RTL)/comp_MLPStack_oFIFO.sv \
		$(GEMM_RTL)/comp_row_bram.sv \
		$(GEMM_RTL)/compute_engine_2d.sv >> $(LOG_FILE) 2>&1 || \
		(echo "ERROR: RTL compilation failed. See $(LOG_FILE)" && exit 1)
	@echo "Compiling testbench..." | tee -a $(LOG_FILE)
	@export LD_LIBRARY_PATH="" && \
	vlog $(VLOG_OPTIONS) \
		tb_compute_engine_2d.sv >> $(LOG_FILE) 2>&1 || \
		(echo "ERROR: Testbench compilation failed. See $(LOG_FILE)" && exit 1)
	@echo "Compilation completed successfully" | tee -a $(LOG_FILE)
	@echo ""

# Run simulation
run_vsim: compile
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "  Compute Engine 2D Simulation Started: $$(date)" | tee -a $(LOG_FILE)
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "Running compute_engine_2d simulation..." | tee -a $(LOG_FILE)
	@export LD_LIBRARY_PATH="" && \
	vsim -c -asdb_skip -do "run -all; quit -force" work.$(SIM_TOP) >> $(LOG_FILE) 2>&1 || \
		(echo "ERROR: Simulation failed. See $(LOG_FILE)" && exit 1)
	@echo "" | tee -a $(LOG_FILE)
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "  Compute Engine 2D Simulation Completed: $$(date)" | tee -a $(LOG_FILE)
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "" | tee -a $(LOG_FILE)
	@echo "Extracting test summary..." | tee -a $(LOG_FILE)
	@grep -E "PASS|FAIL|ALL TESTS|Test|SUMMARY" $(LOG_FILE) | tail -30 || echo "Warning: Could not find test summary"
	@echo ""
	@echo "Full log available in: $(LOG_FILE)"

# Run tests
run: run_vsim

# Debug with GUI
debug: compile
	@echo "=== Running Compute Engine 2D Debug Simulation ==="
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
		grep -E "PASS|FAIL|Test|SUMMARY" $(LOG_FILE) | tail -40; \
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

# =========================================================================
# Multi-Configuration Targets
# =========================================================================
# Run all NUM_MLPS configurations: 2, 4, 8 (NUM_COLS: 4, 8, 16)
run_all_configs:
	@echo "========================================================================"
	@echo "  Running All NUM_MLPS Configurations"
	@echo "========================================================================"
	@echo ""
	@echo "=== Configuration: NUM_MLPS=2 (NUM_COLS=4) ===" && \
		$(MAKE) clean > /dev/null 2>&1 && \
		$(MAKE) run NUM_MLPS=2 && \
		echo ""
	@echo "=== Configuration: NUM_MLPS=4 (NUM_COLS=8) ===" && \
		$(MAKE) clean > /dev/null 2>&1 && \
		$(MAKE) run NUM_MLPS=4 && \
		echo ""
	@echo "=== Configuration: NUM_MLPS=8 (NUM_COLS=16) ===" && \
		$(MAKE) clean > /dev/null 2>&1 && \
		$(MAKE) run NUM_MLPS=8 && \
		echo ""
	@echo "========================================================================"
	@echo "  All Configurations Complete"
	@echo "========================================================================"

# Help
help:
	@echo "========================================================================"
	@echo "  Makefile for compute_engine_2d Simulation"
	@echo "========================================================================"
	@echo ""
	@echo "Purpose: Test compute_engine_2d.sv with:"
	@echo "  - comp_row_bram for activations"
	@echo "  - comp_MLPStack for computation"
	@echo "  - comp_MLPStack_oFIFO for result buffering"
	@echo ""
	@echo "Current Configuration: NUM_MLPS=$(NUM_MLPS), NUM_COLS=$(NUM_COLS)"
	@echo ""
	@echo "Targets:"
	@echo "  make                  - Compile and run simulation (outputs to $(LOG_FILE))"
	@echo "  make run              - Compile and run simulation (same as make)"
	@echo "  make run NUM_MLPS=2   - Run with 2 MLPs (4 columns)"
	@echo "  make run NUM_MLPS=4   - Run with 4 MLPs (8 columns)"
	@echo "  make run NUM_MLPS=8   - Run with 8 MLPs (16 columns)"
	@echo "  make run_all_configs  - Run all configurations (2, 4, 8 MLPs)"
	@echo "  make compile          - Compile only (no simulation)"
	@echo "  make debug            - Run with GUI for debugging"
	@echo "  make summary          - Show test results summary"
	@echo "  make view-log         - View full simulation log"
	@echo "  make clean            - Remove all generated files"
	@echo "  make help             - Show this help message"
	@echo ""
	@echo "========================================================================"

.PHONY: all create_library compile run_vsim run run_all_configs debug view-log summary clean help
