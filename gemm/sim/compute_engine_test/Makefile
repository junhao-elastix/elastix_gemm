# ---------------------------------------------------------------------
# Makefile for MLP Compute Engine Simulation
#
# Purpose: Validate compute_engine_mlp with MLP-based architecture
# Features:
#   - Direct path from row_bram to MLP primitives
#   - 256-bit (16 × FP16) result output
#   - Supports C divisible by 16 (16, 32, 64, 128)
#   - Internal GFP8E5 → GFP8E8 exponent conversion
#
# Author: Compute Engine Testing
# Date: Dec 2025
# ---------------------------------------------------------------------

# Simulation settings
SIM_TOP := tb_compute_engine_mlp
DEVICE := AC7t1500
BASE_NAME := ac7t1500
LOG_FILE := sim_mlp.log

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
VLOG_OPTIONS := +define+SIMULATION
VLOG_OPTIONS += -sv
VLOG_OPTIONS += -timescale "1ps/1ps"
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

# Compile MLP design
compile: create_library
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "  MLP Compilation Started: $$(date)" | tee -a $(LOG_FILE)
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
		$(MLP_RTL)/mlp_dot16_int8.sv \
		$(MLP_RTL)/mlp_dot16_bfp8.sv \
		$(MLP_RTL)/weight_bram.sv \
		$(MLP_RTL)/mlp_bram.sv \
		$(MLP_RTL)/mlp_bram_col.sv \
		$(MLP_RTL)/fp24_add.sv \
		$(MLP_RTL)/fp_to_int.sv \
		$(MLP_RTL)/int_to_fp.sv \
		$(MLP_RTL)/int_adder_tree.sv \
		$(MLP_RTL)/fp_adder_pipeline.sv \
		$(MLP_RTL)/mlp_bram_col_ctrl.sv \
		$(MLP_RTL)/row_bram.sv \
		$(MLP_RTL)/fp24_to_fp16.sv \
		$(MLP_RTL)/compute_engine_mlp.sv >> $(LOG_FILE) 2>&1 || \
		(echo "ERROR: MLP RTL compilation failed. See $(LOG_FILE)" && exit 1)
	@echo "Compiling testbench..." | tee -a $(LOG_FILE)
	@export LD_LIBRARY_PATH="" && \
	vlog $(VLOG_OPTIONS) \
		tb_compute_engine_mlp.sv >> $(LOG_FILE) 2>&1 || \
		(echo "ERROR: Testbench compilation failed. See $(LOG_FILE)" && exit 1)
	@echo "MLP compilation completed successfully" | tee -a $(LOG_FILE)
	@echo ""

# Run MLP simulation
run_vsim: compile
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "  MLP Simulation Started: $$(date)" | tee -a $(LOG_FILE)
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "Running Compute Engine MLP simulation..." | tee -a $(LOG_FILE)
	@export LD_LIBRARY_PATH="" && \
	vsim -c -do "run -all; quit -force" work.$(SIM_TOP) >> $(LOG_FILE) 2>&1 || \
		(echo "ERROR: MLP simulation failed. See $(LOG_FILE)" && exit 1)
	@echo "" | tee -a $(LOG_FILE)
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "  MLP Simulation Completed: $$(date)" | tee -a $(LOG_FILE)
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "" | tee -a $(LOG_FILE)
	@echo "Extracting test summary..." | tee -a $(LOG_FILE)
	@grep -E "PASS|FAIL|ALL TESTS" $(LOG_FILE) | tail -10 || echo "Warning: Could not find test summary"
	@echo ""
	@echo "Full log available in: $(LOG_FILE)"

# Run tests
run: run_vsim

# Debug MLP with GUI
debug: compile
	@echo "=== Running Compute Engine MLP Debug Simulation ==="
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
		grep "PASS\|FAIL" $(LOG_FILE) | grep -E "^\# KERNEL:" | sed 's/\# KERNEL: //'; \
		echo ""; \
		grep -A 10 "TEST SUMMARY" $(LOG_FILE) | sed 's/\# KERNEL: //'; \
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
	@echo "  Makefile for MLP Compute Engine Simulation"
	@echo "========================================================================"
	@echo ""
	@echo "Purpose: Test compute_engine_mlp.sv with MLP-based architecture"
	@echo "         Validates 256-bit (16 × FP16) output and GFP8 computation"
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
	@echo "Key Features:"
	@echo "  - MLP-based compute engine (replaces modular)"
	@echo "  - 256-bit result output (16 × FP16 per cycle)"
	@echo "  - Internal GFP8E5 → GFP8E8 exponent conversion"
	@echo "  - Supports C = 16, 32, 64, 128 (divisible by 16)"
	@echo "  - All output logged to $(LOG_FILE)"
	@echo ""
	@echo "Test Configurations:"
	@echo "  C=16:  B16_C16_V8 (baseline)"
	@echo "  C>16:  B4_C32_V4, B8_C32_V2, B8_C64_V2, B2_C128_V1"
	@echo ""
	@echo "========================================================================"

.PHONY: all create_library compile run_vsim run debug view-log summary clean help
