# ---------------------------------------------------------------------
# Makefile for Compute Engine Modular Simulation
#
# Purpose: Validate complete compute engine with dual BRAM interface and FP16 output
# Features:
#   - Full BCV loop orchestration
#   - Dual BRAM read interfaces (left/right matrices)
#   - Exponent read interfaces
#   - GFP8 to FP16 conversion
#   - Result validation with FP16 golden reference
#
# Author: Compute Engine Modular Testing
# Date: Fri Oct 24 2025
# ---------------------------------------------------------------------

# Simulation settings
SIM_TOP := tb_compute_engine_modular
DEVICE := AC7t1500
BASE_NAME := ac7t1500
LOG_FILE := sim.log

# Achronix environment setup
export ACX_DEVICE_INSTALL_DIR := $(ACE_INSTALL_DIR)/system/data/$(DEVICE)
DSM_INCLUDE_FILE := $(ACX_DEVICE_INSTALL_DIR)/sim/$(BASE_NAME)_dsm_incdirs.f
DSM_COMPILE_FILE := $(ACX_DEVICE_INSTALL_DIR)/sim/$(BASE_NAME)_dsm_filelist.v
DEVICE_MODELS := $(ACE_INSTALL_DIR)/libraries/device_models/$(DEVICE)_simmodels.sv

# Achronix Speedster7t library paths
ACX_LIB_S7T := $(ACE_INSTALL_DIR)/libraries/speedster7t

# Source directories (PORTABLE - all dependencies are local)
GEMM_RTL := ./rtl
GEMM_INC := ./include
GEMM_TB := .

# Compilation flags
VLOG_OPTIONS := +define+SIMULATION
VLOG_OPTIONS += -sv
VLOG_OPTIONS += -timescale "1ps/1ps"
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

# Compile the design
compile: create_library
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "  Compilation Started: $$(date)" | tee -a $(LOG_FILE)
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "Compiling packages..." | tee -a $(LOG_FILE)
	@export LD_LIBRARY_PATH="" && \
	vlog $(VLOG_OPTIONS) \
		$(GEMM_INC)/gemm_pkg.sv >> $(LOG_FILE) 2>&1 || \
		(echo "ERROR: Package compilation failed. See $(LOG_FILE)" && exit 1)
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
		$(GEMM_RTL)/gfp8_group_dot_mlp.sv \
		$(GEMM_RTL)/gfp8_nv_dot.sv \
		$(GEMM_RTL)/gfp8_bcv_controller.sv \
		$(GEMM_RTL)/gfp8_to_fp16.sv \
		$(GEMM_RTL)/compute_engine_modular.sv \
		tb_compute_engine_modular.sv >> $(LOG_FILE) 2>&1 || \
		(echo "ERROR: RTL compilation failed. See $(LOG_FILE)" && exit 1)
	@echo "Compilation completed successfully" | tee -a $(LOG_FILE)
	@echo ""

# Run simulation
run_vsim: compile
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "  Simulation Started: $$(date)" | tee -a $(LOG_FILE)
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "Running Compute Engine Modular simulation..." | tee -a $(LOG_FILE)
	@export LD_LIBRARY_PATH="" && \
	vsim -c -do "run -all; quit -force" work.$(SIM_TOP) >> $(LOG_FILE) 2>&1 || \
		(echo "ERROR: Simulation failed. See $(LOG_FILE)" && exit 1)
	@echo "" | tee -a $(LOG_FILE)
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "  Simulation Completed: $$(date)" | tee -a $(LOG_FILE)
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "" | tee -a $(LOG_FILE)
	@echo "Extracting test summary..." | tee -a $(LOG_FILE)
	@grep -A 10 "TEST SUMMARY" $(LOG_FILE) || echo "Warning: Could not find test summary"
	@echo ""
	@echo "Full log available in: $(LOG_FILE)"

# Complete run (compile + simulate)
run: run_vsim

# Run with GUI for debugging
debug: compile
	@echo "=== Running Compute Engine Modular Debug Simulation ==="
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
	@echo "  Makefile for Compute Engine Modular Simulation"
	@echo "========================================================================"
	@echo ""
	@echo "Purpose: Test compute_engine_modular.sv with dual BRAM and FP16 output"
	@echo "         Validates full BCV orchestration, GFP8 computation, and format conversion"
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
	@echo "  - Dual BRAM interface (parallel left/right matrix reads)"
	@echo "  - Separate exponent read ports"
	@echo "  - FP16 result output validation"
	@echo "  - Golden reference comparison with tolerance"
	@echo "  - All output logged to $(LOG_FILE)"
	@echo ""
	@echo "Test Configurations:"
	@echo "  B1_C1_V1, B2_C2_V2, B4_C4_V4, B2_C2_V64, B4_C4_V32,"
	@echo "  B8_C8_V16, B1_C128_V1, B128_C1_V1, B1_C1_V128"
	@echo ""
	@echo "========================================================================"

.PHONY: all create_library compile run_vsim run debug view-log summary clean help
