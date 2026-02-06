# ---------------------------------------------------------------------
# Makefile for gfp_norm_quant Riviera-PRO Simulation
#
# Purpose: E2E streaming test for GFP11e5 -> GFP8e5 normalize and quantize
# Tests 8 vectors of 32 elements with varied exponents
#
# Author: Elastix GEMM Team
# Date: Feb 2026
# ---------------------------------------------------------------------

# Simulation settings
SIM_TOP := tb_gfp_norm_quant
LOG_FILE := sim_gfp_norm_quant.log

# Source directories
RTL_DIR := ../../rtl
COMMON_DIR := ../../../common

# Compilation flags
VLOG_OPTIONS := +define+SIMULATION
VLOG_OPTIONS += -sv2k12
VLOG_OPTIONS += -timescale "1ns/1ps"
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
	@echo "  GFP Norm Quant Compilation Started: $$(date)" | tee -a $(LOG_FILE)
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "Compiling common FIFO modules..." | tee -a $(LOG_FILE)
	@export LD_LIBRARY_PATH="" && \
	vlog $(VLOG_OPTIONS) \
		$(COMMON_DIR)/fifo.sv \
		$(COMMON_DIR)/two_fifo.sv >> $(LOG_FILE) 2>&1 || \
		(echo "ERROR: FIFO compilation failed. See $(LOG_FILE)" && exit 1)
	@echo "Compiling RTL modules..." | tee -a $(LOG_FILE)
	@export LD_LIBRARY_PATH="" && \
	vlog $(VLOG_OPTIONS) \
		$(RTL_DIR)/gfp_align_quant.sv \
		$(RTL_DIR)/gfp_find_max_exp.sv \
		$(RTL_DIR)/gfp_norm_quant.sv >> $(LOG_FILE) 2>&1 || \
		(echo "ERROR: RTL compilation failed. See $(LOG_FILE)" && exit 1)
	@echo "Compiling testbench..." | tee -a $(LOG_FILE)
	@export LD_LIBRARY_PATH="" && \
	vlog $(VLOG_OPTIONS) \
		tb_gfp_norm_quant.sv >> $(LOG_FILE) 2>&1 || \
		(echo "ERROR: Testbench compilation failed. See $(LOG_FILE)" && exit 1)
	@echo "Compilation completed successfully" | tee -a $(LOG_FILE)
	@echo ""

# Run simulation
run_vsim: compile
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "  GFP Norm Quant Simulation Started: $$(date)" | tee -a $(LOG_FILE)
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "Running simulation..." | tee -a $(LOG_FILE)
	@export LD_LIBRARY_PATH="" && \
	vsim -c -do "run -all; quit -force" work.$(SIM_TOP) >> $(LOG_FILE) 2>&1 || \
		(echo "ERROR: Simulation failed. See $(LOG_FILE)" && exit 1)
	@echo "" | tee -a $(LOG_FILE)
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "  GFP Norm Quant Simulation Completed: $$(date)" | tee -a $(LOG_FILE)
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "" | tee -a $(LOG_FILE)
	@echo "Extracting test summary..." | tee -a $(LOG_FILE)
	@grep -E "PASS|FAIL|ALL TESTS|ERROR|Accuracy|vectors|elements" $(LOG_FILE) | tail -20 || echo "Warning: Could not find test summary"
	@echo ""
	@echo "Full log available in: $(LOG_FILE)"

# Run tests
run: run_vsim

# Debug with GUI
debug: compile
	@echo "=== Running GFP Norm Quant Debug Simulation ==="
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
		grep -E "PASS|FAIL|ALL TESTS|ERROR|Accuracy|vectors|elements" $(LOG_FILE) | tail -30; \
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
	@rm -f library.cfg
	@echo "Clean complete"

# Help
help:
	@echo "========================================================================"
	@echo "  Makefile for gfp_norm_quant Riviera-PRO Simulation"
	@echo "========================================================================"
	@echo ""
	@echo "Purpose: E2E streaming test for GFP11e5 -> GFP8e5 conversion"
	@echo "         8 vectors x 32 elements with varied exponents"
	@echo ""
	@echo "Targets:"
	@echo "  make             - Compile and run simulation (outputs to $(LOG_FILE))"
	@echo "  make run         - Compile and run simulation (same as make)"
	@echo "  make compile     - Compile only (no simulation)"
	@echo "  make debug       - Run with GUI for debugging"
	@echo "  make summary     - Show test results summary"
	@echo "  make view-log    - View full simulation log"
	@echo "  make clean       - Remove all generated files"
	@echo "  make help        - Show this help message"
	@echo ""
	@echo "Test Coverage:"
	@echo "  - 8 vectors of 32 GFP11e5 elements (256 total)"
	@echo "  - Each element has unique exponent (stress test alignment)"
	@echo "  - Concurrent producer/consumer streaming"
	@echo "  - 100% accuracy check against golden model"
	@echo ""
	@echo "========================================================================"

.PHONY: all create_library compile run_vsim run debug view-log summary clean help
