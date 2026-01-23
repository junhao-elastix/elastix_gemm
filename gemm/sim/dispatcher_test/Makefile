# ---------------------------------------------------------------------
# Makefile for dispatcher_2d Simulation
#
# Purpose: Validate the dispatcher 2D module with flex_fifo
# Features:
#   - 2-stage stream processing (exponent buffer + mantissa routing)
#   - LEFT path: sequential write to row_bram
#   - RIGHT path: round-robin distribution to 16 column BRAMs
#   - 16-bit one-hot write enable for column selection
#
# Author: Dispatcher Testing
# Date: Jan 2026
# ---------------------------------------------------------------------

# Simulation settings
SIM_TOP := tb_dispatcher
LOG_FILE := sim_dispatcher.log

# Source directories
GEMM_RTL := ../../src/rtl
GEMM_INC := ../../src/include
GEMM_TB := .

# Compilation flags
VLOG_OPTIONS := +define+SIMULATION
VLOG_OPTIONS += -sv
VLOG_OPTIONS += -timescale "1ns/1ps"
VLOG_OPTIONS += -err VCP2675 W1   # Suppress warning: initial block + always_ff on same signal
VLOG_OPTIONS += +incdir+$(GEMM_INC)
VLOG_OPTIONS += -msg 0

# Default target
all: run

# Create work library
create_library:
	@echo "Creating work library..." | tee $(LOG_FILE)
	@vlib work >> $(LOG_FILE) 2>&1

# Compile dispatcher design
compile: create_library
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "  Dispatcher Compilation Started: $$(date)" | tee -a $(LOG_FILE)
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "Compiling RTL modules..." | tee -a $(LOG_FILE)
	@export LD_LIBRARY_PATH="" && \
	vlog $(VLOG_OPTIONS) \
		$(GEMM_INC)/gemm_pkg.sv \
		$(GEMM_RTL)/flex_fifo.sv \
		$(GEMM_RTL)/comp_row_bram.sv \
		$(GEMM_RTL)/dispatcher_2d.sv >> $(LOG_FILE) 2>&1 || \
		(echo "ERROR: RTL compilation failed. See $(LOG_FILE)" && exit 1)
	@echo "Compiling testbench..." | tee -a $(LOG_FILE)
	@export LD_LIBRARY_PATH="" && \
	vlog $(VLOG_OPTIONS) \
		tb_dispatcher.sv >> $(LOG_FILE) 2>&1 || \
		(echo "ERROR: Testbench compilation failed. See $(LOG_FILE)" && exit 1)
	@echo "Dispatcher compilation completed successfully" | tee -a $(LOG_FILE)
	@echo ""

# Run dispatcher simulation
run_vsim: compile
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "  Dispatcher Simulation Started: $$(date)" | tee -a $(LOG_FILE)
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "Running dispatcher_2d simulation..." | tee -a $(LOG_FILE)
	@export LD_LIBRARY_PATH="" && \
	vsim -c -do "run -all; quit -force" work.$(SIM_TOP) >> $(LOG_FILE) 2>&1 || \
		(echo "ERROR: Dispatcher simulation failed. See $(LOG_FILE)" && exit 1)
	@echo "" | tee -a $(LOG_FILE)
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "  Dispatcher Simulation Completed: $$(date)" | tee -a $(LOG_FILE)
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "" | tee -a $(LOG_FILE)
	@echo "Extracting test summary..." | tee -a $(LOG_FILE)
	@grep -E "PASS|FAIL|ALL TESTS|TEST|Error" $(LOG_FILE) | tail -30 || echo "Warning: Could not find test summary"
	@echo ""
	@echo "Full log available in: $(LOG_FILE)"

# Run tests
run: run_vsim

# Debug dispatcher with GUI
debug: compile
	@echo "=== Running dispatcher_2d Debug Simulation ==="
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
		grep -E "PASS|FAIL|TEST|SUMMARY|Error" $(LOG_FILE) | tail -40; \
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
	@echo "  Makefile for dispatcher_2d Simulation"
	@echo "========================================================================"
	@echo ""
	@echo "Purpose: Test dispatcher_2d.sv with flex_fifo upstream"
	@echo "         Validates 2-stage dispatch to row_bram and 16 column BRAMs"
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
	@echo "  Test 1: LEFT dispatch (B=4, V=2) - sequential write to row_bram"
	@echo "  Test 2: RIGHT dispatch (C=4, V=2) - round-robin to 4 columns"
	@echo "  Test 3: RIGHT dispatch (C=8, V=2) - round-robin to 8 columns"
	@echo "  Test 4: RIGHT dispatch with col_start=2"
	@echo ""
	@echo "Architecture:"
	@echo "  - flex_fifo (256-bit, 1024 deep) as upstream"
	@echo "  - dispatcher_2d with 2-stage processing"
	@echo "  - comp_row_bram for LEFT path verification"
	@echo "  - 16 mock column BRAMs for RIGHT path verification"
	@echo ""
	@echo "========================================================================"

.PHONY: all create_library compile run_vsim run debug view-log summary clean help
