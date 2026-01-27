# ---------------------------------------------------------------------
# Makefile for FP Adder Pipeline Testing
#
# Purpose: Validate new integer-domain FP adder pipeline modules
# Modules Tested:
#   - fp_to_int: FP24/FP16 to wide integer conversion
#   - int_to_fp: Wide integer to FP24/FP16 with RNE rounding
#   - int_adder_tree: Pipelined integer adder tree
#   - fp_adder_pipeline: Complete FP addition pipeline
#
# Author: GEMM Project
# Date: Dec 2025
# ---------------------------------------------------------------------

# Source directories
RTL_DIR := ../../src/rtl
TB_DIR := .

# Compilation flags
VLOG_OPTIONS := +define+SIMULATION
VLOG_OPTIONS += -sv2k12
VLOG_OPTIONS += -timescale "1ps/1ps"
VLOG_OPTIONS += -work work

# Simulation flags
VSIM_FLAGS := -c -do "run -all; quit -force"

# Log file
LOG_FILE := sim_adder.log

# Default target
all: run

# Create work library
create_library:
	@echo "Creating work library..."
	@vlib work > /dev/null 2>&1 || true

# Compile all RTL modules
compile: create_library
	@echo "======================================================================" | tee $(LOG_FILE)
	@echo "  FP Adder Pipeline Compilation Started: $$(date)" | tee -a $(LOG_FILE)
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "Compiling RTL modules..." | tee -a $(LOG_FILE)
	@vlog $(VLOG_OPTIONS) \
		$(RTL_DIR)/fp_to_int.sv \
		$(RTL_DIR)/int_to_fp.sv \
		$(RTL_DIR)/int_adder_tree.sv \
		$(RTL_DIR)/fp_adder_pipeline.sv >> $(LOG_FILE) 2>&1 || \
		(echo "ERROR: RTL compilation failed. See $(LOG_FILE)" && exit 1)
	@echo "Compiling testbenches..." | tee -a $(LOG_FILE)
	@vlog $(VLOG_OPTIONS) \
		$(TB_DIR)/tb_fp_to_int_all.sv \
		$(TB_DIR)/tb_int_to_fp_all.sv \
		$(TB_DIR)/tb_fp_adder_all_combos.sv \
		$(TB_DIR)/tb_adder_tree_all.sv \
		$(TB_DIR)/tb_fp_to_int_detailed.sv \
		$(TB_DIR)/tb_int_to_fp_detailed.sv \
		$(TB_DIR)/tb_fp_adder_comprehensive.sv >> $(LOG_FILE) 2>&1 || \
		(echo "ERROR: Testbench compilation failed. See $(LOG_FILE)" && exit 1)
	@echo "Compilation completed successfully" | tee -a $(LOG_FILE)
	@echo ""

# Run all comprehensive tests (main target)
run: run_all_comprehensive

# Run all comprehensive tests
run_all_comprehensive: compile
	@echo "" | tee -a $(LOG_FILE)
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "  COMPREHENSIVE TEST SUITE" | tee -a $(LOG_FILE)
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "" | tee -a $(LOG_FILE)
	@echo "Test 1: FP → Integer Conversions (FP24/FP16 → Int)" | tee -a $(LOG_FILE)
	@echo "----------------------------------------------------------------------" | tee -a $(LOG_FILE)
	@vsim $(VSIM_FLAGS) work.tb_fp_to_int_all >> $(LOG_FILE) 2>&1
	@echo "" | tee -a $(LOG_FILE)
	@echo "Test 2: Integer → FP Conversions (Int → FP24/FP16)" | tee -a $(LOG_FILE)
	@echo "----------------------------------------------------------------------" | tee -a $(LOG_FILE)
	@vsim $(VSIM_FLAGS) work.tb_int_to_fp_all >> $(LOG_FILE) 2>&1
	@echo "" | tee -a $(LOG_FILE)
	@echo "Test 3: Complete Adder Pipeline (All 4 combinations, 4/8/16 inputs)" | tee -a $(LOG_FILE)
	@echo "----------------------------------------------------------------------" | tee -a $(LOG_FILE)
	@vsim $(VSIM_FLAGS) work.tb_fp_adder_all_combos >> $(LOG_FILE) 2>&1
	@echo "" | tee -a $(LOG_FILE)
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "  All Tests Completed: $$(date)" | tee -a $(LOG_FILE)
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo ""
	@echo "Full log available in: $(LOG_FILE)"

# Run individual detailed tests (legacy)
run_fp_to_int: compile
	@echo "" | tee -a $(LOG_FILE)
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "  Test: FP24 → Integer Conversion" | tee -a $(LOG_FILE)
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@vsim $(VSIM_FLAGS) work.tb_fp_to_int_detailed >> $(LOG_FILE) 2>&1
	@echo "" | tee -a $(LOG_FILE)

run_int_to_fp: compile
	@echo "" | tee -a $(LOG_FILE)
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "  Test: Integer → FP16 Conversion" | tee -a $(LOG_FILE)
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@vsim $(VSIM_FLAGS) work.tb_int_to_fp_detailed >> $(LOG_FILE) 2>&1
	@echo "" | tee -a $(LOG_FILE)

run_comprehensive: compile
	@echo "" | tee -a $(LOG_FILE)
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "  Test: Complete FP Adder Pipeline (legacy)" | tee -a $(LOG_FILE)
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@vsim $(VSIM_FLAGS) work.tb_fp_adder_comprehensive >> $(LOG_FILE) 2>&1
	@echo "" | tee -a $(LOG_FILE)

# Debug with GUI
debug: compile
	@echo "=== Running Debug Simulation ==="
	@vsim -gui work.tb_fp_adder_comprehensive &

# View simulation log
view-log:
	@if [ -f $(LOG_FILE) ]; then \
		less +G $(LOG_FILE); \
	else \
		echo "Error: $(LOG_FILE) not found. Run 'make run' first."; \
	fi

# Show summary
summary:
	@if [ -f $(LOG_FILE) ]; then \
		echo ""; \
		echo "Test Results:"; \
		echo "======================================"; \
		grep -E "Testing|Test completed|PASS|FAIL|ERROR" $(LOG_FILE) | grep -E "KERNEL:" | sed 's/\# KERNEL: //'; \
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
	@rm -f library.cfg
	@echo "Clean complete"

# Help
help:
	@echo "========================================================================"
	@echo "  Makefile for FP Adder Pipeline Testing"
	@echo "========================================================================"
	@echo ""
	@echo "Purpose: Test new integer-domain floating-point adder modules"
	@echo "         Eliminates compounding truncation errors in FP24 addition"
	@echo ""
	@echo "Targets:"
	@echo "  make                      - Run comprehensive test suite (all combinations)"
	@echo "  make run                  - Same as above"
	@echo "  make run_all_comprehensive - Run all comprehensive tests"
	@echo "  make run_fp_to_int        - Test FP24 → Integer only (legacy)"
	@echo "  make run_int_to_fp        - Test Integer → FP16 only (legacy)"
	@echo "  make run_comprehensive    - Test adder pipeline only (legacy)"
	@echo "  make compile              - Compile only (no simulation)"
	@echo "  make debug                - Run test with GUI for debugging"
	@echo "  make summary              - Show test results summary with RMSE"
	@echo "  make view-log             - View full simulation log"
	@echo "  make clean                - Remove all generated files"
	@echo "  make help                 - Show this help message"
	@echo ""
	@echo "Test Coverage:"
	@echo "  Conversion Tests:"
	@echo "    - FP24 → Integer and FP16 → Integer"
	@echo "    - Integer → FP24 and Integer → FP16 with RNE rounding"
	@echo "  "
	@echo "  Adder Tree Tests (all 4 combinations):"
	@echo "    - FP24 → FP24  |  FP24 → FP16"
	@echo "    - FP16 → FP16  |  FP16 → FP24"
	@echo "  "
	@echo "  Input Sizes: 4, 8, 16, 32 inputs per test"
	@echo "  Test Patterns: zeros, ones, small values, large values,"
	@echo "                 wide dynamic range, alternating signs"
	@echo "  Metrics: Pass/Fail rate, RMSE, Max Error"
	@echo ""
	@echo "Example:"
	@echo "  make              # Run comprehensive tests with RMSE"
	@echo "  make debug        # Debug test in GUI"
	@echo ""
	@echo "========================================================================"

.PHONY: all create_library compile run run_all_comprehensive run_fp_to_int run_int_to_fp run_comprehensive debug view-log summary clean help

