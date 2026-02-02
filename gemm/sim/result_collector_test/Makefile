# ---------------------------------------------------------------------
# Makefile for result_collector_2d + result_to_dma Simulation
#
# Purpose: Validate the complete result data path:
#   CE FIFOs -> result_collector_2d -> result_to_dma -> Result BRAM
#
# Features:
#   - Mock CE FIFO interface
#   - Auto-drain without READOUT command
#   - result_to_dma always-drain circular buffer
#   - Circular buffer with wr_ptr/rd_ptr verification
#   - FP16 row reduction via comp_fp_adder_pipeline
#   - 256-bit output packing
#
# Author: Result Collector 2D + Result to DMA Testing
# Date: Jan 29, 2026 (Integrated with result_to_dma)
# ---------------------------------------------------------------------

# Simulation settings
SIM_TOP := tb_result_collector_2d
DEVICE := AC7t1500
BASE_NAME := ac7t1500
LOG_FILE := sim_result_collector_2d.log

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

# Default target
all: run

# Create work library
create_library:
	@echo "Creating work library..." | tee $(LOG_FILE)
	@vlib work >> $(LOG_FILE) 2>&1

# Compile design
compile: create_library
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "  Result Collector 2D Compilation Started: $$(date)" | tee -a $(LOG_FILE)
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
		$(GEMM_RTL)/flex_fifo.sv \
		$(GEMM_RTL)/fp_to_int.sv \
		$(GEMM_RTL)/int_to_fp.sv \
		$(GEMM_RTL)/int_adder_tree.sv \
		$(GEMM_RTL)/comp_fp_adder_pipeline.sv \
		$(GEMM_RTL)/result_collector_2d.sv \
		$(GEMM_RTL)/result_to_dma.sv >> $(LOG_FILE) 2>&1 || \
		(echo "ERROR: RTL compilation failed. See $(LOG_FILE)" && exit 1)
	@echo "Compiling testbench..." | tee -a $(LOG_FILE)
	@export LD_LIBRARY_PATH="" && \
	vlog $(VLOG_OPTIONS) \
		tb_result_collector_2d.sv >> $(LOG_FILE) 2>&1 || \
		(echo "ERROR: Testbench compilation failed. See $(LOG_FILE)" && exit 1)
	@echo "Compilation completed successfully" | tee -a $(LOG_FILE)
	@echo ""

# Run simulation
run_vsim: compile
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "  Result Collector 2D Simulation Started: $$(date)" | tee -a $(LOG_FILE)
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "Running result_collector_2d simulation..." | tee -a $(LOG_FILE)
	@export LD_LIBRARY_PATH="" && \
	vsim -c -do "run -all; quit -force" work.$(SIM_TOP) >> $(LOG_FILE) 2>&1 || \
		(echo "ERROR: Simulation failed. See $(LOG_FILE)" && exit 1)
	@echo "" | tee -a $(LOG_FILE)
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "  Result Collector 2D Simulation Completed: $$(date)" | tee -a $(LOG_FILE)
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "" | tee -a $(LOG_FILE)
	@echo "Extracting test summary..." | tee -a $(LOG_FILE)
	@grep -E "PASS|FAIL|TEST|SUMMARY" $(LOG_FILE) | tail -30 || echo "Warning: Could not find test summary"
	@echo ""
	@echo "Full log available in: $(LOG_FILE)"

# Run tests
run: run_vsim

# Debug with GUI
debug: compile
	@echo "=== Running Result Collector 2D Debug Simulation ==="
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
		grep -E "PASS|FAIL|TEST|SUMMARY" $(LOG_FILE) | tail -40; \
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
	@echo "  Makefile for result_collector_2d + result_to_dma Simulation"
	@echo "========================================================================"
	@echo ""
	@echo "Purpose: Test complete result data path:"
	@echo "  CE FIFOs -> result_collector_2d -> result_to_dma -> Result BRAM"
	@echo ""
	@echo "Features:"
	@echo "  - Mock CE FIFO interface with random FP16 data"
	@echo "  - Auto-drain without READOUT command"
	@echo "  - result_to_dma always-drain circular buffer"
	@echo "  - wr_ptr/rd_ptr circular buffer verification"
	@echo "  - FP16 row reduction via comp_fp_adder_pipeline"
	@echo "  - 256-bit output packing with keep masks"
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
	@echo "========================================================================"

.PHONY: all create_library compile run_vsim run debug view-log summary clean help
