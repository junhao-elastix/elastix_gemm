# ---------------------------------------------------------------------
# Makefile for Compute -> Result Collector -> Result to DMA Simulation
#
# Purpose: Validate the complete compute-to-output data path:
#   - 16 compute_engine_2d instances
#   - result_collector_2d (row reduction)
#   - result_to_dma (circular buffer to BRAM)
#
# Test: B=1, C=64, V=2 with auto-drain behavior
#
# Author: Comp Readout Testing
# Date: Jan 29, 2026
# ---------------------------------------------------------------------

# Simulation settings
SIM_TOP := tb_comp_readout
DEVICE := AC7t1500
BASE_NAME := ac7t1500
LOG_FILE := sim_comp_readout.log

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

# Fixed parameters for 16-row test
NUM_MLPS := 2
NUM_COLS := 4

# Compilation flags
VLOG_OPTIONS := +define+SIMULATION +define+SPEEDSTER7T_SIMULATION +define+ACX_ENABLE_MLP_SIM +define+ACX_ENABLE_BRAM_SIM +define+ACX_ENABLE_PRIMITIVE_SIM +define+USE_BEHAVIORAL_BRAM
VLOG_OPTIONS += +define+NUM_MLPS=$(NUM_MLPS)
VLOG_OPTIONS += +define+NUM_COLS=$(NUM_COLS)
VLOG_OPTIONS += -sv
VLOG_OPTIONS += -timescale "1ps/1ps"
VLOG_OPTIONS += -err VCP2675 W1
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
	@echo "  Comp Readout Compilation Started: $$(date)" | tee -a $(LOG_FILE)
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "Compiling Achronix primitives..." | tee -a $(LOG_FILE)
	@export LD_LIBRARY_PATH="" && \
	vlog $(VLOG_OPTIONS) \
		$(DSM_COMPILE_FILE) \
		$(DEVICE_MODELS) \
		$(ACX_LIB_S7T)/common/acx_integer.sv \
		$(ACX_LIB_S7T)/common/acx_floating_point.sv >> $(LOG_FILE) 2>&1 || \
		(echo "ERROR: ACX library compilation failed. See $(LOG_FILE)" && exit 1)
	@echo "Compiling compute engine RTL..." | tee -a $(LOG_FILE)
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
		(echo "ERROR: CE RTL compilation failed. See $(LOG_FILE)" && exit 1)
	@echo "Compiling result collector and DMA RTL..." | tee -a $(LOG_FILE)
	@export LD_LIBRARY_PATH="" && \
	vlog $(VLOG_OPTIONS) \
		$(GEMM_RTL)/result_collector_2d.sv \
		$(GEMM_RTL)/result_to_dma.sv >> $(LOG_FILE) 2>&1 || \
		(echo "ERROR: RC/DMA RTL compilation failed. See $(LOG_FILE)" && exit 1)
	@echo "Compiling testbench..." | tee -a $(LOG_FILE)
	@export LD_LIBRARY_PATH="" && \
	vlog $(VLOG_OPTIONS) \
		tb_comp_readout.sv >> $(LOG_FILE) 2>&1 || \
		(echo "ERROR: Testbench compilation failed. See $(LOG_FILE)" && exit 1)
	@echo "Compilation completed successfully" | tee -a $(LOG_FILE)
	@echo ""

# Run simulation
run_vsim: compile
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "  Comp Readout Simulation Started: $$(date)" | tee -a $(LOG_FILE)
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "Running simulation..." | tee -a $(LOG_FILE)
	@export LD_LIBRARY_PATH="" && \
	vsim -c -do "run -all; quit -force" work.$(SIM_TOP) >> $(LOG_FILE) 2>&1 || \
		(echo "ERROR: Simulation failed. See $(LOG_FILE)" && exit 1)
	@echo "" | tee -a $(LOG_FILE)
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "  Comp Readout Simulation Completed: $$(date)" | tee -a $(LOG_FILE)
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "" | tee -a $(LOG_FILE)
	@echo "Extracting test summary..." | tee -a $(LOG_FILE)
	@grep -E "PASS|FAIL|RESULTS|wr_ptr|bram_writes|STATUS" $(LOG_FILE) | tail -20 || echo "Warning: Could not find test summary"
	@echo ""
	@echo "Full log available in: $(LOG_FILE)"

# Run tests
run: run_vsim

# Debug with GUI
debug: compile
	@echo "=== Running Comp Readout Debug Simulation ==="
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
		grep -E "PASS|FAIL|RESULTS|wr_ptr|STATUS" $(LOG_FILE) | tail -20; \
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
	@echo "  Makefile for Comp Readout Simulation"
	@echo "========================================================================"
	@echo ""
	@echo "Purpose: Test compute-to-output data path:"
	@echo "  16 CEs -> result_collector_2d -> result_to_dma -> Result BRAM"
	@echo ""
	@echo "Test Configuration: B=1, C=64, V=2"
	@echo "  - 64 results, 4 output lines"
	@echo "  - Auto-drain behavior (no READOUT command)"
	@echo ""
	@echo "Targets:"
	@echo "  make             - Compile and run simulation"
	@echo "  make run         - Same as above"
	@echo "  make compile     - Compile only"
	@echo "  make debug       - Run with GUI"
	@echo "  make summary     - Show test results"
	@echo "  make view-log    - View full log"
	@echo "  make clean       - Remove generated files"
	@echo "  make help        - Show this message"
	@echo ""
	@echo "========================================================================"

.PHONY: all create_library compile run_vsim run debug view-log summary clean help
