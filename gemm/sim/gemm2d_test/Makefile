# ---------------------------------------------------------------------
# Makefile for 2-D GEMM Full Integration Simulation
#
# Purpose: Validate the complete 2-D GEMM architecture with:
#   - engine_top_2d (top-level)
#   - master_control_2d (command processor)
#   - 16 x dispatcher_control_2d (per-row GDDR6 fetch/dispatch)
#   - 16 x compute_engine_2d (per-row MLP compute)
#   - result_collector_2d (cross-row reduction)
#
# Configuration: B=4, C=4, V=32 with 16 hex file pairs
#
# Author: Junhao Pan
# Date: Jan 22, 2026
# ---------------------------------------------------------------------

# Simulation settings
SIM_TOP := tb_gemm2d
SIM_TOP_MULTI := tb_gemm2d_multi_iter
SIM_TOP_CSR := tb_gemm2d_csr
DEVICE := AC7t1500
BASE_NAME := ac7t1500
LOG_FILE := sim_gemm2d.log
LOG_FILE_MULTI := sim_gemm2d_multi_iter.log
LOG_FILE_CSR := sim_gemm2d_csr.log

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
SIM_DIR := .

# Configurable parameters (default: 8 MLPs, 16 columns)
# Override via: make run NUM_MLPS=2  (or NUM_MLPS=4, NUM_MLPS=8)
NUM_MLPS ?= 8
NUM_COLS ?= $(shell echo $$(($(NUM_MLPS) * 2)))

# Compilation flags
VLOG_OPTIONS := +define+SIMULATION +define+SPEEDSTER7T_SIMULATION +define+ACX_ENABLE_MLP_SIM +define+ACX_ENABLE_BRAM_SIM +define+ACX_ENABLE_PRIMITIVE_SIM
VLOG_OPTIONS += +define+NUM_MLPS=$(NUM_MLPS)
VLOG_OPTIONS += +define+NUM_COLS=$(NUM_COLS)
VLOG_OPTIONS += -sv
VLOG_OPTIONS += -timescale "1ps/1ps"

# =========================================================================
# BRAM Model Selection - Enable behavioral model for weight_bram
# The ACX_BRAM72K mlpram_dout2mlp path doesn't work standalone in simulation
# =========================================================================
VLOG_OPTIONS += +define+USE_BEHAVIORAL_BRAM

# =========================================================================
# Debug Macros - Uncomment to enable verbose output per module
# =========================================================================
# VLOG_OPTIONS += +define+DEBUG_DISPATCHER        # dispatcher_2d.sv
# VLOG_OPTIONS += +define+DEBUG_FETCHER           # fetcher_2d.sv
# VLOG_OPTIONS += +define+DEBUG_DISPATCHER_CTRL   # dispatcher_control_2d.sv
# VLOG_OPTIONS += +define+DEBUG_MASTER_CTRL       # master_control_2d.sv
# VLOG_OPTIONS += +define+DEBUG_MLPSTACK          # comp_MLPStack.sv, comp_MLPStack_oFIFO.sv, weight_bram.sv, comp_fp_adder_pipeline.sv
# VLOG_OPTIONS += +define+DEBUG_COMPUTE           # compute_engine_2d.sv
# VLOG_OPTIONS += +define+DEBUG_FLEX_FIFO         # flex_fifo.sv (config display)
# VLOG_OPTIONS += +define+DEBUG_CMD_FIFO          # cmd_fifo.sv (FIFO writes/reads)
# VLOG_OPTIONS += +define+DEBUG_ENGINE_TOP        # engine_top_2d.sv (weight address calc)
# VLOG_OPTIONS += +define+DEBUG_TB                # tb_gemm2d.sv (AXI, FIFO, MC state)
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
	@echo "  2-D GEMM Full Integration Compilation Started: $$(date)" | tee -a $(LOG_FILE)
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "Compiling Achronix primitives..." | tee -a $(LOG_FILE)
	@export LD_LIBRARY_PATH="" && \
	vlog $(VLOG_OPTIONS) \
		$(DSM_COMPILE_FILE) \
		$(DEVICE_MODELS) \
		$(ACX_LIB_S7T)/common/acx_integer.sv \
		$(ACX_LIB_S7T)/common/acx_floating_point.sv >> $(LOG_FILE) 2>&1 || \
		(echo "ERROR: ACX library compilation failed. See $(LOG_FILE)" && exit 1)
	@echo "Compiling package and include files..." | tee -a $(LOG_FILE)
	@export LD_LIBRARY_PATH="" && \
	vlog $(VLOG_OPTIONS) \
		$(GEMM_INC)/gemm_pkg.sv >> $(LOG_FILE) 2>&1 || \
		(echo "ERROR: Package compilation failed. See $(LOG_FILE)" && exit 1)
	@echo "Compiling MLP primitives..." | tee -a $(LOG_FILE)
	@export LD_LIBRARY_PATH="" && \
	vlog $(VLOG_OPTIONS) \
		$(GEMM_RTL)/comp_mlp_dot16_bfp8.sv \
		$(GEMM_RTL)/weight_bram.sv \
		$(GEMM_RTL)/comp_MLP.sv \
		$(GEMM_RTL)/comp_MLPRow.sv \
		$(GEMM_RTL)/comp_stack_fifo.sv >> $(LOG_FILE) 2>&1 || \
		(echo "ERROR: MLP primitives compilation failed. See $(LOG_FILE)" && exit 1)
	@echo "Compiling FP arithmetic modules..." | tee -a $(LOG_FILE)
	@export LD_LIBRARY_PATH="" && \
	vlog $(VLOG_OPTIONS) \
		$(GEMM_RTL)/fp_to_int.sv \
		$(GEMM_RTL)/int_to_fp.sv \
		$(GEMM_RTL)/int_adder_tree.sv \
		$(GEMM_RTL)/comp_fp_adder_pipeline.sv >> $(LOG_FILE) 2>&1 || \
		(echo "ERROR: FP arithmetic compilation failed. See $(LOG_FILE)" && exit 1)
	@echo "Compiling FIFO and BRAM modules..." | tee -a $(LOG_FILE)
	@export LD_LIBRARY_PATH="" && \
	vlog $(VLOG_OPTIONS) \
		$(GEMM_RTL)/flex_fifo.sv \
		$(GEMM_RTL)/comp_row_bram.sv \
		$(GEMM_RTL)/comp_MLPStack.sv \
		$(GEMM_RTL)/comp_MLPStack_oFIFO.sv >> $(LOG_FILE) 2>&1 || \
		(echo "ERROR: FIFO/BRAM compilation failed. See $(LOG_FILE)" && exit 1)
	@echo "Compiling Fetcher and Dispatcher modules..." | tee -a $(LOG_FILE)
	@export LD_LIBRARY_PATH="" && \
	vlog $(VLOG_OPTIONS) \
		$(GEMM_RTL)/fetcher_2d.sv \
		$(GEMM_RTL)/dispatcher_2d.sv \
		$(GEMM_RTL)/dispatcher_control_2d.sv >> $(LOG_FILE) 2>&1 || \
		(echo "ERROR: Fetcher/Dispatcher compilation failed. See $(LOG_FILE)" && exit 1)
	@echo "Compiling Compute Engine and Control modules..." | tee -a $(LOG_FILE)
	@export LD_LIBRARY_PATH="" && \
	vlog $(VLOG_OPTIONS) \
		$(GEMM_RTL)/compute_engine_2d.sv \
		$(GEMM_RTL)/cmd_fifo.sv \
		$(GEMM_RTL)/cmd_bram_fifo_bridge.sv \
		$(GEMM_RTL)/master_control_2d.sv \
		$(GEMM_RTL)/result_collector_2d.sv \
		$(GEMM_RTL)/result_to_dma.sv >> $(LOG_FILE) 2>&1 || \
		(echo "ERROR: Control modules compilation failed. See $(LOG_FILE)" && exit 1)
	@echo "Compiling Top-level module..." | tee -a $(LOG_FILE)
	@export LD_LIBRARY_PATH="" && \
	vlog $(VLOG_OPTIONS) \
		$(GEMM_RTL)/engine_top_2d.sv >> $(LOG_FILE) 2>&1 || \
		(echo "ERROR: Top-level compilation failed. See $(LOG_FILE)" && exit 1)
	@echo "Compiling Memory Models..." | tee -a $(LOG_FILE)
	@export LD_LIBRARY_PATH="" && \
	vlog $(VLOG_OPTIONS) \
		$(SIM_DIR)/tb_mem_model_parameterized.sv >> $(LOG_FILE) 2>&1 || \
		(echo "ERROR: Memory model compilation failed. See $(LOG_FILE)" && exit 1)
	@echo "Compiling testbench..." | tee -a $(LOG_FILE)
	@export LD_LIBRARY_PATH="" && \
	vlog $(VLOG_OPTIONS) \
		$(SIM_DIR)/tb_gemm2d.sv >> $(LOG_FILE) 2>&1 || \
		(echo "ERROR: Testbench compilation failed. See $(LOG_FILE)" && exit 1)
	@echo "Compilation completed successfully" | tee -a $(LOG_FILE)
	@echo ""

# Run simulation
run_vsim: compile
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "  2-D GEMM Full Integration Simulation Started: $$(date)" | tee -a $(LOG_FILE)
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "Running 2-D GEMM simulation..." | tee -a $(LOG_FILE)
	@export LD_LIBRARY_PATH="" && \
	vsim -c -asdb_skip -do "run -all; quit -force" work.$(SIM_TOP) >> $(LOG_FILE) 2>&1 || \
		(echo "ERROR: Simulation failed. See $(LOG_FILE)" && exit 1)
	@echo "" | tee -a $(LOG_FILE)
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "  2-D GEMM Full Integration Simulation Completed: $$(date)" | tee -a $(LOG_FILE)
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "" | tee -a $(LOG_FILE)
	@echo "Extracting test summary..." | tee -a $(LOG_FILE)
	@grep -E "PASS|FAIL|ALL TESTS|Test|SUMMARY|ERROR|MATCH" $(LOG_FILE) | tail -40 || echo "Warning: Could not find test summary"
	@echo ""
	@echo "Full log available in: $(LOG_FILE)"

# Run tests
run: run_vsim

# =========================================================================
# Multi-Iteration Test Targets
# Tests weight persistence across 10 iterations
# =========================================================================
compile_multi: create_library
	@echo "======================================================================" | tee $(LOG_FILE_MULTI)
	@echo "  Multi-Iteration GEMM Compilation Started: $$(date)" | tee -a $(LOG_FILE_MULTI)
	@echo "======================================================================" | tee -a $(LOG_FILE_MULTI)
	@echo "Compiling Achronix primitives..." | tee -a $(LOG_FILE_MULTI)
	@export LD_LIBRARY_PATH="" && \
	vlog $(VLOG_OPTIONS) \
		$(DSM_COMPILE_FILE) \
		$(DEVICE_MODELS) \
		$(ACX_LIB_S7T)/common/acx_integer.sv \
		$(ACX_LIB_S7T)/common/acx_floating_point.sv >> $(LOG_FILE_MULTI) 2>&1 || \
		(echo "ERROR: ACX library compilation failed. See $(LOG_FILE_MULTI)" && exit 1)
	@echo "Compiling package and include files..." | tee -a $(LOG_FILE_MULTI)
	@export LD_LIBRARY_PATH="" && \
	vlog $(VLOG_OPTIONS) \
		$(GEMM_INC)/gemm_pkg.sv >> $(LOG_FILE_MULTI) 2>&1 || \
		(echo "ERROR: Package compilation failed. See $(LOG_FILE_MULTI)" && exit 1)
	@echo "Compiling MLP primitives..." | tee -a $(LOG_FILE_MULTI)
	@export LD_LIBRARY_PATH="" && \
	vlog $(VLOG_OPTIONS) \
		$(GEMM_RTL)/comp_mlp_dot16_bfp8.sv \
		$(GEMM_RTL)/weight_bram.sv \
		$(GEMM_RTL)/comp_MLP.sv \
		$(GEMM_RTL)/comp_MLPRow.sv \
		$(GEMM_RTL)/comp_stack_fifo.sv >> $(LOG_FILE_MULTI) 2>&1 || \
		(echo "ERROR: MLP primitives compilation failed. See $(LOG_FILE_MULTI)" && exit 1)
	@echo "Compiling FP arithmetic modules..." | tee -a $(LOG_FILE_MULTI)
	@export LD_LIBRARY_PATH="" && \
	vlog $(VLOG_OPTIONS) \
		$(GEMM_RTL)/fp_to_int.sv \
		$(GEMM_RTL)/int_to_fp.sv \
		$(GEMM_RTL)/int_adder_tree.sv \
		$(GEMM_RTL)/comp_fp_adder_pipeline.sv >> $(LOG_FILE_MULTI) 2>&1 || \
		(echo "ERROR: FP arithmetic compilation failed. See $(LOG_FILE_MULTI)" && exit 1)
	@echo "Compiling FIFO and BRAM modules..." | tee -a $(LOG_FILE_MULTI)
	@export LD_LIBRARY_PATH="" && \
	vlog $(VLOG_OPTIONS) \
		$(GEMM_RTL)/flex_fifo.sv \
		$(GEMM_RTL)/comp_row_bram.sv \
		$(GEMM_RTL)/comp_MLPStack.sv \
		$(GEMM_RTL)/comp_MLPStack_oFIFO.sv >> $(LOG_FILE_MULTI) 2>&1 || \
		(echo "ERROR: FIFO/BRAM compilation failed. See $(LOG_FILE_MULTI)" && exit 1)
	@echo "Compiling Fetcher and Dispatcher modules..." | tee -a $(LOG_FILE_MULTI)
	@export LD_LIBRARY_PATH="" && \
	vlog $(VLOG_OPTIONS) \
		$(GEMM_RTL)/fetcher_2d.sv \
		$(GEMM_RTL)/dispatcher_2d.sv \
		$(GEMM_RTL)/dispatcher_control_2d.sv >> $(LOG_FILE_MULTI) 2>&1 || \
		(echo "ERROR: Fetcher/Dispatcher compilation failed. See $(LOG_FILE_MULTI)" && exit 1)
	@echo "Compiling Compute Engine and Control modules..." | tee -a $(LOG_FILE_MULTI)
	@export LD_LIBRARY_PATH="" && \
	vlog $(VLOG_OPTIONS) \
		$(GEMM_RTL)/compute_engine_2d.sv \
		$(GEMM_RTL)/cmd_fifo.sv \
		$(GEMM_RTL)/master_control_2d.sv \
		$(GEMM_RTL)/result_collector_2d.sv >> $(LOG_FILE_MULTI) 2>&1 || \
		(echo "ERROR: Control modules compilation failed. See $(LOG_FILE_MULTI)" && exit 1)
	@echo "Compiling Top-level module..." | tee -a $(LOG_FILE_MULTI)
	@export LD_LIBRARY_PATH="" && \
	vlog $(VLOG_OPTIONS) \
		$(GEMM_RTL)/engine_top_2d.sv >> $(LOG_FILE_MULTI) 2>&1 || \
		(echo "ERROR: Top-level compilation failed. See $(LOG_FILE_MULTI)" && exit 1)
	@echo "Compiling Multi-Iteration Memory Model..." | tee -a $(LOG_FILE_MULTI)
	@export LD_LIBRARY_PATH="" && \
	vlog $(VLOG_OPTIONS) \
		$(SIM_DIR)/tb_mem_model_multi_iter.sv >> $(LOG_FILE_MULTI) 2>&1 || \
		(echo "ERROR: Memory model compilation failed. See $(LOG_FILE_MULTI)" && exit 1)
	@echo "Compiling Multi-Iteration Testbench..." | tee -a $(LOG_FILE_MULTI)
	@export LD_LIBRARY_PATH="" && \
	vlog $(VLOG_OPTIONS) \
		$(SIM_DIR)/tb_gemm2d_multi_iter.sv >> $(LOG_FILE_MULTI) 2>&1 || \
		(echo "ERROR: Testbench compilation failed. See $(LOG_FILE_MULTI)" && exit 1)
	@echo "Compilation completed successfully" | tee -a $(LOG_FILE_MULTI)
	@echo ""

run_vsim_multi: compile_multi
	@echo "======================================================================" | tee -a $(LOG_FILE_MULTI)
	@echo "  Multi-Iteration GEMM Simulation Started: $$(date)" | tee -a $(LOG_FILE_MULTI)
	@echo "======================================================================" | tee -a $(LOG_FILE_MULTI)
	@echo "Running Multi-Iteration GEMM simulation (10 iterations)..." | tee -a $(LOG_FILE_MULTI)
	@export LD_LIBRARY_PATH="" && \
	vsim -c -asdb_skip -do "run -all; quit -force" work.$(SIM_TOP_MULTI) >> $(LOG_FILE_MULTI) 2>&1 || \
		(echo "ERROR: Simulation failed. See $(LOG_FILE_MULTI)" && exit 1)
	@echo "" | tee -a $(LOG_FILE_MULTI)
	@echo "======================================================================" | tee -a $(LOG_FILE_MULTI)
	@echo "  Multi-Iteration GEMM Simulation Completed: $$(date)" | tee -a $(LOG_FILE_MULTI)
	@echo "======================================================================" | tee -a $(LOG_FILE_MULTI)
	@echo "" | tee -a $(LOG_FILE_MULTI)
	@echo "Extracting test summary..." | tee -a $(LOG_FILE_MULTI)
	@grep -E "PASS|FAIL|ALL TESTS|ITERATION|MATCH|Captured|MISMATCH|errors" $(LOG_FILE_MULTI) | tail -50 || echo "Warning: Could not find test summary"
	@echo ""
	@echo "Full log available in: $(LOG_FILE_MULTI)"

run_multi: run_vsim_multi

# =========================================================================
# CSR-to-FIFO Bridge Test Targets
# Tests the hardware CSR interface path
# =========================================================================
compile_csr: create_library
	@echo "======================================================================" | tee $(LOG_FILE_CSR)
	@echo "  CSR Bridge GEMM Compilation Started: $$(date)" | tee -a $(LOG_FILE_CSR)
	@echo "======================================================================" | tee -a $(LOG_FILE_CSR)
	@echo "Compiling Achronix primitives..." | tee -a $(LOG_FILE_CSR)
	@export LD_LIBRARY_PATH="" && \
	vlog $(VLOG_OPTIONS) \
		$(DSM_COMPILE_FILE) \
		$(DEVICE_MODELS) \
		$(ACX_LIB_S7T)/common/acx_integer.sv \
		$(ACX_LIB_S7T)/common/acx_floating_point.sv >> $(LOG_FILE_CSR) 2>&1 || \
		(echo "ERROR: ACX library compilation failed. See $(LOG_FILE_CSR)" && exit 1)
	@echo "Compiling package and include files..." | tee -a $(LOG_FILE_CSR)
	@export LD_LIBRARY_PATH="" && \
	vlog $(VLOG_OPTIONS) \
		$(GEMM_INC)/gemm_pkg.sv >> $(LOG_FILE_CSR) 2>&1 || \
		(echo "ERROR: Package compilation failed. See $(LOG_FILE_CSR)" && exit 1)
	@echo "Compiling MLP primitives..." | tee -a $(LOG_FILE_CSR)
	@export LD_LIBRARY_PATH="" && \
	vlog $(VLOG_OPTIONS) \
		$(GEMM_RTL)/comp_mlp_dot16_bfp8.sv \
		$(GEMM_RTL)/weight_bram.sv \
		$(GEMM_RTL)/comp_MLP.sv \
		$(GEMM_RTL)/comp_MLPRow.sv \
		$(GEMM_RTL)/comp_stack_fifo.sv >> $(LOG_FILE_CSR) 2>&1 || \
		(echo "ERROR: MLP primitives compilation failed. See $(LOG_FILE_CSR)" && exit 1)
	@echo "Compiling FP arithmetic modules..." | tee -a $(LOG_FILE_CSR)
	@export LD_LIBRARY_PATH="" && \
	vlog $(VLOG_OPTIONS) \
		$(GEMM_RTL)/fp_to_int.sv \
		$(GEMM_RTL)/int_to_fp.sv \
		$(GEMM_RTL)/int_adder_tree.sv \
		$(GEMM_RTL)/comp_fp_adder_pipeline.sv >> $(LOG_FILE_CSR) 2>&1 || \
		(echo "ERROR: FP arithmetic compilation failed. See $(LOG_FILE_CSR)" && exit 1)
	@echo "Compiling FIFO and BRAM modules..." | tee -a $(LOG_FILE_CSR)
	@export LD_LIBRARY_PATH="" && \
	vlog $(VLOG_OPTIONS) \
		$(GEMM_RTL)/flex_fifo.sv \
		$(GEMM_RTL)/comp_row_bram.sv \
		$(GEMM_RTL)/comp_MLPStack.sv \
		$(GEMM_RTL)/comp_MLPStack_oFIFO.sv >> $(LOG_FILE_CSR) 2>&1 || \
		(echo "ERROR: FIFO/BRAM compilation failed. See $(LOG_FILE_CSR)" && exit 1)
	@echo "Compiling Fetcher and Dispatcher modules..." | tee -a $(LOG_FILE_CSR)
	@export LD_LIBRARY_PATH="" && \
	vlog $(VLOG_OPTIONS) \
		$(GEMM_RTL)/fetcher_2d.sv \
		$(GEMM_RTL)/dispatcher_2d.sv \
		$(GEMM_RTL)/dispatcher_control_2d.sv >> $(LOG_FILE_CSR) 2>&1 || \
		(echo "ERROR: Fetcher/Dispatcher compilation failed. See $(LOG_FILE_CSR)" && exit 1)
	@echo "Compiling Compute Engine and Control modules..." | tee -a $(LOG_FILE_CSR)
	@export LD_LIBRARY_PATH="" && \
	vlog $(VLOG_OPTIONS) \
		$(GEMM_RTL)/compute_engine_2d.sv \
		$(GEMM_RTL)/cmd_fifo.sv \
		$(GEMM_RTL)/csr_to_fifo_bridge.sv \
		$(GEMM_RTL)/master_control_2d.sv \
		$(GEMM_RTL)/result_collector_2d.sv \
		$(GEMM_RTL)/result_to_dma.sv >> $(LOG_FILE_CSR) 2>&1 || \
		(echo "ERROR: Control modules compilation failed. See $(LOG_FILE_CSR)" && exit 1)
	@echo "Compiling Top-level module..." | tee -a $(LOG_FILE_CSR)
	@export LD_LIBRARY_PATH="" && \
	vlog $(VLOG_OPTIONS) \
		$(GEMM_RTL)/engine_top_2d.sv >> $(LOG_FILE_CSR) 2>&1 || \
		(echo "ERROR: Top-level compilation failed. See $(LOG_FILE_CSR)" && exit 1)
	@echo "Compiling Memory Models..." | tee -a $(LOG_FILE_CSR)
	@export LD_LIBRARY_PATH="" && \
	vlog $(VLOG_OPTIONS) \
		$(SIM_DIR)/tb_mem_model_parameterized.sv >> $(LOG_FILE_CSR) 2>&1 || \
		(echo "ERROR: Memory model compilation failed. See $(LOG_FILE_CSR)" && exit 1)
	@echo "Compiling CSR Bridge Testbench..." | tee -a $(LOG_FILE_CSR)
	@export LD_LIBRARY_PATH="" && \
	vlog $(VLOG_OPTIONS) \
		$(SIM_DIR)/tb_gemm2d_csr.sv >> $(LOG_FILE_CSR) 2>&1 || \
		(echo "ERROR: Testbench compilation failed. See $(LOG_FILE_CSR)" && exit 1)
	@echo "Compilation completed successfully" | tee -a $(LOG_FILE_CSR)
	@echo ""

run_vsim_csr: compile_csr
	@echo "======================================================================" | tee -a $(LOG_FILE_CSR)
	@echo "  CSR Bridge GEMM Simulation Started: $$(date)" | tee -a $(LOG_FILE_CSR)
	@echo "======================================================================" | tee -a $(LOG_FILE_CSR)
	@echo "Running CSR Bridge GEMM simulation..." | tee -a $(LOG_FILE_CSR)
	@export LD_LIBRARY_PATH="" && \
	vsim -c -asdb_skip -do "run -all; quit -force" work.$(SIM_TOP_CSR) >> $(LOG_FILE_CSR) 2>&1 || \
		(echo "ERROR: Simulation failed. See $(LOG_FILE_CSR)" && exit 1)
	@echo "" | tee -a $(LOG_FILE_CSR)
	@echo "======================================================================" | tee -a $(LOG_FILE_CSR)
	@echo "  CSR Bridge GEMM Simulation Completed: $$(date)" | tee -a $(LOG_FILE_CSR)
	@echo "======================================================================" | tee -a $(LOG_FILE_CSR)
	@echo "" | tee -a $(LOG_FILE_CSR)
	@echo "Extracting test summary..." | tee -a $(LOG_FILE_CSR)
	@grep -E "PASS|FAIL|ALL TESTS|Test|SUMMARY|ERROR|MATCH|mc_state|fifo_count" $(LOG_FILE_CSR) | tail -60 || echo "Warning: Could not find test summary"
	@echo ""
	@echo "Full log available in: $(LOG_FILE_CSR)"

run_csr: run_vsim_csr

debug_csr: compile_csr
	@echo "=== Running CSR Bridge GEMM Debug Simulation ==="
	@export LD_LIBRARY_PATH="" && \
	vsim -gui work.$(SIM_TOP_CSR) &

# Debug with GUI
debug: compile
	@echo "=== Running 2-D GEMM Debug Simulation ==="
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
		grep -E "PASS|FAIL|Test|SUMMARY|ERROR" $(LOG_FILE) | tail -50; \
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
	@echo "  Makefile for 2-D GEMM Full Integration Simulation"
	@echo "========================================================================"
	@echo ""
	@echo "Purpose: Test the complete 2-D GEMM architecture with:"
	@echo "  - engine_top_2d (top-level)"
	@echo "  - master_control_2d (command processor)"
	@echo "  - 16 x dispatcher_control_2d (per-row GDDR6 fetch/dispatch)"
	@echo "  - 16 x compute_engine_2d (per-row MLP compute)"
	@echo "  - result_collector_2d (cross-row reduction)"
	@echo ""
	@echo "Current Configuration: NUM_MLPS=$(NUM_MLPS), NUM_COLS=$(NUM_COLS)"
	@echo ""
	@echo "Targets:"
	@echo "  make                  - Compile and run single-iteration test ($(LOG_FILE))"
	@echo "  make run              - Compile and run single-iteration test (same as make)"
	@echo "  make run NUM_MLPS=2   - Run with 2 MLPs (4 columns)"
	@echo "  make run NUM_MLPS=4   - Run with 4 MLPs (8 columns)"
	@echo "  make run NUM_MLPS=8   - Run with 8 MLPs (16 columns)"
	@echo "  make run_all_configs  - Run all configurations (2, 4, 8 MLPs)"
	@echo "  make run_multi        - Run multi-iteration test (10 iters, weight persistence)"
	@echo "  make run_csr          - Run CSR bridge test"
	@echo "  make compile          - Compile only (no simulation)"
	@echo "  make debug            - Run single-iteration test with GUI"
	@echo "  make summary          - Show test results summary"
	@echo "  make view-log         - View full simulation log"
	@echo "  make clean            - Remove all generated files"
	@echo "  make help             - Show this help message"
	@echo ""
	@echo "Multi-Iteration Test:"
	@echo "  - Tests weight persistence across 10 MATMUL iterations"
	@echo "  - Weights loaded once, activations reloaded each iteration"
	@echo "  - Verifies all 160 results (10 x 16) are identical"
	@echo ""
	@echo "========================================================================"

.PHONY: all create_library compile run_vsim run run_all_configs compile_multi run_vsim_multi run_multi compile_csr run_vsim_csr run_csr debug debug_csr view-log summary clean help
