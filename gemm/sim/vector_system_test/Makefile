# Makefile for GEMM Engine Top Simulation (MLP-Based)
# Uses engine_top.sv with MLP compute engine and direct FIFO interface
# Tests: Complete MS2.0 pipeline with FIFO-based command/result interface
# Updated: Dec 2025 - MLP-only mode (modular compute engine deprecated)

TB ?= tb_engine_top
TOP ?= $(TB)
WORK = work
LOG_FILE = sim.log

# Riviera-PRO commands
VLIB = vlib
VLOG = vlog
VSIM = vsim

# Memory model: GDDR6 Realistic (40-cycle latency, 32 outstanding ARs)
# Always uses tb_memory_model_realistic.sv for accurate GDDR6 timing
LATENCY ?= 40                   # Realistic GDDR6 latency (100ns @ 400MHz)
VLOG_DEFINES = +define+LATENCY_CYCLES=$(LATENCY)

# Achronix environment setup (for ACX primitives)
DEVICE := AC7t1500
BASE_NAME := ac7t1500
export ACX_DEVICE_INSTALL_DIR := $(ACE_INSTALL_DIR)/system/data/$(DEVICE)
DSM_INCLUDE_FILE := $(ACX_DEVICE_INSTALL_DIR)/sim/$(BASE_NAME)_dsm_incdirs.f
DSM_COMPILE_FILE := $(ACX_DEVICE_INSTALL_DIR)/sim/$(BASE_NAME)_dsm_filelist.v
DEVICE_MODELS := $(ACE_INSTALL_DIR)/libraries/device_models/$(DEVICE)_simmodels.sv
ACX_LIB_S7T := $(ACE_INSTALL_DIR)/libraries/speedster7t

# Source directories 
GEMM_RTL = ../../src/rtl
GEMM_INC = ../../src/include
GEMM_TB = ../../src/tb

# Include paths (added ACX paths for primitives)
INCLUDES = +incdir+$(CE_W8A8_INC) +incdir+$(GEMM_INC) +incdir+$(ACE_INSTALL_DIR)/libraries/ +incdir+$(ACX_DEVICE_INSTALL_DIR)/sim +incdir+$(ACX_LIB_S7T)/common

# Testbench sources - Always uses GDDR6 realistic memory model
TB_SOURCES = ../../src/tb/tb_memory_model_realistic.sv $(TB).sv

# RTL sources (MS2.0 MLP-based architecture - Dec 2025)
# engine_top.sv uses compute_engine_mlp with direct 256-bit output
# Legacy modules archived to archive_dec15/:
#   - compute_engine_modular, gfp8_*, tile_bram, tile_result_fifo
#   - result_arbiter, result_bram (not used in MLP mode)
RTL_SOURCES = \
	$(GEMM_RTL)/flex_fifo.sv \
	$(GEMM_RTL)/cmd_fifo.sv \
	$(GEMM_RTL)/master_control.sv \
	$(GEMM_RTL)/fetcher.sv \
	$(GEMM_RTL)/dispatcher_control.sv \
	$(GEMM_RTL)/result_fifo_to_simple_bram.sv \
	$(GEMM_RTL)/comp_row_bram.sv \
	$(GEMM_RTL)/weight_bram.sv \
	$(GEMM_RTL)/comp_mlp_bram.sv \
	$(GEMM_RTL)/comp_mlp_bram_col.sv \
	$(GEMM_RTL)/comp_mlp_bram_col_wrapper.sv \
	$(GEMM_RTL)/comp_bram_fill_ctrl.sv \
	$(GEMM_RTL)/comp_mlp_dispatch.sv \
	$(GEMM_RTL)/comp_mlp_col_ctrl.sv \
	$(GEMM_RTL)/comp_mlp_dot16_int8.sv \
	$(GEMM_RTL)/comp_mlp_dot16_bfp8.sv \
	$(GEMM_RTL)/fp24_add.sv \
	$(GEMM_RTL)/fp24_to_fp16.sv \
	$(GEMM_RTL)/fp_to_int.sv \
	$(GEMM_RTL)/int_to_fp.sv \
	$(GEMM_RTL)/int_adder_tree.sv \
	$(GEMM_RTL)/comp_fp_adder_pipeline.sv \
	$(GEMM_RTL)/compute_engine_mlp.sv \
	$(GEMM_RTL)/engine_top.sv

# NAP wrapper (contains t_AXI4 interface)
NAP_WRAPPER = $(GEMM_RTL)/nap_responder_wrapper.sv

.PHONY: all clean run compile debug view-log summary help run_realistic

# Default target: run simulation
all: run

# Create work library
$(WORK):
	@echo "Creating work library..." | tee $(LOG_FILE)
	@$(VLIB) $(WORK) >> $(LOG_FILE) 2>&1

# Compile
compile: $(WORK)
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "  Compilation Started: $$(date)" | tee -a $(LOG_FILE)
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "Compiling packages..." | tee -a $(LOG_FILE)
	@$(VLOG) -sv $(INCLUDES) -timescale "1ps/1ps" -work $(WORK) \
		$(GEMM_INC)/gemm_pkg.sv >> $(LOG_FILE) 2>&1 || \
		(echo "ERROR: Package compilation failed. See $(LOG_FILE)" && exit 1)
	@echo "Compiling ACX libraries and primitives..." | tee -a $(LOG_FILE)
	@export LD_LIBRARY_PATH="" && \
	$(VLOG) -sv $(INCLUDES) +define+SIMULATION \
		-timescale "1ps/1ps" \
		-f $(DSM_INCLUDE_FILE) \
		$(DSM_COMPILE_FILE) \
		$(DEVICE_MODELS) \
		$(ACX_LIB_S7T)/common/acx_floating_point.sv \
		$(ACX_LIB_S7T)/common/acx_integer.sv >> $(LOG_FILE) 2>&1 || \
		(echo "ERROR: ACX library compilation failed. See $(LOG_FILE)" && exit 1)
	@echo "Compiling testbench and RTL (MLP mode)..." | tee -a $(LOG_FILE)
	@export LD_LIBRARY_PATH="" && \
	$(VLOG) -sv $(INCLUDES) $(VLOG_DEFINES) +define+SIMULATION +define+SIM_VERBOSE \
		-timescale "1ps/1ps" \
		-err VCP2675 W1 \
		-work $(WORK) \
		$(NAP_WRAPPER) \
		$(RTL_SOURCES) \
		$(TB_SOURCES) >> $(LOG_FILE) 2>&1 || \
		(echo "ERROR: RTL/TB compilation failed. See $(LOG_FILE)" && exit 1)
	@echo "Compilation completed successfully" | tee -a $(LOG_FILE)
	@echo ""

# Run simulation
run:
	@$(MAKE) clean
	@$(MAKE) compile
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "  Simulation Started: $$(date)" | tee -a $(LOG_FILE)
	@echo "  Features: MLP compute engine, 256-bit direct result output" | tee -a $(LOG_FILE)
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "Running GEMM Engine Top simulation..." | tee -a $(LOG_FILE)
	@$(VSIM) -c -do "run -all; quit -force" $(WORK).$(TOP) >> $(LOG_FILE) 2>&1 || \
		(echo "ERROR: Simulation failed. See $(LOG_FILE)" && exit 1)
	@echo "" | tee -a $(LOG_FILE)
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "  Simulation Completed: $$(date)" | tee -a $(LOG_FILE)
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "" | tee -a $(LOG_FILE)
	@echo "Extracting test summary..." | tee -a $(LOG_FILE)
	@grep -A 6 "TEST SUMMARY" $(LOG_FILE) || echo "Warning: Could not find test summary"
	@echo ""
	@echo "Full log available in: $(LOG_FILE)"

# Run with explicit GDDR6 realistic timing (40-cycle latency)
run_realistic: clean
	@echo "======================================================================" | tee $(LOG_FILE)
	@echo "  GDDR6 REALISTIC MEMORY MODEL (40-cycle latency, 32 outstanding ARs)" | tee -a $(LOG_FILE)
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@$(MAKE) LATENCY=40 run

# Run with GUI for debugging
debug: compile
	@echo ""
	@echo "Running simulation with GUI (logs to sim_debug.log)..."
	@echo ""
	$(VSIM) $(WORK).$(TOP) > sim_debug.log 2>&1 &

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
		grep -A 6 "TEST SUMMARY" $(LOG_FILE) | sed 's/\# KERNEL: //'; \
	else \
		echo "Error: $(LOG_FILE) not found. Run 'make run' first."; \
	fi

# Clean
clean:
	@echo "Cleaning simulation files..."
	@rm -rf $(WORK)
	@rm -f transcript
	@rm -f *.wlf
	@rm -f *.vcd
	@rm -f *.asdb
	@rm -f *.tmp
	@echo "Clean complete"

help:
	@echo "========================================================================"
	@echo "  Makefile for GEMM Engine Top Simulation (MLP Mode)"
	@echo "========================================================================"
	@echo ""
	@echo "Purpose: Test engine_top.sv with MLP compute engine"
	@echo "         MS2.0 architecture with command/result FIFOs"
	@echo ""
	@echo "Targets:"
	@echo "  make              - Compile and run simulation"
	@echo "  make run          - Same as make"
	@echo "  make run LATENCY=N - Run with N-cycle memory latency (default: 40)"
	@echo "  make run_realistic - Explicitly run with 40-cycle GDDR6 latency"
	@echo "  make compile      - Compile only (no simulation)"
	@echo "  make debug        - Run with GUI for debugging"
	@echo "  make summary      - Show test results summary"
	@echo "  make view-log     - View full simulation log ($(LOG_FILE))"
	@echo "  make clean        - Remove all generated files"
	@echo "  make help         - Show this help message"
	@echo ""
	@echo "Memory Model:"
	@echo "  Always uses: tb_memory_model_realistic.sv (GDDR6 realistic)"
	@echo "  - 40-cycle latency (100ns @ 400MHz)"
	@echo "  - 32 outstanding AR transactions"
	@echo "  - Realistic GDDR6+NoC timing characteristics"
	@echo ""
	@echo "Key Features:"
	@echo "  - MLP-based compute engine (compute_engine_mlp)"
	@echo "  - 256-bit direct result output (16 × FP16 per cycle)"
	@echo "  - Internal GFP8E5 → GFP8E8 exponent conversion"
	@echo "  - Supports C = 16, 32, 64, 128 (divisible by 16)"
	@echo "  - GDDR6 realistic memory model"
	@echo "  - Configurable latency via LATENCY parameter"
	@echo "  - All output logged to $(LOG_FILE)"
	@echo ""
	@echo "Test Configurations:"
	@echo "  C=16:  B4_C16_V8, B8_C16_V4, B16_C16_V8"
	@echo "  C>16:  B4_C32_V4, B8_C32_V2, B8_C64_V2, B2_C128_V1"
	@echo ""
	@echo "========================================================================"

.PHONY: multi-tile

# Multi-tile debug test
multi-tile: clean
	@echo "Creating work library..."
	@$(VLIB) $(WORK) > /dev/null 2>&1
	@echo "Compiling multi-tile test..."
	@$(VLOG) -quiet -work $(WORK) -f $(DSM_INCLUDE_FILE) $(DSM_COMPILE_FILE) $(DEVICE_MODELS) > /dev/null 2>&1
	@$(VLOG) -quiet -work $(WORK) $(INCLUDES) $(VLOG_DEFINES) -sv $(RTL_SOURCES) ../../src/tb/tb_memory_model_realistic.sv tb_multi_tile_test.sv > /dev/null 2>&1
	@echo "Running multi-tile test..."
	@$(VSIM) -batch -c tb_multi_tile_test -do "run -all; quit" > multi_tile.log 2>&1
	@echo "Multi-tile test complete. Results:"
	@echo ""
	@grep -E "TEST|PASS|FAIL|MONITOR" multi_tile.log || echo "No test results found"
