# Makefile for GEMM Engine Top Simulation (FIFO Interface)
# Uses engine_top.sv with direct FIFO interface
# Tests: Complete MS2.0 pipeline with FIFO-based command/result interface
# Updated: Uses ACX_INT_MULT_ADD primitives for hardware acceleration
# Modified: Redirects compilation and simulation output to sim.log

TB = tb_engine_top
TOP = tb_engine_top
WORK = work
LOG_FILE = sim.log

# Riviera-PRO commands
VLIB = vlib
VLOG = vlog
VSIM = vsim

# Achronix environment setup (for ACX primitives)
DEVICE := AC7t1500
BASE_NAME := ac7t1500
export ACX_DEVICE_INSTALL_DIR := $(ACE_INSTALL_DIR)/system/data/$(DEVICE)
DSM_INCLUDE_FILE := $(ACX_DEVICE_INSTALL_DIR)/sim/$(BASE_NAME)_dsm_incdirs.f
DSM_COMPILE_FILE := $(ACX_DEVICE_INSTALL_DIR)/sim/$(BASE_NAME)_dsm_filelist.v
DEVICE_MODELS := $(ACE_INSTALL_DIR)/libraries/device_models/$(DEVICE)_simmodels.sv
ACX_LIB_S7T := $(ACE_INSTALL_DIR)/libraries/speedster7t

# Source directories  
CE_W8A8_TB = /home/workstation/compute_engine_w8a8/src/tb
CE_W8A8_RTL = /home/workstation/compute_engine_w8a8/src/rtl
CE_W8A8_INC = /home/workstation/compute_engine_w8a8/src/include
GEMM_RTL = ../../src/rtl
GEMM_INC = ../../src/include
GEMM_TB = ../../src/tb  # Local testbench directory

# Include paths (added ACX paths for primitives)
INCLUDES = +incdir+$(CE_W8A8_INC) +incdir+$(GEMM_INC) +incdir+$(ACE_INSTALL_DIR)/libraries/ +incdir+$(ACX_DEVICE_INSTALL_DIR)/sim +incdir+$(ACX_LIB_S7T)/common

# Testbench sources
TB_SOURCES = ../../src/tb/tb_memory_model.sv tb_engine_top.sv

# RTL sources (from gemm - MS2.0 FIFO architecture!)
RTL_SOURCES = \
	$(GEMM_RTL)/cmd_fifo.sv \
	$(GEMM_RTL)/tile_result_fifo.sv \
	$(GEMM_RTL)/master_control.sv \
	$(GEMM_RTL)/fetcher.sv \
	$(GEMM_RTL)/dispatcher.sv \
	$(GEMM_RTL)/dispatcher_control.sv \
	$(GEMM_RTL)/dispatcher_bram.sv \
	$(GEMM_RTL)/tile_bram.sv \
	$(GEMM_RTL)/compute_engine_modular_opt.sv \
	$(GEMM_RTL)/gfp8_bcv_controller_opt.sv \
	$(GEMM_RTL)/gfp8_nv_dot_ultra_opt.sv \
	$(GEMM_RTL)/gfp8_group_dot_mlp.sv \
	$(GEMM_RTL)/gfp8_to_fp16.sv \
	$(GEMM_RTL)/result_bram.sv \
	$(GEMM_RTL)/result_fifo_to_simple_bram.sv \
	$(GEMM_RTL)/engine_top.sv

# NAP wrapper (contains t_AXI4 interface)
NAP_WRAPPER = $(GEMM_RTL)/nap_responder_wrapper.sv

# Include GDDR6-specific Makefile rules
include Makefile.gddr6

.PHONY: all clean run compile debug view-log summary

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
	@$(VLOG) -sv $(INCLUDES) -work $(WORK) \
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
	@echo "Compiling testbench and RTL..." | tee -a $(LOG_FILE)
	@export LD_LIBRARY_PATH="" && \
	$(VLOG) -sv $(INCLUDES) +define+SIMULATION +define+SIM_VERBOSE \
		-err VCP2675 W1 \
		-work $(WORK) \
		$(NAP_WRAPPER) \
		$(RTL_SOURCES) \
		$(TB_SOURCES) >> $(LOG_FILE) 2>&1 || \
		(echo "ERROR: RTL/TB compilation failed. See $(LOG_FILE)" && exit 1)
	@echo "Compilation completed successfully" | tee -a $(LOG_FILE)
	@echo ""

# Run simulation
run: compile
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "  Simulation Started: $$(date)" | tee -a $(LOG_FILE)
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

# Run with GUI for debugging (logs to sim_debug.log)
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
	@rm -f *.log
	@rm -f *.vcd
	@rm -f *.asdb
	@rm -f *.tmp
	@echo "Clean complete"

help:
	@echo "========================================================================"
	@echo "  Makefile for GEMM Engine Top Simulation"
	@echo "========================================================================"
	@echo ""
	@echo "Purpose: Test engine_top.sv with direct FIFO interface"
	@echo "         MS2.0 architecture with command/result FIFOs"
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
	@echo "  - Direct FIFO interface (no CSR bridge)"
	@echo "  - Command FIFO: 4096x32-bit"
	@echo "  - Result FIFO: 16384x16-bit (FP16)"
	@echo "  - Complete MS2.0 pipeline integration"
	@echo "  - All output logged to $(LOG_FILE)"
	@echo ""
	@echo "Test Configurations:"
	@echo "  B1_C1_V1, B2_C2_V2, B4_C4_V4, B2_C2_V64, B4_C4_V32,"
	@echo "  B8_C8_V16, B1_C128_V1, B128_C1_V1, B1_C1_V128"
	@echo ""
	@echo "========================================================================"

