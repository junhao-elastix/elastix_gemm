# Makefile for GEMM Engine Top Simulation (FIFO Interface)
# Uses engine_top.sv with direct FIFO interface
# Tests: Complete MS2.0 pipeline with FIFO-based command/result interface
# Updated: Uses ACX_INT_MULT_ADD primitives for hardware acceleration

TB = tb_engine_top
TOP = tb_engine_top
WORK = work

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
CE_W8A8_TB = /home/dev/Dev/compute_engine_w8a8/src/tb
CE_W8A8_RTL = /home/dev/Dev/compute_engine_w8a8/src/rtl
CE_W8A8_INC = /home/dev/Dev/compute_engine_w8a8/src/include
GEMM_RTL = ../../src/rtl
GEMM_INC = ../../src/include
GEMM_TB = ../../src/tb  # Local testbench directory

# Include paths (added ACX paths for primitives)
INCLUDES = +incdir+$(CE_W8A8_INC) +incdir+$(GEMM_INC) +incdir+$(ACE_INSTALL_DIR)/libraries/ +incdir+$(ACX_DEVICE_INSTALL_DIR)/sim +incdir+$(ACX_LIB_S7T)/common

# Testbench sources
TB_SOURCES = ../../src/tb/tb_memory_model.sv tb_engine_top.sv

# RTL sources (from gemm - MS2.0 Multi-Tile architecture!)
RTL_SOURCES = \
	$(GEMM_RTL)/cmd_fifo.sv \
	$(GEMM_RTL)/master_control.sv \
	$(GEMM_RTL)/dispatcher_control.sv \
	$(GEMM_RTL)/dispatcher_bram_dual_read.sv \
	$(GEMM_RTL)/tile_bram_wrapper.sv \
	$(GEMM_RTL)/compute_tile_array.sv \
	$(GEMM_RTL)/compute_engine_modular.sv \
	$(GEMM_RTL)/gfp8_bcv_controller.sv \
	$(GEMM_RTL)/gfp8_nv_dot.sv \
	$(GEMM_RTL)/gfp8_group_dot_mlp.sv \
	$(GEMM_RTL)/gfp8_to_fp16.sv \
	$(GEMM_RTL)/result_bram.sv \
	$(GEMM_RTL)/engine_top.sv

# NAP wrapper (contains t_AXI4 interface)
NAP_WRAPPER = $(GEMM_RTL)/nap_responder_wrapper.sv

.PHONY: all clean run compile debug

all: run

# Create work library
$(WORK):
	@echo "Creating work library..."
	$(VLIB) $(WORK)

# Compile
compile: $(WORK)
	@echo "Compiling packages first..." | tee compile.log
	$(VLOG) -sv $(INCLUDES) -work $(WORK) \
		$(GEMM_INC)/gemm_pkg.sv >> compile.log 2>&1
	@echo "Compiling ACX libraries and primitives..." | tee -a compile.log
	@export LD_LIBRARY_PATH="" && \
	$(VLOG) -sv $(INCLUDES) +define+SIMULATION \
		-timescale "1ps/1ps" \
		-f $(DSM_INCLUDE_FILE) \
		$(DSM_COMPILE_FILE) \
		$(DEVICE_MODELS) \
		$(ACX_LIB_S7T)/common/acx_floating_point.sv \
		$(ACX_LIB_S7T)/common/acx_integer.sv >> compile.log 2>&1
	@echo "Compiling testbench and RTL..." | tee -a compile.log
	@export LD_LIBRARY_PATH="" && \
	$(VLOG) -sv $(INCLUDES) +define+SIMULATION +define+SIM_VERBOSE \
		-err VCP2675 W1 \
		-work $(WORK) \
		$(NAP_WRAPPER) \
		$(RTL_SOURCES) \
		$(TB_SOURCES) >> compile.log 2>&1
	@echo "Compilation complete. Check compile.log for details."

# Run simulation
run: compile
	@echo ""
	@echo "=============================================="
	@echo "  Running GEMM Engine Top (FIFO Interface)  "
	@echo "=============================================="
	@echo ""
	@echo "Simulation output redirected to sim.log"
	$(VSIM) -c -noasdb -do "run -all; quit -force" $(WORK).$(TOP) > sim.log 2>&1
	@echo "Simulation complete. Check sim.log for details."

# Run with GUI for debugging
debug: compile
	@echo ""
	@echo "Running simulation with GUI..."
	@echo ""
	$(VSIM) $(WORK).$(TOP)

# Clean
clean:
	rm -rf $(WORK)
	rm -f transcript
	rm -f *.wlf
	rm -f *.log
	rm -f compile.log
	rm -f sim.log
	rm -f *.vcd
	rm -f *.asdb

help:
	@echo "Makefile for GEMM Engine Top Simulation"
	@echo ""
	@echo "Purpose: Test engine_top.sv with direct FIFO interface"
	@echo "         MS2.0 architecture with command/result FIFOs"
	@echo ""
	@echo "Targets:"
	@echo "  make         - Compile and run simulation"
	@echo "  make run     - Compile and run simulation"
	@echo "  make debug   - Run with GUI for debugging"
	@echo "  make compile - Compile only"
	@echo "  make clean   - Remove generated files"
	@echo ""
	@echo "Key features:"
	@echo "  - Direct FIFO interface (no CSR bridge)"
	@echo "  - Command FIFO: 4096x32-bit"
	@echo "  - Result FIFO: 16384x16-bit (FP16)"
	@echo "  - Complete MS2.0 pipeline integration"

