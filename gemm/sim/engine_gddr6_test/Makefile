# ---------------------------------------------------------------------
# GEMM Engine GDDR6 Simulation Makefile
# Based on gddr_ref_design/sim/riviera/Makefile
# ---------------------------------------------------------------------

# Simulation flow - using BFM mode for GDDR6
FLOW := FULLCHIP_BFM

# Top level module
TOP_LEVEL_MODULE := tb_engine_gddr6

# Target device
DEVICE := AC7t1500

# Define the WLF waveform filename
WLF_FILENAME := sim_output.wlf

# Directory for log files
LOG_DIR := ./logs

# Check result
CHECK_SIM_RESULT := grep "STATUS: \[PASS\]" $(LOG_DIR)/$(FLOW)_simulation.log || exit 1;

# -------------------------------------------------------------------------
# Environment and paths
# -------------------------------------------------------------------------

# Convert device name to base filename
BASE_NAME := $(shell echo $(DEVICE) | tr A-Z a-z | grep -E -o "[a-z]*[0-9]+t[0-9]+")

# Device Simulation Model (DSM) files
export ACX_DEVICE_INSTALL_DIR  = $(ACE_INSTALL_DIR)/system/data/$(DEVICE)
DSM_INCLUDE_FILE              := $(ACX_DEVICE_INSTALL_DIR)/sim/$(BASE_NAME)_dsm_incdirs.f
DSM_COMPILE_FILE              := $(ACX_DEVICE_INSTALL_DIR)/sim/$(BASE_NAME)_dsm_filelist.v
ACX_LIB_S7T                   := $(ACE_INSTALL_DIR)/libraries/speedster7t
DEVICE_MODELS                 := $(ACE_INSTALL_DIR)/libraries/device_models/AC7t1500_simmodels.sv

# GDDR6 reference design paths (for includes and models)
GDDR_REF_DIR := ../../../gddr_ref_design
GDDR_TB_DIR  := $(GDDR_REF_DIR)/src/tb
GDDR_INC_DIR := $(GDDR_REF_DIR)/src/include
GDDR_MODEL_DIR := $(GDDR_TB_DIR)/gddr_model

# Our RTL paths
GEMM_RTL_DIR := ../../src/rtl
GEMM_INC_DIR := ../../src/include

# -------------------------------------------------------------------------
# Riviera compilation options
# -------------------------------------------------------------------------

RIVIERA_OPTIONS := -sv -timescale "1ps/1ps" -work work -dbg \
                   +incdir+$(ACX_DEVICE_INSTALL_DIR)/sim \
                   +incdir+$(ACE_INSTALL_DIR)/libraries/ \
                   +incdir+$(GDDR_INC_DIR) \
                   +incdir+$(GDDR_TB_DIR) \
                   +incdir+$(GEMM_INC_DIR) \
                   +define+ACX_DSM_INTERFACES_TO_MONITOR_MODE \
                   +define+ACX_DEVICE_AC7t1500 \
                   +define+ACX_GDDR6_1_FULL \
                   +define+ACX_GDDR6_1_REF_CLK_SEL=2 \
                   +define+ACX_GDDR6_1_NOC_CLK_SEL=2 \
                   +define+ACX_GDDR6_1_DC_CLK_SEL=0 \
                   +define+ACX_GDDR6_1_RST_SEL=17 \
                   +define+GDDR6_DATA_RATE_12 \
                   -err VCP7803 W1 \
                   -err VCP2675 W1 \
                   $(ACE_INSTALL_DIR)/libraries/device_models/$(DEVICE)_simmodels.sv

RIVIERA_FILES_FULLCHIP_BFM := -f $(DSM_INCLUDE_FILE) $(DSM_COMPILE_FILE)

VSIM_OPTIONS          := -L work
NOWARN_OPTIONS        := +nowarnTFMPC
VSIM_OPTIONS_DEBUG    := -voptargs="+acc"
VOPT_OPTIONS          := "+acc"
VOPT_OPTIONS_FULLCHIP := "+noacc+$(BASE_NAME)/fullchip_top."
TOP_LEVEL_MODULE_OPT  := "$(TOP_LEVEL_MODULE)_opt"

VOPT_OPTIONS += $(VOPT_OPTIONS_FULLCHIP)
WAVE_FILE    := wave.do

# -------------------------------------------------------------------------
# File lists
# -------------------------------------------------------------------------

# GDDR6 model and NAP infrastructure
# NOTE: GDDR6 models are included via DSM, don't compile separately
# GDDR_FILES := \
#     $(GDDR_MODEL_DIR)/micron_gddr6_chn.v \
#     $(GDDR_MODEL_DIR)/micron_gddr6_chk.v \
#     $(GDDR_MODEL_DIR)/micron_gddr6_tim.v \
#     $(GDDR_MODEL_DIR)/micron_gddr6_bfm.v
GDDR_FILES :=

# Memory model for testbench
TB_MEM_MODEL := $(GEMM_RTL_DIR)/../tb/tb_memory_model.sv

# GEMM Engine RTL (in dependency order)
GEMM_FILES := \
    $(GEMM_RTL_DIR)/cmd_fifo.sv \
    $(GEMM_RTL_DIR)/csr_to_fifo_bridge.sv \
    $(GEMM_RTL_DIR)/result_bram.sv \
    $(GEMM_RTL_DIR)/result_fifo_to_simple_bram.sv \
    $(GEMM_RTL_DIR)/master_control.sv \
    $(GEMM_RTL_DIR)/dispatcher_control.sv \
    $(GEMM_RTL_DIR)/dispatcher_bram_dual_read.sv \
    $(GEMM_RTL_DIR)/gfp8_nv_dot.sv \
    $(GEMM_RTL_DIR)/gfp8_group_dot_mlp.sv \
    $(GEMM_RTL_DIR)/gfp8_to_fp16.sv \
    $(GEMM_RTL_DIR)/gfp8_bcv_controller.sv \
    $(GEMM_RTL_DIR)/compute_engine_modular.sv \
    $(GEMM_RTL_DIR)/engine_top.sv

# Testbench
TB_FILES := tb_engine_gddr6.sv

# -------------------------------------------------------------------------
# Makefile targets
# -------------------------------------------------------------------------

all : run

run : run_compile run_vsim

debug : run_compile run_vsim_debug

run_compile : make_log_dir check_env
	vlib work
	@echo "Compiling GEMM package..."
	vlog -sv -timescale "1ps/1ps" -work work +incdir+$(GEMM_INC_DIR) \
	     +define+SIMULATION $(GEMM_INC_DIR)/gemm_pkg.sv
	@echo "Compiling ACX libraries and primitives..."
	@export LD_LIBRARY_PATH="" && \
	vlog -sv -timescale "1ps/1ps" -work work \
	     +incdir+$(ACX_DEVICE_INSTALL_DIR)/sim \
	     +incdir+$(ACE_INSTALL_DIR)/libraries/ \
	     +incdir+$(ACX_LIB_S7T)/common \
	     +define+SIMULATION \
	     -f $(DSM_INCLUDE_FILE) \
	     $(DSM_COMPILE_FILE) \
	     $(DEVICE_MODELS) \
	     $(ACX_LIB_S7T)/common/acx_floating_point.sv \
	     $(ACX_LIB_S7T)/common/acx_integer.sv
	@echo "Compiling GEMM RTL and testbench..."
	@export LD_LIBRARY_PATH="" && \
	vlog -sv -timescale "1ps/1ps" -work work -dbg \
	     +incdir+$(GEMM_INC_DIR) \
	     +incdir+$(GDDR_INC_DIR) \
	     +define+SIMULATION \
	     +define+SIM_VERBOSE \
	     -err VCP2675 W1 \
	     $(TB_MEM_MODEL) \
	     $(GEMM_FILES) \
	     $(TB_FILES)

run_vsim : make_log_dir
	vsim -c -do "run -all; exit" $(VSIM_OPTIONS) -l $(LOG_DIR)/$(FLOW)_simulation.log work.$(TOP_LEVEL_MODULE)
	$(CHECK_SIM_RESULT)

run_vsim_debug : make_log_dir run_compile
	vsim -gui $(VSIM_OPTIONS) $(VSIM_OPTIONS_DEBUG) $(NOWARN_OPTIONS) -do $(WAVE_FILE) \
         -l $(LOG_DIR)/$(FLOW)_simulation.log work.$(TOP_LEVEL_MODULE)

open_wave:
	vsim -gui -view $(WLF_FILENAME) -do $(WAVE_FILE) &

make_log_dir:
	mkdir -p $(LOG_DIR)

.PHONY : check_env
check_env :
ifndef ACE_INSTALL_DIR
	$(error ACE_INSTALL_DIR is undefined in the environment)
endif
ifdef LD_LIBRARY_PATH
	$(error LD_LIBRARY_PATH is defined in the environment.  It must be unset to enable Riviera to run)
endif

clean:
	rm -rf $(LOG_DIR)
	rm -rf ./work/
	rm -rf ./library.cfg
	rm -rf ./dataset.asdb
	rm -rf ./$(WLF_FILENAME)
	rm -rf ./transcript

help:
	@echo "GEMM Engine GDDR6 Simulation Makefile"
	@echo ""
	@echo "Purpose: Full system simulation with Micron GDDR6 BFM"
	@echo ""
	@echo "Targets:"
	@echo "  make         - Compile and run simulation"
	@echo "  make run     - Compile and run simulation"
	@echo "  make debug   - Run with GUI for debugging"
	@echo "  make clean   - Remove generated files"
	@echo ""
	@echo "Test Configuration:"
	@echo "  B=2, C=2, V=2"
	@echo "  Test data: /home/dev/Dev/elastix_gemm/hex/left.hex, right.hex"
	@echo "  Golden: golden_B2_C2_V2.hex"
	@echo ""
	@echo "Requirements:"
	@echo "  - ACE_INSTALL_DIR must be set"
	@echo "  - LD_LIBRARY_PATH must NOT be set"
	@echo "  - Micron GDDR6 models must be available"

