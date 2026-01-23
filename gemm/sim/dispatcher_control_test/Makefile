# Makefile for dispatcher_control_2d Module Testbench
# Tests: dispatcher_control_2d.sv with AXI memory model and BRAM verification
# Purpose: End-to-end FETCH + DISPATCH verification
#
# Targets:
#   make run          - Single channel test (default)
#   make run_all      - All 16 GDDR6 channels test
#   make debug        - Single channel with GUI
#   make debug_all    - All channels with GUI

TB = tb_dispatcher_control
TOP = tb_dispatcher_control
TB_ALL = tb_dispatcher_control_all_channels
TOP_ALL = tb_dispatcher_control_all_channels
WORK = work
LOG_FILE = sim_dispatcher_control.log
LOG_FILE_ALL = sim_dispatcher_control_all_channels.log

# Riviera-PRO commands
VLIB = vlib
VLOG = vlog
VSIM = vsim

# Source directories
GEMM_RTL = ../../src/rtl
GEMM_INC = ../../src/include
GEMM_TB = ../../src/tb

# Include paths
INCLUDES = +incdir+$(GEMM_INC) +incdir+$(ACE_INSTALL_DIR)/libraries/

# =========================================================================
# Debug Macros - Uncomment to enable verbose output per module
# =========================================================================
DEBUG_OPTIONS := +define+DEBUG_DISPATCHER_CTRL   # dispatcher_control_2d.sv (enabled by default)
# DEBUG_OPTIONS += +define+DEBUG_DISPATCHER        # dispatcher_2d.sv
# DEBUG_OPTIONS += +define+DEBUG_FETCHER           # fetcher_2d.sv
# =========================================================================

# Testbench sources - single channel
TB_SOURCES = \
	$(GEMM_TB)/tb_memory_model_realistic.sv \
	tb_dispatcher_control.sv

# Testbench sources - all channels
TB_SOURCES_ALL = \
	$(GEMM_TB)/tb_memory_model_multi_channel.sv \
	tb_dispatcher_control_all_channels.sv

# RTL sources (all modules needed for dispatcher_control_2d)
RTL_SOURCES = \
	$(GEMM_RTL)/fetcher_2d.sv \
	$(GEMM_RTL)/flex_fifo.sv \
	$(GEMM_RTL)/dispatcher_2d.sv \
	$(GEMM_RTL)/dispatcher_control_2d.sv \
	$(GEMM_RTL)/comp_row_bram.sv

# NAP wrapper (contains t_AXI4 interface)
NAP_WRAPPER = $(GEMM_RTL)/nap_responder_wrapper.sv

.PHONY: all clean run compile debug view-log summary help run_all compile_all debug_all summary_all

all: run

# Create work library
$(WORK):
	@echo "Creating work library..." | tee $(LOG_FILE)
	@$(VLIB) $(WORK) >> $(LOG_FILE) 2>&1

# Compile
compile: $(WORK)
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "  Dispatcher Control 2D Testbench Compilation Started: $$(date)" | tee -a $(LOG_FILE)
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "Compiling packages..." | tee -a $(LOG_FILE)
	@$(VLOG) -sv $(INCLUDES) -work $(WORK) \
		$(GEMM_INC)/gemm_pkg.sv >> $(LOG_FILE) 2>&1 || \
		(echo "ERROR: Package compilation failed. See $(LOG_FILE)" && exit 1)
	@echo "Compiling testbench and RTL..." | tee -a $(LOG_FILE)
	@$(VLOG) -sv $(INCLUDES) +define+SIMULATION $(DEBUG_OPTIONS) \
		-err VCP2675 W1 \
		-work $(WORK) \
		$(NAP_WRAPPER) \
		$(RTL_SOURCES) \
		$(TB_SOURCES) >> $(LOG_FILE) 2>&1 || \
		(echo "ERROR: Compilation failed. See $(LOG_FILE)" && exit 1)
	@echo "Compilation complete!" | tee -a $(LOG_FILE)
	@echo "======================================================================" | tee -a $(LOG_FILE)

# Simulate
run: compile
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "  Starting Simulation: $$(date)" | tee -a $(LOG_FILE)
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@$(VSIM) -c -do "run -all; quit" $(TOP) >> $(LOG_FILE) 2>&1
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "  Simulation Complete: $$(date)" | tee -a $(LOG_FILE)
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo ""
	@make summary

# Debug with GUI
debug: compile
	@echo "Starting simulation with GUI..."
	@$(VSIM) $(TOP) &

# View simulation log
view-log:
	@less $(LOG_FILE)

# Extract and display summary
summary:
	@echo ""
	@echo "======================================================================="
	@echo "  DISPATCHER_CONTROL_2D TESTBENCH SUMMARY"
	@echo "======================================================================="
	@grep -E "\[TB\]|PASS|FAIL|TEST|dc_id|ACK" $(LOG_FILE) | tail -50 || \
		echo "No summary found. Run 'make view-log' to see full output."
	@echo "======================================================================="
	@echo ""

# Clean
clean:
	@echo "Cleaning simulation files..."
	@rm -rf $(WORK) dataset.asdb $(LOG_FILE) transcript vsim.wlf *.vcd
	@echo "Clean complete."

# =========================================================================
# ALL CHANNELS TEST TARGETS
# =========================================================================

# Compile all channels test
compile_all: $(WORK)
	@echo "======================================================================" | tee $(LOG_FILE_ALL)
	@echo "  All Channels Testbench Compilation Started: $$(date)" | tee -a $(LOG_FILE_ALL)
	@echo "======================================================================" | tee -a $(LOG_FILE_ALL)
	@echo "Compiling packages..." | tee -a $(LOG_FILE_ALL)
	@$(VLOG) -sv $(INCLUDES) -work $(WORK) \
		$(GEMM_INC)/gemm_pkg.sv >> $(LOG_FILE_ALL) 2>&1 || \
		(echo "ERROR: Package compilation failed. See $(LOG_FILE_ALL)" && exit 1)
	@echo "Compiling testbench and RTL..." | tee -a $(LOG_FILE_ALL)
	@$(VLOG) -sv $(INCLUDES) +define+SIMULATION $(DEBUG_OPTIONS) \
		-err VCP2675 W1 \
		-work $(WORK) \
		$(NAP_WRAPPER) \
		$(RTL_SOURCES) \
		$(TB_SOURCES_ALL) >> $(LOG_FILE_ALL) 2>&1 || \
		(echo "ERROR: Compilation failed. See $(LOG_FILE_ALL)" && exit 1)
	@echo "Compilation complete!" | tee -a $(LOG_FILE_ALL)
	@echo "======================================================================" | tee -a $(LOG_FILE_ALL)

# Run all channels test
run_all: compile_all
	@echo "======================================================================" | tee -a $(LOG_FILE_ALL)
	@echo "  Starting All Channels Simulation: $$(date)" | tee -a $(LOG_FILE_ALL)
	@echo "======================================================================" | tee -a $(LOG_FILE_ALL)
	@$(VSIM) -c -do "run -all; quit" $(TOP_ALL) >> $(LOG_FILE_ALL) 2>&1
	@echo "======================================================================" | tee -a $(LOG_FILE_ALL)
	@echo "  Simulation Complete: $$(date)" | tee -a $(LOG_FILE_ALL)
	@echo "======================================================================" | tee -a $(LOG_FILE_ALL)
	@echo ""
	@make summary_all

# Debug all channels with GUI
debug_all: compile_all
	@echo "Starting all channels simulation with GUI..."
	@$(VSIM) $(TOP_ALL) &

# Summary for all channels
summary_all:
	@echo ""
	@echo "======================================================================="
	@echo "  ALL CHANNELS TESTBENCH SUMMARY"
	@echo "======================================================================="
	@grep -E "Testing Row|Ctrl ID|PASS|FAIL|FINAL|Channels" $(LOG_FILE_ALL) | tail -60 || \
		echo "No summary found. Run 'make view-log-all' to see full output."
	@echo "======================================================================="
	@echo ""

# View all channels log
view-log-all:
	@less $(LOG_FILE_ALL)

# =========================================================================
# HELP
# =========================================================================

# Help
help:
	@echo "Dispatcher Control 2D Testbench Makefile"
	@echo "========================================="
	@echo ""
	@echo "Single Channel Targets:"
	@echo "  make          - Compile and run single channel simulation (default)"
	@echo "  make compile  - Compile single channel test only"
	@echo "  make run      - Compile and run single channel simulation"
	@echo "  make debug    - Run single channel with GUI"
	@echo "  make summary  - Display single channel test summary"
	@echo "  make view-log - View single channel simulation log"
	@echo ""
	@echo "All 16 Channels Targets:"
	@echo "  make run_all      - Compile and run ALL 16 GDDR6 channels test"
	@echo "  make compile_all  - Compile all channels test only"
	@echo "  make debug_all    - Run all channels with GUI"
	@echo "  make summary_all  - Display all channels test summary"
	@echo "  make view-log-all - View all channels simulation log"
	@echo ""
	@echo "Utility Targets:"
	@echo "  make clean    - Remove generated files"
	@echo "  make help     - Show this help message"
	@echo ""
	@echo "Output Files:"
	@echo "  Single channel: $(LOG_FILE)"
	@echo "  All channels:   $(LOG_FILE_ALL)"
	@echo ""
