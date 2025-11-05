# Makefile for Fetcher Module Testbench
# Tests: fetcher.sv with dispatcher_bram.sv and behavioral GDDR6 model
# Purpose: Golden reference for fetcher optimization

TB = tb_fetcher
TOP = tb_fetcher
WORK = work
LOG_FILE = sim.log

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

# Testbench sources
TB_SOURCES = \
	$(GEMM_TB)/tb_memory_model_realistic.sv \
	tb_fetcher.sv

# RTL sources (minimal set for fetcher + BRAM)
RTL_SOURCES = \
	$(GEMM_RTL)/fetcher_opt.sv \
	$(GEMM_RTL)/dispatcher_bram.sv

# NAP wrapper (contains t_AXI4 interface)
NAP_WRAPPER = $(GEMM_RTL)/nap_responder_wrapper.sv

.PHONY: all clean run compile debug view-log summary help

all: run

# Create work library
$(WORK):
	@echo "Creating work library..." | tee $(LOG_FILE)
	@$(VLIB) $(WORK) >> $(LOG_FILE) 2>&1

# Compile
compile: $(WORK)
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "  Fetcher Testbench Compilation Started: $$(date)" | tee -a $(LOG_FILE)
	@echo "======================================================================" | tee -a $(LOG_FILE)
	@echo "Compiling packages..." | tee -a $(LOG_FILE)
	@$(VLOG) -sv $(INCLUDES) -work $(WORK) \
		$(GEMM_INC)/gemm_pkg.sv >> $(LOG_FILE) 2>&1 || \
		(echo "ERROR: Package compilation failed. See $(LOG_FILE)" && exit 1)
	@echo "Compiling testbench and RTL..." | tee -a $(LOG_FILE)
	@$(VLOG) -sv $(INCLUDES) +define+SIMULATION \
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
	@echo "  FETCHER TESTBENCH SUMMARY"
	@echo "======================================================================="
	@grep -E "\[TEST\]|PASS|FAIL|PERFORMANCE|Cycles:|Throughput:" $(LOG_FILE) | tail -30 || \
		echo "No summary found. Run 'make view-log' to see full output."
	@echo "======================================================================="
	@echo ""

# Clean
clean:
	@echo "Cleaning simulation files..."
	@rm -rf $(WORK) dataset.asdb $(LOG_FILE) transcript vsim.wlf *.vcd
	@echo "Clean complete."

# Help
help:
	@echo "Fetcher Testbench Makefile"
	@echo "=========================="
	@echo ""
	@echo "Targets:"
	@echo "  make          - Clean, compile, and run simulation (default)"
	@echo "  make compile  - Compile only"
	@echo "  make run      - Compile and run simulation"
	@echo "  make debug    - Run simulation with GUI"
	@echo "  make summary  - Display test summary from log"
	@echo "  make view-log - View full simulation log"
	@echo "  make clean    - Remove generated files"
	@echo "  make help     - Show this help message"
	@echo ""
	@echo "Output:"
	@echo "  All compilation and simulation output is logged to $(LOG_FILE)"
	@echo ""
