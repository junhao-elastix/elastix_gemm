# ==================================================================
# Dispatcher Testbench Makefile
# ==================================================================

# Simulator
SIM = riviera

# Directories
RTL_DIR = ../../src/rtl
PKG_DIR = ../../src/include
WORK_DIR = work

# Source files
RTL_SOURCES = \
	$(PKG_DIR)/gemm_pkg.sv \
	$(RTL_DIR)/dispatcher.sv

TB_SOURCE = tb_dispatcher.sv

# Simulation options
VLOG_OPTS = -sv +define+SIMULATION +incdir+$(PKG_DIR)
VSIM_OPTS = -c -do "run -all; quit"
VSIM_GUI_OPTS = -do "run -all"

# Default target
.PHONY: all
all: clean compile run

# Create work library
$(WORK_DIR)/work.lib:
	@echo "Creating work library..."
	vlib $(WORK_DIR)
	vmap work $(WORK_DIR)/work.lib

# Compile
.PHONY: compile
compile: $(WORK_DIR)/work.lib
	@echo "======================================================================"
	@echo "  Compilation Started: $$(date)"
	@echo "======================================================================"
	@echo "Compiling packages..."
	vlog -work work $(VLOG_OPTS) $(PKG_DIR)/gemm_pkg.sv
	@echo "Compiling RTL modules..."
	vlog -work work $(VLOG_OPTS) $(RTL_SOURCES)
	@echo "Compiling testbench..."
	vlog -work work $(VLOG_OPTS) $(TB_SOURCE)
	@echo "Compilation completed successfully"

# Run simulation
.PHONY: run
run:
	@echo ""
	@echo "======================================================================"
	@echo "  Simulation Started: $$(date)"
	@echo "======================================================================"
	@echo "Running Dispatcher simulation..."
	@echo ""
	vsim $(VSIM_OPTS) work.tb_dispatcher | tee sim.log
	@echo ""
	@echo "======================================================================"
	@echo "  Simulation Completed: $$(date)"
	@echo "======================================================================"

# Run with GUI
.PHONY: debug
debug: compile
	@echo "Starting simulation with GUI..."
	vsim $(VSIM_GUI_OPTS) work.tb_dispatcher &

# View log
.PHONY: view-log
view-log:
	@less sim.log

# Clean
.PHONY: clean
clean:
	@echo "Cleaning simulation files..."
	@rm -rf $(WORK_DIR)
	@rm -f sim.log
	@rm -f transcript
	@rm -f vsim.wlf
	@rm -f *.vcd
	@rm -f *.txt
	@echo "Clean complete"

# Help
.PHONY: help
help:
	@echo "Dispatcher Testbench Makefile"
	@echo ""
	@echo "Targets:"
	@echo "  make         - Clean, compile, and run simulation (default)"
	@echo "  make compile - Compile RTL and testbench"
	@echo "  make run     - Run simulation in batch mode"
	@echo "  make debug   - Run simulation with GUI"
	@echo "  make clean   - Remove generated files"
	@echo "  make help    - Show this help message"
