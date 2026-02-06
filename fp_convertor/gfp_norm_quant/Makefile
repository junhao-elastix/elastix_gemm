# Makefile for GFP11e5 to GFP8e5 normalize and quantize module
# Usage: make test SIM=riviera

SIM ?= riviera
PYTHON ?= python

# Directories
COCOTB_DIR := sim/cocotb
RESULTS_DIR := results

.PHONY: test clean help

# Default target
all: test

# Run cocotb tests
test:
	@echo "Running gfp_norm_quant tests..."
	cd $(COCOTB_DIR) && SIM=$(SIM) $(PYTHON) run_gfp_norm_quant.py

# Clean build artifacts
clean:
	rm -rf $(COCOTB_DIR)/sim_build $(RESULTS_DIR) __pycache__ */__pycache__

# Help
help:
	@echo "GFP11e5 to GFP8e5 Normalize and Quantize Module"
	@echo "============================================"
	@echo ""
	@echo "Usage: make <target> [SIM=riviera|questa|vcs]"
	@echo ""
	@echo "Targets:"
	@echo "  test   - Run cocotb tests (default)"
	@echo "  clean  - Remove build artifacts"
	@echo "  help   - Show this help"
	@echo ""
	@echo "Environment: SIM=$(SIM)"
