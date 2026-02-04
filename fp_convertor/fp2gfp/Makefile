# Makefile for GFP16 to GFP8 cocotb tests
# Usage: make <target> SIM=riviera

SIM ?= riviera
TOPLEVEL_LANG ?= verilog
PYTHON ?= python

# Directories
SIM_BUILD := sim_build
RESULTS_DIR := results
RTL_DIR := rtl
COMMON_DIR := ../common

.PHONY: all clean unit integration full help
.PHONY: test-gfp16-extract test-signed-aligner test-gfp8-quantizer test-max-exp test-stream

# Default target
all: unit

# Clean build artifacts
clean:
	rm -rf $(SIM_BUILD) $(RESULTS_DIR) *.xml __pycache__ */__pycache__ tests/*/__pycache__

# Create results directory
$(RESULTS_DIR):
	mkdir -p $(RESULTS_DIR)

# ==============================================================================
# Unit Tests (GFP16 -> GFP8)
# ==============================================================================

unit: test-gfp16-extract test-signed-aligner test-gfp8-quantizer test-max-exp
	@echo "All unit tests completed"

# Test gfp16_extract module
test-gfp16-extract: $(RESULTS_DIR)
	@echo "Running gfp16_extract tests..."
	cd sim/runners && SIM=$(SIM) $(PYTHON) run_gfp16_extract.py

# Test signed_aligner module
test-signed-aligner: $(RESULTS_DIR)
	@echo "Running signed_aligner tests..."
	cd sim/runners && SIM=$(SIM) $(PYTHON) run_signed_aligner.py

# Test gfp8_quantizer module
test-gfp8-quantizer: $(RESULTS_DIR)
	@echo "Running gfp8_quantizer tests..."
	cd sim/runners && SIM=$(SIM) $(PYTHON) run_gfp8_quantizer.py

# Test group_max_exp_finder module
test-max-exp: $(RESULTS_DIR)
	@echo "Running group_max_exp_finder tests..."
	cd sim/runners && SIM=$(SIM) $(PYTHON) run_group_max_exp_finder.py

# ==============================================================================
# Integration Tests
# ==============================================================================

integration: test-stream
	@echo "Integration tests completed"

# Test full gfp_norm_quant pipeline
test-stream: $(RESULTS_DIR)
	@echo "Running gfp_norm_quant integration tests..."
	cd sim/runners && SIM=$(SIM) $(PYTHON) run_gfp_norm_quant.py

# ==============================================================================
# Full Test Suite
# ==============================================================================

full: clean unit integration
	@echo "Full test suite completed"

# ==============================================================================
# Help
# ==============================================================================

help:
	@echo "GFP16 to GFP8 Converter Test Suite"
	@echo "=================================="
	@echo ""
	@echo "Usage: make <target> [SIM=riviera|questa|vcs]"
	@echo ""
	@echo "Targets:"
	@echo "  all          - Run unit tests (default)"
	@echo "  clean        - Remove build artifacts"
	@echo "  unit         - Run all unit tests"
	@echo "  integration  - Run integration tests"
	@echo "  full         - Clean + unit + integration"
	@echo ""
	@echo "Individual unit tests:"
	@echo "  test-gfp16-extract   - Test gfp16_extract module"
	@echo "  test-signed-aligner  - Test signed_aligner module"
	@echo "  test-gfp8-quantizer  - Test gfp8_quantizer module"
	@echo "  test-max-exp         - Test group_max_exp_finder module"
	@echo ""
	@echo "Integration tests:"
	@echo "  test-stream    - Test full gfp_norm_quant pipeline"
	@echo ""
	@echo "Environment:"
	@echo "  SIM=$(SIM)"
