# Makefile for Elastix GEMM Software Tests
# 128-register configuration test suite for AC7t1500 Speedster7t

DEV_ROOT = /home/dev/Dev

CXX = g++
CXXFLAGS = -std=c++14 -O2 -Wall -Wextra -DDRIVER_ACX
INCLUDES = -I$(DEV_ROOT)/acxsdk/include \
           -I$(DEV_ROOT)/acxsdk/drivers/lib \
           -I$(DEV_ROOT)/eus/shell/devices \
           -I$(DEV_ROOT)/eus/shell/devices/acx/vp815/api \
           -I$(DEV_ROOT)/eus/shell/common/api
LIBS = -L$(DEV_ROOT)/acxsdk/lib \
       -L$(DEV_ROOT)/acxsdk/drivers/lib \
       -lacxsdk -lacxdev \
       -Wl,-rpath,$(DEV_ROOT)/acxsdk/lib:$(DEV_ROOT)/acxsdk/drivers/lib

# VP815 API dependency
VP815_API = $(DEV_ROOT)/eus/shell/devices/acx/vp815/api/vp815.cpp


ESSENTIAL_BINS = test_registers test_gddr6 scan_registers test_bram
ALL_BINS = $(ESSENTIAL_BINS) dma_example dma_simple_example test_mem_endpoints test_dma_access test_gemm test_gemm_full test_multi_tile test_readback test_bulk_dma

# Aliases for convenience
BINS = $(ESSENTIAL_BINS)

# Default target - build essential tests
all: $(ALL_BINS)

# Test build rules
test_registers: test_registers.cpp
	$(CXX) $(CXXFLAGS) $(INCLUDES) $< $(VP815_API) $(LIBS) -o $@

test_gddr6: test_gddr6.cpp
	$(CXX) $(CXXFLAGS) $(INCLUDES) $< $(VP815_API) $(LIBS) -o $@

scan_registers: scan_registers.cpp
	$(CXX) $(CXXFLAGS) $(INCLUDES) $< $(VP815_API) $(LIBS) -o $@

test_mem_endpoints: test_mem_endpoints.cpp
	$(CXX) $(CXXFLAGS) $(INCLUDES) $< $(VP815_API) $(LIBS) -o $@

test_bram: test_bram.cpp
	$(CXX) $(CXXFLAGS) $(INCLUDES) $< $(VP815_API) $(LIBS) -o $@

dma_example: DMA_example.cpp
	$(CXX) $(CXXFLAGS) $(INCLUDES) $< $(VP815_API) $(LIBS) -o $@

dma_simple_example: DMA_simple_example.cpp
	$(CXX) $(CXXFLAGS) $(INCLUDES) $< $(VP815_API) $(LIBS) -o $@

test_gemm: test_gemm.cpp
	$(CXX) $(CXXFLAGS) $(INCLUDES) $< $(VP815_API) $(LIBS) -o $@

test_gemm_full: test_gemm_full.cpp
	$(CXX) $(CXXFLAGS) $(INCLUDES) $< $(VP815_API) $(LIBS) -o $@

test_multi_tile: test_multi_tile.cpp
	$(CXX) $(CXXFLAGS) $(INCLUDES) $< $(VP815_API) $(LIBS) -o $@

test_readback: test_readback.cpp
	$(CXX) $(CXXFLAGS) $(INCLUDES) $< $(VP815_API) $(LIBS) -o $@

test_dma_access: test_dma_access.cpp
	$(CXX) $(CXXFLAGS) $(INCLUDES) $< $(VP815_API) $(LIBS) -o $@

test_bulk_dma: test_bulk_dma.cpp
	$(CXX) $(CXXFLAGS) $(INCLUDES) $< $(VP815_API) $(LIBS) -o $@

# Clean targets
clean:
	rm -f $(ESSENTIAL_BINS) $(ALL_BINS)

cleanall: clean
	rm -rf obsolete_debug_tests/*.o obsolete_debug_tests/*.out

clean_all: clean
	rm -f *.o *~

# Test execution targets
test_basic: test_registers
	@echo "=== Basic Register Test ==="
	./test_registers

test_memory: test_gddr6
	@echo "=== GDDR6 Channel Status ==="
	./test_gddr6

test_scan: scan_registers
	@echo "=== Register Address Space Scan ==="
	./scan_registers

# Comprehensive test suite
test_all: test_basic test_memory
	@echo "=== All Core Tests Complete ==="

# Quick validation test (recommended after flash)
validate: test_basic test_memory
	@echo ""
	@echo "=== Validation Complete ==="
	@echo "✅ Device is healthy and GDDR6 channels are accessible"

# Help target
help:
	@echo "Elastix GEMM Software Test Suite (128-register configuration)"
	@echo ""
	@echo "Targets:"
	@echo "  all              - Build all tests"
	@echo "  clean            - Remove all compiled test binaries"
	@echo "  clean_all        - Remove binaries and temporary files"
	@echo ""
	@echo "Test Execution:"
	@echo "  test_basic       - Run basic register functionality test"
	@echo "  test_memory      - Run GDDR6 channel status test"
	@echo "  test_scan        - Scan all register addresses (0x00-0x1FC)"
	@echo "  test_all         - Run all core tests"
	@echo "  validate         - Quick validation (recommended after flash)"
	@echo ""
	@echo "Individual Tests:"
	@echo "  test_registers   - Essential register interface and device health"
	@echo "  test_gddr6       - GDDR6 channel status and performance counters"
	@echo "  scan_registers   - Diagnostic tool for complete register address space"
	@echo "  test_mem_endpoints - Memory address space scanner for BRAM and GDDR6"
	@echo "  test_bram        - BRAM DMA testing with +42 increment processing"
	@echo "  dma_example      - Advanced DMA testing with performance measurement"
	@echo "  dma_simple_example - Basic DMA round-trip validation"
	@echo "  test_ms2_gemm_full - MS2.0 GEMM engine full integration test"
	@echo "  test_bulk_dma      - Bulk DMA address test for FETCH parameter validation"
	@echo ""

.PHONY: all clean clean_all test_basic test_memory test_scan test_all validate help
