# Makefile for Achronix Device Shell Wrapper
# Copyright (c) 2024
# Updated 2025-01-08: Fixed hardcoded paths and added auto-detection

# Environment variables with defaults
# Auto-detect project root by walking up from current directory
MAKEFILE_DIR := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
PROJ_ROOT ?= $(abspath $(MAKEFILE_DIR)/../../../../..)
ACXSDK_ROOT ?= /home/dev/Dev/acxsdk
SHELL_ROOT ?= $(PROJ_ROOT)/shell

# Compiler settings
CXX = g++
CXXFLAGS = -std=c++14 -Wall -Wextra -O2 -fPIC
INCLUDES = -I$(ACXSDK_ROOT)/include -I. -I$(SHELL_ROOT)/devices -I$(SHELL_ROOT)/devices/acx/vp815/api -I$(SHELL_ROOT)/common/api
LDFLAGS = -L$(ACXSDK_ROOT)/lib
LIBS = -lacx_sdk

# Default to Achronix driver and static compilation
USE_DRIVER ?= achronix
STATIC ?= 1

# Handle USE_DRIVER parameter (similar to examples/Makefile.inc)
ifeq ($(USE_DRIVER),achronix)
    CXXFLAGS += -DDRIVER_ACX
    INCLUDES += -I$(ACXSDK_ROOT)/drivers/lib
    LDFLAGS += -L$(ACXSDK_ROOT)/drivers/lib
    LIBS = -lacxsdk -lacxdev
else ifeq ($(USE_DRIVER),bittware)
    CXXFLAGS += -DDRIVER_BITTWARE
    # Would need BittWare SDK paths
else ifeq ($(USE_DRIVER),bittware_vfio)
    CXXFLAGS += -DDRIVER_BITTWARE_VFIO
    # Would need BittWare VFIO SDK paths
endif

# Handle STATIC linking option
ifeq ($(STATIC),1)
    LINK_TARGET = $(TARGET_STATIC)
    LINK_FLAGS = $(TARGET_STATIC)
    EXE_SUFFIX = 
else
    LINK_TARGET = $(TARGET_LIB)
    LINK_FLAGS = -L. -lachronix_shell
    EXE_SUFFIX = _shared
endif

# Determine the build environment
UNAME_S := $(shell uname -s)
ifeq ($(UNAME_S),Linux)
    SHARED_EXT = .so
    LDFLAGS += -Wl,-rpath,$(ACXSDK_ROOT)/lib -Wl,-rpath,$(ACXSDK_ROOT)/drivers/lib
endif
ifeq ($(UNAME_S),Darwin)
    SHARED_EXT = .dylib
    LDFLAGS += -Wl,-rpath,$(ACXSDK_ROOT)/lib -Wl,-rpath,$(ACXSDK_ROOT)/drivers/lib
endif

# Targets
TARGET_LIB = libachronix_shell$(SHARED_EXT)
TARGET_STATIC = libachronix_shell.a
DMA_EXECUTABLE = dma_test$(EXE_SUFFIX)
MMIO_EXECUTABLE = mmio_test$(EXE_SUFFIX)
ALL_EXECUTABLE = test_all$(EXE_SUFFIX)
INTERRUPT_EXECUTABLE = test_interrupt_callbacks$(EXE_SUFFIX)
REGISTERS_EXECUTABLE = read_registers$(EXE_SUFFIX)

# Source files
SOURCES = $(SHELL_ROOT)/devices/acx/vp815/api/vp815.cpp
OBJECTS = $(SOURCES:.cpp=.o)
DMA_SOURCES = test_dma.cpp
DMA_OBJECTS = $(DMA_SOURCES:.cpp=.o)
MMIO_SOURCES = test_mmio.cpp
MMIO_OBJECTS = $(MMIO_SOURCES:.cpp=.o)
ALL_SOURCES = test_all.cpp
ALL_OBJECTS = $(ALL_SOURCES:.cpp=.o)
INTERRUPT_SOURCES = test_interrupt_callbacks.cpp
INTERRUPT_OBJECTS = $(INTERRUPT_SOURCES:.cpp=.o)
REGISTERS_SOURCES = read_registers.cpp
REGISTERS_OBJECTS = $(REGISTERS_SOURCES:.cpp=.o)

# Default target - build test executables only (no execution)
all: $(LINK_TARGET) $(DMA_EXECUTABLE) $(MMIO_EXECUTABLE)

# All-in-one test target (covers DMA, MMIO, and MSI-X)
all_test: $(ALL_EXECUTABLE)

# Interrupt callback test target
interrupt_test: $(INTERRUPT_EXECUTABLE)

# Register reader target
read_registers: $(REGISTERS_EXECUTABLE)

# Shared library
$(TARGET_LIB): $(OBJECTS)
	$(CXX) -shared -o $@ $^ $(LDFLAGS) $(LIBS)

# Static library
$(TARGET_STATIC): $(OBJECTS)
	ar rcs $@ $^

# DMA test executable
$(DMA_EXECUTABLE): $(DMA_OBJECTS) $(LINK_TARGET)
	$(CXX) -o $@ $< $(LINK_FLAGS) $(LDFLAGS) $(LIBS)

# MMIO test executable
$(MMIO_EXECUTABLE): $(MMIO_OBJECTS) $(LINK_TARGET)
	$(CXX) -o $@ $< $(LINK_FLAGS) $(LDFLAGS) $(LIBS)

# All-in-one test executable
$(ALL_EXECUTABLE): $(ALL_OBJECTS) $(LINK_TARGET)
	$(CXX) -o $@ $< $(LINK_FLAGS) $(LDFLAGS) $(LIBS)

# Interrupt callback test executable
$(INTERRUPT_EXECUTABLE): $(INTERRUPT_OBJECTS) $(LINK_TARGET)
	$(CXX) -o $@ $< $(LINK_FLAGS) $(LDFLAGS) $(LIBS)

# Register reader executable
$(REGISTERS_EXECUTABLE): $(REGISTERS_OBJECTS) $(LINK_TARGET)
	$(CXX) -o $@ $< $(LINK_FLAGS) $(LDFLAGS) $(LIBS)

# Object files
%.o: %.cpp
	$(CXX) $(CXXFLAGS) $(INCLUDES) -c $< -o $@

# Dependencies
$(SHELL_ROOT)/devices/acx/vp815/api/vp815.o: $(SHELL_ROOT)/devices/acx/vp815/api/vp815.cpp $(SHELL_ROOT)/devices/acx/vp815/api/vp815.hpp
test_dma.o: test_dma.cpp $(SHELL_ROOT)/devices/acx/vp815/api/vp815.hpp
test_mmio.o: test_mmio.cpp $(SHELL_ROOT)/devices/acx/vp815/api/vp815.hpp
test_all.o: test_all.cpp $(SHELL_ROOT)/devices/acx/vp815/api/vp815.hpp
test_interrupt_callbacks.o: test_interrupt_callbacks.cpp $(SHELL_ROOT)/devices/acx/vp815/api/vp815.hpp
read_registers.o: read_registers.cpp $(SHELL_ROOT)/devices/acx/vp815/api/vp815.hpp

# Install targets
install: $(TARGET_LIB) $(TARGET_STATIC)
	@echo "Installing shell wrapper..."
	cp $(TARGET_LIB) $(ACXSDK_ROOT)/lib/
	cp $(TARGET_STATIC) $(ACXSDK_ROOT)/lib/
	cp $(SHELL_ROOT)/devices/acx/vp815/api/vp815.hpp $(ACXSDK_ROOT)/include/

# Clean target
clean:
	rm -f $(OBJECTS) $(DMA_OBJECTS) $(MMIO_OBJECTS) $(ALL_OBJECTS) $(INTERRUPT_OBJECTS) $(REGISTERS_OBJECTS) $(TARGET_LIB) $(TARGET_STATIC) dma_test dma_test_shared mmio_test mmio_test_shared test_all test_interrupt_callbacks read_registers

# Debug target
debug: CXXFLAGS += -g -DDEBUG
debug: all

# Test execution targets removed - build only

# Help target
help:
	@echo "Available targets:"
	@echo "  all            - Build library, DMA test, and MMIO test executables"
	@echo "  all_test       - Build all-in-one test (DMA + MMIO + MSI-X)"
	@echo "  interrupt_test - Build interrupt callback test"
	@echo "  read_registers - Build register reader utility"
	@echo "  clean          - Remove all build artifacts"
	@echo "  debug      - Build with debug symbols and DEBUG flag"
	@echo "  install    - Install libraries and headers to SDK directories"
	@echo "  help       - Show this help message"
	@echo ""
	@echo "Environment variables:"
	@echo "  PROJ_ROOT=<path>     - Project root directory (default: auto-detected)"
	@echo "  ACXSDK_ROOT=<path>   - Achronix SDK root directory (default: /home/dev/Dev/acxsdk)"
	@echo "  SHELL_ROOT=<path>    - Shell root directory (default: \$$PROJ_ROOT/shell)"
	@echo ""
	@echo "Build options:"
	@echo "  USE_DRIVER=<driver>  - Specify driver (default: achronix)"
	@echo "  STATIC=<0|1>         - Static/shared build (default: 1 = static)"
	@echo ""
	@echo "Examples:"
	@echo "  make                                        - Build all (static by default)"
	@echo "  make STATIC=0                               - Build with shared library"
	@echo "  PROJ_ROOT=/custom/path make                 - Build with custom project root"
	@echo "  ACXSDK_ROOT=/custom/path make               - Build with custom SDK path"
	@echo "  ./dma_test                                  - Run DMA test manually"
	@echo "  ./mmio_test                                 - Run MMIO test manually"
	@echo "  ./test_all                                  - Run all-in-one test manually"
	@echo "  ./test_interrupt_callbacks                  - Run interrupt callback test manually"
	@echo "  ./read_registers                            - Run register reader utility manually"
	@echo ""
	@echo "Individual targets:"
	@echo "  $(TARGET_LIB)   - Build shared library"
	@echo "  $(TARGET_STATIC)      - Build static library"
	@echo "  $(DMA_EXECUTABLE)           - Build DMA test executable"
	@echo "  $(MMIO_EXECUTABLE)          - Build MMIO test executable"
	@echo "  $(ALL_EXECUTABLE)           - Build all-in-one test executable"
	@echo "  $(INTERRUPT_EXECUTABLE)     - Build interrupt callback test executable"
	@echo "  $(REGISTERS_EXECUTABLE)     - Build register reader utility executable"

.PHONY: all clean debug install help 