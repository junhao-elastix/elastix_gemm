# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This is a comprehensive FPGA-optimized GEMM (General Matrix Multiply) engine development environment featuring multiple specialized matrix multiplication accelerators for Achronix Speedster7t FPGAs. The repository contains four primary sub-projects, each with distinct capabilities and use cases for high-performance matrix operations.

## Critical Development Rules

### Study and memorize the .cursor/rules at the begining of every sesson (MANDATORY)

### **Display verbose and enforce all the following rules (starting from rule 3) at the beginning of every response (MANDATORY)**

<!-- ### **Always invoke agents (MANDATORY)** 
You always want to invoke agents when dealing with specific tasks. You need to invoke **fpga-architect** when working with FPGA hardware designs. You need to invoke **hardware-ml-software-engineer** when working with software system and hardware tests in the host. -->

### **Rigorous Thinking (MANDATORY)**
You need to think step-by-step as a scientist and a engineer carefully and rigorously. Often ask yourself, what if we do this? Then, you need to acticipate the outcomes and analyze. You may also want to think about edge cases or multiple test cases when appropriate. 

### **Find references (CRITICAL)**
When you are stuck, go back to read the relevant documents. **MANDATORY technical documentation:**

#### **Achronix Official Documentation**
- **NoC Architecture**: ~/Dev/elastix_gemm/doc/2D_Network_on_Chip/Speedster7t_2D_Network_on_Chip_User_Guide_UG089.html
- **GDDR6 Integration**: ~/Dev/elastix_gemm/doc/GDDR6_Reference_Design/Speedster7t_GDDR6_Reference_Design_Guide_RD017.html
- **Component Library**: ~/Dev/elastix_gemm/doc/Component_Library/Speedster7t_Component_Library_User_Guide_UG086-1.html  
- **Soft IP Configuration**: ~/Dev/elastix_gemm/doc/Soft_IP/Speedster7t_Soft_IP_User_Guide_UG103_3.html

#### **Reference Projects (READ-ONLY)**
For hardware designs, look for hints and reference designs in ~/Dev/elastix_gemm/llm_vp_demo_pcie_orig, ~/Dev/elastix_gemm/shell_demo, and ~/Dev/elastix_gemm/gddr_ref_degisn. These are reference projects so **do not modify the code there.**

#### **Project Documentation**
You should also read the Markdowns (*.md) in these projects to enhance and refresh your knowledge. Each active project has **REFERENCES.md** for technical documentation integration. 

### **Build Process Rules (MANDATORY)**
```bash
# ALWAYS clean before building
make clean && make run       # Correct
make clean && make all       # Correct
make run                     # WRONG - will cause stale build issues
```

### **Python Environment**
```bash
# ALWAYS activate conda environment for Python work
conda activate elastix

# Package installation priority
conda install -y <package>   # Try conda first
pip install <package>        # Use pip if conda fails
```

### **Documentation Rules (MANDATORY)**
- **Changelog Maintenance**: After EVERY successful compilation, update CHANGELOG.md with timestamp from `date` command
- **Timestamp Requirements**: ALWAYS use `date` command for accurate timestamps in documentation
- **Documentation Verification**: Read existing README.md, CLAUDE.md, and CHANGELOG.md before making changes

### **SystemVerilog Conventions**
- **Use `logic`** instead of `wire` or `reg` (modern SystemVerilog), `always_comb` and `always_ff` for combinational (non-blocking) and registered (blocking) logics.
- **State Machines**: ALWAYS list out explicit control signal assignments in the state machines. State transitions and state controls should be separated into two switch case blocks.
- **Modular Design** ALWAYS keep your code modular and self-contained. You should be able to avoid having monolithic State Machines. The designs should be able to be replaced or upgraded with a similar functionality with similar interfaces.

### **FPGA Recovery Procedures (CRITICAL)**
**VERY IMPORTANT** DO NOT SET TIMEOUT!!! DANDEROUS TO INTERRUPT
```bash

# When device shows 0xffffffff registers (device hang):
/home/dev/Dev/hex_rescan_registers.sh    # Automated recovery (try at least twice before last resort)
# Check PCIe
sudo lspci -d 1b59: -v && sudo lspci -d 12ba: -v
# Last resort:
/home/dev/Dev/flash.sh
sudo reboot
```

### **FPGA Build and Flash (MANDATORY)**
```bash
cd /home/dev/Dev/elastix_gemm/gemm
./build_and_flash.sh

# What the automated script does:
# - cd /home/dev/Dev/elastix_gemm/matmul/build/
# - make clean && make all          # Build RTL
# - /home/dev/Dev/hex.sh            # Program FPGA  
# - source /home/dev/rescan         # Rescan PCIe bus
# - test_registers                  # Verify device health

# Verify Success
# Look for:
# ✅ Device initialized successfully
# ✅ Bitstream ID with correct timestamp
# ✅ All registers readable (not 0xffffffff)
```


### **Monitor the build and flash in foreground (MANDATORY)**
Do not run build in the background and forget to monitor. 
Generating bitstream can take very long. Depending on the complexity of the design, it can take upto hours. You may set a timeout for 1 hour (60 minutes) for now.
You should run it in the foreground and wait for it to return to shell. 
If the returns with the register status, it means the bitstream is built and ready for tests.
Otherwise, the build has failed, and you need to figure out why. You should look for ```@E``` for Errors in the log. Then, you should iterate on yourself.

### **Software test sanity check (MANDATORY)**
After you run each software test, you should run 
```bash
cd ~/Dev/elastix_gemm/matmul/sw_test/test_registers
```
to make sure the FPGA is still in a healthy state. Always check the register offsets. One good indication is to find the Bitstream ID location, which is the timestamp when this bitstream is built.
If the FPGA hangs (showing 0xffffffff), you should engage the recovery protocal immediately to avoid further problems.
If not recovered properly, it can cause the FPGA to enter a much worse state where we need to recover with reboots.
If the FPGA ADM isn't showing 0x3, DMA may not work. At this point, you need to stop developing and get my attention. I will check and potentially reboot.
You should also run bram and ddr basic tests to sanity check the implementation so that you make sure that new features do not break existing ones and the enhancements are incremental.

### **Tests (MANDATORY)**
NEVER hardcode reference results. You should either generate golden output from some reference model or compare the results with a golden output file. 
Before you create new C tests, please always check the existing tests. You can either extend the existing tests or replace the ones that are obsolete. Don't add new tests unless necessary.
Always compile from Makefile. 

## Memory layout
See ./hex/right.hex, ./hex/left.hex. There are tests and documents in ./hex .  

## Specialized Agent Support

This project is actively supported by specialized AI agents that should be proactively engaged:

### fpga-architect Agent
**Expertise**: RTL development, SystemVerilog/Verilog, hardware optimization, timing analysis, interface design (PCIe, DDR, BRAM), debugging hardware issues
**When to engage**:
- Writing or reviewing RTL code for any matrix engine components
- Debugging timing violations or synthesis issues
- Designing new hardware interfaces or memory architectures
- Optimizing FPGA resource utilization
- Analyzing critical paths and performance bottlenecks
- Implementing state machines or control logic

### hardware-ml-software-engineer Agent
**Expertise**: Software-hardware interfaces, ML inference optimization, device drivers, PCIe communication, memory management for accelerators
**When to engage**:
- Developing host software for FPGA communication
- Implementing DMA transfer functions for weight/activation data
- Optimizing matrix multiplication kernels
- Debugging PCIe BAR access or driver issues
- Creating hardware abstraction layers
- Writing test software for hardware validation

**IMPORTANT**: These agents should be proactively invoked for any hardware-related tasks, RTL code reviews, software-hardware interface development, or performance optimization. They provide expert-level guidance specific to FPGA development and ML acceleration.

## Primary Build Commands

### engine_sim - Simulation Project
```bash
cd /home/dev/Dev/elastix_gemm/engine_sim/sim/top_vector_system/
make clean && make run        # Run complete simulation
make clean && make all        # Compile and simulate
```

### matrix_engine_w4gfp8 - GFP Matrix Engine
```bash
# Generate test matrices
cd /home/dev/Dev/elastix_gemm/matrix_engine_w4gfp8/src/tb_py
conda activate elastix
python gfp_gen.py

# Run simulations
cd /home/dev/Dev/elastix_gemm/matrix_engine_w4gfp8/sim/riviera
make clean && make run        # Hardware validation
make clean && make ref_run    # Reference model validation
make debug                    # Run with GUI
```

### matmul - DMA Hardware Design
```bash
cd /home/dev/Dev/elastix_gemm/matmul/build
make clean && make all        # Build bitstream
make clean && make ioring_only # Generate IORing files only

# Software testing
cd /home/dev/Dev/elastix_gemm/matmul/sw_test
./test_registers             # Verify device health
./DMA_example               # Comprehensive DMA test
```

### llm_vp_demo_pcie_orig - LLM Accelerator
```bash
cd /home/dev/Dev/elastix_gemm/llm_vp_demo_pcie_orig/build
make clean && make run        # Full synthesis and P&R
make clean && make synthesis  # Synthesis only
make clean && make pnr        # Place & route only
make clean && make run_mp     # Multiprocessing build (4 jobs)
```

## Architecture Overview

### Hardware Platform
- **Target FPGA**: Achronix AC7t1500 Speedster7t
- **Development Board**: VectorPath 815 (VP815)
- **Interface**: PCIe Gen5x16
- **Memory**: 8x GDDR6 channels + DDR4
- **Network**: NoC (Network-on-Chip) for high-bandwidth memory access

### Common Design Patterns

#### Matrix Processing Architecture
- **GFP Support**: Group Floating Point for efficient storage (matrix_engine_w4gfp8)
- **Dual-Memory**: BRAM for low-latency, GDDR6 for high-bandwidth (matmul)
- **Tensor Cores**: 64 TC arrangement in quadrants (llm_vp_demo_pcie_orig)
- **Pipeline Stages**: Configurable depth for timing closure

#### State Machine Design
- **Two-Process Pattern**: Separate next-state logic from control assignments
- **Explicit Control**: List ALL control signals in EACH state for debugging
- **Handshake Protocols**: Inter-module communication with ready/valid

#### Memory Architecture
- **ACX_BRAM72K**: Asymmetric dual-port for weight storage
- **NAP Placement**: Strategic Network Access Point positioning
- **Dual-Page Buffering**: Ping-pong for continuous processing
- **AXI4 Interfaces**: Burst support up to 16-beat transfers

## Testing Methodology

### Simulation Workflow
1. **Golden Reference**: Python model generates expected results
2. **SystemVerilog Reference**: Validates SV implementation
3. **Hardware Validation**: Verifies actual RTL matches reference

### Hardware Testing
1. **Device Health Check**: Always run `test_registers` first
2. **Incremental Testing**: Start simple, increase complexity
3. **Recovery Procedures**: Use hex.sh + rescan for device hangs
4. **Performance Monitoring**: Check timing reports and resource utilization

## Environment Requirements

### Required Tools
- **Achronix ACE**: v10.3.1+ for synthesis and place-and-route
- **Riviera-PRO**: 2025.04+ for simulation
- **Python**: Conda environment "elastix" with numpy, torch
- **GCC**: For software compilation
- **Linux**: Development and deployment OS

### Environment Variables
```bash
export ACE_INSTALL_DIR=/path/to/achronix/ace/tools
```

## Project-Specific Features

### matrix_engine_w4gfp8 Highlights
- **128×128 Matrix Support**: Full production-ready implementation
- **GFP→BFP Conversion**: Automatic format conversion
- **32 MLP Units**: 4 stacks × 8 MLPs for parallel processing
- **Three-Tier Validation**: Python → SV Reference → Hardware

### matmul Highlights
- **+42 Processing**: Unique increment feature for validation
- **Dual Control**: Independent BRAM and GDDR6 processing
- **Hardware Proven**: Validated on actual VectorPath 815
- **27 User Registers**: Comprehensive control interface

### llm_vp_demo_pcie_orig Highlights
- **64 Tensor Cores**: 4 quadrants × 16 TCs each
- **Multi-Clock Domains**: Register, MCU, MLP clocks
- **Q2Q Ring**: Inter-quadrant communication
- **GDDR6 Integration**: 8 channels with NoC connectivity

## Simulation Validation Results (Verified)

### Validated Functionality
All three modifiable projects have been tested and validated:

| Project | Simulation Status | Key Features Verified | Performance |
|---------|------------------|----------------------|-------------|
| **engine_sim** | ✅ PASS | State machine synchronization, 3-module handshaking | 55 cycles/operation |
| **matrix_engine_w4gfp8** | ✅ PASS | 128×128 matrices, GFP→BFP conversion, FP24 output | 4 results/cycle |
| **matmul** | ✅ PASS (after fixes) | +42 increment processing in BRAM and compute engine | Runtime configurable |

### Important Implementation Details Found

#### matmul Project - +42 Processing
- **Location**: `dma_bram_bridge.sv` (lines 667-689) and `vector_compute_engine.sv` (line 198)
- **Control**: Register bit 0 (BRAM) and bit 1 (GDDR6) enable processing
- **Smart Feature**: Only applies +42 when all byte strobes enabled (32-bit word granularity)
- **LED Status**: D5 (green) = BRAM +42 enabled, D6 (orange) = GDDR6 +42 enabled

#### matrix_engine_w4gfp8 - Matrix Support
- **64×64 matrices**: Baseline configuration working perfectly
- **128×128 matrices**: Full production support with proper BRAM addressing (1024 addresses)
- **Validation**: Python golden reference → SystemVerilog reference → Hardware all match exactly

#### engine_sim - State Machine Flow
- **Verified sequence**: All three FSMs (GC, DC, CE) synchronize correctly
- **Handshaking**: Ready/valid signals properly implemented
- **Performance**: Consistent 55-cycle operation including 30-cycle computation phase

### Simulation Fixes Applied

#### matmul Simulation Issues (Resolved)
1. **Path Problems**: Fixed TCL file generation scripts with correct relative paths
2. **Interface Updates**: Updated testbenches to match evolved RTL module ports
3. **Makefile Corrections**: Fixed Riviera-PRO simulator configurations
4. **Working Location**: `/home/dev/Dev/elastix_gemm/matmul/sim/riviera/gc_vector_global_control/`

## Common Issues and Solutions

### Build Failures
- **Issue**: Protected code blocks or stale artifacts
- **Solution**: Always `make clean` before building

### Simulation Mismatches
- **Issue**: Results don't match reference
- **Solution**: Verify Python environment, regenerate test vectors

### Device Hangs (0xffffffff)
- **Issue**: FPGA drops from PCIe bus
- **Solution**: Run recovery procedure (hex.sh + rescan)

### Timing Violations
- **Issue**: Design doesn't meet timing
- **Solution**: Enable high_frequency mode, adjust pipeline stages

## Development Workflow Best Practices

1. **Always Clean First**: `make clean && make <target>`
2. **Verify Device Health**: Run `test_registers` before hardware tests
3. **Document Changes**: Update CHANGELOG.md with timestamps
4. **Test Incrementally**: Start simple, add complexity gradually
5. **Use Version Control**: Track changes systematically
6. **Monitor Resources**: Check utilization and timing reports

## Quick Reference

### Check Device Status
```bash
./test_registers              # Should show valid register values
sudo lspci -d 1b59: -v       # Should show Achronix device
```

### Common Recovery
```bash
/home/dev/Dev/hex_rescan_registers.sh    # Automated recovery
```

### Build Everything
```bash
make clean && make all        # Universal pattern for all projects
```

## Support and Documentation

Each sub-project contains detailed documentation:
- **README.md**: Project-specific overview and usage
- **CLAUDE.md**: AI assistant guidance (where available)
- **CHANGELOG.md**: Detailed change history with timestamps

For hardware-specific details, refer to:
- Achronix ACE documentation
- VectorPath 815 user guide
- Individual project README files
- @llm_vp_demo_pcie_orig/ is a read-only reference project, you are not supposed to modify the code.
- new rule. absolutely no hardcoded results are allowed. for example, you cannot say things like "this is how things should work" and then put some expected numbers to show the results are matching the reference, but these numbers are not produced but actual dut.
- you should always use the build and flash script.
- remember to display the rules at the start of every response.