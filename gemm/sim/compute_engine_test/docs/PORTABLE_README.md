# Portable Compute Engine Modular Simulation

**Status**: ✅ Self-Contained and Portable
**Created**: Fri Oct 24 2025
**Purpose**: Standalone simulation environment for `compute_engine_modular.sv` testing

---

## Overview

This directory contains a **completely self-contained** simulation environment for the modular compute engine. All dependencies are **locally copied** - no external paths required. This directory can be copied to another machine or project and will work without modification (requires only Achronix ACE tools).

---

## Directory Structure

```
compute_engine_test/
├── rtl/                              # Local RTL dependencies
│   ├── compute_engine_modular.sv     # Main compute engine (dual BRAM interface)
│   ├── gfp8_bcv_controller.sv        # BCV loop orchestration
│   ├── gfp8_nv_dot.sv                # Native Vector dot product
│   ├── gfp8_group_dot_mlp.sv         # Group dot product with MLP primitives
│   └── gfp8_to_fp16.sv               # GFP8 to FP16 conversion
│
├── include/                          # Local include files
│   └── gemm_pkg.sv                   # GEMM package (parameters, types)
│
├── hex/                              # Local test data
│   ├── left.hex                      # Left matrix test data
│   ├── right.hex                     # Right matrix test data
│   ├── golden_B1_C1_V1.hex           # Golden reference (1×1×1)
│   ├── golden_B2_C2_V2.hex           # Golden reference (2×2×2)
│   ├── golden_B4_C4_V4.hex           # Golden reference (4×4×4)
│   ├── golden_B2_C2_V64.hex          # Golden reference (2×2×64)
│   ├── golden_B4_C4_V32.hex          # Golden reference (4×4×32)
│   ├── golden_B8_C8_V16.hex          # Golden reference (8×8×16)
│   ├── golden_B1_C128_V1.hex         # Golden reference (1×128×1)
│   ├── golden_B128_C1_V1.hex         # Golden reference (128×1×1)
│   └── golden_B1_C1_V128.hex         # Golden reference (1×1×128)
│
├── docs/                             # Documentation (this file)
│   └── PORTABLE_README.md
│
├── tb_compute_engine_modular.sv      # Testbench (updated for local paths)
├── Makefile                          # Build system (updated for local paths)
├── README.md                         # Original README
├── VALIDATION_REPORT.md              # Validation results
└── library.cfg                       # Simulator library config

```

---

## What Makes This Portable?

### 1. Local RTL Dependencies
All RTL modules are **copied locally** to `./rtl/`:
- `compute_engine_modular.sv` - Main compute engine
- `gfp8_bcv_controller.sv` - BCV loop controller
- `gfp8_nv_dot.sv` - Native Vector dot product
- `gfp8_group_dot_mlp.sv` - Group dot product
- `gfp8_to_fp16.sv` - Format conversion

**Original location**: `../../src/rtl/`
**Portable location**: `./rtl/`

### 2. Local Include Files
Package definitions copied to `./include/`:
- `gemm_pkg.sv` - All GEMM parameters and types

**Original location**: `../../src/include/`
**Portable location**: `./include/`

### 3. Local Test Data
All hex test files copied to `./hex/`:
- `left.hex`, `right.hex` - Matrix test data
- `golden_*.hex` - Golden reference outputs for validation

**Original location**: `/home/dev/Dev/elastix_gemm/hex/`
**Portable location**: `./hex/`

### 4. Updated Makefile Paths
```makefile
# OLD (required external paths)
GEMM_RTL := ../../src/rtl
GEMM_INC := ../../src/include

# NEW (all local)
GEMM_RTL := ./rtl
GEMM_INC := ./include
GEMM_TB := .
```

### 5. Updated Testbench Paths
All `$fopen()` calls updated from absolute paths to relative:
```systemverilog
// OLD
fd_left = $fopen("/home/dev/Dev/elastix_gemm/hex/left.hex", "r");

// NEW
fd_left = $fopen("./hex/left.hex", "r");
```

---

## Requirements

### Software Requirements
- **Achronix ACE Tools**: v10.3.1+ (for device models and libraries)
- **Questa Sim**: ModelSim/QuestaSim for compilation and simulation
- **Environment Variable**: `ACE_INSTALL_DIR` must be set

### What's NOT Portable
The following **external dependencies** are still required (from Achronix ACE installation):
- Device-specific simulation models: `$(ACE_INSTALL_DIR)/system/data/AC7t1500/sim/`
- Speedster7t component library: `$(ACE_INSTALL_DIR)/libraries/speedster7t/`
- Achronix primitives: `acx_integer.sv`, `acx_floating_point.sv`

**Why?**: These are licensed IP from Achronix and cannot be redistributed. You must have ACE tools installed.

---

## Quick Start

### Build and Run
```bash
cd compute_engine_test/
make clean && make run               # Compile + simulate (logs to sim.log)
```

### View Results
```bash
make summary                         # Show test summary
make view-log                        # View full simulation log
```

### Debug Mode
```bash
make debug                           # Run with GUI
```

---

## Build System

### Available Targets
| Target | Description |
|--------|-------------|
| `make` or `make run` | Compile and run simulation (default) |
| `make compile` | Compile only (no simulation) |
| `make run_vsim` | Run simulation after compilation |
| `make debug` | Launch GUI for debugging |
| `make summary` | Display test results summary |
| `make view-log` | View full simulation log |
| `make clean` | Remove all generated files |
| `make help` | Show detailed help message |

### Output Files
- `sim.log` - Complete simulation log (all output)
- `work/` - Compiled simulation library
- `transcript` - ModelSim transcript
- `*.wlf` - Waveform files (debug mode)

---

## Test Coverage

The testbench validates the following configurations:

| Test | Configuration | Golden Reference | Purpose |
|------|--------------|------------------|---------|
| 1 | B=1, C=1, V=1 | Synthetic | Basic functionality |
| 2 | B=1, C=1, V=4 | Synthetic | V-loop accumulation |
| 3 | B=2, C=2, V=2 | Synthetic | Full BCV loops |
| 4 | B=1, C=1, V=1 | `golden_B1_C1_V1.hex` | Real data validation |
| 5 | B=4, C=4, V=4 | `golden_B4_C4_V4.hex` | Complex case validation |

**Pass Criteria**: FP16 output matches golden reference within tolerance (0.01% relative error)

---

## Portability Testing

### To Test Portability on a New Machine:

1. **Copy entire directory** to new location:
   ```bash
   cp -r compute_engine_test /path/to/new/location/
   cd /path/to/new/location/compute_engine_test
   ```

2. **Ensure ACE tools are available**:
   ```bash
   echo $ACE_INSTALL_DIR
   # Should show path to ACE installation (e.g., /opt/achronix/ace/10.3.1)
   ```

3. **Run simulation**:
   ```bash
   make clean && make run
   ```

4. **Verify success**:
   ```bash
   make summary
   # Should show all tests PASS
   ```

---

## Key Features Validated

### Dual BRAM Interface
- Parallel reads from left and right matrix BRAMs
- Independent read addressing per port
- 256-bit data width per port

### BCV Loop Orchestration
- **B-loop**: Output row iteration
- **C-loop**: Output column iteration
- **V-loop**: Accumulation across vector dimension

### Format Conversion
- **Input**: GFP8 (Group Floating Point 8-bit)
- **Output**: FP16 (IEEE 754 half-precision)
- Automatic exponent handling via separate read ports

### Result Validation
- FP16 golden reference comparison
- Configurable tolerance (default: 0.01% relative error)
- Per-element mismatch reporting

---

## Troubleshooting

### Common Issues

**Issue**: Cannot find ACE libraries
**Solution**: Ensure `ACE_INSTALL_DIR` environment variable is set:
```bash
export ACE_INSTALL_DIR=/path/to/achronix/ace/tools
```

**Issue**: Cannot open hex files
**Solution**: Verify `hex/` directory exists and contains required files:
```bash
ls -l hex/
# Should show left.hex, right.hex, golden_*.hex
```

**Issue**: Compilation fails with missing modules
**Solution**: Verify all RTL files are present in `rtl/`:
```bash
ls -l rtl/
# Should show 5 .sv files
```

**Issue**: Test failures
**Solution**: Check `sim.log` for detailed error messages:
```bash
make view-log
# or
grep "ERROR\|FAIL" sim.log
```

---

## Comparison with Original Setup

### Original (Non-Portable)
- RTL from `../../src/rtl/` (2 levels up)
- Include from `../../src/include/` (2 levels up)
- Hex from `/home/dev/Dev/elastix_gemm/hex/` (absolute path)
- **Cannot be moved** without breaking paths

### Portable (This Version)
- RTL from `./rtl/` (local)
- Include from `./include/` (local)
- Hex from `./hex/` (local)
- **Can be copied anywhere** (requires only ACE tools)

---

## File Dependencies Summary

### Copied from Project
| Source | Destination | Purpose |
|--------|-------------|---------|
| `../../src/rtl/*.sv` (5 files) | `./rtl/` | RTL modules |
| `../../src/include/gemm_pkg.sv` | `./include/` | Package definitions |
| `/home/.../hex/*.hex` (11 files) | `./hex/` | Test data and golden refs |

### External Dependencies (ACE Tools)
| Path | Purpose |
|------|---------|
| `$ACE_INSTALL_DIR/system/data/AC7t1500/sim/` | Device models |
| `$ACE_INSTALL_DIR/libraries/speedster7t/` | Component library |
| `$ACE_INSTALL_DIR/libraries/device_models/` | Simulation models |

---

## Maintenance

### Updating Test Data
To add new test configurations:
1. Copy new golden reference hex files to `./hex/`
2. Update testbench to load new golden references
3. Run `make clean && make run` to validate

### Updating RTL
If RTL modules are updated in the main project:
1. Copy updated files from `../../src/rtl/` to `./rtl/`
2. Run `make clean && make run` to recompile

### Syncing with Main Project
To resync this portable version with the main project:
```bash
# Update RTL
cp ../../src/rtl/compute_engine_modular.sv ./rtl/
cp ../../src/rtl/gfp8_*.sv ./rtl/

# Update includes
cp ../../src/include/gemm_pkg.sv ./include/

# Update hex (if changed)
cp /home/dev/Dev/elastix_gemm/hex/*.hex ./hex/
```

---

## License and Attribution

This simulation environment is part of the Elastix GEMM Engine project.

**Original Project**: `/home/dev/Dev/elastix_gemm/gemm_simple/`
**Created**: Fri Oct 24 2025
**Purpose**: Portable compute engine validation

---

## Contact

For questions about this portable simulation environment:
- See main project README: `../../README.md`
- See main project CLAUDE.md: `../../CLAUDE.md`
- Original testbench: `tb_compute_engine_modular.sv`
- Original validation: `VALIDATION_REPORT.md`

---

**Last Updated**: Fri Oct 24 2025
**Portable Version**: 1.0
**Status**: ✅ Validated and Ready for Distribution
