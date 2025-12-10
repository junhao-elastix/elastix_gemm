# Compute Engine Modular Testbench

**Purpose**: Unit test for `compute_engine_modular.sv` module  
**Status**: ✅ **Functional** - All 10 tests passing  
**DUT**: `compute_engine_modular.sv` (modular compute engine with tile BRAM)

## Quick Start

```bash
cd /home/dev/Dev/elastix_gemm/gemm/sim/compute_engine_test
make clean && make run     # Run simulation
make summary               # View test results summary
make view-log              # View full simulation log
make debug                 # Run with GUI for waveform analysis
```

## Overview

This testbench validates the **compute engine module** (`compute_engine_modular.sv`) in isolation. The compute engine performs GFP8 matrix multiplication with BCV loop orchestration and outputs FP16 results.

### Key Features

- **Modular Architecture**: Uses `compute_engine_modular.sv` with integrated tile_bram
- **Dual BRAM Interface**: Parallel left/right matrix reads via tile_bram
- **BCV Controller**: `gfp8_bcv_controller.sv` for Batch-Column-Vector loop orchestration
- **NV Dot Product**: `gfp8_nv_dot.sv` for Native Vector dot product computation
- **FP16 Output**: GFP8 to FP16 conversion with golden reference validation

## Architecture

### Design Under Test (DUT)
- **Module**: `gemm/src/rtl/compute_engine_modular.sv`
- **BCV Controller**: `gfp8_bcv_controller.sv`
- **NV Dot**: `gfp8_nv_dot.sv`
- **Format Conversion**: `gfp8_to_fp16.sv`
- **BRAM**: `tile_bram.sv` (dual-port for left/right matrices)

### Test Sequence

1. **DISPATCH Simulation**: Testbench writes test data to tile_bram (simulating DISPATCH operation)
2. **TILE Execution**: Compute engine processes matrices with BCV loop
3. **Result Validation**: FP16 results compared against golden references

## Makefile Targets

| Target | Description |
|--------|-------------|
| `make` or `make run` | Clean, compile, and run simulation |
| `make compile` | Compile only (no simulation) |
| `make debug` | Run simulation with GUI |
| `make summary` | Display test results summary |
| `make view-log` | View full simulation log |
| `make clean` | Remove generated files |
| `make help` | Show help message |

## Files

### Active Files
- **tb_compute_engine_modular_opt.sv** - Main testbench module
- **Makefile** - Build and simulation control
- **README.md** - This documentation
- **library.cfg** - Riviera-PRO library configuration

### Source Dependencies
- **DUT**: `../../src/rtl/compute_engine_modular.sv`
- **BCV Controller**: `../../src/rtl/gfp8_bcv_controller.sv`
- **NV Dot**: `../../src/rtl/gfp8_nv_dot.sv`
- **Format Conversion**: `../../src/rtl/gfp8_to_fp16.sv`
- **BRAM**: `../../src/rtl/tile_bram.sv`
- **Package**: `../../src/include/gemm_pkg.sv`

### Test Data
- **Golden References**: `/home/dev/Dev/elastix_gemm/hex/golden_*.hex`

## Test Configurations

The testbench validates 10 B×C×V configurations (matching test_gemm.cpp):
- B1_C1_V1, B2_C2_V2, B4_C4_V4
- B2_C2_V64, B4_C4_V32, B8_C8_V16, B16_C16_V8
- B1_C128_V1, B128_C1_V1, B1_C1_V128

## Success Criteria

✅ **PASS Conditions**:
1. All 10 test configurations complete without errors
2. FP16 results match golden references (within ±5 LSB tolerance)
3. No timeout errors
4. Proper BCV loop execution

## References

- **Compute Engine RTL**: `/home/dev/Dev/elastix_gemm/gemm/src/rtl/compute_engine_modular.sv`
- **System Test**: `/home/dev/Dev/elastix_gemm/gemm/sim/vector_system_test/`
- **Historical Files**: `archive_nov06_obsolete/` (archived Nov 6, 2025)

---

**Last Updated**: Tue Dec 2 2025  
**Status**: ✅ Functional - All 10 tests passing
