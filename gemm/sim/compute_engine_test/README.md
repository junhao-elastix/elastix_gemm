# Compute Engine Modular Testbench

**Purpose**: Unit test for `compute_engine_modular_opt.sv` module  
**Status**: ✅ **Functional** - Compiles successfully  
**DUT**: `compute_engine_modular_opt.sv` (optimized compute engine)

## Quick Start

```bash
cd /home/dev/Dev/elastix_gemm/gemm/sim/compute_engine_test
make clean && make run     # Run simulation
make summary               # View test results summary
make view-log              # View full simulation log
make debug                 # Run with GUI for waveform analysis
```

## Overview

This testbench validates the **compute engine module** (`compute_engine_modular_opt.sv`) in isolation. The compute engine performs GFP8 matrix multiplication with BCV loop orchestration and outputs FP16 results.

### Key Features

- **Optimized Architecture**: Uses `compute_engine_modular_opt.sv` with direct path design
- **Dual BRAM Interface**: Parallel left/right matrix reads
- **BCV Controller**: Optimized 4-state controller (`gfp8_bcv_controller_opt.sv`)
- **Ultra-Optimized NV Dot**: Uses `gfp8_nv_dot_ultra_opt.sv` (2-cycle dot product)
- **FP16 Output**: GFP8 to FP16 conversion with golden reference validation

## Architecture

### Design Under Test (DUT)
- **Module**: `gemm/src/rtl/compute_engine_modular_opt.sv`
- **BCV Controller**: `gfp8_bcv_controller_opt.sv`
- **NV Dot**: `gfp8_nv_dot_ultra_opt.sv`
- **Group Dot**: `gfp8_group_dot_mlp.sv`
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
- **DUT**: `../../src/rtl/compute_engine_modular_opt.sv`
- **BCV Controller**: `../../src/rtl/gfp8_bcv_controller_opt.sv`
- **NV Dot**: `../../src/rtl/gfp8_nv_dot_ultra_opt.sv`
- **Group Dot**: `../../src/rtl/gfp8_group_dot_mlp.sv`
- **Format Conversion**: `../../src/rtl/gfp8_to_fp16.sv`
- **BRAM**: `../../src/rtl/tile_bram.sv`
- **Package**: `../../src/include/gemm_pkg.sv`

### Test Data
- **Golden References**: `/home/dev/Dev/elastix_gemm/hex/golden_*.hex`

## Test Configurations

The testbench validates multiple B×C×V configurations:
- B1_C1_V1, B2_C2_V2, B4_C4_V4
- B2_C2_V64, B4_C4_V32, B8_C8_V16
- B1_C128_V1, B128_C1_V1, B1_C1_V128

## Success Criteria

✅ **PASS Conditions**:
1. All test configurations complete without errors
2. FP16 results match golden references (within tolerance)
3. No timeout errors
4. Proper BCV loop execution

## Performance

The optimized compute engine (`compute_engine_modular_opt.sv`) features:
- **Direct path architecture** (no intermediate buffers)
- **2-cycle NV dot product** (reduced from 3 cycles)
- **33% latency reduction** over baseline
- **Optimized BCV controller** (4-state FSM)

## References

- **Compute Engine RTL**: `/home/dev/Dev/elastix_gemm/gemm/src/rtl/compute_engine_modular_opt.sv`
- **System Test**: `/home/dev/Dev/elastix_gemm/gemm/sim/vector_system_test/`
- **Historical Files**: `archive_nov06_obsolete/` (archived Nov 6, 2025)

---

**Last Updated**: Thu Nov 6 2025  
**Status**: ✅ Functional - Compiles successfully

