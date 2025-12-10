# Compute Engine Testbench

**Purpose**: Unit tests for compute engine modules
**Status**: ✅ **Functional** - All tests passing
**DUTs**: `compute_engine_modular.sv` and `compute_engine_mlp.sv`

## Quick Start

```bash
cd /home/dev/Dev/elastix_gemm/gemm/sim/compute_engine_test

# Original modular compute engine (10 tests)
make clean && make run

# MLP-based compute engine (C=16 only)
make clean && make run_mlp

# Cocotb tests for MLP (12 comprehensive tests)
cd cocotb && uv run python test_compute_engine_mlp.py
```

## Overview

This testbench validates compute engine modules in isolation. Two compute engine implementations are supported:

| Engine | Module | Columns | Output | Precision |
|--------|--------|---------|--------|-----------|
| **Modular** | `compute_engine_modular.sv` | Variable (1-128) | 16-bit FP16 | GFP8 → FP16 |
| **MLP** | `compute_engine_mlp.sv` | 16-128 (×16) | 256-bit (16×FP16) | FP24 → FP16 |

## Makefile Targets

| Target | Description |
|--------|-------------|
| `make run` | Run modular compute engine tests (10 configs) |
| `make run_mlp` | Run MLP compute engine test (B16_C16_V8) |
| `make compile` | Compile modular engine only |
| `make compile_mlp` | Compile MLP engine only |
| `make debug` | Run modular with GUI |
| `make debug_mlp` | Run MLP with GUI |
| `make summary` | Display test results summary |
| `make view-log` | View full simulation log |
| `make clean` | Remove generated files |

## Directory Structure

```
compute_engine_test/
├── tb_compute_engine_modular_opt.sv  # Dual-DUT testbench (ifdef USE_MLP)
├── Makefile                          # Build targets for both engines
├── README.md                         # This file
├── library.cfg                       # Riviera-PRO library config
└── cocotb/                           # Python-based cocotb tests
    ├── test_compute_engine_mlp.py    # Cocotb test runner
    ├── compute_engine_mlp_tests.py   # 12 test functions
    ├── sim_utils/                    # Build utilities
    └── pyproject.toml                # Python dependencies
```

## RTL Dependencies

### Modular Compute Engine
- `gemm/src/rtl/compute_engine_modular.sv`
- `gemm/src/rtl/gfp8_bcv_controller.sv`
- `gemm/src/rtl/gfp8_nv_dot.sv`
- `gemm/src/rtl/gfp8_to_fp16.sv`
- `gemm/src/rtl/tile_bram.sv`
- `gemm/src/include/gemm_pkg.sv`

### MLP Compute Engine
- `gemm/src/rtl/compute_engine_mlp.sv`
- `gemm/src/rtl/mlp_bram_col_ctrl.sv`
- `gemm/src/rtl/mlp_bram_col.sv`, `mlp_bram.sv`
- `gemm/src/rtl/mlp_dot16_int8.sv`, `mlp_dot16_bfp8.sv`
- `gemm/src/rtl/fp24_add.sv`, `fp24_to_fp16.sv`
- `gemm/src/rtl/row_bram.sv`, `weight_bram.sv`

## Test Configurations

### Modular Engine (10 tests)
All B×C×V configurations matching `test_gemm.cpp`:
- B1_C1_V1, B2_C2_V2, B4_C4_V4
- B2_C2_V64, B4_C4_V32, B8_C8_V16, B16_C16_V8
- B1_C128_V1, B128_C1_V1, B1_C1_V128

### MLP Engine (SystemVerilog: 1 test, Cocotb: 18 tests)
- **SystemVerilog**: B16_C16_V8 only
- **Cocotb**: 18 tests including basic ops, batch dimension, multi-NV, golden hex validation, and C > 16 column group tests

**C > 16 Support (Column Groups)**:
- MLP supports C = 16, 32, 64, or 128 (must be divisible by 16)
- For C > 16, columns are processed in groups of 16 sequentially
- Example: C=32 → 2 groups, C=128 → 8 groups

## Test Data

Golden references located at `/home/dev/Dev/elastix_gemm/hex/`:
- `left.hex`, `right.hex` - Input matrices
- `golden_B*_C*_V*.hex` - Expected FP16 results

## Tolerance Levels

| Engine | Absolute | Relative | Notes |
|--------|----------|----------|-------|
| Modular | ±5 LSB | - | Strict, GFP8→FP16 direct |
| MLP | ±50 LSB | 5% | FP24 intermediate, ~1.3% typical error |

## Cocotb Tests

The `cocotb/` directory contains comprehensive Python-based tests:

```bash
cd cocotb
uv run python test_compute_engine_mlp.py
```

**18 Test Functions**:
1. `test_first_8_elements` - Basic 8-element dot product
2. `test_first_32_elements` - Full 32-element (1 group) dot product
3. `test_identity_matrix` - Identity pattern validation
4. `test_all_ones` - All-ones accumulation
5. `test_multi_nv` - Multiple Native Vectors (V > 1)
6. `test_different_columns` - Column-dependent patterns
7. `test_gfp_random_floats` - Random GFP8 data (requires torch)
8. `test_gfp_large_values` - Large value handling (requires torch)
9. `test_batch_dimension` - Batch processing (B > 1)
10. `test_batch_with_multi_nv` - Combined B > 1 and V > 1
11. `test_full_bcv` - Full B=16, C=16, V=8 (requires torch)
12. `test_golden_hex` - Golden reference file validation
13. `test_c16_b4_v8` - B=4, C=16, V=8 (1 column group baseline)
14. `test_c16_b8_v4` - B=8, C=16, V=4 (1 column group baseline)
15. `test_c32_b4_v4` - B=4, C=32, V=4 (2 column groups)
16. `test_c32_b8_v2` - B=8, C=32, V=2 (2 column groups)
17. `test_c64_b8_v2` - B=8, C=64, V=2 (4 column groups)
18. `test_c128_b2_v1` - B=2, C=128, V=1 (8 column groups)

## Architecture Notes

### Dual-DUT Testbench
The testbench `tb_compute_engine_modular_opt.sv` supports both engines via compile-time switch:
- Default: `compute_engine_modular`
- With `+define+USE_MLP`: `compute_engine_mlp`

Key differences handled:
- **Exponent conversion**: MLP needs +118 offset (5-bit bias=15 → 8-bit bias=133)
- **Result width**: Modular=16-bit, MLP=256-bit (serialized to 16-bit)
- **Port naming**: `i_left_exp_*` (modular) vs `i_exp_left_*` (MLP)

### Test Sequence
1. Load test data to BRAM (simulating DISPATCH)
2. Send TILE command with B, C, V parameters
3. Wait for tile_done
4. Collect and validate FP16 results against golden reference

## References

- **Modular RTL**: `gemm/src/rtl/compute_engine_modular.sv`
- **MLP RTL**: `gemm/src/rtl/compute_engine_mlp.sv`
- **System Test**: `gemm/sim/vector_system_test/`
- **Golden Generator**: `hex/generate_nv_hex.py`

---

**Last Updated**: Tue Dec 10 2025
**Status**: ✅ Functional - All tests passing (18 cocotb, 10 SV modular, 1 SV MLP)
