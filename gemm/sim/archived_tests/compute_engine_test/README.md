# Compute Engine MLP Testbench

**Purpose**: Unit tests for MLP-based compute engine
**Status**: ✅ **Functional** - All tests passing
**DUT**: `compute_engine_mlp.sv`

## Quick Start

```bash
cd /home/dev/Dev/elastix_gemm/gemm/sim/compute_engine_test

# Run MLP compute engine tests
make clean && make run

# Cocotb tests (comprehensive 18 test suite)
cd cocotb && uv run python test_compute_engine_mlp.py
```

## Overview

This testbench validates the MLP-based compute engine in isolation. The MLP compute engine replaces the older modular compute engine with improved performance.

| Property | Value |
|----------|-------|
| Module | `compute_engine_mlp.sv` |
| Columns | 16 (fixed hardware) |
| C Support | 16, 32, 64, 128 (multiples of 16) |
| Output | 256-bit (16 × FP16 per cycle) |
| Precision | GFP8E5 → FP24 → FP16 |

## Makefile Targets

| Target | Description |
|--------|-------------|
| `make run` | Run MLP compute engine tests |
| `make compile` | Compile MLP engine only |
| `make debug` | Run with GUI for debugging |
| `make summary` | Display test results summary |
| `make view-log` | View full simulation log |
| `make clean` | Remove generated files |

## Directory Structure

```
compute_engine_test/
├── tb_compute_engine_mlp.sv      # MLP testbench (primary)
├── Makefile                      # Build targets
├── README.md                     # This file
├── library.cfg                   # Riviera-PRO library config
├── cocotb/                       # Python-based cocotb tests
│   ├── test_compute_engine_mlp.py    # Cocotb test runner
│   ├── compute_engine_mlp_tests.py   # 18 test functions
│   ├── sim_utils/                    # Build utilities
│   └── pyproject.toml                # Python dependencies
└── tb_compute_engine_modular_opt.sv  # Legacy (deprecated)
```

## RTL Dependencies

- `gemm/src/rtl/compute_engine_mlp.sv` - MLP compute engine
- `gemm/src/rtl/mlp_bram_col_ctrl.sv` - MLP column controller
- `gemm/src/rtl/mlp_bram_col.sv`, `mlp_bram.sv` - MLP BRAMs
- `gemm/src/rtl/mlp_dot16_int8.sv`, `mlp_dot16_bfp8.sv` - MLP dot products
- `gemm/src/rtl/fp24_add.sv`, `fp24_to_fp16.sv` - FP24 conversion
- `gemm/src/rtl/row_bram.sv`, `weight_bram.sv` - Memory

## Test Configurations

### SystemVerilog Tests
- **B16_C16_V8**: Baseline test (256 results)

### Cocotb Tests (18 total)
1. `test_first_8_elements` - Basic 8-element dot product
2. `test_first_32_elements` - Full 32-element (1 group) dot product
3. `test_identity_matrix` - Identity pattern validation
4. `test_all_ones` - All-ones accumulation
5. `test_multi_nv` - Multiple Native Vectors (V > 1)
6. `test_different_columns` - Column-dependent patterns
7. `test_gfp_random_floats` - Random GFP8 data
8. `test_gfp_large_values` - Large value handling
9. `test_batch_dimension` - Batch processing (B > 1)
10. `test_batch_with_multi_nv` - Combined B > 1 and V > 1
11. `test_full_bcv` - Full B=16, C=16, V=8
12. `test_golden_hex` - Golden reference file validation
13. `test_c16_b4_v8` - B=4, C=16, V=8 (1 column group baseline)
14. `test_c16_b8_v4` - B=8, C=16, V=4 (1 column group baseline)
15. `test_c32_b4_v4` - B=4, C=32, V=4 (2 column groups)
16. `test_c32_b8_v2` - B=8, C=32, V=2 (2 column groups)
17. `test_c64_b8_v2` - B=8, C=64, V=2 (4 column groups)
18. `test_c128_b2_v1` - B=2, C=128, V=1 (8 column groups)

## Test Data

Golden references located at `/home/dev/Dev/elastix_gemm/hex/`:
- `left.hex`, `right.hex` - Input matrices (GFP8E5 format)
- `golden_B*_C*_V*.hex` - Expected FP16 results

## Tolerance Levels

| Tolerance Type | Value | Notes |
|----------------|-------|-------|
| Absolute | ±50 LSB | FP24 intermediate precision |
| Relative | 5% | ~1.3% typical error |

## Architecture Notes

### Exponent Conversion
- Input data stored in **GFP8E5** format (5-bit exponent, bias=15)
- MLP primitives require **GFP8E8** format (8-bit exponent, bias=133)
- **RTL performs conversion internally**: exp_E8 = exp_E5 + 118
- Testbench passes raw E5 data; no testbench conversion needed

### Test Sequence
1. Load test data to row_bram (simulating DISPATCH)
2. Send TILE command with B, C, V parameters
3. Wait for tile_done
4. Collect and validate FP16 results against golden reference

### C > 16 Support (Column Groups)
- MLP hardware has 16 physical columns
- For C > 16, columns are processed in groups of 16 sequentially
- Example: C=32 → 2 groups, C=128 → 8 groups

## References

- **RTL**: `gemm/src/rtl/compute_engine_mlp.sv`
- **System Test**: `gemm/sim/vector_system_test/`
- **Golden Generator**: `hex/generate_nv_hex.py`
- **Architecture Doc**: `gemm/SINGLE_ROW_REFERENCE.md`

---

**Last Updated**: Fri Dec 12 2025
**Status**: ✅ Functional - All tests passing
