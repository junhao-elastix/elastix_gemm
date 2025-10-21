# Vector System Test - Engine Top Testbench

**Status**: ✅ **ALL TESTS PASSING** (9/9)
**Last Validated**: Mon Oct 20 20:39 PDT 2025

## Overview

SystemVerilog testbench for validating the MS2.0 GEMM engine with direct FIFO interface.
Tests various BxCxV configurations with hardware-accurate GFP8 computation.

**New Feature**: All compilation and simulation output is logged to `sim.log` for clean terminal operation.

## Quick Start

```bash
# Clean and run all tests (output logged to sim.log)
make clean && make run

# View test summary
make summary

# View full log
make view-log

# Get help
make help
```

**Expected Output**: Test summary with STATUS: ALL TESTS PASSED

## Makefile Targets

| Target | Description |
|--------|-------------|
| `make` or `make run` | Clean, compile, and run all tests (outputs to sim.log) |
| `make compile` | Compile only (no simulation) |
| `make summary` | Display test results summary from sim.log |
| `make view-log` | View full simulation log (sim.log) |
| `make debug` | Run simulation with GUI |
| `make clean` | Remove all generated files |
| `make help` | Show detailed help message |

## Test Configurations

| Test | Config | Results | Description |
|------|--------|---------|-------------|
| 1 | B=1, C=1, V=1 | 1 | Single output |
| 2 | B=2, C=2, V=2 | 4 | Small matrix |
| 3 | B=4, C=4, V=4 | 16 | Small matrix |
| 4 | B=2, C=2, V=64 | 4 | Large V-loop |
| 5 | B=4, C=4, V=32 | 16 | Medium V-loop |
| 6 | B=8, C=8, V=16 | 64 | Medium matrix |
| 7 | B=1, C=128, V=1 | 128 | Wide matrix |
| 8 | B=128, C=1, V=1 | 128 | Tall matrix (maximum batch) |
| 9 | B=1, C=1, V=128 | 1 | Maximum V-loop |

## Files

### Active Files
- **Makefile** - Primary build script with logging support
- **tb_engine_top.sv** - Main testbench with continuous FIFO draining
- **library.cfg** - Simulator library configuration

### Generated Files (cleaned with `make clean`)
- **sim.log** - Complete compilation and simulation log (all verbose output)
- **work/** - Simulation working directory
- **dataset.asdb** - Simulation dataset
- **sim_debug.log** - Debug GUI log (when using `make debug`)

### Archived Files
- **archive_debug_notes/** - Obsolete debugging files from Oct 2025 validation session

## Golden Reference

Golden reference files are located in `/home/dev/Dev/elastix_gemm/hex/`:
- `golden_B1_C1_V1.hex` through `golden_B128_C1_V1.hex`

Generated using `/home/dev/Dev/compute_engine_w8a8/hex/hardware_gfp_reference.py`

## Architecture

**Testbench Features**:
- Loads test matrices from hex files
- Generates command sequences (FETCH → DISPATCH → TILE → WAIT)
- **Continuously drains result FIFO** to prevent backpressure deadlock
- Validates FP16 results against golden reference
- Reports pass/fail status with mismatch details

**DUT**: `engine_top.sv`
- Command FIFO interface
- Result FIFO interface (256 entries, afull @ 192)
- Dual BRAM dispatcher
- Modular compute engine with V-loop accumulation
- GFP8 to FP16 conversion

## Key Implementation Details

### FIFO Configuration
- **Result FIFO Depth**: 256 entries (increased from 64)
- **Almost Full Threshold**: 192 entries (increased from 48)
- **Continuous Draining**: Testbench reads results as they arrive to prevent deadlock

### Test Sequence
1. Load golden reference from `/home/dev/Dev/elastix_gemm/hex/golden_*.hex`
2. Generate command sequence with B, C, V parameters
3. Submit commands to cmd_fifo
4. Continuously read and verify results from result_fifo
5. Report pass/fail with mismatch count

## Logging and Output

All compilation and simulation output is automatically logged to `sim.log`:
- **Compilation warnings/errors**: Captured during vlog phase
- **Simulation messages**: All $display statements and debug output
- **Test results**: Individual test PASS/FAIL and final summary

### Viewing Results

```bash
# Quick summary (recommended)
make summary

# Full log (for debugging)
make view-log

# Search for specific patterns
grep "ERROR\|WARNING" sim.log
grep "MISMATCH" sim.log
```

## Troubleshooting

### All Tests Pass
✅ System is working correctly! View summary with `make summary`

### Compilation Errors
```bash
make clean
# Check sim.log for detailed error messages
grep "ERROR" sim.log
```

### Timeout Errors
- Review sim.log for state machine progress
- Check that testbench is continuously draining the result FIFO
- Verify FIFO depth and almost-full threshold are sufficient

## Development History

**Oct 20, 2025**: Cleanup for baseline reference (9/9 tests passing)
- Added logging to sim.log for clean terminal operation
- Enhanced Makefile with summary and view-log targets
- Updated test configurations to include B1_C1_V128 edge case
- Improved documentation with detailed Makefile target descriptions

**Oct 12, 2025**: Achieved full validation (8/8 tests passing)
- Fixed golden reference file mismatch
- Increased result FIFO depth (64→256)
- Implemented continuous FIFO draining in testbench
- Fixed count width truncation (7→15 bits)

**Oct 10, 2025**: Initial MS2.0 GEMM engine integration with dual BRAM architecture

## References

- **Main RTL**: `/home/dev/Dev/elastix_gemm/gemm/src/rtl/`
- **Testbench Utilities**: `/home/dev/Dev/compute_engine_w8a8/src/tb/`
- **Golden Reference Generator**: `/home/dev/Dev/compute_engine_w8a8/hex/hardware_gfp_reference.py`














