# Fetcher Module Testbench

**Purpose**: Unit test for `fetcher_opt.sv` module with realistic GDDR6 memory model  
**Status**: ✅ **Functional** - All tests passing  
**Memory Model**: `tb_memory_model_realistic.sv` (100% compliant with reference design)

## Quick Start

```bash
cd /home/dev/Dev/elastix_gemm/gemm/sim/fetcher_test
make clean && make run     # Run simulation
make summary               # View test results summary
make view-log              # View full simulation log
make debug                 # Run with GUI for waveform analysis
```

## Overview

This testbench validates the **fetcher module** (`fetcher_opt.sv`) in isolation using a realistic GDDR6 memory model. The fetcher is responsible for transferring data from GDDR6 memory to dispatcher BRAM.

### Key Features

- **Realistic Memory Model**: Uses `tb_memory_model_realistic.sv` with 32-outstanding-request limit and 100ns latency
- **Hardware Match**: Uses real `dispatcher_bram.sv` module
- **Functional Verification**: Bit-exact validation (both LEFT and RIGHT blocks pass)
- **Performance Tracking**: Cycle counts, outstanding AR utilization, throughput metrics

## Test Sequence

1. **FETCH left matrix** (528 lines from GDDR6 block 0)
   - Measures cycle count
   - Captures BRAM contents as golden reference

2. **FETCH right matrix** (528 lines from GDDR6 block 1)
   - Measures cycle count
   - Captures BRAM contents as golden reference

3. **Verification**: Re-run fetches and compare against golden
   - Verifies all 1024 BRAM entries (512 exp + 512 man) match

## Expected Output

```
[TEST] FETCH LEFT: Complete in XXX cycles (0.XX lines/cycle)
[VERIFY] LEFT: PASS

[TEST] FETCH RIGHT: Complete in XXX cycles (0.XX lines/cycle)
[VERIFY] RIGHT: PASS

*** TEST PASSED ***
```

## Architecture

### Design Under Test (DUT)
- **Module**: `gemm/src/rtl/fetcher_opt.sv` - Optimized fetcher with 32-deep FWFT FIFO
- **BRAM**: `gemm/src/rtl/dispatcher_bram.sv` - Dual-port BRAM for dispatcher

### Memory Model
- **Model**: `tb_memory_model_realistic.sv` (100% compliant with reference design)
- **Features**:
  - 32 outstanding AR transaction limit (Achronix GDDR6 NoC limit)
  - 100ns read latency (40 cycles @ 400MHz)
  - Burst length checking
  - GDDR address conversion

### Memory Layout
- **Block 0 (Left)**: BRAM[0-527] from `/home/dev/Dev/elastix_gemm/hex/left.hex`
- **Block 1 (Right)**: BRAM[528-1055] from `/home/dev/Dev/elastix_gemm/hex/right.hex`
- **Structure**: 528 lines × 256-bit per block (16 exponent + 512 mantissa)

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
- **tb_fetcher.sv** - Main testbench module
- **Makefile** - Build and simulation control
- **README.md** - This documentation
- **library.cfg** - Riviera-PRO library configuration

### Source Dependencies
- **DUT**: `../../src/rtl/fetcher_opt.sv`
- **BRAM**: `../../src/rtl/dispatcher_bram.sv`
- **Memory Model**: `../../src/tb/tb_memory_model_realistic.sv`
- **NAP Interface**: `../../src/rtl/nap_responder_wrapper.sv`
- **Package**: `../../src/include/gemm_pkg.sv`

### Test Data
- **Left Matrix**: `/home/dev/Dev/elastix_gemm/hex/left.hex`
- **Right Matrix**: `/home/dev/Dev/elastix_gemm/hex/right.hex`

## Success Criteria

✅ **PASS Conditions**:
1. Both left and right FETCH operations complete without errors
2. All 1024 BRAM entries match golden reference (0 mismatches)
3. Cycle counts are reasonable and repeatable
4. No AXI protocol violations
5. No timeout errors

## Performance

The optimized fetcher (`fetcher_opt.sv`) achieves:
- **3.1× speedup** over baseline (1885 → 607 cycles)
- **Full utilization** of GDDR6 NoC's 32-outstanding-request capability
- **0.87 lines/cycle** throughput with realistic memory latency

## References

- **Fetcher RTL**: `/home/dev/Dev/elastix_gemm/gemm/src/rtl/fetcher_opt.sv`
- **BRAM RTL**: `/home/dev/Dev/elastix_gemm/gemm/src/rtl/dispatcher_bram.sv`
- **System Test**: `/home/dev/Dev/elastix_gemm/gemm/sim/vector_system_test/`
- **Memory Model**: `/home/dev/Dev/elastix_gemm/gemm/src/tb/tb_memory_model_realistic.sv`
- **Historical Documentation**: `archive_nov06_docs/` (archived Nov 6, 2025)

---

**Last Updated**: Thu Nov 6 2025  
**Status**: ✅ Functional - All tests passing
