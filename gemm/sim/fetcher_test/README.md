# Fetcher Module Testbench

**Purpose**: Validation environment for fetcher optimization with realistic GDDR6 memory model
**Status**: ✅ Baseline established, optimized implementation validated (3.1× speedup achieved)
**Created**: 2025-11-03
**Updated**: 2025-11-03 (Optimization complete)

## Overview

This testbench validates the **fetcher module** in isolation using a realistic GDDR6 memory model. The optimization effort achieved **3.1× performance improvement** (1885 → 607 cycles) through pipelined AR issuing and full utilization of the GDDR6 NoC's 32-outstanding-request capability.

## Performance Results

| Implementation | Cycles | Throughput | Outstanding ARs | Speedup |
|----------------|--------|------------|-----------------|---------|
| **Baseline** (`fetcher.sv`) | 1885 | 0.28 lines/cycle | 1/32 (3.1%) | 1.0× |
| **Optimized** (`fetcher_opt.sv`) | 607 | 0.87 lines/cycle | 32/32 (100%) | **3.1×** |

**Key Achievement**: Full utilization of GDDR6 NoC's 32-outstanding-request architectural limit

## Key Features

- **Realistic Memory Model**: `tb_memory_model_realistic.sv` with 32-outstanding limit and 100ns latency
- **Exact Hardware Match**: Uses real `dispatcher_bram.sv` module
- **Functional Verification**: Bit-exact validation (both LEFT and RIGHT blocks pass)
- **Performance Tracking**: Cycle counts, outstanding AR utilization, throughput metrics
- **Drop-in Replacement**: Optimized fetcher maintains same interface as baseline

## Quick Start

```bash
cd /home/workstation/elastix_gemm/gemm/sim/fetcher_test
make clean && make run     # Run simulation with fetcher_opt.sv
make summary               # View test results summary
make view-log              # View full simulation log
make debug                 # Run with GUI for waveform analysis
```

## Documentation

- **REALISTIC_BASELINE.md** - Baseline characterization with realistic memory model
- **FETCHER_OPT_RESULTS.md** - Complete optimization results and analysis
- **FETCHER_OPT_V2_ANALYSIS.md** - Failed attempt documentation (lessons learned)

## Architecture

### Design Under Test (DUT)

**Current**: `gemm/src/rtl/fetcher_opt.sv` - Optimized with 32-deep FWFT FIFO
**Baseline**: `gemm/src/rtl/fetcher.sv` - Original sequential implementation

### Memory Model

**tb_memory_model_realistic.sv** features:
- 32 outstanding AR transaction limit (Achronix GDDR6 NoC architectural constraint)
- 100ns read latency (40 cycles @ 400MHz)
- AR transaction queue with proper FIFO management
- Statistics tracking (outstanding count, max reached)

### Memory Layout

- **Block 0 (Left)**: BRAM[0-527] from `/home/workstation/elastix_gemm/hex/left.hex`
- **Block 1 (Right)**: BRAM[528-1055] from `/home/workstation/elastix_gemm/hex/right.hex`
- **Structure**: 528 lines × 256-bit per block (16 exponent + 512 mantissa)

### Optimization Technique

**Baseline Problem**:
```
Sequential FSM: Issue AR → Wait 40 cycles → Receive 16 beats → Repeat
Gap: 57 cycles between ARs
Result: Only 1 outstanding AR (3.1% utilization)
```

**Optimized Solution**:
```
Pipelined FSM: Issue all 33 ARs back-to-back via 32-deep FIFO
Decoupled: AR issuing independent of R receiving
Result: All 32 slots utilized (100% utilization)
```

**Implementation Details**:
- 32-deep FWFT FIFO manages AR burst queue
- Simplified 4-state machine (IDLE → INIT → ACTIVE → DONE)
- Preserved exponent unpacking logic unchanged from baseline
- Drop-in replacement (same module interface)

## Test Sequence

### Phase 1: Establish Golden Reference

1. **FETCH left matrix** (target=0)
   - Loads from GDDR6 lines 0-527
   - Measures cycle count
   - Captures BRAM contents as golden

2. **FETCH right matrix** (target=1)
   - Loads from GDDR6 lines 528-1055
   - Measures cycle count
   - Captures BRAM contents as golden

### Phase 2: Verification

3. **Re-FETCH left matrix**
   - Compare against golden left BRAM
   - Verify all 1024 entries (512 exp + 512 man)

4. **Re-FETCH right matrix**
   - Compare against golden right BRAM
   - Verify all 1024 entries (512 exp + 512 man)

### Expected Output

```
================================================================================
FETCHER TESTBENCH - Golden Reference Validation
================================================================================
Purpose: Establish baseline performance for fetcher optimization
DUT:     fetcher.sv (current implementation)
Memory:  tb_memory_model (zero-latency behavioral model)
BRAM:    dispatcher_bram.sv (exact hardware match)
================================================================================

[TB] Waiting for memory initialization...
[TB_MEM_MODEL] Loaded 528 lines from left.hex (Block 0)
[TB_MEM_MODEL] Loaded 528 lines from right.hex (Block 1)

========================================
[TEST] FETCH LEFT MATRIX (528 lines from GDDR6 block 0)
[TEST] Start address: 0x0000000 (line 0)
[TEST] Target: LEFT
========================================
[TEST] Fetch complete in XXX cycles
[TEST] Memory reads: 528
[TEST] Throughput: X.XX lines/cycle

========================================
[TEST] FETCH RIGHT MATRIX (528 lines from GDDR6 block 1)
[TEST] Start address: 0x0004200 (line 528)
[TEST] Target: RIGHT
========================================
[TEST] Fetch complete in XXX cycles
[TEST] Memory reads: 528
[TEST] Throughput: X.XX lines/cycle

================================================================================
VERIFICATION PHASE: Re-run fetches and compare against golden
================================================================================

[VERIFY] Checking LEFT matrix BRAM contents...
[VERIFY] LEFT matrix: PASS (all 1024 entries correct)

[VERIFY] Checking RIGHT matrix BRAM contents...
[VERIFY] RIGHT matrix: PASS (all 1024 entries correct)

================================================================================
PERFORMANCE SUMMARY - BASELINE (Current fetcher.sv)
================================================================================
Left Matrix Fetch:
  Cycles:     XXX
  Lines:      528
  Throughput: X.XX lines/cycle

Right Matrix Fetch:
  Cycles:     XXX
  Lines:      528
  Throughput: X.XX lines/cycle

Memory Model:
  Total reads: 1056
  Latency:     0 cycles (behavioral model)
================================================================================

*** TEST PASSED ***
Golden reference established for fetcher optimization
```

## Performance Metrics

The testbench tracks the following metrics for optimization comparison:

| Metric | Description | Use Case |
|--------|-------------|----------|
| **Cycle Count** | Total cycles from fetch_en to fetch_done | Primary optimization target |
| **Throughput** | Lines fetched per cycle (528 / cycles) | Efficiency measure |
| **Memory Reads** | Total AXI read transactions | Bandwidth verification |
| **Latency** | Memory model response time | Control variable |

### Baseline Expectations

With **zero-latency memory** (behavioral model):
- **Best case**: ~550-600 cycles (limited by state machine + AXI handshakes)
- **Throughput**: ~0.9-1.0 lines/cycle (near-perfect efficiency)

With **realistic GDDR6 latency** (~55 cycles first-word):
- **Expected**: ~2000-3000 cycles (latency-dominated)
- **Throughput**: ~0.2-0.3 lines/cycle (memory-bound)

## Optimization Workflow

### 1. Establish Baseline

```bash
cd /home/workstation/elastix_gemm/gemm/sim/fetcher_test
make clean && make run
make summary > baseline_results.txt
```

### 2. Modify Fetcher

Edit `/home/workstation/elastix_gemm/gemm/src/rtl/fetcher_optimized.sv`:
- Keep exact same interface
- Modify internal state machine
- Optimize AXI burst patterns

### 3. Compare Performance

```bash
# Update Makefile RTL_SOURCES to use fetcher_optimized.sv
make clean && make run
make summary > optimized_results.txt
diff baseline_results.txt optimized_results.txt
```

### 4. Verify Correctness

**Critical**: Optimized fetcher MUST produce identical BRAM contents:
- All 512 exp_aligned values must match
- All 512 mantissa lines must match
- Both left and right matrices

Any mismatch = **FAIL** (even if faster)

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
- **sim.log** - Compilation and simulation output (generated)

### Source Dependencies
- **DUT**: `../../src/rtl/fetcher.sv`
- **BRAM**: `../../src/rtl/dispatcher_bram.sv`
- **Memory Model**: `../../src/tb/tb_memory_model_behavioral.sv`
- **NAP Interface**: `../../src/rtl/nap_responder_wrapper.sv`
- **Package**: `../../src/include/gemm_pkg.sv`

### Test Data
- **Left Matrix**: `/home/workstation/elastix_gemm/hex/left.hex`
- **Right Matrix**: `/home/workstation/elastix_gemm/hex/right.hex`

## Debugging

### Compilation Errors

```bash
make clean
grep "ERROR" sim.log
```

### Verification Mismatches

Check log for BRAM content mismatches:
```bash
grep "MISMATCH" sim.log
```

### Performance Issues

Check state machine transitions:
```bash
grep "\[TEST\]" sim.log
```

### Waveform Analysis

```bash
make debug
# GUI will open with waveform viewer
# Add signals: u_fetcher/*, u_dispatcher_bram/*, axi_nap/*
```

## Success Criteria

✅ **PASS Conditions**:
1. Both left and right FETCH operations complete without errors
2. All 1024 BRAM entries match golden reference (0 mismatches)
3. Cycle counts are reasonable and repeatable
4. No AXI protocol violations
5. No timeout errors

❌ **FAIL Conditions**:
- Any BRAM content mismatch
- Timeout (>100k cycles)
- AXI errors (rresp != 0x00)
- Unexpected state machine hangs

## Future Extensions

1. **Realistic Memory Model**: Replace behavioral model with `tb_memory_model_gddr6.sv` (55-cycle latency)
2. **Burst Optimization**: Test different AXI burst lengths (4, 8, 16 beats)
3. **Pipelining**: Measure overlapped fetch + unpack performance
4. **Multi-Target**: Test rapid left→right switching
5. **Error Injection**: Validate error handling paths

## References

- **Fetcher RTL**: `/home/workstation/elastix_gemm/gemm/src/rtl/fetcher.sv`
- **BRAM RTL**: `/home/workstation/elastix_gemm/gemm/src/rtl/dispatcher_bram.sv`
- **System Test**: `/home/workstation/elastix_gemm/gemm/sim/vector_system_test/`
- **Memory Models**: `/home/workstation/elastix_gemm/gemm/src/tb/tb_memory_model*.sv`

---

**Maintained by**: Fetcher Optimization Team
**Last Updated**: 2025-11-03
**Status**: Ready for baseline testing ✅
