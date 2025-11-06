# GEMM Engine GDDR6 Full System Simulation

**Purpose**: Comprehensive simulation with Micron GDDR6 BFM to debug computation results

## Quick Start

```bash
# 1. Setup environment
source /tools/Achronix/Acex/ACE-9.2/Achronix_ac7t1500_fpga_only/setup.bash
unset LD_LIBRARY_PATH

# 2. Create symbolic links
bash setup.sh

# 3. Run simulation
make clean && make run
```

## What This Simulates

- **Full GEMM engine** with real GDDR6 memory model
- **Test sequence**: FETCH → DISPATCH → MATMUL (B=2, C=2, V=2)
- **Test data**: Preloaded from `/home/dev/Dev/elastix_gemm/hex/left.hex` and `right.hex`
- **Expected results**: 4 FP16 values matching `golden_B2_C2_V2.hex`

## Why This Simulation

Hardware testing has **black box limitations**:
- Can't see GDDR6 data being read
- Can't inspect dispatcher BRAM contents
- Debug registers hardwired to zero
- No visibility into compute engine loop

This simulation provides **complete waveform visibility**:
- ✓ AXI transactions to GDDR6
- ✓ Dispatcher BRAM writes
- ✓ BCV loop indices
- ✓ Accumulator values
- ✓ Result generation

## Current Hardware Issue

```
Hardware results: 0x3c98, 0x3c98, 0x2180, 0x2180  [WRONG + DUPLICATES]
Expected golden:  0xb414, 0x2ecb, 0x3345, 0x326b  [CORRECT]
```

**Goal**: Use simulation to identify where computation diverges from expected behavior.

## Documentation

- **RUNNING_SIMULATION.md** - Detailed setup and execution instructions
- **SIMULATION_OVERVIEW.md** - Architecture, debugging workflow, waveform analysis
- **wave.do** - Waveform configuration for Riviera-PRO

## Success Criteria

✅ Simulation passes when:
1. FETCH reads 528 lines × 2 from GDDR6 (page ID = 0x2)
2. Dispatcher BRAM populated with correct data
3. Compute engine processes with B=2, C=2, V=2
4. Results match golden reference: `0xb414, 0x2ecb, 0x3345, 0x326b`

## Debugging with GUI

```bash
make clean && make debug
```

Opens Riviera-PRO with waveforms. Key signals:
- AXI: `nap/arvalid`, `nap/araddr`, `nap/rdata`
- Dispatcher: `u_dispatcher_control/bram_wr_*`
- Compute: `u_compute_engine/i_dim_*`
- Results: `result_fifo_rdata`

## Files

- `tb_engine_gddr6.sv` - Main testbench (660 lines)
- `Makefile` - Build system
- `setup.sh` - Creates symbolic links to GDDR6 includes
- `wave.do` - Waveform setup

## Requirements

- Achronix ACE tools (ACE-9.2)
- Riviera-PRO simulator
- Micron GDDR6 BFM models (in `gddr_ref_design/src/tb/gddr_model/`)
- Test data (`hex/left.hex`, `hex/right.hex`, `hex/golden_B2_C2_V2.hex`)

## Compilation Time

- GDDR6 models: ~2 minutes
- GEMM RTL: ~1 minute
- Total: ~3-5 minutes

## Simulation Time

- FETCH operations: ~50k cycles
- DISPATCH + MATMUL: ~20k cycles
- Total: ~100k-200k cycles (~5-15 minutes wall time)

## Output

Success:
```
========================================================================
TEST SUMMARY
========================================================================
Results captured: 4
Errors: 0
TEST PASSED
========================================================================
```

Failure indicators:
- "Timeout waiting for engine idle"
- "Mismatch: expected 0xXXXX, got 0xYYYY"
- Wrong number of results

## Integration with Hardware

Once simulation passes:
1. Same RTL generates bitstream
2. Hardware should produce same results
3. If hardware still fails → synthesis/timing issue, not logic bug

## Next Steps After Simulation Passes

1. Test additional configurations (B=4, C=4, etc.)
2. Stress test with back-to-back commands
3. Performance analysis and optimization
4. Coverage analysis for all states and paths
