# GEMM Engine GDDR6 Simulation - Overview

**Created**: October 14, 2025  
**Purpose**: Full-system simulation with GDDR6 BFM to debug computation results

## What This Simulation Does

This testbench provides **complete visibility** into the GEMM engine datapath that hardware testing cannot provide:

### Hardware Testing Limitations ❌
- Can't see GDDR6 data being read
- Can't inspect dispatcher BRAM contents
- Can't trace compute engine indices
- Debug registers hardwired to zero
- Black box between FETCH and results

### Simulation Capabilities ✅
- **See GDDR6 transactions**: Every AXI read with address and data
- **Monitor BRAM writes**: Exact data being written to dispatcher BRAM
- **Trace BCV loop**: Watch B, C, V indices increment
- **Inspect accumulators**: See GFP8 dot products and accumulation
- **Verify results**: Compare with golden reference cycle-by-cycle

## Architecture

```
Testbench
├── Test Control Logic
│   ├── CSR write tasks (emulating software)
│   ├── Command sequencer
│   └── Result checker
│
├── DUT: engine_top
│   ├── csr_to_fifo_bridge
│   ├── cmd_fifo
│   ├── master_control
│   ├── dispatcher_control ──────┐
│   │   ├── Reads from GDDR6     │
│   │   └── Writes to BRAM       │
│   ├── dispatcher_bram_dual_read│
│   └── compute_engine_modular   │
│       ├── BCV controller        │
│       ├── GFP8 dot products     │
│       └── Accumulator           │
│                                 │
├── NAP Responder Wrapper         │
│   └── AXI slave interface ──────┤
│                                 │
└── Micron GDDR6 BFM <────────────┘
    ├── Preloaded with left.hex
    └── Preloaded with right.hex
```

## Test Sequence

### 1. Preload Phase
```
Testbench reads left.hex and right.hex
  ↓
Backdoor write to GDDR6 BFM memory
  ↓
Verify data accessible via AXI
```

### 2. Command Phase
```
Issue CSR writes (like software):
  FETCH left  → dispatcher reads 528 lines via NAP
  FETCH right → dispatcher reads 528 lines via NAP
  DISPATCH left  → configure CE for left matrix
  DISPATCH right → configure CE for right matrix
  MATMUL → compute B×C results
```

### 3. Verification Phase
```
Monitor result FIFO
  ↓
Capture 4 FP16 values
  ↓
Compare with golden_B2_C2_V2.hex:
  Expected: 0xb414, 0x2ecb, 0x3345, 0x326b
```

## Key Waveform Signals

### AXI Transactions
- `nap/arvalid, nap/arready` - Read request handshake
- `nap/araddr` - Address (check page ID = 0x2)
- `nap/rvalid, nap/rready` - Read data handshake
- `nap/rdata` - 256-bit data from GDDR6

### Dispatcher State
- `u_dispatcher_control/state_reg` - FSM state
- `u_dispatcher_control/current_line_reg` - Line being fetched
- `u_dispatcher_control/exp_lines_fetched_reg` - Exponent lines (0-15)
- `u_dispatcher_control/man_lines_fetched_reg` - Mantissa lines (16-527)

### Dispatcher BRAM Writes
- `bram_wr_en_reg` - Write enable
- `bram_wr_addr_reg` - Address (should be 0-527 for left, 528-1055 for right)
- `bram_wr_data_reg` - 256-bit GFP8 data

### Compute Engine
- `u_compute_engine/i_dim_b` - Batch dimension (should be 2)
- `u_compute_engine/i_dim_c` - Column dimension (should be 2)
- `u_compute_engine/i_dim_v` - Vector dimension (should be 2)

### BCV Loop
- `i_gfp_bcv_ctrl/b_idx_reg` - B index (0, 1)
- `i_gfp_bcv_ctrl/c_idx_reg` - C index (0, 1)
- `i_gfp_bcv_ctrl/v_idx_reg` - V index (0, 1)
- `i_gfp_bcv_ctrl/state_reg` - BCV state machine

### Results
- `result_fifo_count` - Number of results available
- `result_fifo_rdata` - Result data (FP16)
- `result_idx` - Results captured by testbench

## What We're Debugging

### Current Hardware Behavior
```
Results: 0x3c98, 0x3c98, 0x2180, 0x2180
         ^^^^^^  ^^^^^^  ^^^^^^  ^^^^^^
         Wrong   Duped   Wrong   Duped
```

### Expected Results
```
Golden:  0xb414, 0x2ecb, 0x3345, 0x326b
         ^^^^^^  ^^^^^^  ^^^^^^  ^^^^^^
         -0.254  +0.224  +0.817  +0.653
```

### Possible Root Causes (To Debug in Sim)

1. **GDDR6 Read Incorrect**
   - Wrong page ID (FIXED - now using page 2)
   - Wrong line addressing
   - Data corruption in transit

2. **Dispatcher BRAM Population**
   - GFP8 unpacking errors (exp vs mantissa)
   - BRAM write address calculation
   - Left/right matrix placement

3. **Compute Engine Addressing**
   - BRAM read addresses for NV fetching
   - Left vs right matrix selection
   - Group alignment issues

4. **BCV Loop Indexing**
   - B, C, V dimension capture
   - Loop iteration count
   - Result address calculation

5. **Accumulator Issues**
   - GFP8 dot product calculation
   - Exponent alignment
   - FP16 conversion

## Success Criteria

Simulation is successful when:

✅ **FETCH reads correct data from GDDR6**
- AXI transactions show page ID = 0x2
- All 528 lines read for each matrix
- No AXI protocol errors

✅ **Dispatcher BRAM populated correctly**
- BRAM addresses 0-527 written (left)
- BRAM addresses 528-1055 written (right)
- Data matches parsed left.hex/right.hex

✅ **Compute engine gets correct dimensions**
- `i_dim_b = 2`
- `i_dim_c = 2`
- `i_dim_v = 2`

✅ **BCV loop produces 4 results**
- B loops: 0, 1
- C loops: 0, 1  
- 2×2 = 4 results generated

✅ **Results match golden reference**
```
Result[0] = 0xb414 ✓
Result[1] = 0x2ecb ✓
Result[2] = 0x3345 ✓
Result[3] = 0x326b ✓
```

## Files

### Main Testbench
- `tb_engine_gddr6.sv` - Top-level testbench (660 lines)
  - Clock generation
  - Reset sequencing
  - GDDR6 preload
  - CSR write tasks
  - Command sequence
  - Result checking

### Build System
- `Makefile` - Compilation and simulation control
- `setup.sh` - Environment setup script
- `wave.do` - Waveform configuration

### Documentation
- `README.md` - Quick reference
- `RUNNING_SIMULATION.md` - Detailed instructions
- `SIMULATION_OVERVIEW.md` - This file

### Dependencies
- GDDR6 models: `../../../gddr_ref_design/src/tb/gddr_model/`
- NAP wrapper: `../../../gddr_ref_design/src/rtl/nap_responder_wrapper.sv`
- GEMM RTL: `../../src/rtl/`
- Test data: `/home/dev/Dev/elastix_gemm/hex/`

## Running Quick Start

```bash
# 1. Setup
cd /home/dev/Dev/elastix_gemm/gemm/sim/engine_gddr6_test
source /tools/Achronix/Acex/ACE-9.2/Achronix_ac7t1500_fpga_only/setup.bash
unset LD_LIBRARY_PATH
./setup.sh

# 2. Run
make clean
make run

# 3. Check results
grep "TEST PASSED" logs/FULLCHIP_BFM_simulation.log
```

## Expected Timeline

- **Compilation**: ~2-5 minutes
  - GDDR6 models (largest)
  - GEMM RTL
  - Testbench

- **Simulation**: ~5-15 minutes
  - FETCH: ~50k cycles (reading 528 lines × 2)
  - DISPATCH: ~10k cycles
  - MATMUL: ~10k cycles
  - Total: ~100k-200k cycles @ 500MHz

## Debugging Workflow

1. **Run simulation**
   ```bash
   make clean && make run
   ```

2. **Check for "TEST PASSED"**
   ```bash
   tail logs/FULLCHIP_BFM_simulation.log
   ```

3. **If test fails, run with GUI**
   ```bash
   make debug
   ```

4. **Focus waveform investigation**:
   - Start with AXI transactions
   - Verify GDDR6 addresses
   - Check BRAM write data
   - Trace BCV loop
   - Inspect results

5. **Identify root cause**
   - Compare expected vs actual at each stage
   - Find first point of divergence
   - Fix RTL or test data
   - Re-run

## Integration with Hardware

Once simulation passes:

1. **Bitstream matches simulation**
   - Same RTL
   - Same synthesis/P&R flow
   - Same constraints

2. **Hardware test should pass**
   - Use same test data (left.hex, right.hex)
   - Issue same command sequence
   - Expect same results

3. **If hardware still fails**
   - Synthesis issues
   - Timing violations
   - Place & route problems
   - Clock domain crossing
   - Not a logic bug!

## Next Steps

After this simulation validates the design:

1. **Test more configurations**
   - B=4, C=4, V=4
   - B=8, C=8, V=16
   - Maximum: B=128, C=128, V=1

2. **Stress testing**
   - Back-to-back commands
   - Maximum throughput
   - Edge cases (B=1, C=1, V=1)

3. **Performance analysis**
   - Cycle counts per operation
   - Bottleneck identification
   - Optimization opportunities

4. **Coverage analysis**
   - All opcodes tested
   - All state transitions
   - Error conditions

## Conclusion

This simulation environment provides **complete visibility** into the GEMM engine that hardware testing cannot match. It's the essential tool for:

- ✓ Validating correct operation
- ✓ Debugging computation errors
- ✓ Understanding dataflow
- ✓ Optimizing performance

The simulation matches hardware exactly (same RTL), so **simulation PASS = hardware SHOULD PASS**.


