# Running GEMM Engine GDDR6 Simulation

## Quick Start

```bash
cd /home/dev/Dev/elastix_gemm/gemm/sim/engine_gddr6_test

# Setup environment
source /tools/Achronix/Acex/ACE-9.2/Achronix_ac7t1500_fpga_only/setup.bash

# Create symbolic links to GDDR6 reference design includes
./setup.sh

# Run simulation
make clean
make run
```

## Prerequisites

### 1. Environment Setup
```bash
# ACE tools must be available
source /tools/Achronix/Acex/ACE-9.2/Achronix_ac7t1500_fpga_only/setup.bash

# Verify ACE_INSTALL_DIR is set
echo $ACE_INSTALL_DIR

# Ensure LD_LIBRARY_PATH is NOT set (Riviera requirement)
unset LD_LIBRARY_PATH
```

### 2. Micron GDDR6 Models

The simulation requires Micron GDDR6 BFM models. These should be located at:
```
/home/dev/Dev/elastix_gemm/gddr_ref_design/src/tb/gddr_model/
```

Files required:
- `micron_gddr6_bfm.v`
- `micron_gddr6_chn.v`
- `micron_gddr6_chk.v`
- `micron_gddr6_tim.v`

### 3. Test Data

Test matrices must be present in `/home/dev/Dev/elastix_gemm/hex/`:
- `left.hex` - Matrix A (528 lines x 32 bytes)
- `right.hex` - Matrix B (528 lines x 32 bytes)  
- `golden_B2_C2_V2.hex` - Expected results (4 FP16 values)

## Setup Script

Create and run `setup.sh`:

```bash
#!/bin/bash
# Create symbolic links to GDDR6 reference design includes

GDDR_TB_DIR="../../../gddr_ref_design/src/tb"

echo "Creating symbolic links to GDDR6 includes..."

ln -sf ${GDDR_TB_DIR}/gddr_dci_port_names.svh .
ln -sf ${GDDR_TB_DIR}/gddr_model_names.svh .

echo "Setup complete!"
ls -la *.svh
```

## Running the Simulation

### Standard Run (Command Line)
```bash
make clean
make run
```

This will:
1. Compile GDDR6 models
2. Compile NAP wrapper
3. Compile GEMM RTL
4. Compile testbench
5. Run simulation in batch mode
6. Check for "TEST PASSED" in log

### Debug Run (With GUI)
```bash
make clean
make debug
```

This opens Riviera-PRO GUI with waveforms for debugging.

### View Waveforms Later
```bash
make open_wave
```

## Simulation Flow

The testbench executes this sequence:

1. **Initialization**
   - Release reset
   - Preload GDDR6 with left.hex and right.hex

2. **FETCH Commands**
   - FETCH left matrix (528 lines from 0x0)
   - FETCH right matrix (528 lines from 0x4200)

3. **DISPATCH Commands**
   - DISPATCH left (addr=0, len=128)
   - WAIT_DISPATCH
   - DISPATCH right (addr=528, len=128)
   - WAIT_DISPATCH

4. **MATMUL**
   - MATMUL (B=2, C=2, V=2)
   - WAIT_MATMUL

5. **Check Results**
   - Capture 4 FP16 results from result FIFO
   - Compare with golden reference

## Expected Output

### Success
```
========================================================================
GEMM Engine GDDR6 Simulation Test
Test: B=2, C=2, V=2
========================================================================

[TB] Reset released

[TB] Preloading GDDR6 with test matrices...
[TB]   Loaded left.hex: 528 lines
[TB]   Loaded right.hex: 528 lines
[TB] GDDR6 preload complete

[TB] Step 1: FETCH left matrix (528 lines from 0x0)
[TB] Engine idle after XXXX cycles

[TB] Step 2: FETCH right matrix (528 lines from 0x4200)
[TB] Engine idle after XXXX cycles

[TB] Step 3: DISPATCH left (addr=0, len=128)
[TB] Engine idle after XXXX cycles

[TB] Step 4: WAIT_DISPATCH left (id=3)
[TB] Engine idle after XXXX cycles

[TB] Step 5: DISPATCH right (addr=528, len=128)
[TB] Engine idle after XXXX cycles

[TB] Step 6: WAIT_DISPATCH right (id=5)
[TB] Engine idle after XXXX cycles

[TB] Step 7: MATMUL (B=2, C=2, V=2)
[TB] Engine idle after XXXX cycles

[TB] Step 8: WAIT_MATMUL
[TB] Engine idle after XXXX cycles

[TB] Result[0] = 0xb414
[TB] Result[1] = 0x2ecb
[TB] Result[2] = 0x3345
[TB] Result[3] = 0x326b

========================================================================
TEST SUMMARY
========================================================================
Results captured: 4
Errors: 0
TEST PASSED
========================================================================
```

### Failure Indicators
- "Timeout waiting for engine idle"
- "Failed to open left.hex" or "right.hex"
- Incorrect number of results
- Results don't match golden reference

## Debugging Tips

### 1. Check GDDR6 Transactions
Look at waveforms for:
- `nap/arvalid`, `nap/arready` - AXI handshake
- `nap/araddr` - Should show page ID 0x2 (channel 1)
- `nap/rdata` - Data being read from GDDR6

### 2. Monitor Dispatcher BRAM
- `u_dispatcher_control/bram_wr_en_reg` - Write enable
- `u_dispatcher_control/bram_wr_addr_reg` - Write address (0-1055)
- `u_dispatcher_control/bram_wr_data_reg` - Data being written

### 3. Check Compute Engine
- `u_compute_engine/i_dim_b` - Should be 2
- `u_compute_engine/i_dim_c` - Should be 2
- `u_compute_engine/i_dim_v` - Should be 2
- `i_gfp_bcv_ctrl/b_idx_reg` - Should loop 0, 1
- `i_gfp_bcv_ctrl/c_idx_reg` - Should loop 0, 1

### 4. Verify Results
- `result_fifo_count` - Should reach 4
- `result_fifo_rdata` - Check each result
- Compare with golden: `0xb414, 0x2ecb, 0x3345, 0x326b`

## Common Issues

### Issue: "ACE_INSTALL_DIR is undefined"
**Solution**: Source ACE setup script
```bash
source /tools/Achronix/Acex/ACE-9.2/Achronix_ac7t1500_fpga_only/setup.bash
```

### Issue: "LD_LIBRARY_PATH is defined"
**Solution**: Unset it
```bash
unset LD_LIBRARY_PATH
```

### Issue: "Failed to open left.hex"
**Solution**: Check test data path
```bash
ls -la /home/dev/Dev/elastix_gemm/hex/left.hex
```

### Issue: Compilation errors for GDDR6 models
**Solution**: Verify models are present
```bash
ls -la ../../../gddr_ref_design/src/tb/gddr_model/*.v
```

### Issue: "Cannot find gddr_dci_port_names.svh"
**Solution**: Run setup script
```bash
./setup.sh
```

## Output Files

After simulation:
- `logs/FULLCHIP_BFM_simulation.log` - Full simulation log
- `sim_output.wlf` - Waveform database (if generated)
- `work/` - Compiled simulation library

## Makefile Targets

- `make` or `make run` - Clean, compile, and run simulation
- `make debug` - Run with GUI for debugging
- `make clean` - Remove all generated files
- `make help` - Show help message
- `make open_wave` - View saved waveforms

## Test Configuration

Current test parameters (defined in testbench):
```systemverilog
parameter TEST_B = 2;
parameter TEST_C = 2;
parameter TEST_V = 2;
```

To test different configurations, modify these parameters in `tb_engine_gddr6.sv` and regenerate test data:
```bash
cd /home/dev/Dev/elastix_gemm/hex
python3 generate_nv_hex.py -B <rows> -C <cols> -V <vectors>
```

## Next Steps After Simulation

Once simulation passes:
1. Verify hardware results match simulation
2. Debug any discrepancies in datapath
3. Test additional configurations (different B, C, V)
4. Stress test with larger matrices
5. Performance analysis and optimization


