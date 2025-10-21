# Run GDDR6 Simulation - Manual Steps

## Terminal Issues

The automated terminal is having issues. Please follow these manual steps:

## Quick Run (Single Command)

```bash
cd /home/dev/Dev/elastix_gemm/gemm/sim/engine_gddr6_test
bash run_sim.sh
```

This will:
1. Setup ACE environment
2. Verify dependencies
3. Clean previous builds
4. Compile (3-5 minutes)
5. Run simulation (5-15 minutes)
6. Show results

## Manual Steps (If Script Fails)

### 1. Navigate to Directory
```bash
cd /home/dev/Dev/elastix_gemm/gemm/sim/engine_gddr6_test
```

### 2. Setup Environment
```bash
source /tools/Achronix/Acex/ACE-9.2/Achronix_ac7t1500_fpga_only/setup.bash
unset LD_LIBRARY_PATH
```

### 3. Verify Setup
```bash
echo $ACE_INSTALL_DIR  # Should show ACE path
echo $LD_LIBRARY_PATH  # Should be empty
```

### 4. Clean and Compile
```bash
make clean
make run_compile
```

**Expected compilation time**: 3-5 minutes

**What's being compiled**:
- GDDR6 Micron models (slowest part)
- NAP responder wrapper
- GEMM engine RTL (10+ files)
- Testbench

### 5. Run Simulation
```bash
make run_vsim
```

**Expected simulation time**: 5-15 minutes

**What's being simulated**:
- Reset sequence
- FETCH left matrix (528 lines)
- FETCH right matrix (528 lines)
- DISPATCH operations
- MATMUL (B=2, C=2, V=2)
- Result capture

## Expected Output

### Success Case
```
========================================================================
TEST SUMMARY
========================================================================
Results captured: X
Errors: Y
TEST PASSED or TEST FAILED
========================================================================
```

### Likely First Run (Without GDDR6 Preload)
```
[TB] GDDR6 preload placeholder
[TB] NOTE: In real hardware, matrices are written via DMA before test
[TB] TODO: Implement AXI write sequence or Micron backdoor write

[TB] Step 1: FETCH left matrix (528 lines from 0x0)
[TB] Engine idle after XXXX cycles

[TB] Step 2: FETCH right matrix (528 lines from 0x4200)
[TB] Engine idle after XXXX cycles

... (DISPATCH and MATMUL steps) ...

[TB] Result[0] = 0xXXXX  (probably wrong - no data loaded)
[TB] Result[1] = 0xXXXX
[TB] Result[2] = 0xXXXX
[TB] Result[3] = 0xXXXX

Results captured: 4
Errors: X
TEST FAILED (results don't match golden)
```

## What To Look For

### 1. Compilation Success
Check for these files after `make run_compile`:
- `work/` directory created
- No ERROR messages in console

### 2. Simulation Progress
Watch for these messages:
- `[TB] Reset released`
- `[TB] Step 1: FETCH left matrix...`
- `[TB] Engine idle after XXXX cycles` (should be reasonable, not timeout)
- `[TB] Result[X] = 0xXXXX`

### 3. AXI Transactions (in logs)
Look for evidence of:
- AXI AR (read address) transactions
- AXI R (read data) responses
- Dispatcher BRAM writes

### 4. Potential Issues

#### Issue: Compilation Error "Module not found"
**Cause**: Missing RTL file or wrong path  
**Fix**: Check Makefile GEMM_FILES list

#### Issue: Compilation Error "Include file not found"
**Cause**: Wrong include path  
**Fix**: Check Makefile GDDR_INC_DIR

#### Issue: Simulation Timeout
**Cause**: FSM stuck, no data flow  
**Action**: Check which step timed out, run with GUI

#### Issue: Wrong Number of Results
**Cause**: BCV loop not iterating correctly  
**Action**: Check waveforms for b_idx_reg, c_idx_reg

#### Issue: Results All Zeros
**Cause**: GDDR6 not preloaded (EXPECTED for first run)  
**Action**: This is normal, proceed to implement preload

## Debug with GUI

If something fails, run with GUI to see waveforms:

```bash
make debug
```

This opens Riviera-PRO with waveforms. Key signals are already configured in `wave.do`:
- Clock and reset
- Engine status (mc_state, dc_state, ce_state)
- Command interface
- AXI transactions
- Dispatcher BRAM writes
- Compute engine dimensions
- Results

## Log Files

After running:
- `logs/FULLCHIP_BFM_simulation.log` - Full simulation output
- `transcript` - Riviera transcript
- `sim_output.wlf` - Waveform database (if GUI was used)

## Next Steps After First Run

### If Compilation Fails
1. Read error messages carefully
2. Check file paths in Makefile
3. Verify ACE_INSTALL_DIR is set
4. Check GDDR6 model files exist

### If Simulation Runs But Results Wrong
**This is EXPECTED!** GDDR6 is not preloaded yet.

Next task:
1. Implement `preload_gddr6()` task
2. Either backdoor write or AXI write
3. Re-run simulation

### If Simulation Shows Good Command Flow
Even with wrong results, if you see:
- ✓ Commands being issued
- ✓ FSM transitions
- ✓ AXI transactions
- ✓ Results being captured

Then infrastructure is working! Just need to add data.

## Quick Reference

```bash
# Full clean and run
cd /home/dev/Dev/elastix_gemm/gemm/sim/engine_gddr6_test
bash run_sim.sh

# Manual compile only
make clean && make run_compile

# Manual simulation only (after compile)
make run_vsim

# Debug with GUI
make debug

# Clean everything
make clean

# View previous waveforms
make open_wave
```

## Estimated Time

- **Setup**: 1 minute
- **Compilation**: 3-5 minutes
- **Simulation**: 5-15 minutes
- **Total**: ~10-20 minutes for first run

## Contact Points

If stuck:
1. Check `logs/FULLCHIP_BFM_simulation.log`
2. Look for ERROR or FATAL messages
3. Check which test step failed
4. Run with GUI to see waveforms


