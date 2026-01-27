# GDDR6 Simulation Checklist

## Pre-Run Verification

### ✅ Files Created
- [x] tb_engine_gddr6.sv (660 lines)
- [x] Makefile (FULLCHIP_BFM flow)
- [x] wave.do (waveform config)
- [x] setup.sh (dependency check)
- [x] run_sim.sh (automated run)
- [x] Documentation (5 files)

### ✅ Dependencies Verified
- [x] GDDR6 models exist (4 files)
  - micron_gddr6_bfm.v
  - micron_gddr6_chn.v
  - micron_gddr6_chk.v
  - micron_gddr6_tim.v
- [x] GDDR6 includes exist
  - gddr_dci_port_names.svh
  - gddr_model_names.svh
- [x] NAP wrapper exists
  - nap_responder_wrapper.sv
- [x] GEMM RTL exists (14 core files)
  - engine_top.sv
  - master_control.sv
  - dispatcher_control.sv
  - compute_engine_modular.sv
  - All other dependencies
- [x] Test data exists
  - left.hex (528 lines)
  - right.hex (528 lines)
  - golden_B2_C2_V2.hex (4 values)

## Run Steps

### Step 1: Navigate to Directory
```bash
cd /home/dev/Dev/elastix_gemm/gemm/sim/engine_gddr6_test
```
- [ ] In correct directory

### Step 2: Run Simulation
```bash
bash run_sim.sh
```
- [ ] Script started
- [ ] ACE environment sourced
- [ ] Dependencies verified
- [ ] Clean completed

### Step 3: Compilation (3-5 minutes)
Expected phases:
- [ ] GDDR6 models compiled (2-3 min)
- [ ] NAP wrapper compiled
- [ ] GEMM package compiled
- [ ] NAP interfaces compiled
- [ ] GEMM RTL compiled (1-2 min)
- [ ] Testbench compiled
- [ ] Compilation SUCCESS (no errors)

### Step 4: Simulation (5-15 minutes)
Expected sequence:
- [ ] Reset released
- [ ] GDDR6 preload (placeholder message)
- [ ] Step 1: FETCH left (should not timeout)
- [ ] Step 2: FETCH right (should not timeout)
- [ ] Step 3: DISPATCH left
- [ ] Step 4: WAIT_DISPATCH left
- [ ] Step 5: DISPATCH right
- [ ] Step 6: WAIT_DISPATCH right
- [ ] Step 7: MATMUL
- [ ] Step 8: WAIT_MATMUL
- [ ] Results captured (4 values)
- [ ] Simulation complete (no hangs)

## Expected First Run Results

### ⚠️ Known Issue: GDDR6 Not Preloaded
- [ ] Simulation completes without hang
- [ ] 4 results captured
- [ ] Results are WRONG (no data in GDDR6) - THIS IS EXPECTED
- [ ] No ERROR/FATAL messages (warnings OK)

### ✅ What Should Work
- [x] Compilation completes
- [ ] Commands flow through system
- [ ] FSM transitions observed
- [ ] AXI transactions occur
- [ ] Results generated (even if incorrect)

### ❌ What Won't Work Yet
- [ ] Results match golden (need GDDR6 preload)
- [ ] Data correctness (no data loaded)

## Post-Run Analysis

### Check Logs
```bash
cat logs/FULLCHIP_BFM_simulation.log | grep -E "TEST|ERROR|Result"
```
- [ ] Log file exists
- [ ] No FATAL errors
- [ ] TEST SUMMARY printed
- [ ] Results captured

### Check For Issues

#### If Compilation Failed
- [ ] Check error message
- [ ] Verify ACE_INSTALL_DIR set
- [ ] Check file paths in Makefile
- [ ] Verify GDDR6 models exist

#### If Simulation Timed Out
- [ ] Check which step timed out
- [ ] Run with GUI: `make debug`
- [ ] Check FSM states in waveform
- [ ] Verify AXI handshaking

#### If Wrong Number of Results
- [ ] Check BCV loop iteration
- [ ] Verify B=2, C=2, V=2 captured
- [ ] Check result FIFO count

#### If Simulation Hangs
- [ ] Check for infinite loops
- [ ] Verify FSM state transitions
- [ ] Check AXI deadlock

## Next Steps

### After Successful First Run (Even With Wrong Results)
1. [ ] Review simulation log
2. [ ] Identify command flow is working
3. [ ] Confirm no hangs or errors
4. [ ] Document cycle counts for each phase

### Implement GDDR6 Preload (Priority 1)
Choose approach:
- [ ] Option A: Micron backdoor write (simpler, faster)
- [ ] Option B: AXI write transactions (more realistic)

Implementation location: `tb_engine_gddr6.sv`, task `preload_gddr6()`

### Re-run After Preload
- [ ] Compile (no changes needed)
- [ ] Run simulation
- [ ] Verify results match golden:
  - Result[0] = 0xb414 ✓
  - Result[1] = 0x2ecb ✓
  - Result[2] = 0x3345 ✓
  - Result[3] = 0x326b ✓

### Debug with Waveforms
- [ ] Run `make debug` to open GUI
- [ ] Verify AXI transactions:
  - Address includes page ID 0x2
  - Read data from GDDR6
- [ ] Check dispatcher BRAM:
  - Addresses 0-527 for left
  - Addresses 528-1055 for right
  - Data matches GDDR6 reads
- [ ] Trace compute engine:
  - B index loops 0, 1
  - C index loops 0, 1
  - V index loops 0, 1
  - 4 results generated

### Hardware Correlation
After simulation passes:
- [ ] Compare simulation results with hardware
- [ ] Identify differences in waveforms
- [ ] Check timing in hardware
- [ ] Verify GDDR6 training status

## Success Criteria

### Phase 1: Infrastructure (Current)
- [x] All files created
- [x] All dependencies verified
- [ ] Compilation succeeds
- [ ] Simulation runs to completion
- [ ] No hangs or fatal errors

### Phase 2: With GDDR6 Preload
- [ ] Data loaded correctly
- [ ] Results match golden reference
- [ ] All 4 values correct
- [ ] TEST PASSED message

### Phase 3: Hardware Debug
- [ ] Simulation matches hardware command flow
- [ ] Identify root cause of hardware issue
- [ ] Fix applied and verified
- [ ] Hardware matches simulation

## Time Estimates

- Setup: 1 minute
- Compilation: 3-5 minutes
- Simulation: 5-15 minutes
- Analysis: 5-10 minutes
- **Total First Run**: 15-30 minutes

## Files to Reference

- **RUN_NOW.md** - Detailed manual steps if script fails
- **START_HERE.txt** - Quick start instructions
- **STATUS.md** - Current status and GDDR6 preload TODO
- **RUNNING_SIMULATION.md** - Complete simulation guide
- **SIMULATION_OVERVIEW.md** - Architecture and debugging

## Notes

- Terminal automation is not working, hence manual run script
- GDDR6 preload is intentionally not implemented yet
- First run should show command flow working (infrastructure validation)
- Second run (after preload) should show correct results


