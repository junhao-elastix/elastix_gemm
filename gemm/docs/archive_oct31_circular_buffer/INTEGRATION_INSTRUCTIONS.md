# Integration Instructions for Optimized Fetcher

## Quick Integration (5 minutes)

### Step 1: Backup Current Implementation
```bash
cd /home/workstation/elastix_gemm/gemm/src/rtl
cp fetcher.sv fetcher_original.sv
```

### Step 2: Replace Fetcher Module
```bash
# Option A: Replace directly
cp fetcher_optimized.sv fetcher.sv

# Option B: Update instantiation name (if keeping both)
# Edit dispatcher_control.sv to use fetcher_optimized module name
```

### Step 3: Test in Simulation
```bash
cd /home/workstation/elastix_gemm/gemm/sim/vector_system_test
make clean && make run
grep "FETCHER" sim.log | tail -50  # Check optimization messages
```

### Step 4: Verify Performance
```bash
# Look for these key indicators in sim.log:
grep "Predictive AR" sim.log        # Should see predictive issuing
grep "RLAST.*FIFO_entries" sim.log  # Should show multiple outstanding
grep "FETCH_COMPLETE" sim.log       # Should complete faster
```

## Expected Simulation Output

### Original Implementation
```
[FETCHER] @100ns FETCH_START
[FETCHER] @150ns RLAST (burst 0)
[FETCHER] @168ns AR issued (18 cycle gap!)
[FETCHER] @218ns RLAST (burst 1)
...
[FETCHER] @720ns FETCH_COMPLETE
```

### Optimized Implementation
```
[FETCHER] @100ns FETCH_START
[FETCHER] @147ns Predictive AR #1 at beat 3 before RLAST
[FETCHER] @150ns RLAST: ARs_issued=2, FIFO_entries=1
[FETCHER] @151ns First beat of next burst (NO GAP!)
...
[FETCHER] @561ns FETCH_COMPLETE (22% faster!)
```

## Rollback Plan

If any issues arise:
```bash
cd /home/workstation/elastix_gemm/gemm/src/rtl
cp fetcher_original.sv fetcher.sv
cd ../../sim/vector_system_test
make clean && make run
```

## Key Files Modified

1. **fetcher.sv** - The actual implementation
2. **sim.log** - Contains performance metrics
3. **FETCHER_OPTIMIZATION_PLAN.md** - Technical details

## Success Criteria

✅ All simulation tests pass (10/10)
✅ No data corruption (BRAM contents match expected)
✅ Fetch completes in ~561 cycles (vs ~720 original)
✅ Inter-burst gaps reduced to 0-1 cycles (vs 18 original)

## Hardware Testing (After Simulation Success)

```bash
cd /home/workstation/elastix_gemm/gemm
./build_and_flash.sh
cd sw_test
./test_ms2_gemm_full
```

Monitor for:
- Faster GEMM execution time
- No data errors
- Stable operation