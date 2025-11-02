# test_readback.cpp Setup and Validation

**Date**: November 1, 2025
**Status**: ✅ **COMPLETE - Compiled and Validated**

## Summary

Added new test `test_readback.cpp` to the Makefile and validated it compiles and runs successfully.

## Changes Made

### 1. Makefile Updates

**File**: `/home/workstation/elastix_gemm/gemm/sw_test/Makefile`

**Added to ALL_BINS**:
```makefile
ALL_BINS = ... test_multi_tile test_readback
```

**Added build rule**:
```makefile
test_readback: test_readback.cpp
	$(CXX) $(CXXFLAGS) $(INCLUDES) $< $(VP815_API) $(LIBS) -o $@
```

### 2. Compilation Verification

```bash
make clean && make test_readback
```

**Result**: ✅ Compiled successfully with no warnings or errors
- Binary size: 127 KB
- Executable: `./test_readback`

### 3. Sanity Check Test

**Test command**:
```bash
./test_readback 2 2 32
```

**Configuration tested**:
- B=2, C=2, V=32
- max_left_tiles=2, max_right_tiles=2
- num_tiles=2 (bottleneck)
- total_results=8

**Test results**:
```
✅ Device initialized successfully
✅ FETCH complete (528 lines × 2 matrices)
✅ DISPATCH complete (memory block distributed)
✅ 2 TILE commands executed
✅ 8 FP16 results collected
✅ Circular buffer state: wr_ptr=8, rd_ptr=0, used=8
✅ Results appear valid (not all zeros/invalid)
```

**Stages executed**:
1. ✅ DMA Transfer to GDDR6
2. ✅ FETCH Memory Block (left + right)
3. ✅ DISPATCH Memory Block
4. ✅ Execute TILE Commands (2 tiles, lockstep addressing)
5. ✅ Collect ALL Results (8 FP16 values)
6. ✅ Results Breakdown by Tile
7. ⚠️  Validation (golden reference not found - expected)

### 4. FPGA Health Check

**Post-test validation**:
```bash
./test_registers
```

**FPGA status**:
```
✅ Bitstream ID: 0x11011629 (Build: 11/01 16:29)
✅ ADM Status: 0x3 (GDDR6 training complete)
✅ LTSSM State: 0x11 (PCIe link up)
✅ All registers readable and functional
```

## Current Code Structure

### test_readback.cpp Features

Currently copied from `test_multi_tile.cpp`, includes:

**Stages 1-4**: Setup and execution
- DMA transfer to GDDR6
- FETCH memory blocks
- DISPATCH to compute column
- Execute TILE commands

**Stages 5-7**: Readback (to be optimized)
- Stage 5: Collect ALL results (single DMA read)
- Stage 6: Results breakdown by tile
- Stage 7: Validation against golden reference

**Dual-mode operation**:
- Single test: `./test_readback B C V`
- Multi-test suite: `./test_readback` (runs all 14 configs)

## Next Steps (User's Goal)

The user wants to optimize Stages 5-7 for aggressive readback testing:

**Current behavior** (Stages 5-7):
- Reads results for individual tests
- Single configuration per run
- Golden reference validation

**Desired behavior**:
- Optimize readback to identify multiple test patterns in hardware
- Test can identify different configurations from result stream
- More aggressive testing of readback functionality

## Files Modified

- ✅ `/home/workstation/elastix_gemm/gemm/sw_test/Makefile`
  - Added `test_readback` to ALL_BINS
  - Added build rule for `test_readback`

## Files Ready for Optimization

- `/home/workstation/elastix_gemm/gemm/sw_test/test_readback.cpp`
  - Currently: Copy of test_multi_tile.cpp
  - Next: Optimize Stages 5-7 for pattern identification

---

**Status**: ✅ **SETUP COMPLETE - Ready for Optimization**
**Compilation**: ✅ Success (no warnings)
**Sanity Check**: ✅ Passed (B=2,C=2,V=32)
**FPGA Health**: ✅ Verified
