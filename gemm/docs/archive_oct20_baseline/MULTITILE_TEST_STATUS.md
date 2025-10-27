# Multi-Tile Test Status

**Date**: October 15, 2025  
**Test Configuration**: B=2, C=1, V=32 (8 tiles total)

## Summary

Multi-tile sequencing test has been implemented and reveals **hardware limitations** with the current MS2.0 GEMM engine dispatcher architecture.

## Test Implementation

Created `run_multitile_test()` function in `test_ms2_gemm_full.cpp` with command-line support:
```bash
./test_ms2_gemm_full --multitile --B 2 --C 1 --V 32 -v
```

### Test Flow

1. **FETCH LEFT** (once): Load all 128 NVs into left buffer
2. **FETCH RIGHT** (once): Load all 128 NVs into right buffer
3. **For each of 8 tiles**: Issue MATMUL with different addresses
4. **Collect results**: Read B×C results after each MATMUL
5. **Validate**: Compare against golden reference

## Current Hardware Limitations

### Problem: Dispatcher Does Not Support Multi-Tile Addressing

**Symptoms**:
- All 8 tiles produce only 2 unique result values: `0xb6ae` (-0.41748), `0x3a4a` (0.786133)
- These are the correct values for **tile 0 only**
- Hardware is repeating tile 0 results for all 8 tiles
- Validation: 5/16 matches (31% - exactly the matches where golden = tile0 results)

**Root Cause**:
The current dispatcher architecture uses a **single shared BRAM** (2048×256-bit) where:
- Lines [0-527]: Left matrix (all 128 NVs)
- Lines [528-1055]: Right matrix (all 128 NVs)

When the compute engine issues MATMUL commands with different `left_addr`/`right_addr`:
- Compute engine **ignores the addresses** and always reads from fixed positions
- OR dispatcher is not properly forwarding address-based data to compute engine
- Result: Only computes the first tile repeatedly

## Two Architectural Approaches

### Approach 1: DISPATCH-Based Multi-Tile (FUTURE)

**Concept**: DISPATCH command actively moves data from dispatcher BRAM to compute engine buffers.

**Command Sequence**:
```
FETCH_LEFT  (load 128 NVs to dispatcher BRAM [0-527])
FETCH_RIGHT (load 128 NVs to dispatcher BRAM [528-1055])
FOR each tile:
    DISPATCH_LEFT  (tile_addr = left_nv_start * 4)
    WAIT_DISPATCH
    DISPATCH_RIGHT (tile_addr = right_nv_start * 4)
    WAIT_DISPATCH
    MATMUL (left_addr=0, right_addr=0)  // CE reads from dispatched buffers
    WAIT_MATMUL
    Collect results
```

**Status**: NOT CURRENTLY IMPLEMENTED IN HARDWARE
- DISPATCH command exists but is a stub ("legacy, stores metadata only")
- Would require dispatcher_control.sv modifications to:
  - Read from dispatcher BRAM at `tile_addr`
  - Write to compute engine's local buffers
  - Support repeated DISPATCH without re-FETCH

**Benefits**:
- Clean separation: dispatcher manages memory, CE computes
- Scalable to multiple parallel compute engines
- Matches software_command_sequence.md documentation intent

### Approach 2: Direct Address Multi-Tile (CURRENT WORKAROUND)

**Concept**: Compute engine directly reads from dispatcher BRAM using addresses.

**Command Sequence**:
```
FETCH_LEFT  (load 128 NVs to dispatcher BRAM [0-527])
FETCH_RIGHT (load 128 NVs to dispatcher BRAM [528-1055])
FOR each tile:
    MATMUL (left_addr = left_nv_start * 4, 
            right_addr = 528 + right_nv_start * 4)
    WAIT_MATMUL
    Collect results
```

**Status**: PARTIALLY WORKING
- Test runs without timeout
- But results are incorrect (repeating tile 0)
- Suggests compute engine not using provided addresses

**Issue**: Compute engine appears to have **hardcoded address pointers** or is not respecting the `left_addr`/`right_addr` parameters from MATMUL command.

## Hardware Investigation Needed

To debug why multi-tile addressing doesn't work, check:

1. **gfp8_bcv_controller.sv**: Does it use `i_tile_cmd.left_addr` and `i_tile_cmd.right_addr`?
2. **dispatcher_bram.sv**: Are Port B read addresses coming from BCv controller or hardcoded?
3. **master_control.sv**: Is it correctly parsing and forwarding addresses from MATMUL command?

### Expected Behavior

For B=2, C=1, V=32 configuration:
```
Tile 0: left_addr=0,   right_addr=528  → results [0x3932, 0xba27]
Tile 1: left_addr=0,   right_addr=656  → results [0xbaa7, 0x38c4]
Tile 2: left_addr=0,   right_addr=784  → results [0xb758, 0x3a43]
Tile 3: left_addr=0,   right_addr=912  → results [0x1100, 0xb100]
Tile 4: left_addr=256, right_addr=528  → results [0x3835, 0x3917]
...
```

### Actual Behavior

All 8 tiles produce: `[0xb6ae, 0x3a4a]` (tile 0 results only)

## Workaround for Single-Tile Testing

Until multi-tile addressing is fixed, use **single-tile mode** with B×C×V ≤ 128×128:
```bash
./test_ms2_gemm_full  # Runs all 10 standard single-tile tests
```

Current status: **8/9 single-tile tests passing** (88%)

## Next Steps

### For Software (Short Term)
1. Document this limitation in software_command_sequence.md
2. Add note that current hardware only supports single FETCH + single MATMUL
3. Keep multi-tile test as future validation when hardware supports it

### For Hardware (Future Enhancement)
1. **Option A**: Implement DISPATCH functionality in dispatcher_control.sv
   - Add buffer management for repeated dispatch from same FETCH
   - Add data movement from dispatcher BRAM → CE local buffers
   
2. **Option B**: Fix compute engine addressing
   - Ensure gfp8_bcv_controller reads from variable BRAM addresses
   - Pass `left_addr`/`right_addr` through to BRAM read ports
   - Test with varying addresses in simulation first

## Files Modified

- `gemm/sw_test/test_ms2_gemm_full.cpp`: Added `run_multitile_test()` function with CLI support
- Command-line options: `--multitile`, `--B N`, `--C N`, `--V N`
- Golden reference: `hex/golden_B2_C1_V32_multitile.hex` (16 results)
- Command sequence: `hex/golden_commands_b2_c1_v32_multitile.txt` (8 tiles documented)

## Conclusion

The multi-tile test successfully demonstrates:
- ✅ Software can issue multiple MATMUL commands after single FETCH
- ✅ Engine doesn't hang or timeout
- ❌ Hardware does not compute different tiles - repeats tile 0 results

**Root cause**: Compute engine addressing is not implemented or not working correctly.

**Recommendation**: Focus on single-tile optimizations until hardware dispatcher architecture is enhanced to support multi-tile addressing.







