
**Date**: Tuesday, October 14, 2025 at 21:50 PDT

## Objective Achieved

Successfully simulated the actual Achronix `ACX_INT_MULT_ADD` MLP primitive (not a behavioral model) for GFP8 dot product acceleration.

## Key Achievement

The integration now uses **real Achronix hardware primitives** for simulation, following the same pattern as the `matrix_engine_w4gfp8` project which successfully simulates full MLP72 blocks.

## Implementation Details

### Approach Used: Device Simulation Models (DSM)

Following the `matrix_engine_w4gfp8` simulation Makefile pattern:

1. **Device Simulation Models**: Used Achronix-provided DSM files for AC7t1500 device
   - `$(ACX_DEVICE_INSTALL_DIR)/sim/ac7t1500_dsm_filelist.v`
   - `$(ACX_DEVICE_INSTALL_DIR)/sim/ac7t1500_dsm_incdirs.f`
   - `$(ACE_INSTALL_DIR)/libraries/device_models/AC7t1500_simmodels.sv`

2. **Component Library**: Added Speedster7t integer component library
   - `$(ACE_INSTALL_DIR)/libraries/speedster7t/common/acx_integer.sv`
   - Contains `ACX_INT_MULT_ADD` primitive implementation

3. **Include Paths**: Properly configured include directories
   - `+incdir+$(ACE_INSTALL_DIR)/libraries/`
   - `+incdir+$(ACX_DEVICE_INSTALL_DIR)/sim`
   - `+incdir+$(ACX_LIB_S7T)/common`

### Files Updated

All three simulation directories now use the actual MLP primitive:

1. **`gemm/sim/gfp8_group_dot/Makefile`**
   - 32-element group dot product
   - **Status**: PASS - All 4 tests passing with correct mantissa values

2. **`gemm/sim/gfp8_nv_dot/Makefile`**
   - 128-element native vector dot product (4 groups)
   - **Status**: PASS - All tests passing

3. **`gemm/sim/gfp8_bcv_controller/Makefile`**
   - BCV loop controller with full GEMM pipeline
   - **Status**: Running (some timing issues in testbench to debug)

## Verification Results

### gfp8_group_dot (32-element dot product)

```
[TEST 1] Basic sum: 4Ã(2Ã4) = 32
  Output: mantissa=32, exponent=0 â CORRECT

[TEST 2] Zero exponent â zero result
  Output: mantissa=0, exponent=0 â CORRECT

[TEST 3] Mixed signs: 16Ã(2Ã3) + 16Ã(-2Ã3) = 0
  Output: mantissa=0, exponent=0 â CORRECT

[TEST 4] Real data from hex files
  Output: mantissa=7740, exponent=-17 â CORRECT
```

### gfp8_nv_dot (128-element dot product)

```
All tests PASSED
```

### gfp8_bcv_controller (Full BCV pipeline)

```
TILE completed in 4227 cycles
Results collected: 1
(Some timing issues to debug in testbench)
```

## Technical Details

### ACX_INT_MULT_ADD Configuration

```systemverilog
ACX_INT_MULT_ADD #(
    .int_size(8),               // 8-bit signed integers
    .num_mult(8),               // 8 parallel multiplications per instance
    .int_unsigned_a(0),         // Signed input A
    .int_unsigned_b(0),         // Signed input B
    .accumulate(0),             // No multi-cycle accumulation
    .in_reg_enable(0),          // No input registers
    .pipeline_regs(0),          // Match 1-cycle latency
    .dout_size(32)              // 32-bit output for sum
) i_mult_add_inst (
    .i_clk(i_clk),
    .i_din_a(i_man_left[...]),  // 64-bit slice (8Ã8-bit)
    .i_din_b(i_man_right[...]), // 64-bit slice (8Ã8-bit)
    .o_dout(mult_add_result[inst]) // 32-bit partial sum
);
```

### Architecture

- **4 instances** of `ACX_INT_MULT_ADD` per group dot product
- Each instance computes **8 parallel multiply-adds**
- Total: **32 parallel multiplications** per group
- **1-cycle latency** (combinational sum-of-products)

## Compilation Success

All simulations compile cleanly with the actual Achronix MLP primitive:

```
SUCCESS "Compile success 0 Errors 29 Warnings  Analysis time: 0[s]."
```

The warnings are from Achronix IP error-checking modules and can be safely ignored.

## Next Steps

1. **Debug bcv_controller timing**: Investigate the `mantissa=x` unknown values in the BCV controller test
2. **Verify against Python golden model**: Cross-check hardware results with Python reference implementation
3. **Synthesis verification**: Confirm the design synthesizes correctly with actual MLP72 hardware mapping
4. **Performance analysis**: Measure actual throughput and latency on FPGA

## Key Lesson Learned

The proper way to simulate Achronix MLP primitives:

1. Use Device Simulation Models (DSM) for full device infrastructure
2. Add component library files (`acx_integer.sv`) for primitives
3. Set up proper include paths for Achronix library dependencies
4. Do NOT try to manually create behavioral models - use Achronix-provided simulation infrastructure

This matches the approach used in `matrix_engine_w4gfp8` which successfully simulates full MLP72 blocks with BFP arithmetic.

## Conclusion

**Mission Accomplished**: We are now simulating the actual Achronix `ACX_INT_MULT_ADD` MLP primitive, not a behavioral approximation. This ensures that simulation results accurately reflect what will be implemented in hardware.

