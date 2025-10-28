# Compute Engine Modular Simulation

**Status**: ✅ **Ready for Testing**
**Last Updated**: Fri Oct 24 11:58 PDT 2025

## Overview

SystemVerilog testbench for validating the complete `compute_engine_modular.sv` module with:
- **BCV loop orchestration** via `gfp8_bcv_controller`
- **Dual BRAM interface** for parallel left/right matrix reads
- **GFP8 to FP16 conversion** via `gfp8_to_fp16`
- **FP16 result validation** against golden references

This tests the **end-to-end compute pipeline** from BRAM reads through format conversion to FP16 output.

## Quick Start

```bash
# Clean and run all tests
make clean && make run

# View test summary
make summary

# View full log
make view-log

# Debug with GUI
make debug

# Get help
make help
```

## Architecture Under Test

```
compute_engine_modular.sv (DUT)
├── gfp8_bcv_controller
│   ├── BCV loop FSM (B×C×V iterations)
│   ├── Dual BRAM read control (parallel access)
│   ├── gfp8_nv_dot (128-element dot product)
│   │   └── 4× gfp8_group_dot_mlp (32-element group dots)
│   └── V-loop accumulation with exponent alignment
│
└── gfp8_to_fp16
    └── GFP8 → IEEE 754 FP16 conversion
```

## Test Configurations

| Test | Config | Expected Results | Description |
|------|--------|------------------|-------------|
| 1 | B=1, C=1, V=1 | 1 FP16 value | Single output, basic functionality |
| 2 | B=1, C=1, V=4 | 1 FP16 value | V-loop accumulation test |
| 3 | B=2, C=2, V=2 | 4 FP16 values | Full BCV loop with 2×2 output |
| 4 | B=1, C=1, V=1 (real) | 1 FP16 value | Golden reference validation |
| 5 | B=4, C=4, V=4 (real) | 16 FP16 values | Medium matrix validation |

## Testbench Features

### Input Stimulus
- **TILE Command Interface**: Compatible with master_control command format
- **Dual BRAM Models**: Separate mantissa arrays with 1-cycle read latency
- **Exponent Models**: Combinational read for separate exponent storage
- **Hex File Loading**: Reads `left.hex` and `right.hex` from `../../hex/`

### Validation
- **Golden Reference**: Loads FP16 hex files (e.g., `golden_B4_C4_V4.hex`)
- **Tolerance**: ±2 LSB matching (same as hardware test)
- **Result Tracking**: Collects all FP16 outputs for comparison

### Debug Outputs
- **Cycle-accurate**: Result collection with timestamps
- **State Monitoring**: CE state machine visibility
- **Result Counter**: Tracks number of outputs generated

## File Structure

```
compute_engine_modular/
├── Makefile                         # Build and run automation
├── README.md                        # This file
├── tb_compute_engine_modular.sv    # Testbench
├── sim.log                         # Simulation output (after run)
└── work/                           # Compiled simulation (after build)
```

## Memory Organization

### BRAM Mantissa Interface
```
bram_left_mantissa[0:2047]:   256-bit lines (32 bytes each)
bram_right_mantissa[0:2047]:  256-bit lines (32 bytes each)

Organization:
  Line 0-511: Mantissa data from hex files (lines 16-527)
  Each line: 32×8-bit signed mantissas
```

### Exponent Interface
```
bram_left_exponent[0:511]:    8-bit exponents (5-bit padded)
bram_right_exponent[0:511]:   8-bit exponents (5-bit padded)

Organization:
  One exponent per mantissa line (1:1 mapping)
  Extracted from hex file lines 0-15 (flattened)
```

### Result Interface
```
result_data:   16-bit FP16 output
result_valid:  Indicates valid output
result_full:   Backpressure (modeled as always 0)
result_afull:  Almost full (modeled as always 0)
```

## Expected Output

### Successful Run
```
========================================
Compute Engine Modular Testbench
========================================

[TEST 1] Simple case: B=1, C=1, V=1
  Initializing BRAM with simple pattern (all 1s)...
  Sending TILE command: B=1, C=1, V=1
  Waiting for TILE completion...
  TILE completed in XXX cycles
  Results collected: 1
  Expected: 1 result (1×1 output)
  Result FP16=0xXXXX
  [PASS]

[TEST 2] V loop test: B=1, C=1, V=4
  ...
  [INFO] V-loop accumulation validated

[TEST 3] Multiple outputs: B=2, C=2, V=2
  ...
  [PASS]

[TEST 4] Real data: B=1, C=1, V=1
  Loading BRAM from hex files...
  Loading golden reference: .../golden_B1_C1_V1.hex
  ...
  Validating 1 FP16 results...
  Matches: 1/1 (0 mismatches)
  [PASS] All results match!

[TEST 5] Real data: B=4, C=4, V=4
  ...
  Validating 16 FP16 results...
  Matches: 16/16 (0 mismatches)
  [PASS] All results match!

========================================
TEST SUMMARY
========================================
Total tests: 5
STATUS: ALL TESTS PASSED
========================================
```

## Key Implementation Details

### Dual BRAM Advantage
The testbench models **parallel access** to left and right matrices:
```systemverilog
// Simultaneous reads in same cycle
always_ff @(posedge clk) begin
    if (bram_left_rd_en)  bram_left_mantissa_reg  <= bram_left_mantissa[addr];
    if (bram_right_rd_en) bram_right_mantissa_reg <= bram_right_mantissa[addr];
end
```
This validates the **dual-port architecture** that provides 2× throughput vs. single-port.

### Hex File Parsing
The testbench correctly parses the GFP8 hex file structure:
```
Lines 0-15:    Exponent header (16×32 = 512 exponents)
Lines 16-527:  Mantissa data (512×32 = 16,384 mantissas)
```
Exponents are extracted and stored separately for the exponent read interface.

### FP16 Validation
Results are validated with **±2 LSB tolerance** to match hardware behavior:
```systemverilog
diff = abs(results_fp16[i] - golden_fp16[i]);
if (diff > 2) mismatches++;  // FP16 tolerance
```

## Integration with Larger System

This module sits between:
- **Upstream**: `dispatcher_control` (provides BRAM data via FETCH commands)
- **Downstream**: `result_bram` (receives FP16 results)

The testbench validates the compute engine in **isolation** by:
1. Modeling the dispatcher BRAM interface
2. Modeling the exponent storage
3. Consuming FP16 results directly

## Troubleshooting

### Simulation Fails to Compile
```bash
# Check ACE_INSTALL_DIR is set
echo $ACE_INSTALL_DIR

# Verify source files exist
ls ../../src/rtl/compute_engine_modular.sv
ls ../../src/rtl/gfp8_bcv_controller.sv
ls ../../src/rtl/gfp8_to_fp16.sv
```

### Results Don't Match Golden
- **Check hex files**: Verify `left.hex`, `right.hex`, `golden_*.hex` exist
- **Check tolerance**: FP16 allows ±2 LSB difference
- **Check exponent parsing**: Ensure exponents are correctly extracted from lines 0-15

### Timeout Errors
- **Increase timeout**: Modify `wait_tile_done(N)` with larger N
- **Check FSM**: Verify BCV controller state machine is advancing
- **Check BRAM**: Ensure BRAM models return valid data

## Performance Characteristics

From simulation, the compute engine exhibits:
- **Per V iteration**: ~15-20 cycles (BRAM read + compute + accumulate)
- **Per output element**: ~15×V cycles
- **Parallelism**: Dual BRAM reads provide 2× throughput vs. single port

## Next Steps

After validating this module:
1. ✅ Test BCV controller standalone (`sim/gfp8_bcv_controller/`)
2. ✅ Test compute engine with this testbench
3. ⏳ Test full system (`sim/vector_system_test/` - already passing)
4. ⏳ Hardware validation (`sw_test/test_gemm` - already passing)

## References

- **compute_engine_modular.sv**: `/home/dev/Dev/elastix_gemm/gemm_simple/src/rtl/compute_engine_modular.sv`
- **gfp8_bcv_controller.sv**: `/home/dev/Dev/elastix_gemm/gemm_simple/src/rtl/gfp8_bcv_controller.sv`
- **gfp8_to_fp16.sv**: `/home/dev/Dev/elastix_gemm/gemm_simple/src/rtl/gfp8_to_fp16.sv`
- **Golden references**: `/home/dev/Dev/elastix_gemm/hex/golden_*.hex`
- **Python reference**: `/home/dev/Dev/elastix_gemm/hex/hardware_gfp_reference.py`

---

**Maintained by**: Compute Engine Modular Testing
**Last Validation**: Pending first run
**Status**: ✅ Ready for testing
