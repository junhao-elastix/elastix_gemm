# Two-Stage Circular Buffer Validation Test

## Overview
Modified test_gemm.cpp to implement a rigorous two-stage validation of the circular buffer mechanism.

## Test Strategy

### Stage 1: Individual Tests (Baseline)
**Purpose:** Establish golden reference with traditional reset-per-test approach

**Procedure:**
1. For each of 10 tests:
   - **Reset both pointers:** rd_ptr=0, wr_ptr=0
   - Run GEMM operation
   - Validate results against golden reference
   - **Collect results** into `results_stage1[]` array
2. All 10 tests must pass for Stage 2 to proceed

**Register Operations:**
```cpp
gemm_device.mmio_write32(0, 0x230, 0x00000000);  // REG_RD_PTR = 0
gemm_device.mmio_write32(0, 0x22C, 0x00000000);  // ENGINE_WRITE_TOP = 0 (triggers wr_ptr reset)
```

### Stage 2: Batched Tests (Circular Buffer Validation)
**Purpose:** Test persistent circular buffer with batched reads

**Procedure:**
1. Initial reset: rd_ptr=0, wr_ptr=0
2. Run 10 tests in 5 batches of 2 tests each:
   - **NO reset between tests within a batch**
   - Pointers persist across tests
   - Read accumulated results after each batch
   - **Collect results** into `results_stage2[]` array
3. Update rd_ptr after each batch read

**Example - Batch 1:**
```
Test 1 (B1_C1_V1): 1 result
  Before: wr_ptr=0, rd_ptr=0, used=0
  After:  wr_ptr=1, rd_ptr=0, used=1

Test 2 (B2_C2_V2): 4 results
  Before: wr_ptr=1, rd_ptr=0, used=1
  After:  wr_ptr=5, rd_ptr=0, used=5

[Batch Read] Read 5 accumulated results (1+4)
  Update rd_ptr: 0 -> 5
  New state: wr_ptr=5, rd_ptr=5, used=0
```

### Final Validation
**Purpose:** Prove circular buffer works correctly

**Comparison:**
```cpp
if (results_stage1[i] == results_stage2[i]) {
    // For all i = 0 to total_results
    SUCCESS! Circular buffer validated!
}
```

If Stage 1 == Stage 2 element-by-element, the circular buffer mechanism is correct!

## Key Implementation Details

### Pointer Reset Mechanism
**Critical:** Both pointers must be reset in Stage 1 to avoid wraparound issues

```cpp
// Reset rd_ptr (host-controlled)
gemm_device.mmio_write32(0, 0x230, 0x00000000);

// Reset wr_ptr (hardware-controlled) via write_top_reset signal
gemm_device.mmio_write32(0, 0x22C, 0x00000000);
```

**RTL Behavior:**
```systemverilog
// elastix_gemm_top.sv:703
assign result_write_top_reset = write_strobes[ENGINE_WRITE_TOP] && 
                                (user_regs_write[ENGINE_WRITE_TOP] == 32'h0);

// result_fifo_to_simple_bram.sv:87-88
end else if (i_write_top_reset) begin
    wr_ptr <= 13'd0;  // Hardware resets wr_ptr
```

### Register Map
| Register | Offset | Access | Description |
|----------|--------|--------|-------------|
| ENGINE_WRITE_TOP | 0x22C | RW | Write 0x0 triggers wr_ptr reset |
| REG_RD_PTR | 0x230 | RW | Host read pointer (13-bit, 0-8191) |
| REG_WR_PTR | 0x234 | RO | Hardware write pointer (13-bit, 0-8191) |
| REG_USED_ENTRIES | 0x238 | RO | Available results (14-bit, 0-8192) |

### Result Collection
Both stages collect FP16 results by unpacking from BRAM:
- Read complete 32-byte lines (16 FP16 values per line)
- Extract individual FP16 values at correct byte offsets
- Append to stage-specific result arrays

## Expected Output

```
================================================================
STAGE 1: Individual Tests (Baseline with Reset)
================================================================

Test 1/10: B1_C1_V1
  [Stage 1] Reset: rd_ptr=0, wr_ptr=0
  [PASS] B1_C1_V1

...

[Stage 1 Complete] Tests: 10/10 passed
[Stage 1 Complete] Collected: 677 FP16 results

================================================================
STAGE 2: Batched Tests (Circular Buffer - No Reset)
================================================================

[Stage 2 Init] Reset: rd_ptr=0, wr_ptr=0

=== BATCH 1: Tests 1-2 ===

--- Test 1/10: B1_C1_V1 ---
  [Before] wr_ptr=0, rd_ptr=0, used=0
  [After] wr_ptr=1, rd_ptr=0, used=1 (expected +1)

--- Test 2/10: B2_C2_V2 ---
  [Before] wr_ptr=1, rd_ptr=0, used=1
  [After] wr_ptr=5, rd_ptr=0, used=5 (expected +4)

[Batch Read] Reading 5 accumulated results...
[Batch Complete] rd_ptr updated to 5, used_entries now 0

...

[Stage 2 Complete] Collected: 677 FP16 results

================================================================
FINAL VALIDATION: Comparing Stage 1 vs Stage 2
================================================================
Comparing 677 results...

================================================================
SUCCESS! All 677 results match!
✓ Circular buffer mechanism validated!
✓ Stage 1 (individual with reset) == Stage 2 (batched persistent)
================================================================
```

## Usage

```bash
cd /home/workstation/elastix_gemm/gemm/sw_test
make test_gemm
./test_gemm              # Run two-stage validation
./test_gemm -v           # Verbose mode
./test_gemm -B 4 -C 4 -V 4  # Single test mode (old behavior)
```

## Validation Checklist

✓ Stage 1: All 10 tests pass with golden reference  
✓ Stage 2: wr_ptr advances correctly across tests  
✓ Stage 2: rd_ptr updates correctly after reads  
✓ Stage 2: used_entries calculation accurate  
✓ Final: results_stage1 == results_stage2 (element-by-element)  
✓ Circular buffer wraps at 8192 (if tested with larger batches)

## Notes
- Backup saved as test_gemm.cpp.backup
- Single-test mode still available via `-B -C -V` flags
- Focus on circular buffer mechanism validation
- Both stages use identical GEMM operations (same matrices, same configs)
