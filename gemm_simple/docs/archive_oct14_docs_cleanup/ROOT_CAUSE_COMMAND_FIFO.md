# ROOT CAUSE: Command FIFO Persistence Issue

**Date**: Mon Oct 13, 2025 - 15:27 PDT  
**Status**: ✅ ROOT CAUSE IDENTIFIED

## Problem Summary
- Commands written to FIFO but engine sits idle
- Only produces 1 FP16 result instead of expected B×C=4
- BCV_DIMS reads as 0x0 (no dimensions captured)

## Investigation Trail

### 1. Initial Symptoms
- `cmd_fifo_count = 64` (FULL)
- `mc_state = 0x0` (IDLE)
- `engine_busy = 0`
- Commands ARE written to FIFO (verified with CSR test)

### 2. Critical Discovery
After adding ONE more command:
- FIFO count went: 64 → 48 (net -16 entries)
- **16 entries = 4 commands processed!**
- Engine returned to IDLE

### 3. Root Cause Analysis
Reading `ENGINE_DEBUG = 0x00000030`:
- Decoded: `last_opcode = 0x3`
- **0x3 is NOT a valid MS2.0 opcode!** (should be 0xF0-0xF4)
- Valid opcodes: 0xF0 (FETCH), 0xF1 (DISPATCH), 0xF2 (TILE), 0xF3 (WAIT_DISPATCH), 0xF4 (WAIT_MATMUL)

## ROOT CAUSE

**The command FIFO contains stale/invalid commands from earlier tests that were never cleared!**

- FIFO persists across software resets (bit[4] of CONTROL register)
- Multiple test iterations added commands on top of old ones
- Engine processed 4 commands, hit invalid opcode 0x3, and halted
- 48 stale commands remain in FIFO blocking new valid commands

## Why This Happened

1. **FIFO is persistent** - doesn't clear on `engine_soft_reset`
2. **Earlier tests** used wrong opcodes (0xC, 0x8, 0x3, 0x4 instead of 0xF0-0xF4)
3. **No FIFO flush** mechanism between test iterations
4. **Commands accumulated** over multiple debugging sessions

## Solution Options

### Option 1: Rebuild & Reflash (RECOMMENDED)
```bash
cd /home/dev/Dev/elastix_gemm/gemm
./build_and_flash.sh
```
- Cleanest solution
- Clears all FIFO state
- Ensures known-good starting point

### Option 2: Drain FIFO (Software Workaround)
- Would need to add command to drain/flush FIFO
- Requires RTL modification to add FIFO reset capability
- More complex, not recommended

### Option 3: Power Cycle
- Full FPGA power cycle would clear FIFO
- Requires system reboot
- Less reliable than rebuild

## Verification After Fix

After rebuild/reflash, verify:
```bash
cd sw_test
./check_fifo_debug  # Should show cmd_fifo_count = 0
./test_simple_bcv2  # Should produce 4 results for B=2,C=2,V=2
```

Expected results:
- `cmd_fifo_count = 0` initially
- `mc_state` transitions through states
- `ENGINE_RESULT_COUNT = 4` (B×C = 2×2)
- Result registers populated with FP16 values

## Lessons Learned

1. **FIFO persistence** - Need to document FIFO behavior across resets
2. **Command validation** - Verify opcodes before submission
3. **Test isolation** - Clear state between test iterations
4. **Debug infrastructure** - `last_opcode` register was KEY to diagnosis

## Files Modified This Session

### RTL (Already Correct)
- `elastix_gemm_top.sv` - Result register infrastructure ✓
- `result_fifo_to_bram.sv` - First 4 result capture ✓
- `engine_top.sv` - Command FIFO interface ✓

### Software Tests (Corrected)
- `test_simple_bcv2.cpp` - Fixed register addresses (0x50, 0x54 not 0x30, 0x34) ✓
- `test_bcv2_correct_encoding.cpp` - Proper cmd_tile_s bit packing ✓
- All debug/diagnostic tools created

## Next Action

**REBUILD AND REFLASH TO CLEAR STALE FIFO:**
```bash
cd /home/dev/Dev/elastix_gemm/gemm
./build_and_flash.sh
cd sw_test
./test_simple_bcv2
```

Expected: Full success with 4 FP16 results!
