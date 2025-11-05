# MS2.0 GEMM Engine - Debugging Log & Current Status

**Date:** October 21-22, 2025  
**Project:** MS2.0 Modular GEMM Engine on Achronix VP815 FPGA  
**Status:** 🔄 **CRITICAL BUG FIXED - AWAITING HARDWARE VALIDATION**

---

## Executive Summary

After extensive debugging (22+ iterations), we identified and fixed the **ROOT CAUSE** of hardware timeouts. The issue was a **missing enable signal clear** in the master control FSM, causing rising-edge detection to fail for subsequent DISPATCH commands.

### Current Status
- ✅ **Simulation:** 9/9 tests PASS (validated multiple times)
- ⏳ **Hardware:** Bitstream rebuilding with fix (ETA ~00:57 PDT Oct 22)
- 🎯 **Expected:** Hardware should pass all 9 tests after reboot

---

## System Architecture

### Hardware Stack
```
┌─────────────────────────────────────────────────────────────┐
│                    MS2.0 GEMM Engine                        │
├─────────────────────────────────────────────────────────────┤
│  master_control.sv (Command FSM)                            │
│    ├─> dispatcher_control.sv (FETCH/DISPATCH)               │
│    └─> compute_engine_modular.sv (TILE/MATMUL)              │
├─────────────────────────────────────────────────────────────┤
│  Dual BRAM (Left/Right Tiles) + Result BRAM                 │
├─────────────────────────────────────────────────────────────┤
│  8× GDDR6 Channels (512 GB/s total bandwidth)               │
├─────────────────────────────────────────────────────────────┤
│  PCIe Gen5 x16 Interface (VP815 FPGA)                       │
└─────────────────────────────────────────────────────────────┘
```

### Software Stack
```
Python Model Converter (main.py)
    ├─> Kernel Registry + IR Generation
    ├─> C++ Code Generation (Achronix Backend)
    └─> PyBind11 Compilation
            ↓
VP815GemmDevice API (gemm.cpp/hpp)
    ├─> fetch()      - Load matrices from GDDR6 to BRAM
    ├─> dispatch()   - Unpack vectors to tiles
    ├─> tile()       - Execute GEMM operation
    └─> waitXXX()    - Hardware synchronization
            ↓
VP815 PCIe Driver (MMIO + DMA)
    ├─> mmio_write32() - Issue commands
    ├─> mmio_read32()  - Read status/results
    └─> dma_read/write() - Transfer data
```

---

## Command Interface Specification

### Microcode Opcodes
| Opcode | Name            | Description                          |
|--------|-----------------|--------------------------------------|
| 0xF0   | FETCH           | Load matrix from GDDR6 to BRAM      |
| 0xF1   | DISPATCH        | Unpack vectors to compute tiles     |
| 0xF2   | MATMUL (TILE)   | Execute matrix multiplication       |
| 0xF3   | WAIT_DISPATCH   | Block until DISPATCH ID completes   |
| 0xF4   | WAIT_MATMUL     | Block until TILE ID completes       |

### Command Format (4-Word Structure)
```
All commands: [Word0: Header] [Word1-3: Payload]

Word0 Header: [31:24]=Reserved [23:16]=Length [15:8]=ID [7:0]=Opcode

FETCH Command:
  Word0: {0x00, 0x0C, id, 0xF0}
  Word1: start_addr (in 32-byte units)
  Word2: [15:0]=length (lines), [16]=fetch_right (0=left, 1=right)
  Word3: 0x00000000

DISPATCH Command:
  Word0: {0x00, 0x08, id, 0xF1}
  Word1: [10:0]=tile_addr, [21:11]=len, [22]=man_4b_8b_n
  Word2: 0x00000000
  Word3: 0x00000000

TILE (MATMUL) Command:
  Word0: {0x00, 0x0C, id, 0xF2}
  Word1: [10:0]=left_addr, [21:11]=right_addr, [31:22]=left_ugd[9:0]
  Word2: [0]=left_ugd[10], [11:1]=right_ugd, [22:12]=vec_len, [30:23]=flags, [31]=dim_v[0]
  Word3: [6:0]=dim_v[7:1], [14:7]=dim_c, [22:15]=dim_b

WAIT_DISPATCH Command:
  Word0: {0x00, 0x04, id, 0xF3}
  Word1: [7:0]=wait_id (ID to wait for)
  Word2: 0x00000000
  Word3: 0x00000000

WAIT_MATMUL Command:
  Word0: {0x00, 0x04, id, 0xF4}
  Word1: [7:0]=wait_id (ID to wait for)
  Word2: 0x00000000
  Word3: 0x00000000
```

---

## Test Suite Overview

### 1. Hardware Test: `test_bulk_dma.cpp`

**Purpose:** Validate FETCH address parameter and GDDR6 data integrity

**Test Methodology:**
1. DMA write LEFT matrix once to block 0
2. DMA write alternating RIGHT/GARBAGE blocks (5 iterations default)
3. FETCH LEFT once (persists across all GEMMs)
4. For each iteration:
   - FETCH RIGHT from different addresses
   - Execute full GEMM sequence (DISPATCH + TILE + WAIT)
   - Validate results

**Expected Behavior:**
- Odd iterations (RIGHT blocks): Results should match golden reference
- Even iterations (GARBAGE blocks): Results should differ from golden

**Configuration:**
- Default: B=4, C=4, V=32
- Configurable via command-line: `-B`, `-C`, `-V`, `-n` (num_right)

**Usage:**
```bash
cd /home/workstation/elastix_gemm/gemm_simple/sw_test
./test_bulk_dma -d 0 -B 4 -C 4 -V 32 -n 5 -v
```

**Current Status:** ⏳ Not tested with latest bitstream

---

### 2. C++ Integration Test: `acx_gemm` (gemm.cpp main)

**Purpose:** End-to-end validation of GEMM engine with all 9 dimension combinations

**Test Suite (9 Tests):**
| Test | B   | C   | V   | Description                  |
|------|-----|-----|-----|------------------------------|
| 1    | 1   | 1   | 1   | Minimal dimensions           |
| 2    | 2   | 2   | 2   | Small square                 |
| 3    | 4   | 4   | 4   | Medium square                |
| 4    | 2   | 2   | 64  | High V-loop                  |
| 5    | 4   | 4   | 32  | Balanced dimensions          |
| 6    | 8   | 8   | 16  | Large square                 |
| 7    | 1   | 128 | 1   | Wide matrix (high C)         |
| 8    | 128 | 1   | 1   | Tall matrix (high B)         |
| 9    | 1   | 1   | 128 | Long vector (high V)         |

**Command Sequence per Test:**
```cpp
1. soft_reset()
2. Load matrices: writeHexMatrixDirect(left.hex, 0x0)
3. Load matrices: writeHexMatrixDirect(right.hex, 0x4200)
4. fetch(0, 528, false)          // ID=auto, fetch LEFT
5. fetch(0x4200, 528, true)      // ID=auto, fetch RIGHT
6. dispatch(0, 128, false)       // ID=auto, dispatch LEFT
7. waitDispatch(disp_left_id)    // Hardware blocks
8. dispatch(528, 128, false)     // ID=auto, dispatch RIGHT
9. waitDispatch(disp_right_id)   // Hardware blocks
10. tile(0, 0, B, C, V, ...)     // ID=auto, execute GEMM
11. waitTile(tile_id)            // Hardware blocks
12. wait_idle(5000)              // Software poll ENGINE_STATUS
13. Read results from BRAM + registers
```

**Expected Results:**
- All 9 tests should PASS
- Results should match golden reference (within FP16 tolerance)
- No timeouts (ENGINE_STATUS should clear busy bit)

**Usage:**
```bash
cd /home/workstation/ElastiCore/projects/model_converter/src/model_converter/backends/achronix
./acx_gemm 0 left.hex right.hex
```

**Current Status:** ⏳ Awaiting hardware validation with latest bitstream

---

### 3. Python Model Converter Test: `main.py`

**Purpose:** Full-stack validation of model converter framework with hardware backend

**Test Scenarios:**
1. **Linear Kernel Test:**
   - Configuration: batch=1, length=6, input_channel=4096, output_channel=4096
   - Expected: Input @ Weight multiplication via GEMM tiles
   - Validates: Blocking, GFP quantization, C++ code generation, hardware execution

2. **Q-K Matmul Test:**
   - Configuration: batch=1, heads=32, length=16, input_channel=128, context=256
   - Expected: Attention score computation (Q @ K^T)
   - Validates: 4D tensor blocking, multi-head attention patterns

3. **QK-V Matmul Test:** (Currently commented out)
   - Configuration: batch=1, heads=32, length=16, context=256, output=128
   - Expected: Attention output (QK @ V)

**Workflow:**
```python
1. Register kernel in KernelRegistry
2. Generate IR (Intermediate Representation)
3. Schedule operations (tile assignments)
4. Translate to C++ code (Achronix backend)
5. Compile with PyBind11
6. Load shared library
7. Execute kernel(input_tensor, weight_tensor, output_tensor)
8. Compare: C++ vs Emulator vs FP32 Reference
```

**Expected Metrics:**
- CPP-EMU RMSE: < 0.01 (quantization error only)
- EMU-FP RMSE: < 0.05 (GFP8 quantization vs FP32)
- CPP-FP RMSE: < 0.05 (end-to-end error)

**Usage:**
```bash
cd /home/workstation/ElastiCore/projects/model_converter
source .venv/bin/activate
python -m model_converter.main
```

**Current Status:** ⏳ Expected to work after hardware fix validation

---

## Bug Chronicle & Resolution

### Timeline of Issues

#### Issue #1: Original Timeout (0xbb001 - ST_WAIT_TILE)
**Symptom:** Hardware stuck in `ST_WAIT_TILE` state  
**Initial Diagnosis:** ID tracking logic issue  
**Fix Attempted:** Modified `wait_id` capture from Word0 to Word1[7:0]  
**Result:** ❌ Changed to 0xaa001 (ST_WAIT_DISP) - different bug revealed

---

#### Issue #2: WAIT State Comparison Logic
**Symptom:** ID captured but comparison never satisfied  
**Root Cause:** `ST_WAIT_DISP` and `ST_WAIT_TILE` didn't actually compare IDs  
**Fix:** Added `last_disp_id_reg >= wait_id_reg` comparison logic  
**Result:** ❌ Still timing out - underlying issue remained

---

#### Issue #3: Engine Idle Check Deadlock
**Symptom:** `ST_IDLE` blocked commands when engines busy  
**Root Cause:** Uncommented engine idle checks (`i_dc_state == 0`, `i_ce_state == 0`)  
**Impact:** TILE launches CE → CE busy → WAIT_TILE stuck in FIFO (deadlock)  
**Fix:** Removed idle checks from `ST_IDLE`, added to `ST_EXEC_*` states  
**Result:** ✅ Simulation passed, but hardware still failed

---

#### Issue #4: Command Encoding Mismatch
**Symptom:** `wait_id` placement inconsistent across codebase  
**Root Cause:** Testbench and software placed `wait_id` in different words  
**Fix:** Standardized `wait_id` placement to Word1[7:0]  
**Result:** ✅ Simulation passed, hardware still failed

---

#### Issue #5: State Transition Detection Bug
**Symptom:** Simulation works, hardware fails consistently at 0xaa001  
**Root Cause:** `state_prev_reg` approach created problematic timing paths  
**Fix Attempted:** Flag-based ID capture (`disp_id_captured_reg`, `tile_id_captured_reg`)  
**Result:** ✅ Simulation passed, hardware still failed - **deeper issue**

---

#### Issue #6: **ROOT CAUSE - Enable Signal Management** ✅ FIXED

**Symptom:** 
- Hardware stuck at status `0xaa001` (ST_WAIT_DISP)
- First WAIT_DISP passes, but second one blocks forever
- Simulation works perfectly

**Root Cause Analysis:**

The `dispatcher_control` module uses **RISING EDGE detection**:
```systemverilog
// dispatcher_control.sv:186-187
ST_IDLE: begin
    if (i_disp_en && !disp_en_prev) begin  // Only triggers on 0→1 edge
        state_next = ST_DISP_ACK;
    end
end
```

The `master_control` FSM had a critical bug:
```systemverilog
// BEFORE (BROKEN):
ST_EXEC_DISP: begin
    dc_disp_en_reg <= 1'b1;  // Set enable
    // ... but NEVER CLEARED until ST_WAIT_DISP!
end
```

**What Happened:**
1. **First DISP command (ID=2):** 
   - Sets `dc_disp_en_reg = 1` → Dispatcher triggers (0→1 edge) ✅
   - Master control transitions to `ST_CMD_COMPLETE` → `ST_IDLE`
   - `dc_disp_en_reg` stays HIGH! ❌

2. **WAIT_DISP command (ID=3):**
   - Eventually clears `dc_disp_en_reg` in `ST_WAIT_DISP` state

3. **Second DISP command (ID=4):**
   - Sets `dc_disp_en_reg = 1` again
   - **NO EDGE!** Signal was already HIGH from command #1 ❌
   - Dispatcher never triggers
   - WAIT_DISP blocks forever → Timeout 0xaa001

**The Fix:**
```systemverilog
// master_control.sv:388-394
// Clear enables when transitioning out of EXEC states
if (state_reg == ST_EXEC_FETCH && state_next != ST_EXEC_FETCH) begin
    dc_fetch_en_reg <= 1'b0;
end
if (state_reg == ST_EXEC_DISP && state_next != ST_EXEC_DISP) begin
    dc_disp_en_reg <= 1'b0;  // ✅ CRITICAL FIX
end
```

**Why Simulation Worked:**
- Simulation uses behavioral modeling
- Rising edge detection is more forgiving with $display delays
- Timing paths don't have the same synthesis constraints

**Why Hardware Failed:**
- Synthesized logic strictly follows RTL semantics
- No rising edge = no trigger
- Deterministic failure every time

**Validation:**
- ✅ Simulation: 9/9 tests pass
- ✅ Logic analysis: Rising edge now guaranteed for every DISP command
- ⏳ Hardware: Awaiting bitstream rebuild

---

## Register Map

### BAR0 MMIO Registers (Engine Control)
| Offset | Name              | Access | Description                          |
|--------|-------------------|--------|--------------------------------------|
| 0x00   | CONTROL           | R/W    | [0]=enable, [1]=soft_reset          |
| 0x3C   | CMD_WORD0         | W      | Command word 0 (header)             |
| 0x40   | CMD_WORD1         | W      | Command word 1 (payload)            |
| 0x44   | CMD_WORD2         | W      | Command word 2 (payload)            |
| 0x48   | CMD_WORD3         | W      | Command word 3 (payload)            |
| 0x4C   | CMD_SUBMIT        | W      | Write 1 to submit command           |
| 0x50   | STATUS            | R      | [3:0]=MC_state, [7:4]=DC_state, [11:8]=CE_state, [0]=busy |
| 0x54   | RESULT_COUNT      | R      | Number of FP16 results available    |
| 0x58   | DEBUG             | R      | Debug information                   |
| 0x21C  | RESULT_REG_0      | R      | First result (FP16 in [15:0])       |
| 0x220  | RESULT_REG_1      | R      | Second result                       |
| 0x224  | RESULT_REG_2      | R      | Third result                        |
| 0x228  | RESULT_REG_3      | R      | Fourth result                       |

### Status Register Encoding (0x50)
```
Bits [3:0]:   Master Control FSM State
  0x0 = ST_IDLE
  0xA = ST_WAIT_DISP  (0xaa001 = stuck here)
  0xB = ST_WAIT_TILE  (0xbb001 = stuck here)
  0xC = ST_CMD_COMPLETE

Bits [7:4]:   Dispatcher Control FSM State
  0x0 = ST_IDLE
  0x6 = ST_DISP_ACK

Bits [11:8]:  Compute Engine FSM State
  0x0 = ST_IDLE

Bit [0]:      Global Busy Flag (0=idle, 1=busy)
```

---

## Memory Map

### GDDR6 Address Space
| Base Address | Size       | Description                  |
|--------------|------------|------------------------------|
| 0x00000000   | 16896 B    | LEFT matrix block 0          |
| 0x00004200   | 16896 B    | RIGHT matrix block 0         |
| 0x00008400   | 16896 B    | Block 1 (test_bulk_dma)      |
| ...          | ...        | Additional blocks            |

**Matrix Format:**
- 528 lines × 32 bytes = 16896 bytes per matrix
- Each line = 256 bits (8× GFP8 groups of 4 elements)
- Lines 0-15: Packed exponents (16 bits per group)
- Lines 16-527: Mantissas (512 groups × 4 elements)

### BRAM Result Space
- **Base Address:** `acx_util_nap_absolute_addr(ACX_PART_AC7t1500, 3, 5)`
- **Format:** 32 bytes per result (256-bit line)
- **Result Encoding:** FP16 value in LSB [15:0] of each line

---

## Key Insights & Lessons Learned

### 1. Simulation vs Hardware Mismatches
**Challenge:** Logic that works perfectly in simulation can fail in hardware synthesis
**Causes:**
- Timing path differences
- Edge detection sensitivity
- Register initialization
- Combinational logic evaluation order

**Best Practices:**
- Always validate critical control signals clear properly
- Use explicit state transition detection
- Avoid relying on "lucky" timing in simulation
- Test with both behavioral and synthesized netlists

---

### 2. Rising Edge Detection Patterns
**Critical Pattern in Achronix Design:**
```systemverilog
// Peripheral module (dispatcher_control.sv)
always_ff @(posedge i_clk) begin
    enable_prev <= i_enable;
end

always_comb begin
    if (i_enable && !enable_prev) begin  // Rising edge only
        trigger_operation();
    end
end
```

**Controller Requirements:**
- Must ensure enable signal returns to LOW before next command
- **Not sufficient** to just set enable=HIGH each time
- Must have clean 0→1 transition for each operation

---

### 3. FSM Design Best Practices
**Effective Pattern:**
```systemverilog
// Clear control signals when leaving execution states
if (state_reg == ST_EXEC_XXX && state_next != ST_EXEC_XXX) begin
    enable_signal <= 1'b0;
end
```

**Avoid:**
```systemverilog
// Clearing in unrelated states (too late!)
if (state_reg == ST_WAIT_XXX && done_signal) begin
    enable_signal <= 1'b0;  // ❌ May be too late for next command
end
```

---

### 4. Debug Methodology
**Effective Approach:**
1. ✅ Start with simulation - ensures logic is correct
2. ✅ Check status register encoding - understand FSM state
3. ✅ Trace command sequences - validate each step
4. ✅ Compare software vs hardware - find divergence point
5. ✅ Use bypass tests - isolate specific bugs
6. ✅ Verify signal timing - check enables clear properly

**Less Effective:**
- ❌ Jumping to conclusions about ID tracking
- ❌ Adding complex state detection logic without understanding root cause
- ❌ Focusing only on simulation results

---

## Next Steps

### Immediate (Post-Bitstream)
1. ⏳ **Wait for bitstream build completion** (~00:57 PDT Oct 22)
2. 🔄 **System will auto-reboot** after flashing
3. ✅ **Run validation test:**
   ```bash
   cd /home/workstation/ElastiCore/projects/model_converter/src/model_converter/backends/achronix
   ./acx_gemm 0 left.hex right.hex
   ```
4. ✅ **Expected: 9/9 tests PASS** with no timeouts

### Follow-up Testing
1. **Test bulk DMA address validation:**
   ```bash
   cd /home/workstation/elastix_gemm/gemm_simple/sw_test
   ./test_bulk_dma -d 0 -B 4 -C 4 -V 32 -n 5 -v
   ```

2. **Test Python model converter:**
   ```bash
   cd /home/workstation/ElastiCore/projects/model_converter
   source .venv/bin/activate
   python -m model_converter.main
   ```

3. **Performance benchmarking:**
   - Measure GEMM throughput for different tile sizes
   - Validate GDDR6 bandwidth utilization
   - Profile command submission latency

### Future Enhancements
1. **Remove redundant wait_idle() calls** - Hardware FSM now handles synchronization
2. **Implement result streaming** - DMA results during computation
3. **Add interrupt-driven completion** - Replace polling with MSI-X
4. **Optimize tile scheduling** - Minimize GDDR6 access patterns
5. **Add hardware debug counters** - Cycle-accurate performance monitoring

---

## Build Information

### Latest Bitstream
- **Timestamp:** 10/21 23:57 (in progress)
- **Key Changes:**
  - Fixed enable signal clearing in master_control.sv
  - Added explicit state transition detection for enables
  - Verified flag-based ID capture logic
- **Expected Bitstream ID:** `0x1021XXXX` (will show time when complete)

### Build Command
```bash
cd /home/workstation/elastix_gemm/gemm_simple
./build_and_flash.sh
```

**Process:**
1. Clean previous build
2. Synplify synthesis (~15 min)
3. ACE place & route (~30 min)
4. Generate bitstream (~5 min)
5. Flash device (auto)
6. Reboot system (auto)

### Verification After Boot
```bash
reg  # Check bitstream ID and registers
# Should show new bitstream timestamp
# ADM Status should be 0x3
```

---

## Contact & References

### Key Files
- **RTL:** `/home/workstation/elastix_gemm/gemm_simple/src/rtl/`
- **Software:** `/home/workstation/elastix_gemm/gemm_simple/sw_test/`
- **Model Converter:** `/home/workstation/ElastiCore/projects/model_converter/`
- **Simulation:** `/home/workstation/elastix_gemm/gemm_simple/sim/vector_system_test/`

### Build Logs
- **Latest:** `/home/workstation/elastix_gemm/gemm_simple/build_flash_enable_fix.log`
- **Previous:** `/home/workstation/elastix_gemm/gemm_simple/build_flash2.log`

---

**Document Version:** 1.0  
**Last Updated:** October 21, 2025 23:57 PDT  
**Status:** Awaiting Hardware Validation ⏳


