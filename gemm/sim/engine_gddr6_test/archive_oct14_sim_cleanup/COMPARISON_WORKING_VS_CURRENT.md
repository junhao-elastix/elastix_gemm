# Comparison: Working vs Current Simulation

**Date**: Sun Oct 13 18:20 PDT 2025  
**Working Testbench**: `vector_system_test/tb_engine_top.sv` - [PASS] ALL 8 TESTS  
**Current Testbench**: `engine_gddr6_test/tb_engine_gddr6.sv` - [FAIL] Incorrect results

---

## Executive Summary

**Root Cause Found**: The `engine_gddr6_test` testbench is using **manual bit-packing** for commands, which differs from the working testbench that uses **structure-based packing** from `gemm_pkg`. The command format mismatch causes incorrect execution.

**Key Difference**: The working testbench uses the **TWO-BRAM architecture** where both left and right matrices are addressed starting from 0, while `engine_gddr6_test` uses absolute addressing (right_addr=528).

---

## Architecture Comparison

### Working Testbench (`vector_system_test/tb_engine_top.sv`)

| Component | Implementation |
|---|---|
| **DUT** | `engine_top` (direct FIFO interface) |
| **Command Entry** | Direct FIFO writes (`cmd_fifo_wdata`, `cmd_fifo_wen`) |
| **Command Format** | Structure-based (`cmd_header_s`, `cmd_tile_s`) from `gemm_pkg` |
| **Result Reading** | Direct FIFO reads (`result_fifo_rdata`, `result_fifo_ren`) |
| **Memory Model** | `tb_memory_model` via AXI responder |
| **BRAM Architecture** | Two-BRAM (left @ addr 0-527, right @ addr 0-527) |

### Current Testbench (`engine_gddr6_test/tb_engine_gddr6.sv`)

| Component | Implementation |
|---|---|
| **DUT** | `engine_top` + `csr_to_fifo_bridge` + `result_fifo_to_bram` |
| **Command Entry** | CSR register writes -> bridge -> FIFO |
| **Command Format** | Manual bit-packing with shifts/masks |
| **Result Reading** | Via `result_fifo_to_bram` adapter registers |
| **Memory Model** | `tb_memory_model` via AXI responder |
| **BRAM Architecture** | Assumed single-BRAM (right @ addr 528) |

---

## Command Format Differences

### TILE Command Example (B=2, C=2, V=2)

#### Working Testbench (Structure-Based)
```systemverilog
task automatic generate_tile_command(
    input logic [7:0] id,
    input logic [tile_mem_addr_width_gp-1:0] left_addr,   // 0
    input logic [tile_mem_addr_width_gp-1:0] right_addr,  // 0 (TWO-BRAM!)
    input int dim_b,  // 2
    input int dim_c,  // 2
    input int dim_v,  // 2
    output logic [31:0] cmd [0:3]
);
    cmd_header_s header;
    cmd_tile_s payload;
    
    // Pack header
    header.op       = e_cmd_op_tile;       // 0xF2
    header.id       = id;                  // 4
    header.len      = cmd_tile_len_gp;     // 12
    header.reserved = 8'h00;
    
    // Pack payload using structure (automatic bit width handling)
    payload.left_addr      = left_addr;    // 0
    payload.right_addr     = right_addr;   // 0  <- KEY DIFFERENCE!
    payload.left_ugd_len   = 11'd1;
    payload.right_ugd_len  = 11'd1;
    payload.vec_len        = dim_v[10:0];  // 2
    payload.dim_b          = dim_b[7:0];   // 2
    payload.dim_c          = dim_c[7:0];   // 2
    payload.dim_v          = dim_v[7:0];   // 2
    payload.flags.left_man_4b        = 1'b0;
    payload.flags.right_man_4b       = 1'b0;
    payload.flags.main_loop_over_left = 1'b0;
    payload.flags.reserved            = '0;
    
    // Automatic structure packing to words
    cmd[0] = {header.reserved, header.len, header.id, header.op};
    cmd[1] = payload[31:0];
    cmd[2] = payload[63:32];
    cmd[3] = payload[95:64];
endtask
```

**Command Output** (Working):
```
cmd[0] = 0x00_0C_04_F2  (reserved=0, len=12, id=4, op=0xF2)
cmd[1] = [left_addr:right_addr:left_ugd_len bits]
cmd[2] = [right_ugd_len:vec_len:dim_b bits]
cmd[3] = [dim_c:dim_v:flags]
```

#### Current Testbench (Manual Bit-Packing)
```systemverilog
// Step 7: MATMUL
w0 = (0 << 24) | (12 << 16) | (9 << 8) | OPCODE_MATMUL;  // 0x000C09F2
w1 = ((128 & 10'h3FF) << 22) | ((528 & 11'h7FF) << 11) | (0 & 11'h7FF);
     //  ^^^ left_ugd_len?      ^^^ right_addr=528!     ^^^ left_addr
w2 = ((TEST_V & 1) << 31) | ((0 & 8'hFF) << 23) | ((128 & 11'h7FF) << 12) | ((128 & 11'h7FF) << 1);
w3 = ((TEST_B & 8'hFF) << 15) | ((TEST_C & 8'hFF) << 7) | ((TEST_V >> 1) & 7'h7F);
```

**Problems**:
1. **right_addr = 528** (single-BRAM addressing, but hardware uses TWO-BRAM!)
2. **Bit field positions may not match** `cmd_tile_s` structure layout
3. **No validation** that packed bits align with structure definition

---

## Memory Addressing: Critical Difference

### Two-BRAM Architecture (Actual Hardware)

From `vector_system_test/README.md` and `tb_engine_top.sv`:
```
**Dual BRAM dispatcher** - key performance feature (42% faster)
```

**Address Space Layout**:
```
dispatcher_bram.sv (2048 entries × 256-bit):
- Left matrix:  Lines 0-527    (Port B dual-read: left data)
- Right matrix: Lines 0-527    (Port B dual-read: right data simultaneously)
```

**TILE Command Addressing**:
```systemverilog
generate_tile_command(4, 0, 0, B, C, V, tile_cmd);
//                      id  ^left_addr=0
//                          ^right_addr=0 (separate address space!)
```

**Why This Works**:
- `dispatcher_bram.sv` has **dual read ports** on Port B
- Reads from left and right happen **simultaneously** from separate regions
- Both address spaces start at 0

### Single-BRAM Addressing (Incorrect Assumption in engine_gddr6_test)

**Current Test Assumes**:
```systemverilog
w1 = ((128 & 10'h3FF) << 22) | ((528 & 11'h7FF) << 11) | (0 & 11'h7FF);
//                                ^^^ right_addr = 528
```

**Problem**: Hardware doesn't have a single BRAM with left @ 0-527 and right @ 528-1055. It has **two separate address spaces**, both starting at 0.

---

## Test Flow Comparison

### Working Testbench Flow

```systemverilog
// 1. Generate command sequence
build_test_sequence(config_B, config_C, config_V, cmd_sequence, num_commands);
// Produces: FETCH_LEFT, FETCH_RIGHT, DISP, WAIT_DISP, TILE, WAIT_TILE

// 2. Submit all commands at once
for (cmd_idx = 0; cmd_idx < num_commands; cmd_idx++) begin
    cmd_fifo_wdata = cmd_sequence[cmd_idx];
    cmd_fifo_wen = 1'b1;
    @(posedge clk);
end
cmd_fifo_wen = 1'b0;

// 3. Continuously drain result FIFO as results arrive
while (results_seen < expected_results && timeout_count < watchdog) begin
    @(posedge clk);
    if (!result_fifo_empty) begin
        result_fifo_ren = 1'b1;
        @(posedge clk);
        result_fifo_ren = 1'b0;
        @(posedge clk);  // Wait for BRAM latency
        fp16_hw = result_fifo_rdata;
        // Validate against golden reference
    end
end
```

**Key Feature**: Continuous FIFO draining prevents backpressure deadlock.

### Current Testbench Flow

```systemverilog
// 1. Issue commands one-by-one via CSR writes
issue_command(w0, w1, w2, w3);  // Writes to CSR regs, pulses SUBMIT
wait_engine_idle(timeout);       // Wait for engine_busy to clear

// 2. Repeat for each command (FETCH_LEFT, FETCH_RIGHT, DISP, etc.)

// 3. Read results via result_fifo_to_bram adapter registers
// Results captured in result_0, result_1, result_2, result_3
```

**Difference**: 
- CSR interface adds bridge latency
- Result adapter adds packing logic
- May not be draining FIFO continuously

---

## Result Path Comparison

### Working Testbench (Direct FIFO Read)

```
engine_top.result_fifo -> tb reads result_fifo_rdata directly
```

**Advantages**:
- Direct access to FP16 results as they arrive
- No intermediate logic to debug
- Simple validation flow

### Current Testbench (Via Adapter)

```
engine_top.result_fifo -> result_fifo_to_bram adapter -> result_0..3 registers
                                                      -> result_bram (256-bit lines)
```

**Advantages**:
- Tests the full hardware path (more accurate)
- Validates result packing logic

**Disadvantages**:
- Additional complexity
- Adapter could introduce bugs
- Only exposes first 4 results to registers

---

## Golden Reference Comparison

### Working Testbench
```systemverilog
golden_filename = $sformatf("/home/dev/Dev/elastix_gemm/hex/golden_%s.hex", test_name);
// Example: golden_B2_C2_V2.hex

// File format: One FP16 value per line (4 hex digits)
3c00  // Result 0
bc00  // Result 1
4200  // Result 2
c200  // Result 3
```

**Pre-generated**: All golden files exist for test configurations.

### Current Testbench
```systemverilog
// No golden reference loaded yet
// Results monitored via result_adapter output registers
```

**Missing**: Golden reference validation not implemented.

---

## Recommendations

### Option 1: Simplify to Match Working Testbench (Recommended)

**Goal**: Get simulation working quickly with known-good command format.

**Changes**:
1. **Remove CSR bridge and adapter** from testbench (test `engine_top` directly)
2. **Copy command generation tasks** from `vector_system_test/tb_engine_top.sv`
3. **Use structure-based packing** from `gemm_pkg`
4. **Fix addressing**: Use left_addr=0, right_addr=0 (two-BRAM)
5. **Add golden reference validation** (copy from working testbench)
6. **Implement continuous FIFO draining**

**Pros**:
- Fast path to working simulation
- Known-good command format
- Can validate compute results immediately

**Cons**:
- Doesn't test CSR bridge or result adapter
- Less representative of full hardware

---

### Option 2: Fix Current Testbench Command Format (More Work)

**Goal**: Keep full hardware path, fix command encoding.

**Changes**:
1. **Import command structures** from `gemm_pkg`
2. **Use structure packing** instead of manual bit manipulation
3. **Fix addressing**: Change right_addr from 528 to 0
4. **Add golden reference** loading and validation
5. **Verify result adapter** is continuously draining FIFO
6. **Add debug** to compare packed command bits vs structures

**Pros**:
- Tests full hardware path
- More accurate hardware representation

**Cons**:
- More debugging required
- Longer iteration cycle

---

## Recommended Next Steps

### Immediate Action: Adopt Working Command Format

1. **Copy command generation tasks** from `tb_engine_top.sv`:
   - `generate_fetch_command()`
   - `generate_disp_command()`
   - `generate_tile_command()`
   - `generate_wait_disp_command()`
   - `generate_wait_tile_command()`

2. **Fix TILE command addressing**:
   ```systemverilog
   // WRONG (current):
   generate_tile_command(4, 0, 528, B, C, V, tile_cmd);
   
   // CORRECT (two-BRAM):
   generate_tile_command(4, 0, 0, B, C, V, tile_cmd);
   ```

3. **Replace manual command packing** with structure-based calls

4. **Add golden reference validation**:
   ```systemverilog
   golden_filename = $sformatf("/home/dev/Dev/elastix_gemm/hex/golden_B%0d_C%0d_V%0d.hex", 
                                TEST_B, TEST_C, TEST_V);
   ```

5. **Ensure continuous FIFO draining** (via result_adapter or direct read)

---

## File Locations

### Working Reference Files
- **Testbench**: `/home/dev/Dev/elastix_gemm/gemm/sim/vector_system_test/tb_engine_top.sv`
- **Makefile**: `/home/dev/Dev/elastix_gemm/gemm/sim/vector_system_test/Makefile`
- **README**: `/home/dev/Dev/elastix_gemm/gemm/sim/vector_system_test/README.md`
- **Golden Refs**: `/home/dev/Dev/elastix_gemm/hex/golden_*.hex`

### Current Files to Update
- **Testbench**: `/home/dev/Dev/elastix_gemm/gemm/sim/engine_gddr6_test/tb_engine_gddr6.sv`
- **Makefile**: `/home/dev/Dev/elastix_gemm/gemm/sim/engine_gddr6_test/Makefile`

---

## Summary

**The working testbench succeeds because**:
1. Uses correct command structures from `gemm_pkg`
2. Addresses both left and right matrices starting at 0 (two-BRAM architecture)
3. Continuously drains result FIFO to prevent deadlock
4. Validates against pre-generated golden references

**The current testbench fails because**:
1. Manual bit-packing may not match structure layout
2. Uses incorrect addressing (right_addr=528 instead of 0)
3. May not be draining result FIFO continuously
4. No golden reference validation yet

**Fastest path forward**: Copy command generation and test flow from `vector_system_test` into `engine_gddr6_test`, adjusting only for CSR interface if needed, or simplify to test `engine_top` directly.

---

**Status**: Ready to implement fixes based on working testbench patterns.

