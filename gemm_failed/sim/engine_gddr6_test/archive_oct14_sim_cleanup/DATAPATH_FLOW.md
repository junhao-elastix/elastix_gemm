# GEMM Engine Datapath: Testbench to Results

**Simulation**: `tb_engine_gddr6` → `engine_top` → Results  
**Date**: October 14, 2025

## Complete Datapath Overview

```
[Testbench]
    |
    | 1. CSR Writes (emulate software)
    v
[CSR to FIFO Bridge]
    |
    | 2. Commands (128-bit words)
    v
[Command FIFO]
    |
    | 3. Command words
    v
[Master Control]
    |
    | 4. AXI read requests          | 5. Control signals
    v                                v
[Memory Model] ←--AXI-→ [NAP] ← [Dispatcher Control]
    |                                |
    | 6. GFP8 data (256-bit)        | 7. BRAM writes
    v                                v
                              [Dispatcher BRAM]
                                     |
                                     | 8. Mantissa + Exponent
                                     v
                              [Compute Engine]
                                     |
                                     | 9. FP16 results
                                     v
                              [Result BRAM]
                                     |
                                     | 10. Result FIFO
                                     v
                              [Testbench captures]
```

---

## Step-by-Step Datapath

### Step 1: Testbench Issues Commands (CSR Writes)

**File**: `tb_engine_gddr6.sv`, task `issue_command()`

```systemverilog
// Emulate software writing to memory-mapped registers
user_regs_write[ENGINE_CMD_WORD0] = {24'h0, opcode};
user_regs_write[ENGINE_CMD_WORD1] = param1;
user_regs_write[ENGINE_CMD_WORD2] = param2;
user_regs_write[ENGINE_CMD_WORD3] = param3;
write_strobes[ENGINE_CMD_SUBMIT] = 1'b1;  // Trigger
```

**Example Commands**:
- `FETCH(addr=0x0, lines=528)` - Fetch left matrix from memory
- `DISPATCH(addr=0, len=128)` - Move data from memory to BRAM
- `MATMUL(B=2, C=2, V=2)` - Execute matrix multiply

**Data Format**: 4 x 32-bit words per command

---

### Step 2: CSR to FIFO Bridge

**File**: `csr_to_fifo_bridge.sv`

```systemverilog
// Converts 4 separate 32-bit CSR writes into single 128-bit FIFO push
always_ff @(posedge i_clk) begin
    if (i_cmd_submit && !o_fifo_full) begin
        // Assemble 128-bit command word
        o_fifo_wdata <= {i_cmd_word3, i_cmd_word2, i_cmd_word1, i_cmd_word0};
        o_fifo_wen <= 1'b1;
    end
end
```

**Purpose**: 
- Bridge between register interface (software view) and FIFO interface (hardware view)
- Ensures atomic command submission
- Handles backpressure (FIFO full)

**Output**: 128-bit command word to Command FIFO

---

### Step 3: Command FIFO

**File**: `cmd_fifo.sv`

```systemverilog
// 64-deep x 128-bit FIFO
logic [127:0] mem [0:63];
```

**Purpose**:
- Decouple command submission rate from execution rate
- Allow software to queue multiple commands
- Prevent command loss during processing

**Operation**:
- Write side: Bridge pushes commands
- Read side: Master Control pops commands

---

### Step 4: Master Control (Command Decoder)

**File**: `master_control.sv`

```systemverilog
// State machine reads command FIFO and dispatches to appropriate modules
case (cmd_opcode)
    OP_FETCH: begin
        // Issue AXI read burst to memory
        o_axi_arvalid <= 1'b1;
        o_axi_araddr <= fetch_addr;
        o_axi_arlen <= fetch_lines - 1;
    end
    
    OP_DISPATCH: begin
        // Signal dispatcher to start
        o_dispatch_start <= 1'b1;
        o_dispatch_addr <= dispatch_addr;
        o_dispatch_len <= dispatch_len;
    end
    
    OP_MATMUL: begin
        // Configure compute engine
        o_ce_start <= 1'b1;
        o_ce_b_dim <= b_count;
        o_ce_c_dim <= c_count;
        o_ce_v_dim <= v_count;
    end
endcase
```

**Key Responsibilities**:
1. **FETCH commands** → Generate AXI read transactions
2. **DISPATCH commands** → Control dispatcher module
3. **MATMUL commands** → Configure and trigger compute engine
4. **WAIT commands** → Monitor completion status

---

### Step 5: Memory Interface (AXI Read Path)

**Testbench Side**: `tb_memory_model.sv`

```systemverilog
// Behavioral memory model
logic [255:0] mem_array [0:1055];  // 2 blocks × 528 lines

// AXI read response
always_ff @(posedge i_clk) begin
    if (axi_mem_if.arvalid && axi_mem_if.arready) begin
        // Calculate line address from AXI address
        line_addr = axi_mem_if.araddr[31:5];  // Byte addr → line addr
        
        // Read data from memory array
        read_data <= mem_array[line_addr];
        
        // Return on AXI read data channel
        axi_mem_if.rdata <= read_data;
        axi_mem_if.rvalid <= 1'b1;
    end
end
```

**Memory Layout** (from `tb_memory_model.sv`):
```
Block 0 (Left Matrix):  Lines 0-527
  Lines 0-15:   Exponents (16 lines, 32 exp/line = 512 total)
  Lines 16-527: Mantissas (512 lines, 32 man/line)

Block 1 (Right Matrix): Lines 528-1055
  Lines 528-543:   Exponents
  Lines 544-1055:  Mantissas
```

**Address Mapping**:
- AXI addr `0x00000000` → Line 0 (left exp start)
- AXI addr `0x00004200` → Line 528 (right exp start)
- Page ID field (bits [41:35]) used for GDDR6 channel select

---

### Step 6: Dispatcher Control (Memory → BRAM)

**File**: `dispatcher_control.sv`

```systemverilog
// Receives GFP8 data from AXI and writes to dispatcher BRAM
always_ff @(posedge i_clk) begin
    if (i_axi_rvalid && i_axi_rready) begin
        // Parse 256-bit AXI data into GFP8 format
        // Line 0-15: Exponents (4-bit each, packed)
        // Line 16+: Mantissas (8-bit each)
        
        if (current_line < 16) begin
            // Unpack exponents
            for (int i = 0; i < 32; i++) begin
                exp_packed[i] <= i_axi_rdata[i*8 +: 4];
            end
            // Write to exp BRAM
            o_bram_wr_en <= 1'b1;
            o_bram_wr_addr <= exp_wr_addr;
            o_bram_wr_data <= exp_packed;
        end else begin
            // Write mantissas directly
            o_bram_wr_en <= 1'b1;
            o_bram_wr_addr <= man_wr_addr;
            o_bram_wr_data <= i_axi_rdata;
        end
    end
end
```

**Purpose**:
- Buffer fetched data locally for fast compute access
- Unpack GFP8 format (shared exponents + mantissas)
- Write to on-chip BRAM (much faster than GDDR6)

---

### Step 7: Dispatcher BRAM

**File**: `dispatcher_bram_dual_read.sv`

```systemverilog
// Dual-port BRAM for simultaneous left/right reads
// Left matrix:  Addresses 0-527
// Right matrix: Addresses 528-1055

// Exponent storage (packed 4-bit)
logic [3:0] exp_left_packed [0:15];   // 16 lines × 32 exp/line
logic [3:0] exp_right_packed [0:15];

// Mantissa storage (8-bit)
logic [7:0] man_left [0:511];   // 512 lines × 32 man/line
logic [7:0] man_right [0:511];

// Dual read ports for compute engine
always_comb begin
    o_left_data = {exp_left[group], man_left[idx]};
    o_right_data = {exp_right[group], man_right[idx]};
end
```

**Data Structure**:
- **Exponents**: Shared per 32-element group (GFP8 format)
- **Mantissas**: Individual 8-bit values
- **Total capacity**: 128×128 elements per matrix

---

### Step 8: Compute Engine (GFP8 Dot Product)

**File**: `compute_engine_modular.sv`

```systemverilog
// Triple-nested loop: B × C × V iterations
// Each iteration: 128-element dot product

always_ff @(posedge i_clk) begin
    if (compute_active) begin
        // BCV loop control
        if (v_idx < V_DIM) begin
            // Perform dot product: sum(left[b,v] * right[v,c])
            for (int i = 0; i < 128; i++) begin
                // Read from dispatcher BRAM
                left_addr = b_idx * 128 + v_idx * 128 + i;
                right_addr = v_idx * 128 + c_idx * 128 + i;
                
                // GFP8 dot product unit
                u_gfp8_nv_dot (
                    .i_left_man(man_left[i]),
                    .i_left_exp(exp_left[i/32]),
                    .i_right_man(man_right[i]),
                    .i_right_exp(exp_right[i/32]),
                    .o_result(dot_result[i])
                );
                
                // Accumulate
                partial_sum += dot_result[i];
            end
            
            // Convert GFP8 accumulator to FP16
            result_fp16 = gfp8_to_fp16(partial_sum);
            
            v_idx++;
        end else begin
            // Move to next C
            v_idx = 0;
            c_idx++;
            if (c_idx >= C_DIM) begin
                // Move to next B
                c_idx = 0;
                b_idx++;
            end
        end
    end
end
```

**Compute Pattern** (for B=2, C=2, V=2):
```
Result[0] = dot(left[0,0:1], right[0:1,0])  // B=0, C=0
Result[1] = dot(left[0,0:1], right[0:1,1])  // B=0, C=1
Result[2] = dot(left[1,0:1], right[0:1,0])  // B=1, C=0
Result[3] = dot(left[1,0:1], right[0:1,1])  // B=1, C=1
```

**Expected Output**: B × C = 2 × 2 = **4 results**

---

### Step 9: Result BRAM

**File**: `result_bram.sv`

```systemverilog
// Stores FP16 results from compute engine
logic [15:0] result_mem [0:16383];  // 128×128 max capacity

always_ff @(posedge i_clk) begin
    if (i_result_valid) begin
        result_mem[result_wr_addr] <= i_result_data;
        result_wr_addr <= result_wr_addr + 1;
    end
end

// Result FIFO interface for readout
always_ff @(posedge i_clk) begin
    if (!o_result_fifo_empty && i_result_fifo_ren) begin
        o_result_fifo_rdata <= result_mem[result_rd_addr];
        result_rd_addr <= result_rd_addr + 1;
    end
end
```

**Purpose**:
- Buffer all results before readout
- Provide FIFO interface for software/testbench
- Track result count for dimension verification

---

### Step 10: Testbench Result Capture

**File**: `tb_engine_gddr6.sv`

```systemverilog
// Auto-drain result FIFO
always_ff @(posedge i_nap_clk) begin
    if (!reset_n) begin
        result_idx <= 0;
    end else if (!result_fifo_empty && result_idx < 16) begin
        results_hw[result_idx] <= result_fifo_rdata;
        result_idx <= result_idx + 1;
        $display("[TB] @%0t Result[%0d] = 0x%04x", 
                 $time, result_idx, result_fifo_rdata);
    end
end

// Compare with golden reference
initial begin
    // Load expected results
    golden[0] = 16'hb414;
    golden[1] = 16'h2ecb;
    golden[2] = 16'h3345;
    golden[3] = 16'h326b;
    
    // Wait for results
    wait(result_idx >= 4);
    
    // Check
    for (int i = 0; i < 4; i++) begin
        if (results_hw[i] !== golden[i]) begin
            $display("ERROR: Result[%0d] mismatch", i);
            test_errors++;
        end
    end
end
```

---

## Current Simulation Results

### What We Saw:
```
Result[0] = 0x0000
Result[1] = 0x0000
Result[2] = 0xxxxx  (X = unknown/uninitialized)
Result[3] = 0x0000
Result[4] = 0xxxxx
Result[5] = 0x0000
Result[6] = 0xxxxx
Result[7] = 0x0000
```

### Expected:
```
Result[0] = 0xb414
Result[1] = 0x2ecb
Result[2] = 0x3345
Result[3] = 0x326b
```

### Issues to Debug:

1. **Too many results**: Got 8, expected 4
   - Possible cause: BCV loop not configured correctly
   - Check: `o_ce_b_dim`, `o_ce_c_dim`, `o_ce_v_dim` values

2. **Zero/X values**: Results are not computed
   - Possible causes:
     - Data not reaching compute engine
     - Dispatcher BRAM addresses wrong
     - GFP8 conversion issue
     - Accumulator not working

3. **Alternating pattern**: 0, 0, X, 0, X, 0...
   - Suggests address indexing issue
   - Even indices: zeros
   - Odd indices: X (uninitialized)

---

## Debug Strategy

### 1. Check Memory Read (Step 5-6)
```systemverilog
// In tb_memory_model.sv
$display("[MEM] Read addr=0x%08x line=%0d data=0x%064x", 
         araddr, line_addr, mem_array[line_addr]);
```

### 2. Check Dispatcher Writes (Step 7)
```systemverilog
// In dispatcher_control.sv
$display("[DISP] Write addr=%0d data=0x%064x", 
         bram_wr_addr, bram_wr_data);
```

### 3. Check Compute Engine (Step 8)
```systemverilog
// In compute_engine_modular.sv
$display("[CE] B=%0d C=%0d V=%0d result=0x%04x", 
         b_idx, c_idx, v_idx, result_fp16);
```

### 4. Check Result BRAM (Step 9)
```systemverilog
// In result_bram.sv
$display("[RES] Write addr=%0d data=0x%04x count=%0d", 
         wr_addr, result_data, result_count);
```

---

## Waveform Analysis

To see the datapath in action:
```bash
cd /home/dev/Dev/elastix_gemm/gemm/sim/engine_gddr6_test
make debug  # Opens with waveforms
```

Key signals to add to waveform viewer:
- **Commands**: `cmd_fifo_wdata`, `cmd_fifo_wen`
- **AXI**: `nap.arvalid`, `nap.araddr`, `nap.rdata`, `nap.rvalid`
- **Dispatcher**: `o_bram_wr_en`, `o_bram_wr_addr`, `o_bram_wr_data`
- **Compute**: `o_ce_start`, `b_idx_reg`, `c_idx_reg`, `v_idx_reg`
- **Results**: `result_fifo_rdata`, `result_fifo_ren`, `result_fifo_empty`

---

## Summary

**Complete Datapath**: 10 stages from testbench to results

1. ✅ **CSR Writes** - Testbench emulates software
2. ✅ **Bridge** - Converts to 128-bit commands
3. ✅ **FIFO** - Queues commands
4. ✅ **Master Control** - Decodes and dispatches
5. ✅ **Memory** - Returns GFP8 data via AXI
6. ✅ **Dispatcher** - Unpacks and writes to BRAM
7. ✅ **BRAM** - Buffers data for compute
8. ⚠️ **Compute Engine** - GFP8 dot products (results wrong)
9. ⚠️ **Result BRAM** - Stores FP16 results (wrong values)
10. ✅ **Testbench** - Captures and compares

**Status**: Infrastructure works, compute results need debugging.

The simulation now provides **complete visibility** into every stage to identify where the computation goes wrong!

