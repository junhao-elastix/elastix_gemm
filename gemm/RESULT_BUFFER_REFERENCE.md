# Result Buffer Circular Queue Reference Manual

**Document Version**: 2.0
**Date**: January 28, 2026
**Component**: Result BRAM Circular Buffer (Pseudo-FIFO)
**Related Modules**: `result_to_dma.sv`, `dma_bram_bridge.sv`, `elastix_gemm_top.sv`, `engine_top_2d.sv`

---

## 1. Overview

The Result Buffer implements a **circular queue (ring buffer)** using random-access BRAM with manual pointer management. This design provides FIFO semantics for producer-consumer data flow between the GEMM engine (producer) and host DMA (consumer) while maintaining the flexibility of random-access reads required by the AXI4 DMA interface.

### 1.1 Key Characteristics

- **Capacity**: 8192 FP16 results (512 BRAM lines x 16 FP16/line)
- **Storage**: 2x ACX_BRAM72K_SDP instances (256-bit data width) in `dma_bram_bridge.sv`
- **Addressing**: 9-bit line addresses (512 locations), 13-bit FP16 pointers
- **Producer**: `result_collector_2d` -> `result_to_dma` (writes 256-bit lines)
- **Consumer**: Host via PCIe DMA (reads via AXI4 through `dma_bram_bridge`)
- **Backpressure**: `almost_full` signal blocks `result_collector_2d` via `o_ready`

### 1.2 Design Rationale

This design combines the benefits of:
- **FIFO ordering**: Results processed in strict order (oldest first)
- **Random access**: AXI4 DMA can perform burst reads at arbitrary addresses
- **Decoupled operation**: Engine and host operate independently at different rates
- **Efficient backpressure**: Hardware prevents buffer overflow automatically

---

## 2. Architecture

### 2.1 Module Hierarchy

```
elastix_gemm_top.sv
    |
    +-- engine_top_2d.sv
    |       |
    |       +-- result_collector_2d.sv   (produces 256-bit lines via ready-valid)
    |       |
    |       +-- result_to_dma.sv         (circular buffer logic, pointer management)
    |               |
    |               +-- (outputs: o_bram_wr_en, o_bram_wr_addr, o_bram_wr_data)
    |
    +-- dma_bram_bridge.sv               (BRAM storage with AXI4 interface)
            |
            +-- 2x ACX_BRAM72K_SDP       (512 x 256-bit physical storage)
```

### 2.2 Data Flow

```
result_collector_2d          result_to_dma              dma_bram_bridge
      |                            |                          |
      | (ready-valid)              |                          |
      | i_data[255:0]       -----> | (circular buffer)        |
      | i_keep[15:0]        -----> | wr_ptr management        |
      | i_valid             -----> | backpressure logic       |
      | o_ready             <----- |                          |
      |                            |                          |
      |                            | o_bram_wr_en      -----> | i_internal_wr_en
      |                            | o_bram_wr_addr    -----> | i_internal_wr_addr
      |                            | o_bram_wr_data    -----> | i_internal_wr_data
      |                            | o_bram_wr_strobe  -----> | i_internal_wr_strobe
      |                            |                          |
      |                            |                          | <-- AXI4 (Host DMA Read)
```

### 2.3 Buffer Organization

```
Physical BRAM Layout (512 lines x 256 bits):
+----------------------------------------------------+
| Line 0:   [FP16_15][FP16_14]...[FP16_1][FP16_0]    | <- 16 FP16 results
| Line 1:   [FP16_31][FP16_30]...[FP16_17][FP16_16]  |
| ...                                                 |
| Line 511: [...][FP16_8191]                         |
+----------------------------------------------------+

Logical Circular Buffer (8192 FP16 results):
      +---------------------------+
      |   [rd_ptr]                | <- Host reads here
      |   +---------------+       |   (consumed space)
      |   | Valid Results |       |
      |   +---------------+       |
      |   [wr_ptr]                | <- Engine writes here
      |   +---------------+       |   (free space)
      |   | Free Space    |       |
      |   +---------------+       |
      +---------------------------+
         (wraps at 512 lines)
```

---

## 3. Module Specifications

### 3.1 result_to_dma.sv

**Purpose**: Converts ready-valid stream from `result_collector_2d` to BRAM write interface with circular buffer semantics.

**Ports**:

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `i_clk` | Input | 1 | System clock |
| `i_reset_n` | Input | 1 | Active-low reset |
| `i_data` | Input | 256 | Data from result_collector (16 FP16 packed) |
| `i_keep` | Input | 16 | Valid FP16 mask (1 bit per FP16) |
| `i_last` | Input | 1 | Last transfer in sequence |
| `i_valid` | Input | 1 | Data valid |
| `o_ready` | Output | 1 | Ready to accept (backpressure) |
| `i_rd_ptr` | Input | 9 | Read pointer from host register |
| `o_wr_ptr` | Output | 9 | Current write pointer |
| `o_used_entries` | Output | 10 | Number of valid lines (0-512) |
| `o_almost_full` | Output | 1 | Backpressure signal |
| `o_empty` | Output | 1 | Buffer empty flag |
| `o_bram_wr_en` | Output | 1 | BRAM write enable |
| `o_bram_wr_addr` | Output | 9 | BRAM write address (line) |
| `o_bram_wr_data` | Output | 256 | BRAM write data |
| `o_bram_wr_strobe` | Output | 32 | BRAM byte enables |

**Key Logic**:

```systemverilog
// Circular buffer calculations (line-based, 9-bit addresses)
localparam BUFFER_DEPTH = 512;
localparam ALMOST_FULL_THRESHOLD = BUFFER_DEPTH - 16;  // 496 lines margin

// Used entries calculation
always_comb begin
    if (wr_ptr >= rd_ptr)
        used_entries = wr_ptr - rd_ptr;
    else
        used_entries = (BUFFER_DEPTH - rd_ptr) + wr_ptr;
end

// Backpressure
assign almost_full = (used_entries >= ALMOST_FULL_THRESHOLD);
assign o_ready = ~almost_full;  // Block when almost full
assign empty = (wr_ptr == rd_ptr);

// Write pointer management with wrap
always_ff @(posedge i_clk or negedge i_reset_n) begin
    if (!i_reset_n)
        wr_ptr <= 9'd0;
    else if (i_valid && o_ready)
        wr_ptr <= (wr_ptr == BUFFER_DEPTH - 1) ? 9'd0 : wr_ptr + 1;
end
```

### 3.2 dma_bram_bridge.sv

**Purpose**: Dual-port BRAM responder with internal write port for engine and AXI4 read interface for host DMA.

**Key Features**:
- 512 locations x 256 bits (using 2x ACX_BRAM72K_SDP)
- Internal write port has priority over DMA access
- AXI4 interface supports burst reads up to 16 beats
- 2-cycle read latency (output register enabled)

**BRAM Configuration**:

```systemverilog
// Lower 144 bits
ACX_BRAM72K_SDP xact_mem_lo (
    .din      (actual_wr_data[143:0]),
    .we       (actual_wstrb[17:0]),
    .wren     (actual_wr_en),
    .wraddr   ({actual_wr_addr, 5'h00}),  // 9-bit line address
    .dout     (xact_r_dout[143:0]),
    ...
);

// Upper 112 bits (with 32-bit padding)
ACX_BRAM72K_SDP xact_mem_hi (
    .din      ({32'h0, actual_wr_data[255:144]}),
    .we       ({4'h0, actual_wstrb[31:18]}),
    ...
);
```

---

## 4. Register Interface

### 4.1 Register Definitions

| Register | Address | Type | Width | Description |
|----------|---------|------|-------|-------------|
| `REG_RD_PTR` | 0x230 | RW | [8:0] | Host-controlled read pointer (line address) |
| `REG_WR_PTR` | 0x234 | RO | [8:0] | Current write pointer (line address) |
| `REG_USED_ENTRIES` | 0x238 | RO | [9:0] | Number of valid lines (0-512) |
| `REG_RESULT_EMPTY` | 0x23C | RO | [0:0] | Buffer empty flag (1=empty) |
| `ENGINE_WRITE_TOP` | 0x22C | RO | [8:0] | Legacy: same as REG_WR_PTR |

### 4.2 Pointer Semantics

**Line-Based Addressing**:
- Pointers are 9-bit line addresses (0-511)
- Each line holds 16 FP16 results (256 bits)
- Total capacity: 512 lines = 8192 FP16 results

**Write Pointer (Hardware)**:
- Auto-increments on each valid write
- Wraps automatically at 512
- Read-only from host perspective

**Read Pointer (Software)**:
- Host updates after consuming data
- Host handles wrap calculation: `new_rd_ptr = (rd_ptr + lines_read) % 512`
- Must not advance past write pointer

### 4.3 Register Access in elastix_gemm_top.sv

```systemverilog
// Current implementation (to be connected to result_to_dma outputs)
assign user_regs_read[REG_RD_PTR] = user_regs_write[REG_RD_PTR];  // Host-controlled
assign user_regs_read[REG_WR_PTR] = {23'h0, circular_wr_ptr};     // From result_to_dma
assign user_regs_read[REG_USED_ENTRIES] = {22'h0, used_entries};  // From result_to_dma
assign user_regs_read[REG_RESULT_EMPTY] = {31'h0, buffer_empty};  // From result_to_dma
```

---

## 5. Flow Control and Backpressure

### 5.1 Used Entries Calculation

```systemverilog
// Line-based (9-bit pointers, 512 lines)
used_entries[9:0] = (wr_ptr >= rd_ptr) ?
                    (wr_ptr - rd_ptr) :              // Normal case
                    (512 - rd_ptr + wr_ptr);         // Wrapped case
```

**Examples**:
- `wr_ptr=100, rd_ptr=50` -> `used_entries=50` (normal)
- `wr_ptr=10, rd_ptr=500` -> `used_entries=512-500+10=22` (wrapped)

### 5.2 Backpressure Mechanism

```
1. Engine writes results -> wr_ptr increments -> used_entries increases
2. When used_entries >= 496 (THRESHOLD) -> almost_full asserts
3. result_to_dma.o_ready = 0 -> result_collector_2d stalls
4. Engine pipeline naturally drains (no new MATMUL commands)
5. Host reads via DMA -> updates rd_ptr -> used_entries decreases
6. When used_entries < 496 -> almost_full deasserts
7. o_ready = 1 -> result_collector_2d resumes
```

### 5.3 Integration with Master Control

The `almost_full` signal should be connected to master_control_2d to block new READOUT commands when buffer is full:

```systemverilog
// In master_control_2d.sv state machine
ST_EXEC_READOUT: begin
    if (!i_result_almost_full) begin
        // Issue READOUT command
        state_next = ST_WAIT_READOUT;
    end else begin
        // Wait for buffer to drain
        state_next = ST_EXEC_READOUT;
    end
end
```

---

## 6. Host Software Interface

### 6.1 Polling and Reading

```c
// Check if data available
uint32_t empty = read_reg(REG_RESULT_EMPTY);
if (empty) return NO_DATA;

// Get available count
uint32_t used = read_reg(REG_USED_ENTRIES);
uint32_t rd_ptr = read_reg(REG_RD_PTR);
uint32_t lines_to_read = min(used, MAX_BATCH_LINES);

// Calculate DMA parameters
uint32_t byte_addr = rd_ptr * 32;  // Each line is 32 bytes (256 bits)
uint32_t bytes_to_read = lines_to_read * 32;

// Handle wrap-around case
if (rd_ptr + lines_to_read > 512) {
    // Split into two DMA reads
    uint32_t first_chunk = 512 - rd_ptr;
    uint32_t second_chunk = lines_to_read - first_chunk;
    
    dma_read(RESULT_BRAM_BASE + rd_ptr * 32, first_chunk * 32, dest);
    dma_read(RESULT_BRAM_BASE, second_chunk * 32, dest + first_chunk * 32);
    
    write_reg(REG_RD_PTR, second_chunk);
} else {
    dma_read(RESULT_BRAM_BASE + byte_addr, bytes_to_read, dest);
    write_reg(REG_RD_PTR, rd_ptr + lines_to_read);
}
```

### 6.2 Initialization

```c
void result_buffer_init(void) {
    // Reset read pointer to 0
    write_reg(REG_RD_PTR, 0);
    
    // Wait for engine to reset write pointer (via engine soft reset)
    write_reg(CONTROL_REG, 0x2);  // Assert soft reset
    usleep(1000);
    write_reg(CONTROL_REG, 0x0);  // Release soft reset
    
    // Verify both pointers at 0
    while (read_reg(REG_WR_PTR) != 0 || read_reg(REG_RD_PTR) != 0);
}
```

---

## 7. Implementation Checklist

### 7.1 result_to_dma.sv Modifications

- [ ] Add `i_rd_ptr` input port (from host register)
- [ ] Change `addr_counter` to `wr_ptr` with wrap-around
- [ ] Add `used_entries` combinational calculation
- [ ] Add `almost_full` threshold comparison
- [ ] Change `o_ready` from `1'b1` to `~almost_full`
- [ ] Add `o_wr_ptr`, `o_used_entries`, `o_empty`, `o_almost_full` outputs

### 7.2 engine_top_2d.sv Modifications

- [ ] Add `i_rd_ptr` input port (from top-level)
- [ ] Add `o_wr_ptr`, `o_used_entries`, `o_empty`, `o_almost_full` outputs
- [ ] Connect new ports to `result_to_dma` instance

### 7.3 elastix_gemm_top.sv Modifications

- [ ] Connect `user_regs_write[REG_RD_PTR]` to engine `i_rd_ptr`
- [ ] Connect engine outputs to `user_regs_read[REG_WR_PTR]`, etc.
- [ ] (Optional) Connect `almost_full` to master_control_2d

### 7.4 Simulation Verification

- [ ] Verify `used_entries` normal case (wr > rd)
- [ ] Verify `used_entries` wrapped case (wr < rd)
- [ ] Verify `almost_full` triggers at threshold
- [ ] Verify `empty` when wr_ptr == rd_ptr
- [ ] Verify `wr_ptr` wraps at 512
- [ ] Verify backpressure blocks result_collector_2d
- [ ] Stress test: continuous write/read cycles

---

## 8. Performance Characteristics

### 8.1 Latency

| Operation | Latency | Notes |
|-----------|---------|-------|
| Engine Write | 1 cycle | Registered output from result_to_dma |
| Pointer Update | 0 cycles | Combinational in result_to_dma |
| Flag Update | 0-1 cycles | Combinational or registered |
| Host Read | 2 cycles | BRAM output register enabled |
| DMA Burst | N cycles | Depends on AXI burst length |

### 8.2 Buffer Sizing

**Why 512 lines (8192 FP16)?**
- Matches single BRAM72K depth (512 entries)
- Large enough to absorb compute bursts
- 16-line margin (256 FP16) for backpressure latency
- Power-of-2 simplifies modulo arithmetic

---

## 9. Revision History

| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 1.0 | 2025-10-31 | Claude | Initial legacy design |
| 2.0 | 2026-01-28 | Claude | Rewritten for result_to_dma + dma_bram_bridge architecture |

---

## 10. References

- **MULTI_ROW_REFERENCE.md**: 2D engine command structure and execution flow
- **Component Library UG086**: ACX_BRAM72K primitives
- **result_to_dma.sv**: Implementation source (circular buffer adapter)
- **dma_bram_bridge.sv**: BRAM storage with AXI4 interface
- **engine_top_2d.sv**: Engine integration point
