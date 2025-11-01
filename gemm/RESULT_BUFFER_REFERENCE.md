# Result Buffer Circular Queue Reference Manual

**Document Version**: 1.0
**Date**: October 31, 2025
**Component**: Result BRAM Circular Buffer (Pseudo-FIFO)
**Related Modules**: `result_fifo_to_simple_bram.sv`, `dma_bram_bridge.sv`, `elastix_gemm_top.sv`

---

## 1. Overview

The Result Buffer implements a **circular queue (ring buffer)** using random-access BRAM with manual pointer management. This design provides FIFO semantics for producer-consumer data flow between the GEMM engine (producer) and host DMA (consumer) while maintaining the flexibility of random-access reads required by the AXI4 DMA interface.

### 1.1 Key Characteristics

- **Capacity**: 8192 FP16 results (512 BRAM lines × 16 FP16/line)
- **Storage**: 2× ACX_BRAM72K_SDP instances (256-bit data width)
- **Addressing**: 13-bit pointers in 2-byte (FP16) granularity
- **Producer**: GEMM compute engine (writes results)
- **Consumer**: Host via PCIe DMA (reads results)
- **Backpressure**: Master control blocks commands when buffer almost full

### 1.2 Design Rationale

This design combines the benefits of:
- **FIFO ordering**: Results processed in strict order (oldest first)
- **Random access**: AXI4 DMA can perform burst reads at arbitrary addresses
- **Decoupled operation**: Engine and host operate independently at different rates
- **Efficient backpressure**: Hardware prevents buffer overflow automatically

---

## 2. Architecture

### 2.1 Buffer Organization

```
Physical BRAM Layout (512 lines × 256 bits):
┌────────────────────────────────────────────────────┐
│ Line 0:   [FP16_15][FP16_14]...[FP16_1][FP16_0]   │ ← 16 FP16 results
│ Line 1:   [FP16_31][FP16_30]...[FP16_17][FP16_16] │
│ ...                                                 │
│ Line 511: [...][FP16_8191]                         │
└────────────────────────────────────────────────────┘

Logical Circular Buffer (8192 FP16 results):
      ┌───────────────────────────┐
      │   [rd_ptr]                │ ← Host reads here
      │   ├─────────────────┤     │   (consumed space)
      │   │ Valid Results   │     │
      │   ├─────────────────┤     │
      │   [wr_ptr]                │ ← Engine writes here
      │   ├─────────────────┤     │   (free space)
      │   │ Free Space      │     │
      │   └─────────────────┘     │
      └───────────────────────────┘
         (wraps at 8192)
```

### 2.2 Pointer System

#### Write Pointer (wr_ptr)
- **Width**: 13 bits (0-8191)
- **Management**: Hardware auto-increments
- **Wrapping**: Automatic at 8192
- **Update**: Every FP16 write from compute engine
- **Exposure**: Read-only register for host monitoring

#### Read Pointer (rd_ptr)
- **Width**: 13 bits (0-8191)
- **Management**: Host controlled via register write
- **Wrapping**: Host responsibility (host computes wrap)
- **Update**: After host consumes N results via DMA
- **Exposure**: Read/write register

### 2.3 Address Mapping

**FP16 Pointer → BRAM Address Conversion:**

```
ptr[12:0] (13-bit FP16 address, 0-8191)
    ↓
BRAM Line Address    = ptr[12:4]  (upper 9 bits, 0-511 lines)
Position within Line = ptr[3:0]   (lower 4 bits, 0-15 FP16s)
Byte Address        = {ptr[12:0], 1'b0}  (2-byte aligned)
```

**Example:**
- `ptr = 13'd145` (FP16 #145)
  - BRAM line = `145 >> 4 = 9` (line 9)
  - Position = `145 & 0xF = 1` (2nd FP16 in line)
  - Byte address = `145 << 1 = 290` (byte 290)

---

## 3. Flow Control and Backpressure

### 3.1 Used Entries Calculation

**Circular Buffer Arithmetic:**

```systemverilog
used_entries[13:0] = (wr_ptr >= rd_ptr) ?
                     (wr_ptr - rd_ptr) :              // Normal case
                     (8192 - rd_ptr + wr_ptr);        // Wrapped case
```

**Examples:**
- `wr_ptr=100, rd_ptr=50` → `used_entries=50` (normal)
- `wr_ptr=10, rd_ptr=8190` → `used_entries=8192-8190+10=12` (wrapped)

### 3.2 Buffer State Flags

#### Almost Full Flag
```systemverilog
almost_full = (used_entries >= 7936)
```
- **Threshold**: 7936 FP16 results (256 results / 16 lines remaining)
- **Purpose**: Trigger backpressure before buffer completely fills
- **Action**: Master control blocks command FIFO
- **Margin**: 256 FP16 safety margin allows in-flight results to drain

#### Empty Flag
```systemverilog
empty = (wr_ptr == rd_ptr)
```
- **Meaning**: No valid results available
- **Purpose**: Host can check before reading
- **Note**: Software responsibility (hardware doesn't enforce)

### 3.3 Backpressure Mechanism

**Flow:**
1. Engine writes results → `wr_ptr` increments → `used_entries` increases
2. When `used_entries >= 7936` → `almost_full` asserts
3. Master control sees `almost_full` → blocks `cmd_fifo` reads
4. No new commands issued → engine starves → stops producing results
5. Host reads results via DMA → updates `rd_ptr` → `used_entries` decreases
6. When `used_entries < 7936` → `almost_full` deasserts
7. Master control resumes → new commands issued → engine continues

**Master Control Integration** (`master_control.sv:163-164`):
```systemverilog
if (!i_cmd_fifo_empty && !i_result_fifo_afull) begin
    state_next = ST_READ_HDR;  // Accept command
end
```

---

## 4. Operation Modes

### 4.1 Producer (Engine Write)

**Hardware Automatic Operation:**

```
For each compute result:
  1. Write FP16 to BRAM[wr_ptr[12:4]] at position wr_ptr[3:0]
  2. wr_ptr = (wr_ptr == 8191) ? 0 : wr_ptr + 1
  3. Update used_entries and almost_full
```

**Packing Behavior** (from `result_fifo_to_simple_bram.sv`):
- Engine produces 1 FP16 result at a time
- Module packs 16 FP16s into 256-bit BRAM line before writing
- Write occurs when 16th FP16 in line is ready
- Partial line flushed on reset

### 4.2 Consumer (Host Read)

**Software-Controlled Operation:**

```
Host DMA Read Procedure:
  1. Check empty flag: if (REG_RESULT_EMPTY) → no data available
  2. Read used_entries: N = REG_USED_ENTRIES
  3. Determine read count: read_count = min(N, desired_batch_size)
  4. DMA read from BRAM starting at REG_RD_PTR:
     - Convert rd_ptr to BRAM line address: line = rd_ptr >> 4
     - Read (read_count + 15) / 16 lines (round up)
  5. Extract FP16 results from read data
  6. Update rd_ptr: new_rd_ptr = (rd_ptr + read_count) % 8192
  7. Write REG_RD_PTR = new_rd_ptr
```

**Host Wrapping Responsibility:**
- Hardware does NOT auto-wrap rd_ptr
- Host must compute: `new_rd_ptr = (old_rd_ptr + N) % 8192`
- If read crosses 8192 boundary, host must handle as 2 separate DMA reads

---

## 5. Register Interface

### 5.1 Register Definitions

| Register Name | Address | Type | Width | Description |
|---------------|---------|------|-------|-------------|
| `REG_RD_PTR` | TBD | RW | [12:0] | Read pointer (host updates after consumption) |
| `REG_WR_PTR` | TBD | RO | [12:0] | Write pointer (current engine position) |
| `REG_USED_ENTRIES` | TBD | RO | [13:0] | Number of valid FP16 results (0-8192) |
| `REG_RESULT_EMPTY` | TBD | RO | [0:0] | Buffer empty flag (1=empty) |

### 5.2 Register Access Patterns

**Host Read Sequence:**
```c
// Check if data available
if (read_reg(REG_RESULT_EMPTY) == 1) {
    return NO_DATA;  // Buffer empty
}

// Determine how many results to read
uint32_t used = read_reg(REG_USED_ENTRIES);
uint32_t rd_ptr = read_reg(REG_RD_PTR);
uint32_t read_count = min(used, MAX_BATCH_SIZE);

// Perform DMA read from BRAM at rd_ptr
uint32_t line_addr = rd_ptr >> 4;
uint32_t lines_to_read = (read_count + 15) / 16;
dma_read(BRAM_BASE + line_addr * 32, lines_to_read * 32, dest_buffer);

// Update read pointer (host handles wrapping)
uint32_t new_rd_ptr = (rd_ptr + read_count) % 8192;
write_reg(REG_RD_PTR, new_rd_ptr);
```

**Host Monitoring:**
```c
// Monitor buffer fullness for performance analysis
uint32_t used = read_reg(REG_USED_ENTRIES);
uint32_t utilization = (used * 100) / 8192;  // Percentage
```

---

## 6. Edge Cases and Special Conditions

### 6.1 Buffer Full Condition

**Scenario**: `used_entries = 8192` (all slots occupied)

**Handling:**
- `almost_full` asserts at 7936 (before full)
- Master control blocks commands → engine stops → no overflow
- 256-entry safety margin allows in-flight results to drain
- True full condition (8192) should never occur in normal operation

### 6.2 Buffer Empty Condition

**Scenario**: `wr_ptr == rd_ptr` (no valid data)

**Handling:**
- `empty` flag asserts
- Host checks flag before reading (software responsibility)
- Reading from empty buffer returns stale data (no hardware protection)
- Host must validate `used_entries > 0` before DMA read

### 6.3 Pointer Wrap Cases

**Write Pointer Wrap** (hardware):
```
wr_ptr = 8191 → next write → wr_ptr = 0 (automatic)
```

**Read Pointer Wrap** (software):
```c
// Host reading 100 results from rd_ptr=8150
uint32_t rd_ptr = 8150;
uint32_t read_count = 100;
uint32_t new_rd_ptr = (8150 + 100) % 8192;  // = 58 (wrapped)

// Must handle as two DMA reads:
// Read 1: lines 509-511 (8150→8191, 42 results)
// Read 2: lines 0-3 (0→57, 58 results)
```

### 6.4 Concurrent Access

**Scenario**: Engine writes while host updates rd_ptr

**Handling:**
- Both operations occur in same clock domain (`i_clk`)
- Hardware updates `wr_ptr` → combinational `used_entries` update
- Host writes `rd_ptr` register → combinational `used_entries` update
- No race condition: pointers update atomically within clock cycle
- `used_entries` reflects most recent pointer values

### 6.5 Reset Behavior

**Hardware Reset** (`i_reset_n = 0`):
```
wr_ptr <= 13'd0
rd_ptr <= 13'd0  (via register reset)
used_entries = 0
almost_full = 0
empty = 1
```

**Software Reset** (`i_write_top_reset = 1`):
```
wr_ptr <= 13'd0  (preserves rd_ptr)
Partial packed line flushed to BRAM
Note: Host should write rd_ptr=0 for full reset
```

---

## 7. Performance Characteristics

### 7.1 Latency

| Operation | Latency | Notes |
|-----------|---------|-------|
| Engine Write | 1 cycle | Write to BRAM when line complete |
| Pointer Update | 0 cycles | Combinational logic |
| Flag Update | 1 cycle | Registered outputs |
| Host Read | ~2 cycles | BRAM read latency (outreg enabled) |
| DMA Burst | N cycles | Depends on AXI burst length |

### 7.2 Throughput

- **Engine Write**: 1 FP16/cycle (after packing)
- **Host Read**: Limited by PCIe/DMA bandwidth
- **Backpressure Latency**: ~10-20 cycles (command pipeline depth)

### 7.3 Buffer Sizing Rationale

**Why 8192 FP16s (512 lines)?**
- Matches BRAM depth (512 entries)
- Large enough to absorb bursts from compute engine
- 256-entry margin allows in-flight operations to complete
- Power-of-2 size simplifies modulo arithmetic

---

## 8. Integration Points

### 8.1 Module Connections

```
result_fifo_to_simple_bram:
  Inputs:  i_fifo_rdata (from compute_engine)
           i_rd_ptr (from register file)
  Outputs: o_wr_ptr, o_used_entries, o_empty (to registers)
           o_bram_wr_addr, o_bram_wr_data, o_bram_wr_en (to dma_bram_bridge)
           o_almost_full (to master_control)

master_control:
  Input:   i_result_fifo_afull (from result_fifo_to_simple_bram)
  Logic:   Block cmd_fifo reads when i_result_fifo_afull = 1

dma_bram_bridge:
  Inputs:  i_internal_wr_addr, i_internal_wr_data, i_internal_wr_en
           (from result_fifo_to_simple_bram via top-level)
  Storage: 2× ACX_BRAM72K_SDP (256-bit data, 512-deep)
  Outputs: AXI4 read interface for host DMA access
```

### 8.2 Clock Domain

- **All operations**: Single clock domain (`i_clk`)
- **No CDC required**: Host register writes synchronous to `i_clk`
- **Assumption**: PCIe register interface is synchronous or properly synchronized

---

## 9. Debug and Monitoring

### 9.1 Real-Time Monitoring

**Registers for debugging:**
```c
uint32_t wr_ptr = read_reg(REG_WR_PTR);
uint32_t rd_ptr = read_reg(REG_RD_PTR);
uint32_t used = read_reg(REG_USED_ENTRIES);
uint32_t empty = read_reg(REG_RESULT_EMPTY);

printf("Buffer: wr=%d rd=%d used=%d empty=%d\n",
       wr_ptr, rd_ptr, used, empty);
```

### 9.2 Common Issues

| Symptom | Possible Cause | Solution |
|---------|----------------|----------|
| Commands stall | Buffer full | Check host is reading results |
| Empty flag never clears | Engine not running | Verify compute engine active |
| used_entries wraps | Pointer arithmetic error | Check rd_ptr update logic |
| Stale data read | Reading from empty | Check empty flag before read |

---

## 10. Software Example

### 10.1 Initialization

```c
void result_buffer_init(void) {
    // Reset both pointers
    write_reg(REG_RD_PTR, 0);
    // Wait for wr_ptr to also reset (hardware reset)
    while (read_reg(REG_WR_PTR) != 0);
}
```

### 10.2 Read Results

```c
int result_buffer_read(fp16_t *dest, uint32_t max_count) {
    // Check if data available
    if (read_reg(REG_RESULT_EMPTY)) {
        return 0;  // No data
    }

    uint32_t used = read_reg(REG_USED_ENTRIES);
    uint32_t rd_ptr = read_reg(REG_RD_PTR);
    uint32_t read_count = (used < max_count) ? used : max_count;

    // Handle wrap-around case
    if (rd_ptr + read_count > 8192) {
        // Split into two DMA reads
        uint32_t first_chunk = 8192 - rd_ptr;
        uint32_t second_chunk = read_count - first_chunk;

        dma_read_fp16(rd_ptr, first_chunk, dest);
        dma_read_fp16(0, second_chunk, dest + first_chunk);

        write_reg(REG_RD_PTR, second_chunk);
    } else {
        // Single DMA read
        dma_read_fp16(rd_ptr, read_count, dest);
        write_reg(REG_RD_PTR, rd_ptr + read_count);
    }

    return read_count;
}
```

---

## 11. Verification Checklist

### 11.1 Unit Tests (Simulation)

- [ ] Verify `used_entries` calculation (normal case: wr > rd)
- [ ] Verify `used_entries` calculation (wrapped case: wr < rd)
- [ ] Verify `almost_full` triggers at 7936
- [ ] Verify `empty` flag when `wr_ptr == rd_ptr`
- [ ] Verify `wr_ptr` wraps at 8192
- [ ] Verify backpressure blocks master_control

### 11.2 Integration Tests (Hardware)

- [ ] Run GEMM operation, verify `wr_ptr` increments
- [ ] Fill buffer to almost_full, verify commands block
- [ ] Host reads results, verify `rd_ptr` updates
- [ ] Verify `used_entries` decreases after read
- [ ] Verify commands resume after draining
- [ ] Stress test: continuous write/read cycles

---

## 12. Revision History

| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 1.0 | 2025-10-31 | Claude | Initial release |

---

## 13. References

- **SINGLE_ROW_REFERENCE.md**: Command structure and execution flow
- **STATE_TRANSITIONS_REFERENCE.md**: Master control FSM behavior
- **Component Library UG086**: ACX_BRAM72K primitives
- **result_fifo_to_simple_bram.sv**: Implementation source
- **master_control.sv**: Backpressure integration
