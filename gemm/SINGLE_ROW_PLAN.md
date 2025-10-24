# Single-Row Multi-Tile Architecture Development Plan

**Project**: GEMM Engine Single-Row Multi-Tile Migration
**Status**: ✅ **PHASE 1 COMPLETE!** All 16 results matching golden values
**Last Updated**: Tue Oct 21 02:17:21 PDT 2025

---

## Executive Summary

Migrating GEMM engine from single compute_engine_modular to scalable single-row multi-tile architecture supporting up to 16 parallel compute tiles per row. Implementing three-level memory hierarchy (L3: GDDR6 → L2: dispatcher_bram → L1: tile_bram) with DISPATCH phase to distribute data across tiles for parallel matrix operations within a row.

**Current Status**: ✅ **PHASE 1 COMPLETE!** All infrastructure, synchronization, and data correctness validated. DISPATCH correctly copies 512 aligned lines to tile_bram, WAIT_DISPATCH synchronization working, and all 16 results match golden values perfectly. Single-tile functionality fully validated, ready for Phase 2 multi-tile DISPATCH implementation.

---

## Overall Goal

**Transform single-tile architecture into multi-tile system**:
- **Before**: 1 compute engine reads from shared dispatcher_bram
- **After**: N compute tiles (N≤16) with private L1 caches, parallel execution

**Key Benefits**:
- **Scalability**: Linear performance scaling with tile count
- **Flexibility**: Runtime-configurable tile count via column_enable mask
- **Efficiency**: Parallel GEMM operations for large matrices

---

## Architecture Overview

### Three-Level Memory Hierarchy

```
L3: GDDR6 (Shared, 8 channels)
    ↓ FETCH (AXI4 burst reads)
L2: dispatcher_bram (Shared per row, 2048×256-bit)
    ↓ DISPATCH (data copy + distribute)
L1: tile_bram (Private per tile, 512×256-bit each)
    ↓ MATMUL (parallel computation)
Compute Tile[0..15] (16 parallel engines)
    ↓ Results
Result Collector (aggregate tile outputs)
```

### Command Flow (5-stage pipeline)

1. **FETCH** (0xF0): GDDR6 → dispatcher_bram (528 lines)
2. **DISPATCH** (0xF1): dispatcher_bram → tile_bram[0..N-1] (broadcast/distribute)
3. **WAIT_DISPATCH** (0xF3): Synchronization barrier
4. **MATMUL** (0xF2): Parallel tile computation
5. **WAIT_MATMUL** (0xF4): Result collection ready

---

## Hardware Architecture Details

### Memory Block Organization

**One Memory Block = 528 Lines Total**

The data fetched from GDDR6 is organized in a packed format optimized for transfer efficiency:

```
Lines 0-15:   Packed Exponents (16 lines)
              ├─ 32 exponents per line × 16 lines = 512 exponents total
              └─ Each exponent is 1 byte (8 bits)

Lines 16-527: Mantissa Groups (512 lines)
              ├─ One group per line (32 mantissa bytes)
              ├─ Each group shares one exponent
              └─ 4 consecutive lines = 1 Native Vector (NV)
```

**Direct 1:1 Exponent-to-Mantissa Mapping:**
- Mantissa line 16 → uses exponent from line 0, byte 0
- Mantissa line 17 → uses exponent from line 0, byte 1
- ...
- Mantissa line 47 → uses exponent from line 0, byte 31
- Mantissa line 48 → uses exponent from line 1, byte 0
- etc.

**Native Vector (NV) Structure:**
- 1 NV = 4 groups = 4 consecutive mantissa lines
- Each group has its own exponent byte
- 128 NVs × 4 groups = 512 groups total

### FETCH Operation - Detailed Flow

**Purpose**: Transfer memory block from GDDR6 and unpack exponents into aligned format

**Command Parameters**
- **Start Address** (32 bits): Address to read from GDDR6
- **Length** (16 bits): Number of memory blocks to fetch. Currently should be expecting . 

**Three-Stage Process:**

1. **Stage 1 - Packed Exponent Fetch** (Lines 0-15):
   - Read 16 lines from GDDR6
   - Write to `exp_packed` staging buffer (256-bit wide)
   - Target: `exp_left_packed[0-15]` or `exp_right_packed[0-15]`

2. **Stage 2 - Mantissa Fetch** (Lines 16-527):
   - Read 512 lines from GDDR6
   - Write to `man` buffer with address translation
   - **Address Translation**: GDDR6 line N → `man[N-16]`
   - Example: Line 16 → man[0], Line 527 → man[511]

3. **Parallel Unpacking** (During Stage 2):
   - While fetching 512 mantissa lines (takes 512 cycles minimum)
   - dispatcher_control reads from `exp_packed` buffer
   - Extracts individual exponent bytes (32 per packed line)
   - Writes to `exp_aligned` buffer: exp[0], exp[1], ..., exp[511]

**Final Result - Four Aligned Buffers:**
- `exp_left_aligned[0-511]`: 512 individual exponent bytes ✓
- `man_left[0-511]`: 512 mantissa group lines ✓
- `exp_right_aligned[0-511]`: 512 individual exponent bytes ✓
- `man_right[0-511]`: 512 mantissa group lines ✓

**Key Feature**: Exponents are now aligned 1:1 with mantissa lines for efficient tile_bram access.

### DISPATCH Operation - Specification

**Purpose**: Copy aligned data from shared L2 (dispatcher_bram) to private L1 (tile_bram)

**Command Parameters** (from MS2.0_uCode-Single_Row.csv):
- **Mantissa NV count** (8 bits): Number of Native Vectors to dispatch
  - Each NV = 4 lines → Total lines = NV_count × 4
  - Example: 128 NVs = 512 lines
- **Tile destination address** (16 bits): Starting line in tile_bram where data will be written
- **UGD vector size** (8 bits): NVs per UGD (kept for compatibility)
- **Flags** (8 bits):
  - Bit [0]: Mantissa width (4-bit vs 8-bit)
  - Bit [1]: **Broadcast** (copy to all tiles) vs **Distribute** (spread across tiles)
  - Bits [6:2]: Distribution start column
  - Bit [7]: Reserved

**Addressing Behavior:**

```
Source (dispatcher_bram aligned buffers):
├─ ALWAYS reads starting from address 0
├─ Reads NV_count × 4 consecutive lines: [0, 1, 2, ..., NV_count×4-1]
└─ Source pointer RESETS to 0 after each DISPATCH command completes

Destination (tile_bram):
├─ Writes starting at command-specified dest_addr
├─ Writes NV_count × 4 lines to: [dest_addr, dest_addr+1, ..., dest_addr+NV_count×4-1]
└─ Multiple DISPATCH commands can fill different tile_bram regions
```

**Example Use Cases:**
```
DISPATCH 1: NV_count=64, dest_addr=0
  → Copies dispatcher_bram[0-255] to tile_bram[0-255]

DISPATCH 2: NV_count=64, dest_addr=256
  → Copies dispatcher_bram[0-255] to tile_bram[256-511]
  (Note: Source always starts at 0!)
```

**CRITICAL DESIGN NOTE**: The testbench parameter `disp_len=528` is INCORRECT. The correct value should be `NV_count × 4 = 512` because DISPATCH operates on aligned buffers (512 lines), not packed memory blocks (528 lines).

### Broadcast vs Distribute Modes

**Broadcast Mode** (Flag bit [1] = 1):
- **Behavior**: Write same line to ALL enabled tiles before advancing source
- **Use Case**: Left activations need to be replicated across all tiles
- **Example**: 64 lines broadcast to 4 enabled tiles
  ```
  Cycle 0: Line 0 → Tile 0
  Cycle 1: Line 0 → Tile 1
  Cycle 2: Line 0 → Tile 2
  Cycle 3: Line 0 → Tile 3
  Cycle 4: Line 1 → Tile 0
  ...
  Total: 64 lines × 4 tiles = 256 write cycles
  ```
- **Result**: All 4 tiles have identical copies of lines [0-63]

**Distribute Mode** (Flag bit [1] = 0):
- **Behavior**: Write each line to ONE tile in round-robin fashion
- **Use Case**: Right weights sharded across tiles for parallel computation
- **Example**: 256 lines distributed to 4 enabled tiles
  ```
  Cycle 0: Line 0 → Tile 0
  Cycle 1: Line 1 → Tile 1
  Cycle 2: Line 2 → Tile 2
  Cycle 3: Line 3 → Tile 3
  Cycle 4: Line 4 → Tile 0
  Cycle 5: Line 5 → Tile 1
  ...
  Total: 256 write cycles
  ```
- **Result**: Each tile gets 64 lines in interleaved pattern
  - Tile 0: [0, 4, 8, 12, ..., 252]
  - Tile 1: [1, 5, 9, 13, ..., 253]
  - Tile 2: [2, 6, 10, 14, ..., 254]
  - Tile 3: [3, 7, 11, 15, ..., 255]

**Phase 1 Configuration**: Broadcast to tile[0] only (column_enable = 0x0001)

### Four Parallel Data Paths

**CRITICAL**: All four paths operate simultaneously in the same clock cycle!

This parallelism is why dispatcher_bram and tile_bram are partitioned into four separate buffers:

```systemverilog
// Left Matrix Paths (2 parallel)
exp_left_aligned[0-511]  ↔  tile_bram_left.exp[0-511]   (8-bit exponents)
man_left[0-511]          ↔  tile_bram_left.man[0-511]   (256-bit mantissas)

// Right Matrix Paths (2 parallel)
exp_right_aligned[0-511] ↔  tile_bram_right.exp[0-511]  (8-bit exponents)
man_right[0-511]         ↔  tile_bram_right.man[0-511]  (256-bit mantissas)
```

**During DISPATCH:**
- All four paths read/write in lockstep
- Single address counter drives all four read addresses
- Single delayed write address drives all four write addresses
- Enables maximum bandwidth utilization (4 × 256-bit + 4 × 8-bit per cycle)

**During MATMUL:**
- Compute engine reads from tile_bram using same four-path structure
- Left and right exponents/mantissas accessed independently
- Supports parallel dot-product computation across groups

### tile_bram Organization

**Key Insight**: tile_bram has IDENTICAL organization to dispatcher_bram's aligned buffers!

```
tile_bram_left:
├─ exp[0-511]:  512 exponent bytes (8-bit each)
└─ man[0-511]:  512 mantissa lines (256-bit each)

tile_bram_right:
├─ exp[0-511]:  512 exponent bytes (8-bit each)
└─ man[0-511]:  512 mantissa lines (256-bit each)
```

**Why This Matters**:
- Compute engine logic remains unchanged from single-tile version
- Address generation works identically for L1 (tile_bram) as it did for L2 (dispatcher_bram)
- Only difference: Compute engine now reads from private tile_bram instead of shared dispatcher_bram

**Storage Capacity per tile**:
- 512 lines × 256-bit = 16 KB mantissa data
- 512 bytes exponent data
- Total: 128 Native Vectors per tile

---

## MS2.0 Microcode Command Reference

This section documents all commands supported by the MS2.0 architecture, aligned with the [MS2.0_uCode-Single_Row.csv](/home/dev/Dev/elastix_gemm/MS2.0_uCode-Single_Row.csv) specification and the actual hardware implementation in [gemm_pkg.sv](/home/dev/Dev/elastix_gemm/gemm/src/include/gemm_pkg.sv).

### Command Architecture

**Fixed 4-Word Format**: All commands in MS2.0 use a consistent 4-word (128-bit) structure for uniform FIFO processing:
- **Word 0**: Command Header (32 bits)
  - Bits [31:16]: Total length in bytes
  - Bits [15:8]: Command ID (for tracking and synchronization)
  - Bits [7:0]: Opcode
- **Words 1-3**: Command Payload (96 bits total, unused words = 0x00000000)

This fixed format simplifies command processing in hardware, even though individual commands may only use 1-2 payload words.

### Command Summary Table

| Opcode | Name | Total Length | Args Bytes | Purpose |
|--------|------|--------------|------------|---------|
| 0xF0 | fetch_memory_block | 12 bytes | 9 | Transfer memory block from GDDR6 to dispatcher_bram |
| 0xF1 | vector_dispatch | 8 bytes | 5 | Copy data from dispatcher_bram to tile_bram (broadcast/distribute) |
| 0xF2 | matmul | 16 bytes | 13 | Execute parallel matrix multiplication across enabled tiles |
| 0xF3 | wait_dispatch | 4 bytes | 1 | Synchronization barrier - wait for DISPATCH command to complete |
| 0xF4 | wait_matmul | 4 bytes | 1 | Synchronization barrier - wait for MATMUL command to complete |
| 0xF5 | vector_readout | 8 bytes | 5 | Read result vectors from result_bram to host |

---

### Command 0xF0: FETCH_MEMORY_BLOCK

**Purpose**: Transfer a memory block (528 lines) from GDDR6 external memory to dispatcher_bram's internal staging buffers.

**Total Length**: 12 bytes (Header: 4 bytes, Payload: 8 bytes)

#### CSV Specification

| Field | Bits | Description |
|-------|------|-------------|
| **Start Address** | 32 | External memory relative address (divided by 8 for byte alignment) |
| **Length** | 16 | Number of 128-byte chunks of data to read (exp+mantissas) |
| **Fetch Right** | 1 | Fetch to right buffer if asserted. Otherwise, fetch to left. |

#### Hardware Packing (4-Word Format)

```systemverilog
// From tb_engine_top.sv generate_fetch_command()
typedef struct packed {
    logic [14:0] reserved;          // 15 bits
    logic        fetch_right;       // 1 bit: 0=left, 1=right
    logic [15:0] len;               // 16 bits: number of lines
    logic [31:0] start_addr;        // 32 bits: byte address
} cmd_fetch_s;                      // Total: 64 bits

// 4-Word Packing:
cmd[0] = {16'd12, cmd_id[7:0], e_cmd_op_fetch};   // Header
cmd[1] = start_addr[31:0];                        // Word 1: Address
cmd[2] = {reserved[15:0], len[15:0]};             // Word 2: Length
cmd[3] = {reserved[30:0], fetch_right}            // Word 3: Target
```

#### Field Details

- **Start Address (32 bits)**: Byte address in GDDR6 memory, divided by 8 for natural alignment
  - Hardware converts to AXI address: `{GDDR6_PAGE_ID[8:0], addr[31:5], 5'b0}`
  - The 5 LSB are for 32-byte (256-bit) alignment
  - Example: 0x00000000 → starts at beginning of GDDR6 page

- **Length (16 bits)**: Number of 256-bit lines to fetch
  - For one memory block: 528 lines (16 exp packed + 512 mantissa)
  - Fetched in AXI bursts of 16 beats each

- **Fetch Right (1 bit)**: Target buffer selection
  - 0 = Write to left buffers (exp_left_packed, man_left)
  - 1 = Write to right buffers (exp_right_packed, man_right)

#### Operation Flow

See "FETCH Operation - Detailed Flow" section above for the 3-stage process:
1. Packed exponent fetch (lines 0-15)
2. Mantissa fetch (lines 16-527) with address translation
3. Parallel exponent unpacking (aligned buffer generation)

**Example**:
```systemverilog
// Fetch left matrix block starting at GDDR6 address 0x0
FETCH: id=1, start_addr=0x0, len=528, fetch_right=0
```

---

### Command 0xF1: VECTOR_DISPATCH

**Purpose**: Copy aligned data from shared L2 (dispatcher_bram) to private L1 (tile_bram) for each compute tile.

**Total Length**: 8 bytes (Header: 4 bytes, Payload: 4 bytes)

#### CSV Specification

| Field | Bits | Description |
|-------|------|-------------|
| **Mantissa NV cnt** | 8 | Number of Native Vectors to process (each NV = 4 lines) |
| **Tile destination address** | 16 | Destination tile buffer start address |
| **UGD vector size** | 8 | Number of native vectors per UGD vector |
| **Flags** | 8 | Control flags (detailed below) |

#### Flags Field (8 bits)

| Bit(s) | Name | Description |
|--------|------|-------------|
| [0] | Mantissa width | 0 = 8-bit mantissas, 1 = 4-bit mantissas |
| [1] | Distribution mode | 0 = Distribute (round-robin across tiles), 1 = Broadcast (replicate to all tiles) |
| [6:2] | Tensor distribution start column | Starting column for distribution (0-15) |
| [7] | Reserved | Reserved for future use |

#### Hardware Packing (4-Word Format)

```systemverilog
// From gemm_pkg.sv and tb_engine_top.sv
typedef struct packed {
    logic [12:0]                      reserved;     // 13 bits
    logic                             man_4b_8b_n;  // 1 bit
    logic [tile_mem_addr_width_gp-1:0] len;        // 11 bits (tile_addr_width=11)
    logic [tile_mem_addr_width_gp-1:0] tile_addr;  // 11 bits
} cmd_disp_s;  // Total: 36 bits (simplified from CSV)

// 4-Word Packing:
cmd[0] = {16'd8, id[7:0], e_cmd_op_disp};              // Header
cmd[1] = {man_4b_8b_n, 10'b0, disp_len, disp_addr};    // Word 1: Payload
cmd[2] = 32'h00000000;                                 // Word 2: Unused
cmd[3] = 32'h00000000;                                 // Word 3: Unused
```

**Note**: Current hardware implementation uses a simplified version compared to CSV spec. Full broadcast/distribute flags are pending Phase 2.3 implementation.

#### Field Details

- **Mantissa NV count (8 bits in CSV, mapped to len×4 in hardware)**:
  - Number of Native Vectors to dispatch
  - Hardware stores as line count: `len = NV_count × 4`
  - Example: 128 NVs → 512 lines

- **Tile destination address (16 bits in CSV, 11 bits in hardware)**:
  - Starting line in tile_bram where data will be written
  - Range: 0-511 (tile_bram has 512 lines)
  - Multiple DISPATCH commands can fill different regions

- **UGD vector size (8 bits)**:
  - Kept for compatibility, typically 1

- **Flags**:
  - Currently only man_4b_8b_n is implemented (bit 0 equivalent)
  - Broadcast/distribute mode (bit 1) planned for Phase 2.3

#### Operation Modes

See "Broadcast vs Distribute Modes" section above for detailed behavior:
- **Broadcast Mode**: Replicates same line to all enabled tiles (for left activations)
- **Distribute Mode**: Round-robin distribution across tiles (for right weights)

**Example**:
```systemverilog
// Dispatch 128 NVs (512 lines) to tile_bram starting at address 0
DISPATCH: id=2, NV_count=128, dest_addr=0, man_4b=0, broadcast=1
```

---

### Command 0xF2: MATMUL

**Purpose**: Execute parallel matrix multiplication across enabled compute tiles.

**Total Length**: 16 bytes (Header: 4 bytes, Payload: 12 bytes)

#### CSV Specification

| Field | Bits | Description |
|-------|------|-------------|
| **Left start address** | 16 | Left vector start pointer in tile_bram |
| **Right start address** | 16 | Right vector start pointer in tile_bram |
| **Left UGD vectors** | 8 | Number of UGD vectors to process on left |
| **Right UGD vectors** | 8 | Number of UGD vectors to process on right |
| **UGD vector size** | 8 | Number of native vectors per UGD vector |
| **Column enable** | 16 | 1 bit per column (tile enable mask) |
| **Flags_0** | 8 | Control flags (detailed below) |
| **Reserved** | 24 | Reserved for future use |

#### Flags_0 Field (8 bits)

| Bit(s) | Name | Description |
|--------|------|-------------|
| [0] | Left mantissa width | 0 = 8-bit, 1 = 4-bit |
| [1] | Right mantissa width | 0 = 8-bit, 1 = 4-bit |
| [2] | Main loop dimension | 0 = loop over right, 1 = loop over left |
| [7:3] | Reserved | Reserved for future use |

#### Hardware Packing (4-Word Format)

```systemverilog
// From gemm_pkg.sv
typedef struct packed {
    logic [7:0]                        dim_b;           // 8 bits: Batch dimension
    logic [7:0]                        dim_c;           // 8 bits: Column dimension
    logic [7:0]                        dim_v;           // 8 bits: Vector count
    cmd_flags_s                        flags;           // 8 bits: Control flags
    logic [tile_mem_addr_width_gp-1:0] vec_len;         // 11 bits: Vector length
    logic [tile_mem_addr_width_gp-1:0] right_ugd_len;   // 11 bits
    logic [tile_mem_addr_width_gp-1:0] left_ugd_len;    // 11 bits
    logic [tile_mem_addr_width_gp-1:0] right_addr;      // 11 bits
    logic [tile_mem_addr_width_gp-1:0] left_addr;       // 11 bits
} cmd_tile_s;  // Total: 87 bits

// 4-Word Packing:
cmd[0] = header;                // {reserved, len, id, opcode}
cmd[1] = payload[31:0];         // {left_addr, right_addr, left_ugd_len[7:0], right_ugd_len[2:0]}
cmd[2] = payload[63:32];        // {right_ugd_len[10:3], vec_len, flags, dim_v}
cmd[3] = {9'b0, payload[86:64]}; // {dim_b, dim_c, padding}
```

#### Field Details

- **Left/Right Addresses (16 bits in CSV, 11 bits in hardware)**:
  - Starting line in tile_bram for left and right matrices
  - Range: 0-511 per tile_bram capacity

- **Left/Right UGD vectors (8 bits)**:
  - Number of Unified Group Dot vectors to process
  - Typically 1 for single-tile mode

- **UGD vector size (8 bits, stored as vec_len[10:0] in hardware)**:
  - Number of Native Vectors per UGD
  - Maps to dim_v parameter

- **Column enable (16 bits)**:
  - Bitmask for enabling tiles: bit 0 = tile 0, bit 1 = tile 1, etc.
  - Phase 1: 0x0001 (single tile)
  - Phase 2+: Variable (1-16 tiles)

- **dim_b, dim_c, dim_v (8 bits each)**:
  - Matrix dimensions for output size calculation
  - dim_b × dim_c = number of FP16 results per tile

**Example**:
```systemverilog
// Execute 4×4 matrix with 32 NVs on single tile
MATMUL: id=3, left_addr=0, right_addr=0, dim_b=4, dim_c=4, dim_v=32
        left_man_4b=0, right_man_4b=0, loop_over_left=0
```

---

### Command 0xF3: WAIT_DISPATCH

**Purpose**: Synchronization barrier - blocks until specified DISPATCH command completes.

**Total Length**: 4 bytes (Header only, no payload)

#### CSV Specification

| Field | Bits | Description |
|-------|------|-------------|
| **ID** | 8 | Command ID to wait for (matches DISPATCH command's ID) |

#### Hardware Packing (4-Word Format)

```systemverilog
// From gemm_pkg.sv and tb_engine_top.sv
typedef struct packed {
    logic [23:0]                reserved;  // 24 bits
    logic [cmd_id_width_gp-1:0] wait_id;   // 8 bits
} cmd_wait_disp_s;  // Total: 32 bits

// 4-Word Packing:
cmd[0] = {16'd4, wait_id[7:0], e_cmd_op_wait_disp};  // Header with wait_id in ID field
cmd[1] = 32'h00000000;                               // Word 1: Unused
cmd[2] = 32'h00000000;                               // Word 2: Unused
cmd[3] = 32'h00000000;                               // Word 3: Unused
```

#### Synchronization Mechanism

Hardware tracks completed DISPATCH commands using `last_disp_id_reg`:
1. When DISPATCH completes: `last_disp_id_reg <= cmd_id`
2. WAIT_DISPATCH blocks until: `last_disp_id_reg >= wait_id`
3. Master control FSM stalls in ST_WAIT_DISP state until condition satisfied

**Example**:
```systemverilog
DISPATCH: id=2, ...              // Start DISPATCH operation
WAIT_DISPATCH: wait_id=2         // Block until DISPATCH id=2 completes
MATMUL: id=3, ...                // Safe to proceed, data is ready
```

---

### Command 0xF4: WAIT_MATMUL

**Purpose**: Synchronization barrier - blocks until specified MATMUL command completes.

**Total Length**: 4 bytes (Header only, no payload)

#### CSV Specification

| Field | Bits | Description |
|-------|------|-------------|
| **ID** | 8 | Command ID to wait for (matches MATMUL command's ID) |

#### Hardware Packing (4-Word Format)

```systemverilog
// From gemm_pkg.sv and tb_engine_top.sv
typedef struct packed {
    logic [23:0]                reserved;  // 24 bits
    logic [cmd_id_width_gp-1:0] wait_id;   // 8 bits
} cmd_wait_tile_s;  // Total: 32 bits

// 4-Word Packing:
cmd[0] = {wait_id[7:0], 8'd0, id[7:0], e_cmd_op_wait_tile};  // Header
cmd[1] = 32'h00000000;                                       // Word 1: Unused
cmd[2] = 32'h00000000;                                       // Word 2: Unused
cmd[3] = 32'h00000000;                                       // Word 3: Unused
```

**Note**: Header format differs slightly from WAIT_DISPATCH - wait_id is in bits [31:24] instead of [15:8].

#### Synchronization Mechanism

Hardware tracks completed MATMUL commands using `last_tile_id_reg`:
1. When MATMUL completes: `last_tile_id_reg <= cmd_id`
2. WAIT_MATMUL blocks until: `last_tile_id_reg >= wait_id`
3. Master control FSM stalls in ST_WAIT_TILE state until condition satisfied

**Example**:
```systemverilog
MATMUL: id=3, ...                // Start matrix multiplication
WAIT_MATMUL: wait_id=3           // Block until MATMUL id=3 completes
// Results are now ready in result_bram
```

---

### Command 0xF5: VECTOR_READOUT

**Purpose**: Read result vectors from result_bram and send to host via PCIe.

**Total Length**: 8 bytes (Header: 4 bytes, Payload: 4 bytes)

#### CSV Specification

| Field | Bits | Description |
|-------|------|-------------|
| **Start Col** | 8 | Starting column index for readout |
| **Length** | 32 | Number of FP16 results to read |

#### Implementation Status

⚠️ **Currently not implemented in this version** - Results are read directly via result FIFO interface in the testbench. This command is defined in the CSV specification for future host-driven result retrieval.

**Planned Usage**:
```systemverilog
VECTOR_READOUT: start_col=0, length=16  // Read 16 FP16 results starting at column 0
```

---

### Command Execution Flow Example

Typical command sequence for a single matrix multiplication:

```systemverilog
// 1. Fetch left matrix (528 lines → dispatcher_bram left buffers)
FETCH: id=1, addr=0x0, len=528, target=left

// 2. Fetch right matrix (528 lines → dispatcher_bram right buffers)
FETCH: id=2, addr=0x10680, len=528, target=right

// 3. Dispatch left data to tile_bram (512 aligned lines)
DISPATCH: id=3, dest_addr=0, len=512, broadcast=1

// 4. Wait for dispatch to complete
WAIT_DISPATCH: wait_id=3

// 5. Execute matrix multiplication
MATMUL: id=4, left_addr=0, right_addr=0, dim_b=4, dim_c=4, dim_v=32

// 6. Wait for computation to complete
WAIT_MATMUL: wait_id=4

// 7. Results now available in result_bram/FIFO
```

This 7-command sequence produces 16 FP16 results (4×4 matrix).

---

## Development Phases

### ✅ Phase 1: Multi-Tile Infrastructure (COMPLETE)

**Goal**: Create foundational multi-tile components with backward compatibility

**Deliverables**:
- [x] tile_bram_wrapper.sv (512×256-bit dual-port BRAM per tile)
- [x] compute_tile_array.sv (NUM_TILES instantiation wrapper)
- [x] engine_top.sv integration (replace single engine with tile array)
- [x] DISPATCH FSM skeleton in dispatcher_control.sv
- [x] Single-tile mode (column_enable = 16'h0001)

**Status**: ✅ **COMPLETE** (Mon Oct 20 14:03:19 PDT 2025)

**Validation**: Compiles successfully, 0 Errors, 19 Warnings

---

### ⚠️ Phase 2: DISPATCH Data Copy Implementation (IN PROGRESS)

**Goal**: Implement L2→L1 data distribution for tile-local execution

**Phase 2.1**: Minimal DISPATCH (Single-Tile Mode) ✅ DONE
- [x] Data copy logic: dispatcher_bram → tile_bram[0]
- [x] Address generation (disp_cnt_reg counter)
- [x] Write enable generation (tile_wr_en_mask = 16'h0001)
- [x] All 4 data paths (left/right × mantissa/exponent)
- [x] Testbench update (disp_len = 528)

**Status**: ✅ Data copy working (5290 cycles for 528 lines verified)

**Phase 2.2**: Synchronization Debug ✅ COMPLETE
- [x] Fix duplicate parameter assignment bug
- [x] Fix testbench DISPATCH length (0 → 528)
- [x] Fix wait_id header location bug (bits [31:24] → [15:8])
- [x] Add ID tracking debug prints
- [x] Verify WAIT_DISPATCH synchronization working

**Phase 1.6**: Result Correctness Debug ✅ COMPLETE
- [x] WAIT_DISPATCH unblocked, results received (16/16)
- [x] Architecture understanding aligned (memory block format, FETCH/DISPATCH flow)
- [x] Fix DISPATCH addressing (source always 0, dest from command, length = NV_count×4)
- [x] Fix testbench disp_len from 528 to 512
- [x] Single-tile data path validated (broadcast/distribute logic deferred to Phase 2.3)
- [x] **ALL 16 results match golden values perfectly!** 🎉

**Phase 2.3**: Full Multi-Tile DISPATCH (PENDING)
- [ ] Broadcast mode: Left activation to all tiles (tile_wr_en_left = column_enable)
- [ ] Distribute mode: Right weights split across tiles
- [ ] Configurable tile count via column_enable parameter
- [ ] Address offset calculation per tile

---

### 🔲 Phase 3: Master Control Updates (PENDING)

**Goal**: Update command processing for multi-tile MATMUL and result collection

**Deliverables**:
- [ ] MATMUL command: Enable N tiles via column_enable
- [ ] Tile enable logic: o_ce_tile_en[15:0] from column_enable
- [ ] Result size calculation: (dim_b × dim_c) × num_enabled_tiles
- [ ] VECTOR_READOUT command: Support tile-interleaved results
- [ ] Wait condition updates for N-tile completion

**Dependencies**: Phase 2 DISPATCH complete

---

### 🔲 Phase 4: Result Collector Implementation (PENDING)

**Goal**: Aggregate results from multiple tiles with proper ordering

**Deliverables**:
- [ ] result_collector.sv module (new file)
- [ ] Tile-major result ordering (tile0_results, tile1_results, ...)
- [ ] FIFO arbitration across N tiles
- [ ] Tile ID tagging for debug
- [ ] Integration with result_bram_writer

**Architecture**:
```systemverilog
result_collector #(
    .NUM_TILES(16),
    .RESULT_WIDTH(16)  // FP16
) u_result_collector (
    .i_tile_result_valid[15:0],   // Per-tile valid signals
    .i_tile_result_data[15:0],     // Per-tile FP16 results
    .i_tile_id[15:0],              // Tile ID for ordering
    .o_result_valid,               // Aggregated output
    .o_result_data,
    .o_tile_id                     // Pass-through for debug
);
```

**Dependencies**: Phase 3 complete

---

### 🔲 Phase 5: Validation and Testing (PENDING)

**Goal**: Comprehensive testing of multi-tile functionality

**Test Configurations**:
- [ ] 1-tile mode (column_enable = 0x0001) - Backward compatibility
- [ ] 2-tile mode (column_enable = 0x0003) - Basic parallelism
- [ ] 4-tile mode (column_enable = 0x000F) - Quadrant test
- [ ] 8-tile mode (column_enable = 0x00FF) - Half capacity
- [ ] 16-tile mode (column_enable = 0xFFFF) - Full capacity

**Validation Metrics**:
- [ ] Functional correctness vs single-tile reference
- [ ] Performance scaling (linear with tile count)
- [ ] Resource utilization (BRAM, LUTs, FFs)
- [ ] Timing closure at target clock frequency

**Test Matrix** (B×C×V configurations):
| Config | Tiles | Expected Speedup | Status |
|--------|-------|------------------|--------|
| B4_C4_V32 | 1 | 1× (baseline) | ❌ Blocked |
| B4_C4_V32 | 4 | 4× | Pending |
| B8_C8_V64 | 8 | 8× | Pending |
| B16_C16_V128 | 16 | 16× | Pending |

**Dependencies**: Phase 4 complete

---

## Current Status (As of Oct 20, 2025 Late Evening)

### ✅ WAIT_DISPATCH Synchronization - FIXED!

**Root Cause Found**: Testbench was placing `wait_id` in wrong header location
- **Wrong**: `cmd[0] = {wait_id, 8'd0, id, e_cmd_op_wait_disp}` → wait_id in bits [31:24]
- **Correct**: `cmd[0] = {16'd4, wait_id, e_cmd_op_wait_disp}` → wait_id in bits [15:8]
- master_control.sv reads ID from bits [15:8], so it was capturing wrong value

**Fix Applied** (tb_engine_top.sv):
1. Fixed `generate_wait_disp_command` task signature (removed `id` parameter)
2. Put `wait_id` directly in header bits [15:8] per MS2.0 spec
3. Updated call site from `(3, 2, cmd)` to `(2, cmd)`

**Verification** (sim.log):
```
@ 20295000: DISPATCH completed: last_disp_id_reg <= 2
@ 20355000: WAIT command decoded: wait_id_reg <= 2
@ 20355000: WAIT_DISP satisfied: last_disp_id=2 >= wait_id=2
```

**Results**: 16/16 results received in 18895 cycles (was 0/16 with timeout)

---

### ⚠️ Current Issue: Result Data Correctness

**Symptom**: All 16 results mismatch golden values

**Evidence** (test_results.log):
```
[0]: hw=0x0000 golden=0xb6ae diff=46766  ← Zero (very wrong)
[1]: hw=0x0000 golden=0xb811 diff=47121  ← Zero (very wrong)
[5]: hw=0x3b48 golden=0x3af5 diff=83     ← Close!
[6]: hw=0xb652 golden=0xb6ec diff=154    ← Close!
[7]: hw=0x381f golden=0x3828 diff=9      ← Very close!
```

**Pattern Analysis**:
- Some results are zero → suggests missing data or wrong addresses
- Some results are close → suggests partial data correctness
- Mixed results → likely address generation or alignment issue

**Hypotheses**:
1. DISPATCH may not be copying all data correctly from dispatcher_bram → tile_bram
2. Compute engine address generation for tile_bram reads may be incorrect
3. Mantissa/exponent data alignment issues between L2 and L1
4. Left vs right data routing problems

**Debug Plan** (Phase 1.6):
1. ~~Add tile_bram write monitoring in dispatcher_control~~ ✓ Done
2. ~~Add tile_bram read monitoring in compute_engine_modular~~
3. ~~Compare dispatcher_bram contents vs tile_bram contents after DISPATCH~~
4. ~~Verify compute engine generates correct tile_bram addresses~~
5. ~~Check exponent data copy (currently tied to mantissa addressing)~~

**Architecture Understanding Breakthrough** (Oct 21, 2025):

After detailed discussion, identified fundamental misalignment in DISPATCH implementation:

**Root Cause Discovery:**
- **Wrong**: DISPATCH was copying 528 lines (packed memory block format) with source address from command
- **Correct**: DISPATCH should copy 512 lines (aligned buffer format) with source ALWAYS at address 0

**Key Insights Documented**:
1. Memory block format: 16 packed exp lines + 512 mantissa lines (528 total)
2. FETCH unpacks exponents → creates aligned buffers (512 exp + 512 man)
3. DISPATCH operates on aligned buffers, NOT packed blocks
4. Source address is implicit (always 0), destination address is explicit (from command)
5. Four parallel data paths (exp_left, man_left, exp_right, man_right) operate simultaneously

**Implementation Fixes Required**:
1. Fix addressing: `disp_addr_reg` = tile_bram WRITE destination (not dispatcher_bram READ source)
2. Fix length: `disp_len = NV_count × 4 = 512` (not 528)
3. Fix counter: Source reads [0:511], destination writes [dest_addr : dest_addr+511]
4. Implement broadcast/distribute modes (Phase 1: broadcast to tile[0] only)

See "Hardware Architecture Details" section above for complete documentation.

---

## Key Design Decisions

### Memory Organization

**L1 Tile BRAM Size**: 512×256-bit per tile
- Stores 128 Native Vectors (NV) per tile
- Each NV = 4 lines × 256-bit = 1KB
- Total per tile: 128 NV × 1KB = 128KB

**L2 Dispatcher BRAM Size**: 2048×256-bit shared
- Left matrix space: [0-527] (528 lines)
- Right matrix space: [528-1055] (528 lines)
- Reserved: [1056-2047] for future expansion

### Tile Enable Encoding

**column_enable[15:0]**: Bitmask for tile activation
- Bit 0 = Tile 0, Bit 1 = Tile 1, ..., Bit 15 = Tile 15
- Phase 1: 0x0001 (tile 0 only)
- Phase 2+: Runtime configurable (1-16 tiles)

### Data Distribution Strategy

**Left Matrix (Activations)**: Broadcast mode
- Same data written to all enabled tiles
- Write enable: `tile_wr_en_left = column_enable`

**Right Matrix (Weights)**: Distribute mode
- Different data to each tile (weight sharding)
- Write enable: `tile_wr_en_right[i] = column_enable[i]`
- Address offset per tile for weight distribution

---

## Success Criteria

### Phase 1 Success ✅ COMPLETE
- [x] DISPATCH data copy verified (5290 cycles measured)
- [x] WAIT_DISPATCH synchronization working
- [x] Single-tile MATMUL executes after DISPATCH (16/16 results received)
- [x] **B4_C4_V32 test passes with ALL results correct!**
- [x] tile_bram data correctness verified (DISPATCH addressing fixed)

### Overall Project Success
- [ ] All 5 phases complete
- [ ] 16-tile mode functional and validated
- [ ] Linear performance scaling demonstrated
- [ ] Timing closure maintained
- [ ] No regression in single-tile mode

---

## Technical Debt / Known Issues

1. **Exponent Handling in DISPATCH**: Currently tied to mantissa logic, needs separate alignment addressing
2. **State Monitoring**: Limited visibility into tile-level state machines
3. **Debug Infrastructure**: Need per-tile debug outputs for parallel debugging
4. **Makefile Cleanup**: Simulation database (.asdb) locking issues persist
5. **Documentation**: Some Phase 2+ details need RTL-level specification

---

## References

**Related Documentation**:
- [CHANGELOG.md](CHANGELOG.md) - Detailed change history
- [CLAUDE.md](CLAUDE.md) - Project overview and context
- [README.md](README.md) - User-facing documentation

**Key RTL Files**:
- [tile_bram_wrapper.sv](src/rtl/tile_bram_wrapper.sv) - Per-tile L1 cache
- [compute_tile_array.sv](src/rtl/compute_tile_array.sv) - Tile instantiation
- [dispatcher_control.sv](src/rtl/dispatcher_control.sv) - FETCH + DISPATCH FSM
- [master_control.sv](src/rtl/master_control.sv) - Command orchestration
- [engine_top.sv](src/rtl/engine_top.sv) - Top-level integration

**Simulation**:
- [tb_engine_top.sv](sim/vector_system_test/tb_engine_top.sv) - Testbench
- [test_results.log](sim/vector_system_test/test_results.log) - Latest results
- [Makefile](sim/vector_system_test/Makefile) - Build configuration

---

## Version History

| Date | Phase | Status | Notes |
|------|-------|--------|-------|
| 2025-10-20 14:03 | Phase 1.1-1.3 | ✅ Complete | Infrastructure created |
| 2025-10-20 19:46 | Phase 1.4 | ✅ Complete | DISPATCH bugs fixed |
| 2025-10-20 19:46 | Phase 2.1 | ✅ Complete | Data copy working |
| 2025-10-20 20:34 | Phase 2.2 | ✅ Complete | WAIT_DISPATCH sync fixed |
| 2025-10-20 20:34 | Phase 1.5 | ✅ Complete | ID tracking working, 16/16 results |
| 2025-10-20 20:34 | Phase 1.6 | ⚠️ In Progress | Result correctness debugging |
| 2025-10-21 02:17 | Phase 1.6 | ✅ Complete | **ALL 16 results match! Phase 1 COMPLETE!** |

---

**Phase 1 Complete!** 🎉 All single-tile infrastructure validated. Ready for Phase 2.3 (Full Multi-Tile DISPATCH) when needed.
