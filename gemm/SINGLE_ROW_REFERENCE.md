# Single-Row Multi-Tile Architecture Development Plan

**Project**: GEMM Engine Single-Row Multi-Tile Extension

---

## Executive Summary

Migrating GEMM engine from single compute_engine_modular to scalable single-row multi-tile architecture supporting up to 16 parallel compute tiles per row. Implementing three-level memory hierarchy (L3: GDDR6 → L2: dispatcher_bram → L1: tile_bram) with DISPATCH phase to distribute data across tiles for parallel matrix operations within a row.

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
L2: dispatcher_bram (Shared per row, buffers FETCH read)
    ↓ DISPATCH (data copy + distribute)
L1: tile_bram (Private per tile, serves the compute)
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

The data fetched from GDDR6 is organized in a packed format optimized for transfer efficiency. The number format is called Group Floating-Point. Refer to the [emulator](/home/dev/Dev/elastix_gemm/emulator/CLAUDE.md) project for details about GFP number format.  

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

**Purpose**: Transfer memory block from GDDR6 (L3) to dispatcher_bram (L2) and unpack exponents into aligned format 

**Command Parameters**
- **Start Address** (32 bits): Address to read from GDDR6
- **Length** (16 bits): Number of 256-bit lines to fetch. For one memory block, this value should be 528 lines (16 packed exponent lines + 512 mantissa lines). Current hardware supports single-block operation only. 

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

**Return Condition:**
FETCH will return DONE signal after all the unpacking has finished. Unpacking must complete before DISPATCH can begin.

**Final Result - Four Aligned Buffers (dispatcher_bram):**
- `exp_left_aligned[0-511]`: 512 individual exponent bytes ✓
- `man_left[0-511]`: 512 mantissa group lines ✓
- `exp_right_aligned[0-511]`: 512 individual exponent bytes ✓
- `man_right[0-511]`: 512 mantissa group lines ✓

**Key Feature**: Exponents are now aligned 1:1 with mantissa lines for efficient tile_bram access.

### DISPATCH Operation - Specification

**Purpose**: Copy aligned data from shared L2 (dispatcher_bram) to private L1 (tile_bram)

**Command Parameters** (see details in the next section **MS2.0 Microcode Command Reference**):
- **Mantissa NV count (man_nv_cnt)**: Number of Native Vectors to dispatch
  - Each NV = 4 lines → Total lines = man_nv_cnt × 4
  - Example: 128 NVs = 512 lines
- **Tile destination address (tile_addr)**: Starting line in tile_bram where data will be written
- **UGD vector size (ugd_nv_size)**: NVs per UGD 
- **Column enable (col_en)**: Bitmask for enabling tiles: bit 0 = tile 0, bit 1 = tile 1, etc.
  - **Hardware Constraint**: All enabled bits must be sequential starting from bit 0
  - Valid: 0x0001, 0x0003, 0x0007, 0x000F, 0xFFFF
  - Invalid: 0x0101 (non-sequential), 0x7000 (doesn't start from bit 0)
- **Flags**:
  - Mantissa width (4-bit vs 8-bit)
  - Broadcast mode (reserved, tied to 0) - Hardware always broadcasts LEFT buffers and distributes RIGHT buffers
  - Distribution start column

**Addressing Behavior:**

Source (dispatcher_bram aligned buffers):
- Keep a dispatch_tile_start register to track the starting address of current UGD NV Size to dispatch to one tile. Dispatch always starting from address 0 in dispatcher bram, so initial value of dispatch_tile_start should be 0 at each DISPATCH command. 
- Keep a receive_tile_start register in each tile to track the starting address of current UGD NV Size to receive to one tile. Initial value of receive_tile_start should be tile_addr.
- Reads ugd_nv_size * 4 consecutive lines: [0, 1, 2, ..., ugd_nv_size*4-1], dispatch to one tile starting from tile_addr
- Depending on Broadcast or Distribute
  - If broadcast, starting from the current dispatch_tile_start again to dispatch the same ugd_nv_size * 4 to the next tile, increment dispatch_tile_start after all enabled tiles are dispatched. Every tile gets the same data. This process repeats until all man_nv_cnt*4 lines are dispatched. Increment receive_tile_start in each tile to prepare to receive the next batch of data.
  - If distribute, increment dispatch_tile_start to dispatch the next ugd_nv_size * 4 to the next tile. Every tile gets different, new data from dispatcher_bram. Increment receive_tile_start in each tile to prepare to receive the next batch of data. 
- When all data in dispatcher_bram are dispatched, or the dispatch_tile_start is at the end of man_nv_cnt, dispatcher stops and returns DONE. Notice man_nv_cnt can be less than the actual capacity of the dispatcher_bram (128 NV or 512 lines).
- dispatch_tile_start **resets** to 0 after each DISPATCH command completes. 

Destination (tile_bram):
- Writes starting at command-specified tile_addr
- Writes ugd_nv_size * 4 lines to: [tile_addr, tile_addr + 1, ..., tile_addr + ugd_nv_size*4 - 1]
- Multiple DISPATCH commands can fill different tile_bram regions, depending on the tile_addr and ugd_nv_size
- Notice the tile_bram may not always be full.

**Multiple DISPATCH Commands (with intermediate FETCH)**:

When filling different tile_bram regions, each DISPATCH should be preceded by a new FETCH to load fresh data.

**Terminology Note**: The term "batch" in DISPATCH context refers to a contiguous chunk of data lines (ugd_nv_size × 4 lines), NOT the batch size in machine learning (number of samples). To avoid confusion:
- **DISPATCH batch**: Data chunking granularity for hardware operations
- **ML batch**: Number of input samples processed together in training/inference

```systemverilog
// Scenario: Fill two separate tile_bram regions with different data

// Load first batch of data
FETCH: cmd_id=1, start_addr=0x0000, len=528, fetch_right=0

// Dispatch to tile_bram[0-255]
DISPATCH: cmd_id=2, man_nv_cnt=64, tile_addr=0, ugd_vec_size=16, ...

// Load second batch of data (REQUIRED for new data)
FETCH: cmd_id=3, start_addr=0x4200, len=528, fetch_right=0

// Dispatch to tile_bram[256-511]
// Reads from dispatcher_bram[0-255] again, but contains new data from FETCH cmd_id=3
DISPATCH: cmd_id=4, man_nv_cnt=64, tile_addr=256, ugd_vec_size=16, ...

// WAIT command is omitted in this example.
```

**Key Point**: Each DISPATCH always reads from dispatcher_bram starting at address 0. To fill different tile_bram regions with **different data**, issue a new FETCH command before each DISPATCH to refresh the dispatcher_bram contents.

### Broadcast vs Distribute Modes

**Hardware Behavior** (Hardcoded):
- **LEFT Buffers**: ALWAYS broadcast to all enabled tiles
- **RIGHT Buffers**: ALWAYS distribute across enabled tiles

**Broadcast (LEFT buffers)**:
- **Behavior**: Write same batch to ALL enabled tiles before advancing source
- **Batch Size**: ugd_nv_size × 4 lines per batch
- **Use Case**: Activations need to be replicated across all tiles
- **Result**: All tiles have identical copies of left data

**Distribute (RIGHT buffers)**:
- **Behavior**: Write data to tiles in round-robin fashion at BATCH level
- **Batch Size**: ugd_nv_size × 4 lines per batch
- **Distribution**: Tile i receives batch i (tile 0 gets first batch, tile 1 gets second batch, etc.)
- **Use Case**: Weights sharded across tiles for parallel computation
- **Result**: Each tile gets different, consecutive batches of right data

**Important**: Distribution happens at batch granularity, NOT line-by-line interleaving.

**Note**: The `broadcast` flag bit is reserved (tied to 0). See Command VECTOR_DISPATCH specification for details on flag reservation and hardware behavior.


**Example Use Cases:** (Assuming 2 tiles, col_en = 0x0003)

DISPATCH 1: man_nv_cnt=64, tile_addr=0, ugd_nv_size = 32
- Broadcast (LEFT buffers)
  - Copies dispatcher_bram[0-127] to tile_0_bram[0-127]
  - Copies dispatcher_bram[0-127] to tile_1_bram[0-127]
  - Copies dispatcher_bram[128-255] to tile_0_bram[128-255]
  - Copies dispatcher_bram[128-255] to tile_1_bram[128-255]
- Distribute (RIGHT buffers)
  - Copies dispatcher_bram[0-127] to tile_0_bram[0-127]
  - Copies dispatcher_bram[128-255] to tile_1_bram[0-127]

DISPATCH 2: man_nv_cnt=64, tile_addr=256, ugd_nv_size = 16
- Broadcast (LEFT buffers)
  - Copies dispatcher_bram[0-63] to tile_0_bram[256-319]
  - Copies dispatcher_bram[0-63] to tile_1_bram[256-319]
  - Copies dispatcher_bram[64-127] to tile_0_bram[320-383]
  - Copies dispatcher_bram[64-127] to tile_1_bram[320-383]
  - Copies dispatcher_bram[128-191] to tile_0_bram[384-447]
  - Copies dispatcher_bram[128-191] to tile_1_bram[384-447]
  - Copies dispatcher_bram[192-255] to tile_0_bram[448-511]
  - Copies dispatcher_bram[192-255] to tile_1_bram[448-511]
- Distribute (RIGHT buffers)
  - Copies dispatcher_bram[0-63] to tile_0_bram[256-319]
  - Copies dispatcher_bram[64-127] to tile_1_bram[256-319]
  - Copies dispatcher_bram[128-191] to tile_0_bram[320-383]
  - Copies dispatcher_bram[192-255] to tile_1_bram[320-383]

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
- Single write address drives all four write addresses
- Enables maximum bandwidth utilization (4 × 256-bit + 4 × 8-bit per cycle)

**During MATMUL:**
- Compute engine reads from tile_bram using the four-path structure
- Left and right exponents/mantissas accessed independently
- Supports parallel dot-product computation across groups

### tile_bram Organization

**Key Insight**: tile_bram has IDENTICAL organization to dispatcher_bram's aligned buffers

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

### Left and Right Behavior

**FETCH Command**: Selectively updates dispatcher_bram
- `fetch_right=0`: Updates only LEFT buffers (exp_left_aligned, man_left)
- `fetch_right=1`: Updates only RIGHT buffers (exp_right_aligned, man_right)
- **Stateful**: Old data remains in the opposite side until overwritten

**DISPATCH Command**: Always dispatches BOTH sides
- Copies ALL 4 buffers simultaneously: exp_left, man_left, exp_right, man_right
- No `disp_right` flag - always copies both left AND right to tile_brams
- Hardware always broadcasts LEFT buffers and distributes RIGHT buffers (see Command VECTOR_DISPATCH section for details)
- Software controls content via selective FETCH commands

**Critical Software Requirement**:
Before the FIRST DISPATCH, software MUST issue at least one FETCH LEFT and one FETCH RIGHT to initialize dispatcher_bram. After that, software can selectively update either side as needed.

**Example Workflow - Reusing Activation Across Multiple Weights**:
```systemverilog
// Initial setup
FETCH LEFT:  activation_row_0    // Load left buffer
FETCH RIGHT: weights_W0          // Load right buffer
DISPATCH                         // Copy BOTH (activation_row_0, weights_W0) to tiles
MATMUL

// Process additional weight matrices with SAME activation
FETCH RIGHT: weights_W1          // Update right buffer only (left unchanged!)
DISPATCH                         // Copy BOTH (activation_row_0, weights_W1) to tiles
MATMUL

FETCH RIGHT: weights_W2          // Update right buffer again
DISPATCH                         // Copy BOTH (activation_row_0, weights_W2) to tiles
MATMUL

// When ready for next activation row
FETCH LEFT:  activation_row_1    // Update left buffer
FETCH RIGHT: weights_W0          // Restart with first weight matrix
DISPATCH                         // Copy BOTH (activation_row_1, weights_W0) to tiles
MATMUL
```

This stateful dispatcher_bram design enables efficient matrix reuse patterns in GEMM operations.

---

## MS2.0 Microcode Command Reference

This section documents all commands supported by the MS2.0 architecture, aligned with the [MS2.0_uCode-Single_Row.csv](/home/dev/Dev/elastix_gemm/MS2.0_uCode-Single_Row.csv) specification, and the actual hardware implementation in [gemm_pkg.sv](/home/dev/Dev/elastix_gemm/gemm/src/include/gemm_pkg.sv) will be updated to match this specification.

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
| 0xF0 | fetch_memory_block | 16 bytes | 12 | Transfer memory block from GDDR6 to dispatcher_bram |
| 0xF1 | vector_dispatch | 16 bytes | 12 | Copy data from dispatcher_bram to tile_bram (broadcast/distribute) |
| 0xF2 | matmul | 16 bytes | 12 | Execute parallel matrix multiplication across enabled tiles |
| 0xF3 | wait_dispatch | 16 bytes | 12 | Synchronization barrier - wait for DISPATCH command to complete |
| 0xF4 | wait_matmul | 16 bytes | 12 | Synchronization barrier - wait for MATMUL command to complete |
| 0xF5 | vector_readout | 16 bytes | 12 | Read result vectors from result_bram to host |

---

### Command 0xF0: FETCH_MEMORY_BLOCK

**Purpose**: Transfer a memory block (528 lines) from GDDR6 external memory to dispatcher_bram's internal staging buffers.

#### CSV Specification

| Field | Bits | Description |
|-------|------|-------------|
| **Start Address** | 32 | External memory address |
| **Length** | 16 | Number of 256-bit lines to fetch. For one memory block: 528 lines. Current hardware supports single-block operation (len=528) only. |
| **Fetch Right** | 1 | Fetch to right buffer if asserted. Otherwise, fetch to left. |

#### Hardware Packing (4-Word Format)

```systemverilog
typedef struct packed {
    logic        fetch_right;       // 1 bit: 0=left, 1=right
    logic [15:0] len;               // 16 bits: number of lines
    logic [31:0] start_addr;        // 32 bits: byte address
} cmd_fetch_s;

// 4-Word Packing:
cmd[0] = {16'd16, cmd_id[7:0], e_cmd_op_fetch};   // Header (16 bytes total)
cmd[1] = start_addr[31:0];                        // Word 1: Address
cmd[2] = {reserved[15:0], len[15:0]};             // Word 2: Length
cmd[3] = {reserved[30:0], fetch_right};           // Word 3: Target
```

#### Field Details

- **Start Address (32 bits)**: Byte address in GDDR6 memory
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
FETCH: cmd_id=1, start_addr=0x0, len=528, fetch_right=0
```

---

### Command 0xF1: VECTOR_DISPATCH

**Purpose**: Copy aligned data from shared L2 (dispatcher_bram) to private L1 (tile_bram) for each compute tile.

#### CSV Specification

| Field | Bits | Description |
|-------|------|-------------|
| **Mantissa NV cnt** | 8 | Number of total Native Vectors to process (each NV = 4 lines) |
| **Tile destination address** | 16 | Destination tile buffer start address |
| **UGD vector size** | 8 | Number of native vectors per UGD vector to dispatch at a time|
| **Flags** | 8 | Control flags (detailed below) |
| **Column enable** | 16 | 1 bit per column (tile enable mask) |

#### Flags Field (8 bits)

| Bit(s) | Name | Description |
|--------|------|-------------|
| [0] | Mantissa width | 0 = 8-bit mantissas, 1 = 4-bit mantissas |
| [1] | Distribution mode (tied to 0) | Hardware always broadcasts LEFT and distributes RIGHT. This bit is reserved for future use. |
| [7:2] | Tensor distribution start column | Starting column for distribution |

**Hardware Behavior**: Regardless of this flag value, DISPATCH always:
- Broadcasts LEFT buffers (exp_left, man_left) to all enabled tiles
- Distributes RIGHT buffers (exp_right, man_right) across enabled tiles in round-robin fashion
- This hardcoded pattern supports all standard matrix multiplication use cases (linear layers, attention mechanisms, etc.)

**Note on Flag Reservation**: The broadcast flag bit is kept in the command structure for compatibility with other architectures where independent control of left/right dispatch behavior may be required. This ensures command format consistency across different hardware implementations.

#### Hardware Packing (4-Word Format)

```systemverilog
// From gemm_pkg.sv and tb_engine_top.sv
typedef struct packed {
    logic [7:0]     man_nv_cnt;     // 8 bits
    logic [7:0]     ugd_vec_size;   // 8 bits
    logic [15:0]    tile_addr;      // 16 bits
    logic           man_4b;         // 1 bit: 0 = 8-bit mantissas, 1 = 4-bit mantissas
    logic           broadcast;      // 1 bit: Reserved (tied to 0). Hardware always broadcasts LEFT, distributes RIGHT
    logic [5:0]     col_start;      // 6 bits: starting column for distribution
    logic [15:0]    col_en;         // 16 bits: column enable bitmask
} cmd_disp_s;

// 4-Word Packing:
cmd[0] = {16'd16, cmd_id[7:0], e_cmd_op_disp};          // Header (16 bytes total)
cmd[1] = {8'b0, man_nv_cnt, 8'b0, ugd_vec_size};
cmd[2] = {16'b0, tile_addr};
cmd[3] = {col_en[15:0], 8'b0, col_start, broadcast, man_4b};     // flags
```

#### Field Details

- **Mantissa NV count (man_nv_cnt)**
  - Mapped to `man_nv_cnt*4` lines in hardware
  - Number of Native Vectors to dispatch from dispatcher bram in total
  - Each tile will not get all the lines at once
  - Hardware stores as line count: `len = man_nv_cnt*4`
  - Example: 128 NVs → 512 lines

- **UGD vector size (ugd_vec_size)**:
  - Determines how many NV to dispatch to a tile at a time
  - Example: if `ugd_vec_size = 4`, then dispatcher will forward `ugd_vec_size*4` lines to one tile, then the next tile will get the next `ugd_vec_size*4`, until all data has been dispatched.

- **Tile destination address (tile_addr)**:
  - Starting line in tile_bram where data will be written
  - Range: 0-511 (tile_bram has 512 lines)
  - **Alignment**: Handled by software. For hardware simplicity, recommend NV-aligned (multiple of 4)
  - Multiple DISPATCH commands can fill different regions

- **Column enable (16 bits)**:
  - Bitmask for enabling tiles: bit 0 = tile 0, bit 1 = tile 1, etc.

- **Flags**:
  - `man_4b` signals whether the mantissa is in 4-bit format
  - `broadcast` is reserved (tied to 0). Hardware behavior is hardcoded: always broadcast LEFT, distribute RIGHT
  - `col_start` specifies which column tile the dispatcher should start to forward the data to

**Important**: DISPATCH always copies BOTH left and right buffers simultaneously (all 4 data paths active). See "Hardware Behavior" note above for details on broadcast (LEFT) vs distribute (RIGHT) behavior.

#### Operation Modes

See "Broadcast vs Distribute Modes" section above for detailed behavior:
- **Broadcast Mode**: Replicates same data to all enabled tiles (for left activations)
- **Distribute Mode**: Round-robin distribution across tiles (for right weights)

#### col_start and col_en Constraints

**Hardware Constraint**: `col_en` must have all enabled bits sequential starting from bit 0.
- ✅ Valid examples: `0x0001` (tile 0), `0x0003` (tiles 0-1), `0x000F` (tiles 0-3), `0xFFFF` (all tiles 0-15)
- ❌ Invalid examples: `0x0101` (non-sequential), `0x7000` (doesn't start from bit 0)

**col_start Behavior**:
- Specifies which tile to start dispatching to (0-15)
- Must point to an enabled tile: `col_en[col_start] == 1`
- If `col_start > 0`, enabled tiles wrap around from col_start

**Example**:
- `col_start = 2`, `col_en = 0x000F` (tiles 0-3 enabled)
- Dispatch order: tile 2, tile 3, tile 0, tile 1 (wraps around)

**Algorithm**:
```systemverilog
num_enabled = popcount(col_en);  // Count of enabled tiles
current_tile = col_start;

for (int i = 0; i < num_enabled; i++) {
    dispatch_to_tile(current_tile % 16);
    current_tile++;
}
```

**Note**: Hardware supports wraparound correctly. Results may be incorrect if `col_start` points to a disabled tile (undefined behavior).

---

### Command 0xF2: MATMUL

**Purpose**: Execute parallel matrix multiplication across enabled compute tiles.

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
    logic [15:0]  left_addr;            // 16 bits: Left start address
    logic [15:0]  right_addr;           // 16 bits: Right start address
    logic [7:0]   left_ugd_len;         // 8 bits: dim_b, Batch dimension, Left UGD vectors
    logic [7:0]   right_ugd_len;        // 8 bits: dim_c, Column dimension, Right UGD vectors
    logic [7:0]   vec_len;              // 8 bits: dim_v, Vector count, UGD vector size
    logic [15:0]  col_en;               // 16 bits: 1 bit per column (tile-enable bitmask)
    logic left_4b;                      // 1 bit flag: Left mantissa width, 0 = 8-bit, 1 = 4-bit
    logic right_4b;                     // 1 bit flag: Right mantissa width, 0 = 8-bit, 1 = 4-bit
    logic main_loop_left;               // 1 bit flag: Main loop dimension, 0 = loop over right first, 1 = loop over left first
} cmd_tile_s; 

// 4-Word Packing:
cmd[0] = {16'd16, cmd_id[7:0], e_cmd_op_tile};                                // Header (16 bytes total)
cmd[1] = {left_addr[15:0], right_addr[15:0]};                                 // Word 1: Addresses
cmd[2] = {8'b0, left_ugd_len[7:0], right_ugd_len[7:0], vec_len[7:0]};        // Word 2: Dimensions
cmd[3] = {col_en[15:0], 13'b0, left_4b, right_4b, main_loop_left};           // Word 3: Column enable and flags
```

#### Field Details

- **Left/Right Addresses (16 bits)**:
  - Starting line in tile_bram for left and right matrices
  - Range: 0-511 per tile_bram capacity

- **Left/Right UGD vectors (8 bits)**:
  - Number of Unified Group Dot vectors to process
  - Maps to dim_b for left and dim_c for right
  - Matrix dimensions for output size calculation
  - dim_b × dim_c = number of FP16 results per tile

- **UGD vector size (8 bits)**:
  - Number of Native Vectors per UGD
  - Similar concept as ugd_vec_size in DISPATCH
  - Maps to dim_v parameter

- **Column enable (16 bits)**:
  - Bitmask for enabling tiles: bit 0 = tile 0, bit 1 = tile 1, etc.

**Example**:
```systemverilog
// Execute 4×4 matrix with a inner dimension of 32 NVs on single tile
MATMUL: cmd_id=3, left_addr=0, right_addr=0, left_ugd_len=4, right_ugd_len=4, vec_len=32
        left_man_4b=0, right_man_4b=0, loop_over_left=1
```

---

### Command 0xF3: WAIT_DISPATCH

**Purpose**: Synchronization barrier - blocks until specified DISPATCH command completes.

#### CSV Specification

| Field | Bits | Description |
|-------|------|-------------|
| **wait_id** | 8 | Command ID to wait for (must be a DISPATCH command) |

#### Hardware Packing (4-Word Format)

```systemverilog
typedef struct packed {
    logic [cmd_id_width_gp-1:0] wait_id;
} cmd_wait_disp_s;

// 4-Word Packing:
cmd[0] = {16'd16, cmd_id[7:0], e_cmd_op_wait_disp};     // Header (16 bytes total)
cmd[1] = {24'd0, wait_id[7:0]};                         // wait_id
cmd[2] = 32'h00000000;                                  // Reserved
cmd[3] = 32'h00000000;                                  // Reserved
```

**Example**:
```systemverilog
DISPATCH: cmd_id=2, ...                   // Start DISPATCH operation
WAIT_DISPATCH: cmd_id = 3, wait_id=2      // Block until DISPATCH cmd_id=2 completes
MATMUL: cmd_id=4, ...                     // Safe to proceed, data is ready
```

---

### Command 0xF4: WAIT_MATMUL

**Purpose**: Synchronization barrier - blocks until specified MATMUL (TILE) command completes.

#### CSV Specification

| Field | Bits | Description |
|-------|------|-------------|
| **wait_id** | 8 | Command ID to wait for (must be a MATMUL command) |

#### Hardware Packing (4-Word Format)

```systemverilog
typedef struct packed {
    logic [cmd_id_width_gp-1:0] wait_id;
} cmd_wait_tile_s;

// 4-Word Packing:
cmd[0] = {16'd16, cmd_id[7:0], e_cmd_op_wait_tile};     // Header (16 bytes total)
cmd[1] = {24'd0, wait_id[7:0]};                         // wait_id
cmd[2] = 32'h00000000;                                  // Reserved
cmd[3] = 32'h00000000;                                  // Reserved
```

**Example**:
```systemverilog
MATMUL: cmd_id=3, ...                       // Start matrix multiplication
WAIT_MATMUL: cmd_id = 4, wait_id=3          // Block until MATMUL id=3 completes
// Results are now ready in result_bram
```

---

### Command 0xF5: VECTOR_READOUT

**Purpose**: Read result vectors from result_bram and send to host via PCIe.

**Total Length**: 16 bytes (4-word format, unused words = 0x00000000)

#### CSV Specification

| Field | Bits | Description |
|-------|------|-------------|
| **Start Col** | 8 | Starting column index for readout |
| **Length** | 32 | Number of FP16 results to read |

#### Hardware Packing (4-Word Format)

```systemverilog
typedef struct packed {
    logic [7:0]  start_col;     // 8 bits: starting column index
    logic [31:0] rd_len;        // 32 bits: number of FP16 results to read
} cmd_readout_s;

// 4-Word Packing:
cmd[0] = {16'd16, cmd_id[7:0], e_cmd_op_readout};       // Header (16 bytes total)
cmd[1] = {24'b0, start_col[7:0]};                       // Word 1: Start column
cmd[2] = rd_len[31:0];                                  // Word 2: Length
cmd[3] = 32'h00000000;                                  // Word 3: Reserved
```

#### Implementation Status

⚠️ **Currently not implemented in this version** - Results are read directly via result FIFO interface in the testbench. This command is defined in the CSV specification for future host-driven result retrieval.

**Planned Usage**:
```systemverilog
VECTOR_READOUT: start_col=0, rd_len=16  // Read 16 FP16 results starting at column 0
```

---

### Command Execution Flow Example

Typical command sequence for a single matrix multiplication:

```systemverilog
// Fetch left matrix (528 lines → dispatcher_bram left buffers)
FETCH: cmd_id=1, start_addr=0, len=528, fetch_right=0

// Fetch right matrix (528 lines → dispatcher_bram right buffers)
FETCH: cmd_id=2, start_addr=528, len=528, fetch_right=1

// Dispatch data to tile_bram
// DISPATCH always copies BOTH left and right buffers simultaneously
// Hardware behavior (hardcoded):
// - LEFT buffers (activation): broadcasted to all tiles
// - RIGHT buffers (weights): distributed across tiles
// broadcast flag is reserved (set to 0)
DISPATCH: cmd_id=3, man_nv_cnt=64, tile_addr = 256, ugd_vec_size = 16, broadcast=0, man_4b = 0, col_start = 0, col_en = 0x00FF

// Wait for dispatch to complete
WAIT_DISPATCH: cmd_id = 4, wait_id=3

// Execute matrix multiplication
MATMUL: cmd_id= 5, left_addr=256, right_addr=256, left_ugd_len=4, right_ugd_len=4, vec_len=16
        left_man_4b=0, right_man_4b=0, loop_over_left=1, col_en = 0x00FF

// Wait for computation to complete
WAIT_MATMUL: cmd_id = 6, wait_id=5 

// Results now available in result_bram/FIFO
```

This command sequence produces 16 FP16 results (4×4 matrix) per tile.

---
