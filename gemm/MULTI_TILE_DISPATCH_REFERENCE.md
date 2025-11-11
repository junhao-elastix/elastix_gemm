# An Example of Multi-Tile Dispatch

## The VECTOR_DISPATCH Command
**Note:** See [SINGLE_ROW_REFERENCE](/home/dev/Dev/elastix_gemm/gemm/SINGLE_ROW_REFERENCE.md) for details:

### Command 0xF1: VECTOR_DISPATCH

**Purpose**: Copy aligned data from shared L2 (dispatcher_bram) to private L1 (tile_bram) for each compute tile.

#### Hardware Packing (4-Word Format)

```verilog
// From gemm_pkg.sv and tb_engine_top.sv
typedef struct packed {
    logic [7:0]     man_nv_cnt;     // 8 bits
    logic [7:0]     ugd_vec_size;   // 8 bits
    logic [15:0]    tile_addr;      // 16 bits
    logic           man_4b;         // 1 bit: 0 = 8-bit mantissas, 1 = 4-bit mantissas
    logic           broadcast;      // 1 bit: 0 = distribute, 1 = broadcast
    logic           disp_right;      // 1 bit: 0 = left, 1 = right
    logic [4:0]     col_start;      // 5 bits: starting column for distribution
    logic [23:0]    col_en;         // 23 bits: column enable bitmask
} cmd_disp_s;

// 4-Word Packing:
cmd[0] = {16'd16, cmd_id[7:0], e_cmd_op_disp};          // Header (16 bytes total)
cmd[1] = {8'b0, man_nv_cnt, 8'b0, ugd_vec_size};
cmd[2] = {16'b0, tile_addr};
cmd[3] = {col_en[23:0], col_start, disp_right, broadcast, man_4b};     // flags
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

- **Column enable (24 bits)**:
  - Bitmask for enabling tiles: bit 0 = tile 0, bit 1 = tile 1, etc.
  - **Default**: 0xFFFFFF (all columns enabled)
  - Actual enabled columns limited by hardware instantiation

- **Flags**:
  - `man_4b` signals whether the mantissa is in 4-bit format
  - `broadcast`  if asserted, broadcast the same chunk of data to all tiles; if not, distribute data to each tile. 
  - `disp_right` if asserted, dispatch to right brams; if not, dispatch to left
  - `col_start` specifies which column tile the dispatcher should start to forward the data to

#### Operation Modes

See "Broadcast vs Distribute Modes" section above for detailed behavior:
- **Broadcast Mode**: Replicates same data to all enabled tiles (for left activations)
- **Distribute Mode**: Round-robin distribution across tiles (for right weights)

## Example Walkthrough

We walk through an example to see how dispatch is done. Assume we have 4 columns enabled. For MATMUL: B = 2, C = 16, V = 4. This will generate B * C = 32 results in total.

### DISPATCH LEFT

```verilog
logic [7:0]     cmd_id          = 3;        \\ Keep track of the commands
logic [15:0]    tile_addr       = 0;        \\ Dispatch to address 0 in tile_bram
logic [7:0]     man_nv_cnt      = 8;        \\ Need to dispatch 8 Native Vectors in total (B * V)
logic [7:0]     ugd_vec_size    = 4;        \\ Dispatch 4 NVs per column before switching
logic           disp_right      = 0;        \\ Dispatch to left
logic           broadcast       = 1;        \\ Broadcast
logic           man_4b          = 0;        \\ Mantissa has 8-bit, default, current hardware does not support 4-bit mantissa yet
logic           col_start       = 0;        \\ Starting from column 0 (tile 0)
logic           col_en          = 0x000F;   \\ Enable four columns (for this example; default would be 0xFFFFFF)
```

Here's what actually happens:

0. FETCH already puts the data from GDDR6 to dispatcher_bram; dispatcher_bram has data needed for this VECTOR_DISPATCH
1. DC understands there are 4 tiles, all of which are enabled. 
2. DC broadcasts data sequentially from dispatcher_bram_left to tile_bram_left
    1. tile_0_bram [15:0]   <= dispatcher_bram [15:0]
    2. tile_1_bram [15:0]   <= dispatcher_bram [15:0]
    3. tile_2_bram [15:0]   <= dispatcher_bram [15:0]
    4. tile_4_bram [15:0]   <= dispatcher_bram [15:0]
    5. tile_0_bram [31:16]  <= dispatcher_bram [31:16]
    6. tile_1_bram [31:16]  <= dispatcher_bram [31:16]
    7. tile_2_bram [31:16]  <= dispatcher_bram [31:16]
    8. tile_4_bram [31:16]  <= dispatcher_bram [31:16]
3. Dispatch done

### DISPATCH RIGHT

```verilog
logic [7:0]     cmd_id          = 3;        \\ Keep track of the commands
logic [15:0]    tile_addr       = 0;        \\ Dispatch to address 0 in tile_bram
logic [7:0]     man_nv_cnt      = 64;       \\ Need to dispatch 64 Native Vectors in total (C * V = 16 * 4)
logic [7:0]     ugd_vec_size    = 4;        \\ Dispatch 4 NVs per column before switching
logic           disp_right      = 1;        \\ Dispatch to right
logic           broadcast       = 0;        \\ Distribute
logic           man_4b          = 0;        \\ Mantissa has 8-bit, default, current hardware does not support 4-bit mantissa yet
logic           col_start       = 0;        \\ Starting from column 0 (tile 0)
logic           col_en          = 0x000F;   \\ Enable four columns (for this example; default would be 0xFFFFFF)
```

Here's what actually happens:

0. FETCH already puts the data from GDDR6 to dispatcher_bram; dispatcher_bram has data needed for this VECTOR_DISPATCH
1. DC understands there are 4 columns enabled, ugd_vec_size=4 (dispatch 4 NVs per column)
2. DC distributes in batches:
    - Column 0: Gets NV[0-3], then NV[16-19], then NV[32-35], then NV[48-51] (16 NVs total)
    - Column 1: Gets NV[4-7], then NV[20-23], then NV[36-39], then NV[52-55] (16 NVs total)
    - Column 2: Gets NV[8-11], then NV[24-27], then NV[40-43], then NV[56-59] (16 NVs total)
    - Column 3: Gets NV[12-15], then NV[28-31], then NV[44-47], then NV[60-63] (16 NVs total)
3. Each column receives C=16 NVs for computing 16 outputs
4. Dispatch done


### [python-style pseudocode](/home/dev/Dev/elastix_gemm/gemm/dispatch.py)

## Data Distribution and Architectural Considerations

**Terminology** (per SINGLE_ROW_REFERENCE.md):
- **Column**: A compute tile (since we're in single-row architecture)
- **man_nv_cnt**: Total number of Native Vectors to distribute
- **ugd_vec_size**: Number of NVs dispatched to a column before switching to next column
- For MATMUL command: left_ugd_len (dim_b), right_ugd_len (dim_c), vec_len (dim_v)

### 1. Round-Robin Distribution Mechanism

**Dispatcher Behavior**: In DISTRIBUTE mode, dispatcher sends ugd_vec_size NVs to each column in round-robin fashion.

Example: man_nv_cnt=64, ugd_vec_size=4, 8 columns enabled
- Column 0 receives NV[0-3] (4 NVs)
- Column 1 receives NV[4-7] (4 NVs)
- Column 2 receives NV[8-11] (4 NVs)
- ...
- Column 7 receives NV[28-31] (4 NVs)
- Wraps around: Column 0 receives NV[32-35] (4 more NVs)
- Continues until all 64 NVs distributed

### 2. Distribution Example with Uneven Division

**Scenario**: man_nv_cnt=14, ugd_vec_size=1, 8 columns enabled

Distribution with ugd_vec_size=1 (one NV at a time):
```
Round 1:
- Column 0 receives NV[0]
- Column 1 receives NV[1]
- Column 2 receives NV[2]
- ...
- Column 7 receives NV[7]

Round 2:
- Column 0 receives NV[8]
- Column 1 receives NV[9]
- Column 2 receives NV[10]
- Column 3 receives NV[11]
- Column 4 receives NV[12]
- Column 5 receives NV[13]
- Columns 6-7 complete (no more NVs)

Final: Columns 0-5 have 2 NVs each, Columns 6-7 have 1 NV each
```

For MATMUL command, each column would set:
- Columns 0-5: right_ugd_len=2
- Columns 6-7: right_ugd_len=1

### 3. Stateless Dispatcher and Multi-Dispatch Continuity

**Critical Design Principle**: The dispatcher is STATELESS - it doesn't know about prior dispatches, just follows the current command parameters.

#### Default Column Enable Assumption

**IMPORTANT**: Unless otherwise specified, `col_en` defaults to 0xFFFFFF (all 24 columns enabled). In practice, the actual number of instantiated columns determines the effective enable mask. For example, if only 8 columns are instantiated, col_en=0xFFFFFF effectively means col_en=0xFF (8 columns enabled).

#### The col_start Parameter Purpose

The `col_start` parameter enables **seamless continuation** across multiple dispatch commands:
- Tells dispatcher which column to start the round-robin distribution
- Maintains continuity when data doesn't evenly divide across columns
- Host software tracks where previous dispatch ended

#### Multi-Dispatch Example
**Assuming col_en=0xFF (8 columns enabled, default for 8-column implementation)**

**First Dispatch**: C=14, V=4, col_start=0, tile_addr=0
```
man_nv_cnt = 56 (14×4), ugd_vec_size = 4, 8 columns
Round 1: Columns 0-7 each get 4 NVs → write to [0-15]
Round 2: Columns 0-5 each get 4 NVs → write to [16-31]
Last NV goes to Column 5
```

**Second Dispatch**: col_start=6, tile_addr=16
```
Continue from Column 6:
- Column 6: Writes to [16-31]
- Column 7: Writes to [16-31]
- Wrap to Column 0: Writes to [32-47] (tile_addr + ugd_vec_size×4)
- Column 1: Writes to [32-47]
```

#### Address Calculation on Wrap-Around

**Key Formula**: When wrapping from last column back to column 0:
```verilog
// Dispatcher's internal address tracking
if (wrapping_to_column_0) begin
    current_addr = tile_addr + ugd_vec_size * 4;
end
```

**Example with 8 columns**:
```
Start: col_start=6, tile_addr=16, ugd_vec_size=4
- Columns 6,7: Write to tile_addr (16)
- Wrap occurs
- Columns 0-5: Write to tile_addr + 16 = 32
- Columns 6,7: Write to tile_addr + 16 = 32
- Next wrap
- Columns 0-5: Write to tile_addr + 32 = 48
```

#### Host Software Responsibilities

The host software must track:
1. **Last dispatch endpoint**: Which column received the last NV
2. **Next col_start**: Where to begin the next dispatch
3. **Next tile_addr**: Base address for next dispatch
4. **V consistency**: Ensure ugd_vec_size remains constant across related dispatches

**Stateless Hardware Benefits**:
- Simple dispatcher logic - just execute current command
- No state retention between commands
- Flexible dispatch patterns under software control
- Easy to verify and debug

### 4. Implementation Requirements

**Hardware-Based Address Management**:
- Reduces host-device communication overhead
- No need for multiple dispatch commands
- Automatic handling of wrap-around cases
- Maintains backward compatibility with single-tile mode

**Key Requirements**:
1. Dispatcher must track per-column write pointers
2. Address increment of ugd_vec_size×4 lines when column receives additional batch
3. Reset pointers on new dispatch command
4. Ensure no address conflicts between columns

### 5. Synchronous Execution and Selective Result Readout

**Critical Design Insight**: All columns execute for the SAME number of cycles, regardless of actual NV distribution.

#### Synchronous SIMD-Style Operation

When NVs are distributed unevenly (e.g., man_nv_cnt=14, ugd_vec_size=1, 8 columns):
- **Columns 0-5**: Receive 2 NVs each → produce 2 valid results each
- **Columns 6-7**: Receive 1 NV each → produce 1 valid result + 1 garbage result

**Hardware Behavior**:
```
All columns run for max(right_ugd_len) = 2 cycles
- Columns 0-5: Process NV[i] and NV[i+8] → 2 valid results
- Columns 6-7: Process NV[i] and undefined data → 1 valid + 1 garbage result
```

#### Why Garbage Results are Acceptable

1. **Simpler Hardware**: No early termination logic or complex masking needed
2. **Lockstep Execution**: All columns complete together, simplifying control
3. **Software Awareness**: Host software tracks actual NV distribution per column

#### Selective Result Collection via VECTOR_READOUT

The VECTOR_READOUT command (0xF5) enables precise result collection:

```systemverilog
// VECTOR_READOUT command structure
typedef struct packed {
    logic [7:0]  start_col;     // Starting column index
    logic [31:0] rd_len;        // Number of FP16 results to read
} cmd_readout_s;
```

**Example for uneven distribution (14 NVs, 8 columns)**:
```
Total valid results = 14
Software issues: VECTOR_READOUT with rd_len = 14
Result arbiter collects exactly 14 valid results, ignoring garbage

Result mapping:
- Results[0-1]:   From Column 0 (2 valid)
- Results[2-3]:   From Column 1 (2 valid)
- Results[4-5]:   From Column 2 (2 valid)
- Results[6-7]:   From Column 3 (2 valid)
- Results[8-9]:   From Column 4 (2 valid)
- Results[10-11]: From Column 5 (2 valid)
- Results[12]:    From Column 6 (1 valid, skips garbage)
- Results[13]:    From Column 7 (1 valid, skips garbage)
```

**Key Implementation Points**:
- Result arbiter must track valid results per column
- Software specifies exact result count via rd_len
- Hardware fills result_bram with exactly rd_len valid results
- Garbage results are never transferred to host

### 6. Memory Block Management and Capacity Limits

**CRITICAL**: Each FETCH-DISPATCH operation gets a NEW memory block (128 NVs)

#### Key Insight: Simple Capacity Rule

**Maximum safe back-to-back FETCH-DISPATCH operations = Number of Columns**

This elegant rule comes from the fundamental balance:
- **Total NVs fetched**: 128 × num_dispatches
- **Total tile capacity**: 128 × num_columns (each tile BRAM holds 128 NVs)
- **At equilibrium**: When num_dispatches = num_columns, tiles are exactly full

#### Why This Works

```
Each dispatch brings 128 NVs and distributes them evenly:
- 1 column:  128 NVs → 1 dispatch fills it completely
- 2 columns: 64 NVs each → 2 dispatches fill them completely
- 4 columns: 32 NVs each → 4 dispatches fill them completely
- 8 columns: 16 NVs each → 8 dispatches fill them completely
- 16 columns: 8 NVs each → 16 dispatches fill them completely
```

#### Safe Dispatch Limits

| Number of Columns | Safe Back-to-Back Dispatches |
|-------------------|------------------------------|
| 1                 | 1                            |
| 2                 | 2                            |
| 4                 | 4                            |
| 8                 | 8                            |
| 16                | 16                           |
| 24                | 24                           |

#### Example: 8 Columns Configuration
```
Total capacity: 8 columns × 128 NVs = 1024 NVs
Each dispatch: 128 NVs distributed as 16 NVs per column

After 8 dispatches:
- Total dispatched: 8 × 128 = 1024 NVs
- Per column: 8 × 16 = 128 NVs (exactly full)
- 9th dispatch would overflow
```

#### Software Responsibilities for Memory Management

1. **Simple rule**: Issue at most `num_columns` FETCH-DISPATCH pairs
2. **Issue MATMUL/COMPUTE** before reaching the limit
3. **Reset with tile_addr=0** after computation to reuse BRAM space
4. **Track dispatch count**: counter should not exceed num_columns

### 7. Testing Requirements

For robust multi-column operation, test these scenarios:
1. **C < num_columns**: Verify idle columns handle no data gracefully
2. **C not divisible by num_columns**: Check round-robin distribution correctness
3. **Multi-round distribution**: Verify address offsets prevent data overwrites
4. **Single-column fallback**: col_en=0x000001 works identically to original
5. **Maximum columns**: Test with all 24 columns enabled (future scalability)

## Notes:

The multi-column dispatcher architecture handles all Native Vector distribution cases including when C < num_columns or when C is not evenly divisible by num_columns. Hardware-based per-column address tracking manages multi-round distributions properly. Round-robin distribution ensures balanced utilization of available compute resources across all configurations.


