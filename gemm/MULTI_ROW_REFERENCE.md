# MULTI-ROW GEMM REFERENCE MANUAL
## Table of Contents

## Numbering Format and Configurations

### Signal Naming Convention
The signals on the interfaces should generally follow this naming convention:
`[i/o]_[fetch/disp/comp or other components]_[field_2]_[field_3]_...[field_n]`. Essentially, the first field should suggest if it is an input or output signal. If it is internal, then, the first two fields should be `[src]_[dest]_...` to show where the signal comes from and goes to. If it is minor miscellaneous signals, it doesn't have to follow the naming convention strictly.

### GFP8 Number Format
[GFP Explanation](../emulator/GFP_EXPLANATION.md)

### Terminology and Default Configurations

- GFP8: 
  - Group Floating-Point
  - 8-bit mantissa, 5-bit exponent
- GFP4: 
  - Group Floating-Point
  - 4-bit mantissa, 5-bit exponent
- Group Size:
  - The size of GFP group that shares one exponent
  - Default: 32
- Native Vector (NV):
  - A vector of GFP numbers
  - May contain multiple groups
  - Hardware considerations
- Native Vector Size:
  - The number of GFP numbers in a Native Vector
  - Default: 128
  - 4 groups of GFP numbers, 4 bytes of exponent, 128 bytes of mantissa
- AXI Bus Width:
  - The bitwidth of the on-chip AXI Bus
  - Default: 256-bit
- Memory Block:
  - A block of memory to be Fetched at once from DDR6 to on-chip BRAM
  - Default: 128 Native Vectors
  - Since the transaction on AXI is limited to 256-bit wide, we save them in 256-bit wide BRAMs. One memory block is therefore 528 memory lines in BRAM: 32 lines of exponents and 512 lines of mantissas, in that order (first 32 lines are exponents; the rest are mantissas.) One NV of the default size is 4 exponents (4 bytes) and 4 lines in BRAM (128 bytes).
- Grouped Dimension (GD):
  - The dimension in a matrix along which the GFP numbers are grouped
  - Usually the inner dimension (V) in the context of Matrix-Matrix Multiplication
- UnGrouped Dimension (UGD):
  - The dimension in a matrix that is not grouped. 
  - Usually the outer dimensions (batch B, column C) in the context of Matrix-Matrix Multiplication
- Left UGD length (B/batch/dim_b):
  - The number of UGD vectors to process on left
- Right UGD length (C/column/dim_c):
  - The number of UGD vectors to process on right
- UGD vector length (V/inner dimension/dim_v):
  - The number of Native Vectors per UGD vector
  - Example: if `ugd_vec_size = 8`, then each UGD vector contains 8 NVs (32 lines)
  - Used in column group processing: each column group processes V NVs per column
- Column:
  - MLP columns within the compute engine
  - Default: 16 columns
- Row:
  - A row of compute engines in 2-D architecture
  - Default: 16 rows, fixed to the number of available DDR6 channels.
---
## General Interpretation of Compute Pattern
### Normal GEMM Compute Pattern:
```cpp
// GEMM: O = A * W
// Activation has dimensions B x V (B rows, V columns)
// Weights has dimensions V x C (V rows, C columns)  
// Outputs has dimensions B x C (B rows, C columns)
for (int b = 0; b < B; ++b) {
  for (int c = 0; c < C; ++c) {
    float sum = 0.0;
    for (int v = 0; v < V; ++v) {
      sum += A[b][v] * W[v][c];
    }
    O[b][c] = sum;
  }
}
```

### 1-D GEMM (one-row) Compute Pattern:
```cpp
int c_per_tile = C / num_tiles;
for (int c = 0; c < num_tiles; ++c) {
  // Below is unrolled by the factor of num_tiles per row
  // Each tile handles c_per_tile contiguous columns
  // num_tiles * c_per_tile = C (total columns)
  for (int b = 0; b < B; ++b) {
    for (int cc = 0; cc < c_per_tile; ++cc) {
      float sum = 0.0;
      int actual_col = c * c_per_tile + cc;  
      // Tile c handles columns [c*c_per_tile, (c+1)*c_per_tile)
      for (int v = 0; v < V; ++v) {
        sum += A[b][v] * W[v][actual_col];
      }
      O[b][actual_col] = sum;
    }
  }
}
```

### 2-D GEMM (multi-row) Compute Pattern:
```cpp
// Need to initialize O to zero.
for (int r = 0; r < num_rows; ++r) {
  // Determine V range for row r.
  // Corresponds to 'UGD Length' distribution in hardware (see Command 0xF0).
  // Logic: First (V % num_rows) rows get (V / num_rows) + 1 elements.
  //        Remaining rows get (V / num_rows) elements.
  int v_base = V / num_rows;
  int v_rem = V % num_rows;
  int v_count, v_start;
  if (r < v_rem) {
    v_count = v_base + 1;
    v_start = r * (v_base + 1);
  } else {
    v_count = v_base;
    v_start = v_rem * (v_base + 1) + (r - v_rem) * v_base;
  }

  for (int c = 0; c < num_tiles; ++c) {
    // Determine C range for tile c.
    // Corresponds to 'Right UGD Length' (C) distribution across tiles.
    // Logic: First (C % num_tiles) tiles get (C / num_tiles) + 1 columns.
    //        Remaining tiles get (C / num_tiles) columns.
    int c_base = C / num_tiles;
    int c_rem = C % num_tiles;
    int c_count, c_start;
    if (c < c_rem) {
      c_count = c_base + 1;
      c_start = c * (c_base + 1);
    } else {
      c_count = c_base;
      c_start = c_rem * (c_base + 1) + (c - c_rem) * c_base;
    }

    for (int b = 0; b < B; ++b) {
      for (int cc = 0; cc < c_count; ++cc) {
        float partial_sum = 0.0;
        int actual_col = c_start + cc;  
        
        for (int vv = 0; vv < v_count; ++vv) {
          int actual_v = v_start + vv;
          partial_sum += A[b][actual_v] * W[actual_v][actual_col];
        }
        // Accumulate partial sum (reduction across rows needed)
        O[b][actual_col] += partial_sum;
      }
    }
  }
}
```
This pseudo code is verified [here](/home/dev/Dev/elastix_gemm/gemm/src/py/multi-row_gemm.py).

### Compute Pattern Summary

**Normal GEMM**: Computes a full matrix multiplication O = A × W where A is B×V, W is V×C, and O is B×C. For each output element O[b][c], the entire dot product across all V elements is computed serially.

**1-D GEMM (One-Row)**: Parallelizes across the column dimension. The `num_tiles` compute tiles each handle `c_per_tile = C/num_tiles` contiguous output columns. Each tile independently computes the full dot product (across all V) for its assigned columns. No reduction is needed since each output element is computed entirely by one tile. This organization is already implemented.

**2-D GEMM (Multi-Row)**: Parallelizes across both the column dimension (via tiles) and the V dimension (via rows). The 1-D GEMM (one-row) hardware is roughly replicated `num_rows` times, with minor tweaks in the controllers.  Each of the `num_rows` rows handles a slice of `v_per_row = V/num_rows` elements from the V dimension. Each of the `num_tiles` tiles per row handles `c_per_tile = C/num_tiles` contiguous columns. Since the dot product is split across rows, each row computes a partial sum for each output element. These partial sums must be accumulated (reduced) across all rows to produce the final output. The output must be initialized to zero before computation begins. This organization still outputs the same number of outputs (num_tiles) at once, the same as the 1-D GEMM organization, after the reduction on each column.

--- 

## Architecture Overview

The 2-D Multi-Row GEMM mainly consists of four functional groups: Master Control (MC), Dispatcher Control (DC), Compute Engine (CE), and Result Collection (RC).

### Master Control (MC)
It is the global control unit group. The components in this group decode the commands from the host and dispatch them to each of the execution groups (DC, CE, RC). It sits outside of the execution units, and there is only one MC globally.  

### Dispatcher Control (DC)
It consists of the Fetcher and Dispatcher. It serves the FETCH and DISPATCH commands. Briefly speaking, the Fetcher fetches a memory block from DDR and pushes into a FIFO. The Dispatcher consumes that FIFO and routes to the local buffers in the compute engines. There is one DC per row. 

### Compute Engine (CE)
Each compute engine is a 1-D array of compute tiles, or compute columns. The compute engine serves the MATMUL (or TILE) command. The compute unit is called Machine Learning Processor (MLP) in Achronix FPGAs. Under the current configuration, each MLP computes two columns. Logically, one MLP represents two compute tiles. Each row in the 2-D GEMM has one compute engine, and each CE computes multiple columns, therefore constituting the 2-D organization. 

### Result Collection (RC)
It sits outside of the rows and collects all the results from each CE columns. It serves the READOUT command. If we have a 2-D GEMM with 16 rows and 32 columns, each compute engine will output 32 results in parallel, and there are 16 compute engines. RC will need to reduce all rows on the column, as we have discussed in the Compute Pattern section. Therefore, RC will also only produce 32 results, one for each column. There is only one RC globally. **IMPORTANT** There are cases where not all rows have meaningful results, in which case these rows needs to be turned off when performing the reduction. We will discuss these cases later.

### Overall Architecture Summary
This is a graph of the 2-D GEMM organization with 16 rows and 32 columns.

```mermaid
graph LR
    %% Global Control and Memory
    MC[Master Control <br/><i>Decodes & Dispatches</i>]
    DDR[(DDR Memory)]

    subgraph Rows [Parallel Row Processing]
        direction TB

        %% Row 0 Detail
        subgraph Row0 [Row 0]
            direction LR
            DC0[Dispatcher 0] --> CE0
            subgraph CE0 [Compute Engine 0]
                direction LR
                MLP0_1[MLP: Col 0-1] --- MLP0_Dots[...] --- MLP0_N[MLP: Col 30-31]
            end
        end

        %% Row 1 Detail
        subgraph Row1 [Row 1]
            direction LR
            DC1[Dispatcher 1] --> CE1
            subgraph CE1 [Compute Engine 1]
                direction LR
                MLP1_1[MLP: Col 0-1] --- MLP1_Dots[...] --- MLP1_N[MLP: Col 30-31]
            end
        end

        Row_Dots[ . . . 16 Rows Total . . . ]

        %% Row 15 Detail
        subgraph Row15 [Row 15]
            direction LR
            DC15[Dispatcher 15] --> CE15
            subgraph CE15 [Compute Engine 15]
                direction LR
                MLP15_1[MLP: Col 0-1] --- MLP15_Dots[...] --- MLP15_N[MLP: Col 30-31]
            end
        end
    end

    %% Global Result Collection
    subgraph RC_Group [Result Collection - RC]
        Sum{Reduction Logic<br/>Σ Row 0-15}
        RC_Unit[READOUT Control]
    end

    %% Control Flow (Dashed)
    MC -.-> DC0 & DC1 & DC15
    MC -.-> RC_Unit

    %% Data Flow (Solid)
    DDR ==> DC0 & DC1 & DC15
    
    CE0 ==> Sum
    CE1 ==> Sum
    CE15 ==> Sum
    
    Sum --> RC_Unit
    RC_Unit ==> Output[/32 Column Results/]

    %% Styling
    classDef dashed fill:#fff,stroke:#666,stroke-dasharray: 5 5;
    class CE0,CE1,CE15 dashed;

    style MC fill:#f9f,stroke:#333
    style DDR fill:#eee,stroke:#333
    style RC_Group fill:#e1f5fe,stroke:#01579b
```

## Core Architecture

### csr_to_fifo_bridge
#### Functionality
It will bridge the CSRs where the host submits the command with the cmd_fifo. It reads one command and forwards it to the cmd_fifo.

#### Implementation Details
The host submits commands in 32-bit word format (see `issue_command` in [vp815_gemm_device.hpp](/home/dev/Dev/elastix_gemm/gemm/sw_test/vp815_gemm_device.hpp) . Each command takes 4 words 128 bits. The output is therefore 128-bit wide to encapsulate one command. 

### cmd_fifo
#### Functionality
This module implements a FIFO to buffer the commands (microcode) from the host. Master Control reads each command from this FIFO and forward the arguments to the other components.

#### Implementation Details
The cmd_fifo takes one command from csr_to_fifo_bridge and pushes it into a FIFO. The FIFO is 128-bit wide and 512 entry deep. Master Control will consume the commands from this cmd_fifo. 


### master_control
#### Functionality
1. Parses Command MicroCodes
2. Routes Commands to Fetcher, Dispatcher, Compute Engine, and Result Collection. 
3. Orchestrates and Synchronizes the operations of each component

#### Implementation Details
The Master Control unit operates as a Finite State Machine (FSM) that parses the 4-word command structure and executes the appropriate operations.

**States and Transitions:**

- **ST_IDLE**
  - **Action**: Waits for non-empty command FIFO.
  - **Transition**:
    - If FIFO not empty -> `ST_DECODE` (Reads Command Header)
    - Else -> `ST_IDLE`

- **ST_DECODE**
  - **Action**: Decodes the Opcode (Command Header) and routes the arguments in the command to the appropriate component and enters the corresponding executing state.
  - **Transition**:
    - `OPC_FETCH` (0xF0) -> `ST_EXEC_FETCH`
    - `OPC_DISPATCH` (0xF1) -> `ST_EXEC_DISP`
    - `OPC_MATMUL` (0xF2) -> `ST_EXEC_TILE`
    - `OPC_WAIT_DISPATCH` (0xF3) -> `ST_WAIT_DISP`
    - `OPC_WAIT_MATMUL` (0xF4) -> `ST_WAIT_TILE`
    - `OPC_READOUT` (0xF5) -> `ST_EXEC_READOUT`
    - Unknown Opcode -> `ST_CMD_COMPLETE`

**ST_EXEC_FETCH**
  - **Action**: Triggers Fetcher unit with parameters (Address, Length).
  - **Transition**: Always -> `ST_WAIT_FETCH`

**ST_WAIT_FETCH**
  - **Action**: Waits for Fetcher to signal completion (`i_dc_fetch_done`).
  - **Transition**:
    - If Done -> `ST_CMD_COMPLETE`
    - Else -> `ST_WAIT_FETCH`

**ST_EXEC_DISP**
  - **Action**: Triggers Dispatch operation directly to Compute Engine. Records Command ID as `pending_disp_id`.
  - **Transition**: Always -> `ST_CMD_COMPLETE` (Async execution)

**ST_EXEC_TILE**
  - **Action**: Triggers MATMUL operation in Compute Engine. Records Command ID as `pending_tile_id`.
  - **Transition**: Always -> `ST_CMD_COMPLETE` (Async execution)

**ST_WAIT_DISP**
  - **Action**: Wait barrier for DISPATCH command. Checks if `wait_id` matches completed dispatch.
  - **Transition**:
    - For MS2.0: Checks if Dispatcher Controller is IDLE (`i_dc_state == 0`).
    - If IDLE -> `ST_CMD_COMPLETE`
    - Else -> `ST_WAIT_DISP`

**ST_WAIT_TILE**
  - **Action**: Wait barrier for MATMUL command. Checks if `wait_id` matches completed tile op.
  - **Transition**:
    - For MS2.0: Checks if Compute Engine is IDLE (`i_ce_state == 0`).
    - If IDLE -> `ST_CMD_COMPLETE`
    - Else -> `ST_WAIT_TILE`

**ST_EXEC_READOUT**
  - **Action**: Triggers Result Arbiter/DMA to read results.
  - **Transition**: Always -> `ST_WAIT_READOUT`

**ST_WAIT_READOUT**
  - **Action**: Waits for Readout completion (`i_readout_done`).
  - **Transition**:
      - If Done -> `ST_CMD_COMPLETE`
      - Else -> `ST_WAIT_READOUT`

**ST_CMD_COMPLETE**
  - **Action**: Final cleanup, ready for next command.
  - **Transition**: Always -> `ST_IDLE`

### Dispatcher Control
#### Functionality (Revised Architecture)
Acts as the central router for the row's data ingress. It couples the `Fetcher` with the `Dispatcher` logic via a streaming FIFO interface, eliminating the need for intermediate L2 storage for weights.

#### Implementation Details
- **Streaming FIFO**: A FIFO connects the `Fetcher` (Producer) and the `Dispatcher` (Consumer).
- **Fetcher Role**: Pure DMA engine. Reads from GDDR6 and pushes raw data into the FIFO. It is agnostic to the data's destination (Left vs. Right).
- **Dispatcher Role**: Consumes the FIFO and performs routing based on the command type:
  - **Left Data (Activations)**: Routed to `row_bram`.
  - **Right Data (Weights)**: Routed directly to `mlp_bram` inside the Compute Columns via round-robin distribution, bypassing `row_bram` entirely.
  - **Right Distribution**: Since L2 is skipped, the dispatcher logic distributes the weights directly to the L1 memories (`mlp_bram`) of the compute columns.

#### Key Architectural Differences
- **No L2 for Weights**: The concept of an "L2 Weight Buffer" in `row_bram` is removed. Weights stream from Memory -> FIFO -> Dispatcher -> L1 (`mlp_bram`), reducing latency and eliminating double-buffering.
- **Dedicated Activation Buffer**: `row_bram` is dedicated solely to storing activations (Left Matrix) which need to be reused (broadcasted) across many compute tiles during the `TILE` operation.

### Fetcher
#### Functionality
Efficiently manages high-bandwidth data transfers from GDDR6 memory to a Streaming FIFO.

#### Implementation Details
- **Burst Management**: Issues up to 32 AXI read bursts back-to-back using a 32-deep FWFT FIFO for Address Read (AR) requests.
- **Data Unpacking**: Separates Exponents and Mantissas from the memory block.
- **Destination**: Writes to the Streaming FIFO interface instead of addressing `row_bram` directly.

### MLP Dispatch Controller
#### Functionality
Consumes the Fetch FIFO and manages the writing of **Activation** data to the `row_bram` and **Weight** data directly into the distributed `mlp_bram`.

#### Implementation Details
- **2-Stage Stream**: For both left (Activation) and right (Weight) data, the Dispatcher always processes data in units of one memory block (528 256-bit lines). "2-Stage" refers to:
  - **Stage-1 (Exponents)**: Reading and buffering the first 16 lines (exponents) to a local exponent BRAM (512 exponents).
  - **Stage-2 (Mantissas)**: Reading the remaining 512 lines (mantissas). For each line, the Dispatcher attaches the corresponding exponent buffered in Stage-1 and forwards the packet to the correct destination: `row_bram` for Left/Activation, or `mlp_bram` for Right/Weight.
- **Distribution Logic**:
  - **Right Data**: Uses `col_start` to Round-Robin distribute the stream to specific columns' `mlp_bram`. **Always Distributes** (no broadcast mode).
  - **Left Data**: Writes are redirected to the `row_bram` write ports.

### Compute Engine (MLP-Based)
#### Functionality
The top-level execution unit for a row. It contains the local activation storage (`row_bram`) and the compute array.

#### Implementation Details
- **Left-Only Storage**: `row_bram` serves **only** as the Activation Buffer. It stores the "Left" matrix data reused across columns.
- **Command Handling**:
  - `FETCH` (Left): Fills `row_bram` via the Dispatcher.
  - `FETCH` (Right) + `DISPATCH`: Operates as a streaming pipeline. The Dispatcher streams data from the Fetch FIFO directly into the `comp_mlp_bram_col_wrapper` (L1).
  - `TILE`: Triggers computation using Activations from `row_bram` and Weights already resident in `mlp_bram`.

### MLP BRAM Column Wrapper (`comp_mlp_bram_col_wrapper`)
#### Functionality
The core computational kernel comprising 16 Compute Columns. It handles the storage of weights in L1 (`mlp_bram`) and executes the Dot Product computation.

#### Implementation Details
- **4-Stack Architecture**: Each column contains 4 parallel "stacks". This increases throughput 4x compared to a single-stack design.
  - **Loading**: Accepts 4 chunks of data in parallel during DISPATCH.
  - **Computing**: Streams 4 partial dot products in parallel during TILE.
- **Pipeline**: Features an integer-domain adder pipeline to sum the partial results from the 4 stacks, improving accuracy before the final FP16 rounding.

### Dispatcher Control and Compute Engine Overview
```mermaid
graph TD
    %% Dispatcher Control Internal
    subgraph DC [Dispatcher Control]
        Fetcher --> FIFO
        FIFO --> Dispatcher
    end

    %% Routing Logic
    Dispatcher --> Split{Route}
    
    %% Compute Engine Context
    subgraph CE [Compute Engine]
        direction TB
        
        %% Shared Memory (Outside Columns)
        RowBRAM[row-bram <br/> Shared Activations]
        
        %% Tightly Coupled Columns
        subgraph Columns [Parallel Compute Columns]
            direction LR
            
            subgraph Col0 [Column 0]
                direction TB
                B0[mlp-bram 0] --> M0[MLP 0]
            end

            subgraph Col1 [Column 1]
                direction TB
                B1[mlp-bram 1] --> M1[MLP 1]
            end

            ColDots[...]

            subgraph ColN [Column 15]
                direction TB
                BN[mlp-bram 15] --> MN[MLP 15]
            end
        end
    end

    %% Dispatch Routing
    Split -- "Left (Activations)" --> RowBRAM
    Split -- "Right (Weights)" --> B0 & B1 & BN

    %% Row BRAM Broadcast to MLPs
    RowBRAM --> |Broadcast| M0
    RowBRAM --> |Broadcast| M1
    RowBRAM --> |Broadcast| MN

    %% Results Connections
    M0 --> R0[result 0]
    M1 --> R1[result 1]
    MN --> RN[result n]

    %% Styling
    style RowBRAM fill:#fff4dd,stroke:#d4a017
    style DC fill:#f5f5f5,stroke:#333
    style Col0 fill:#e1f5fe,stroke:#01579b
    style Col1 fill:#e1f5fe,stroke:#01579b
    style ColN fill:#e1f5fe,stroke:#01579b
    style ColDots fill:#fff,stroke:none
```

## Microcode Command Reference

This section documents all commands supported by the multi-row MS2.0 architecture, aligned with the driver implementation (`vp815_gemm_device.hpp`) and hardware specification.

### Command Organization

**Fixed 4-Word Format**: All commands use a consistent 4-word (128-bit) structure for uniform FIFO processing:
- **Word 0**: Command Header (32 bits)
  - Bits [31:16]: Total length in bytes (usually 16)
  - Bits [15:8]: Command ID (for tracking and synchronization)
  - Bits [7:0]: Opcode
- **Words 1-3**: Command Payload (96 bits total, unused words = 0x00000000)

### Command Summary Table

| Opcode | Name | Number of Arguments | Purpose |
|--------|------|---------------------|---------|
| 0xF0 | fetch_memory_block | 3 | Transfer memory block from GDDR6 to Dispatcher_bram |
| 0xF1 | vector_dispatch | 8 | Copy data from Dispatcher_bram to tile_brams |
| 0xF2 | matmul | 9 | Execute parallel matrix multiplication across enabled tiles |
| 0xF3 | wait_dispatch | 1 | Synchronization barrier - wait for DISPATCH command to complete |
| 0xF4 | wait_matmul | 1 | Synchronization barrier - wait for MATMUL command to complete |
| 0xF5 | vector_readout | 2 | Read result vectors from result_brams to host |

---

### Command 0xF0: FETCH_MEMORY_BLOCK

**Purpose**: Fetch a memory block (528 lines) from GDDR6 external memory. Each row will receive the same number of memory blocks, but different ugd_len is possible (see below for details). The memory lines will be pushed into a FIFO, and the Dispatcher will consume that FIFO. 

#### Hardware Packing (4-Word Format)

```cpp
cmd[0] = {16'd16, cmd_id[7:0], OPC_FETCH}
cmd[1] = {start_addr[31:0]}
cmd[2] = {ugd_len[15:0], len[15:0]}
cmd[3] = {31'b0, fetch_right}
```

#### Field Details

- **Start Address**: 
  - **Definition**: The starting byte address in GDDR6 memory.
  - **Hardware Format**: The host provides a byte address, which hardware converts to 32-byte line units (`addr / 32`) in Word 1.
  - **Scope**: Offset relative to the GDDR6 page base.
  - **2-D Multi-Row Implementation**: This address is treated as a channel-local offset.
    - The Master Control broadcasts this common offset to all rows. 
    - Each row's implementation (Dispatcher) implicitly targets its corresponding DDR channel (e.g., Row 0 -> Channel 0). No explicit channel selection bits are needed in the address field itself.
- **UGD Length**: The total size of the Inner Dimension (V) in terms of Native Vectors. i.e. The number of Native Vectors per UGD. 
  - **Purpose**: Defines the total computational depth along the reduction axis.
  - **Row Distribution Logic**: The Master Control uses this value to calculate and assign the specific workload for each row (`v_count`), ensuring the total `V` is covered even if it doesn't divide evenly by `num_rows`. The Fetcher will get the **ACTUAL** UGD Length it needs to fetch from GDDR6 calculated by the Master Control.
    - `Base_Count = UGD_Length / num_rows`
    - `Remainder = UGD_Length % num_rows`
    - **Allocation**: The first `Remainder` rows are assigned `Base_Count + 1` NVs. The remaining rows are assigned `Base_Count` NVs.
    - **Example**: If `V = 24` and `num_rows = 16`:
      - `Base = 1`, `Rem = 8`.
      - Rows 0 through 7 process 2 NVs each.
      - Rows 8 through 15 process 1 NV each.
- **Length**: Number of lines to fetch
  - Default: 528 (full block: 16 exponents + 512 mantissas)
- **Fetch Right**: Target buffer selection
  - 0: Fetch to left buffers
  - 1: Fetch to right buffers

---

### Command 0xF1: VECTOR_DISPATCH

**Purpose**: Consumes the FIFO produced by the Fetcher and routes data to the Compute Engine. Based on the target (Left vs. Right), it handles data storage differently:
- **Left Data (Activations)**: Written to `row_bram`, which serves as a shared buffer accessible by all compute tiles (Broadcast).
- **Right Data (Weights)**: Distributed round-robin directly to the compute buffers (`mlp_bram`) within the compute tiles (Distribute).

#### Hardware Packing (4-Word Format)

```cpp
cmd[0] = {16'd16, cmd_id[7:0], OPC_DISPATCH}
cmd[1] = {nv_cnt[15:0], ugd_len[15:0]}
cmd[2] = {16'b0, tile_addr[15:0]}
cmd[3] = {16'b0, col_start[7:0], 5'b0, disp_right, broadcast, man_4b}
```

#### Field Details

- **NV Count**: Number of Native Vectors to dispatch total (Hardware processes `cnt * 4` lines). It defaults to 128, which is a whole memory block. 
- **UGD Length**: Number of Native Vectors per UGD vector. It is the same as the UGD Length in the FETCH command.
- **Tile Address**: The starting address of the destination buffer.
  - For Left Data (Activations): Linear address in `row_bram`.
  - For Right Data (Weights): Linear address in `mlp_bram`.
- **Column Start (col_start)**: The starting column index for round-robin distribution. 
  - Used for **Right Data** (Weights) to determine which tile receives the first chunk.
  - Ignored for **Left Data** (Activations) as they are written to the shared `row_bram`.
- **Flags**:
  - `disp_right`: 1=Dispatch to Right (Weights), 0=Dispatch to Left (Activations).
  - `broadcast`: 1=Broadcast to Shared Buffer (Left), 0=Distribute Round-Robin (Right). Typically `broadcast = ~disp_right`.
  - `man_4b`: 1=4-bit mantissa mode, 0=8-bit

---

### Command 0xF2: MATMUL (TILE)

**Purpose**: Execute parallel matrix multiplication across enabled compute tiles.

#### Hardware Packing (4-Word Format)

```cpp
cmd[0] = {16'd16, cmd_id[7:0], OPC_MATMUL}
cmd[1] = {left_addr[15:0], right_addr[15:0]}
cmd[2] = {left_len[15:0], right_len[15:0]}
cmd[3] = {ugd_len[15:0], 13'b0, left_4b, right_4b, main_loop_left}
```

#### Field Details

- **Left/Right Address**: Starting line address in the respective buffers (0-511).
  - **Left**: Address in `row_bram` (Activations).
  - **Right**: Address in `mlp_bram` (Weights).
- **Left Length**: Number of UGD vectors on left (Batch dimension)
- **Right Length**: Number of UGD vectors on right (Column dimension)
- **UGD Length**: Number of Native Vectors per UGD vector (Inner dimension)
- **Flags**:
  - `left_4b`/`right_4b`: 1=4-bit mantissa, 0=8-bit
  - `main_loop_left`: 1=Loop over left matrix first, 0=Loop over right

---

### Command 0xF3: WAIT_DISPATCH

**Purpose**: Synchronization barrier - blocks execution until specified DISPATCH command completes.

#### Hardware Packing (4-Word Format)

```cpp
cmd[0] = {16'd16, cmd_id[7:0], OPC_WAIT_DISPATCH}
cmd[1] = {24'd0, wait_id[7:0]}
cmd[2] = 0
cmd[3] = 0
```

- **wait_id**: The ID of the DISPATCH command to wait for. The Master Control should release the barrier when the `wait_id` is less than the `cmd_id` that the Dispatcher is currently serving. 

---

### Command 0xF4: WAIT_MATMUL

**Purpose**: Synchronization barrier - blocks execution until specified MATMUL command completes.

#### Hardware Packing (4-Word Format)

```cpp
cmd[0] = {16'd16, cmd_id[7:0], OPC_WAIT_MATMUL}
cmd[1] = {24'd0, wait_id[7:0]}
cmd[2] = 0
cmd[3] = 0
```

- **wait_id**: The ID of the MATMUL command to wait for. The Master Control should release the barrier when the `wait_id` is less than the `cmd_id` that the Compute Engine is currently serving. 

---

### Command 0xF5: VECTOR_READOUT

**Purpose**: Read result vectors from Compute Engine output FIFOs to outgoing BRAMs, prepared for Host DMA read. It also includes the all-reduce on columns for all rows.

#### Hardware Packing (4-Word Format)

```cpp
cmd[0] = {16'd16, cmd_id[7:0], OPC_READOUT}
cmd[1] = {left_len[15:0], right_len[15:0]}
cmd[2] = {16'b0, ugd_len[15:0]}
cmd[3] = 0
```

#### Field Details
- **Left Length**: Number of UGD vectors on left (Batch dimension)
- **Right Length**: Number of UGD vectors on right (Column dimension)
- **UGD Length**: Number of Native Vectors per UGD vector (Inner dimension)

### Important Notes
**FETCH** and **DISPATCH** always come together. **MATMUL/TILE** and **READOUT** always come together. These four commands do not block/barrier the execution flow. The synchronization is enforced by the two **WAIT** commands. The purpose for the synchronization or barrier is for memory coherence. For example, **WAIT_TILE** is to ensure that the current in-use local buffers in the Compute Engine is not overwritten by the next **DISPATCH**. Similarly, **WAIT_DISPATCH** is to ensure that the next **MATMUL** do not read from the data that is currently being written. 

**UGD Length** and **Right Length** are the **Total** number of NVs and UGD vectors that is processed by the whole GEMM. Master Control decodes the commands and will pass the appropriate numbers to the execution units in each row. **UGD Length**, **Right Length**, and **Left Length** should be consistent in one **FETCH-DISPATCH** pair and **MATMUL-READOUT** pair. 