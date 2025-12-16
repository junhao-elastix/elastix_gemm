# State Machine Transitions - MS2.0 GEMM Engine

## Master Control (MC)

### FETCH Command (0xF0)
```
IDLE -> READ_HDR -> READ_PL1 -> READ_PL2 -> READ_PL3 -> DECODE -> EXEC_FETCH -> WAIT_FETCH -> CMD_COMPLETE -> IDLE
```

**Trigger**: `dc_fetch_en_reg = 1` when `i_dc_state == IDLE`
**Wait**: Until `i_dc_fetch_done == 1`
**Clear**: `dc_fetch_en_reg = 0` when done detected

### DISPATCH Command (0xF1) - Asynchronous Trigger
```
IDLE -> READ_HDR -> READ_PL1 -> READ_PL2 -> READ_PL3 -> DECODE -> EXEC_DISP -> CMD_COMPLETE -> IDLE
```

**Trigger**: `dc_disp_en_reg = 1` (pulse) when `i_dc_state == IDLE`
**Behavior**: Returns IMMEDIATELY after trigger, does NOT wait for completion
**Background**: DC executes DISPATCH operation asynchronously (duration varies based on parameters)
**ID Tracking**: `pending_disp_id_reg` stores command ID for WAIT_DISPATCH barrier

**Key Design**: This enables pipelined command execution - MC can process next commands while DC copies data

**Duration**: Varies based on man_nv_cnt and ugd_vec_size parameters

**Architecture** (per SINGLE_ROW_REFERENCE.md):
- Four separate BRAMs: exp_left, man_left, exp_right, man_right
- `disp_right` flag selects which side to dispatch (0=left, 1=right)
- `broadcast` flag controls distribution mode (0=distribute, 1=broadcast)
- Two paths (exp + man) for selected side read/write in PARALLEL in same clock cycle
- Single address counter drives both read addresses for the selected side
- Single write address drives both write addresses for the selected side
- Bandwidth per DISPATCH: 2 × 256-bit + 2 × 8-bit per cycle (one side at a time)

### WAIT_DISPATCH Barrier (0xF3) - Synchronization Point
```
IDLE -> READ_HDR -> READ_PL1 -> READ_PL2 -> READ_PL3 -> DECODE -> WAIT_DISP -> CMD_COMPLETE -> IDLE
```

**Purpose**: Synchronization barrier for DISPATCH operations
**Block Condition**: Stays in WAIT_DISP state until `i_dc_state == IDLE` AND `i_dc_disp_done == 1`
**ID Tracking**: `wait_id_reg` stores which command ID we're waiting for (for debug/logging)
**Release**: When DC returns to IDLE state AND signals done, barrier passes
**Use Case**: Insert after DISPATCH commands to ensure DISPATCH operation completes before MATMUL

**Mechanism**: Direct state machine check plus done signal (ensures operation fully complete)

### MATMUL Command (0xF2) - Asynchronous Trigger
```
IDLE -> READ_HDR -> READ_PL1 -> READ_PL2 -> READ_PL3 -> DECODE -> EXEC_TILE -> CMD_COMPLETE -> IDLE
```

**Trigger**: `ce_tile_en_reg = 1` (pulse) when `i_ce_state == IDLE`
**Behavior**: Returns IMMEDIATELY after trigger, does NOT wait for completion
**Background**: CE runs BCV loops asynchronously (varies with B×C×V dimensions)
**ID Tracking**: `pending_tile_id_reg` stores command ID for WAIT_MATMUL barrier

**Key Design**: This enables pipelined command execution - MC can process next commands while CE computes

### WAIT_MATMUL Barrier (0xF4) - Synchronization Point
```
IDLE -> READ_HDR -> READ_PL1 -> READ_PL2 -> READ_PL3 -> DECODE -> WAIT_TILE -> CMD_COMPLETE -> IDLE
```

**Purpose**: Synchronization barrier for MATMUL operations
**Block Condition**: Stays in WAIT_TILE state until `i_ce_state == IDLE`
**ID Tracking**: `wait_id_reg` stores which command ID we're waiting for (for debug/logging)
**Release**: When CE returns to IDLE state, barrier passes and proceeds to CMD_COMPLETE
**Use Case**: Insert after MATMUL commands to ensure computation completes before reading results

**Mechanism**: Direct state machine check (not ID comparison) - simplest and most reliable

### READOUT Command (0xF5) - Result Collection
```
IDLE -> READ_HDR -> READ_PL1 -> READ_PL2 -> READ_PL3 -> DECODE -> EXEC_READOUT -> WAIT_READOUT -> CMD_COMPLETE -> IDLE
```

**Purpose**: Collect results from compute engine and output to result buffer
**Trigger**: `readout_en_reg = 1` in EXEC_READOUT state
**Parameters**:
- `start_col[7:0]`: Starting tile index (0-23)
- `rd_len[31:0]`: Total FP16 results to read

**Wait Condition**: Stays in WAIT_READOUT until `i_readout_done == 1`

**⚠️ CURRENT STATUS: BYPASSED IN MLP MODE**
- `arb_mc_readout_done` is hardwired to `1'b1` in `engine_top.sv`
- Results flow **directly** from `compute_engine_mlp` to `o_result_256_*` outputs
- READOUT command completes immediately without triggering actual result collection
- The MLP compute engine outputs results to circular buffer during ST_COMPUTE phase

---

## Fetcher Module

### FETCH Operation
```
ST_IDLE -> ST_FETCH_INIT -> ST_FETCH_ACTIVE -> ST_FETCH_DONE
```

**Trigger**: `i_fetch_en == 1`
**State Flow**:
- ST_FETCH_INIT: Initialize operation, capture fetch parameters
- ST_FETCH_ACTIVE: Single unified state for issuing AXI AR requests and receiving R data
- ST_FETCH_DONE: All data received, signal completion
**Done Signal**: `o_fetch_done = 1` (1 cycle pulse)
**AXI Reads**: 528 lines total (16 exponent + 512 mantissa via 16-beat bursts with 33 ARs)
**BRAM Write**: Left buffers (exp_left, man_left) OR Right buffers (exp_right, man_right) depending on fetch_right flag

---

## Dispatcher Module

### DISPATCH Operation
```
IDLE -> DISP_BUSY -> DISP_DONE -> IDLE
```

**Trigger**: `i_disp_en == 1`
**Architecture**: Selective two-path operation (per SINGLE_ROW_REFERENCE.md)
- `disp_right=0`: exp_left_aligned[0-511] → tile_bram.exp_left[0-511]
                  man_left[0-511] → tile_bram.man_left[0-511]
- `disp_right=1`: exp_right_aligned[0-511] → tile_bram.exp_right[0-511]
                  man_right[0-511] → tile_bram.man_right[0-511]

**Copy Mechanism**:
- `broadcast=1`: Same data to all enabled tiles (for activations)
- `broadcast=0`: Different data to each tile round-robin (for weights)
- Single address counter drives both read addresses for the selected side
- Two BRAMs (exp + man) for selected side write in PARALLEL in same clock cycle
- Bandwidth per cycle: 2 × 256-bit + 2 × 8-bit (one side only)

**Done Signal**: `o_disp_done = 1` when all man_nv_cnt data dispatched to all enabled tiles
**Duration**: Varies based on man_nv_cnt, ugd_vec_size, number of enabled tiles, and broadcast mode

---

## Compute Engine 

### Top Level (`compute_engine_mlp`)
```
ST_IDLE -> ST_FILL -> ST_COMPUTE -> ST_DONE
        (for C > 16: ST_FILL -> ST_COMPUTE loops for each column group)
```

**Trigger**: `i_tile_en == 1`
**Processing**: MLP column controller executes dot products with 4-stack parallelism
**Done Signal**: `o_tile_done = 1`
**Column Groups**: For C > 16, processes in sequential groups of 16

### MLP Column Controller (`mlp_bram_col_ctrl`)

**Weight Loading FSM**:
```
WT_IDLE -> WT_LOAD -> WT_DONE -> WT_IDLE
```
- WT_LOAD: 4 cycles per NV (4-stack parallel architecture)

**Compute FSM**:
```
COMP_IDLE -> COMP_SETUP -> COMP_STREAM -> COMP_DRAIN -> COMP_IDLE
```
- COMP_SETUP: 1 cycle (BRAM read address setup)
- COMP_STREAM: 4 cycles per NV (parallel 8×8 dot products across 4 stacks)
- COMP_DRAIN: 3 cycles (pipeline flush + FP24 adder tree)

**4-Stack Parallel Architecture**:
- 4 × `mlp_bram_col` stacked in parallel
- Each stack: 32 elements (256-bit mantissa + 8-bit exponent)
- FP24 adder tree: 2-level pipelined (4-cycle latency)
- Output: 8 MLPs × 2 banks (AB+CD) = 16 logical columns

**Output Format** (per MLP):
- `dout[23:0]`: Bank CD (odd column FP24 result)
- `dout[47:24]`: Bank AB (even column FP24 result)
- `dout[71:48]`: Status bits

---

## Synchronization Points

### FETCH Handshake
```
MC: dc_fetch_en=1 ────────────────┐
                                  ▼
Fetcher:              ST_FETCH_INIT → ST_FETCH_ACTIVE → ST_FETCH_DONE
                                        │
                                        │ (issues 33 ARs, receives 528 lines)
                                        │
Fetcher: o_fetch_done=1 ────────────────┤
                                        ▼
MC:                   dc_fetch_en=0, proceed to CMD_COMPLETE
```

### DISPATCH Handshake (Asynchronous)
```
MC: dc_disp_en=1 (pulse) ─────────┐
                                  ▼
MC:                   Returns IMMEDIATELY to CMD_COMPLETE (no blocking!)

DC:                   Starts DISP_BUSY in BACKGROUND
                                  │
                                  │ (varies: selective 2-path copy based on disp_right flag)
                                  │ Counter drives 2 BRAMs (exp + man) for selected side simultaneously
                                  │ Distribution controlled by broadcast flag (broadcast or distribute to tiles)
                                  │
DC: state DISP_BUSY → DISP_DONE → IDLE
                                  ▼
DC: o_disp_done=1 (pulse)     Done signal

Later (separate WAIT_DISPATCH command):
MC: Enters WAIT_DISP state ───────┐
                                  ▼
MC:                   Checks: (i_dc_state == IDLE) && (i_dc_disp_done == 1) ?
                                  │
                                  │ If YES: barrier passes
                                  ▼
MC:                   Proceeds to CMD_COMPLETE
```

### MATMUL Handshake (Asynchronous)
```
MC: ce_tile_en=1 (pulse) ─────────┐
                                  ▼
MC:                   Returns IMMEDIATELY to CMD_COMPLETE (no blocking!)

CE:                   Starts COMP_BUSY in BACKGROUND
                                  │
                                  │ (varies with B×C×V dimensions)
                                  │ BCV controller executes nested loops
                                  │
CE: state COMP_BUSY → COMP_DONE → IDLE
                                  ▼
CE: o_tile_done=1 (pulse)     Done signal

Later (separate WAIT_MATMUL command):
MC: Enters WAIT_TILE state ───────┐
                                  ▼
MC:                   Checks: i_ce_state == IDLE ?
                                  │
                                  │ If YES: barrier passes
                                  ▼
MC:                   Proceeds to CMD_COMPLETE
```

### READOUT Handshake (BYPASSED IN MLP MODE)
```
MC: readout_en=1 ─────────────────┐
                                  ▼
MC:                   Enters ST_EXEC_READOUT → ST_WAIT_READOUT
                                  │
                                  │ arb_mc_readout_done = 1'b1 (hardwired)
                                  ▼
MC:                   Immediately proceeds to CMD_COMPLETE

Actual Result Path (Direct MLP Output):
compute_engine_mlp: o_result_256_valid ────┐
                                           ▼
engine_top:         o_result_256_data/valid/wr_addr → external circular buffer
```

**Note**: In MLP mode, results are output directly during ST_COMPUTE phase via the 256-bit result interface. The READOUT command exists in the command flow but the actual result collection is handled by the direct MLP output path.