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
**Block Condition**: Stays in WAIT_DISP state until `i_dc_state == IDLE`
**ID Tracking**: `wait_id_reg` stores which command ID we're waiting for (for debug/logging)
**Release**: When DC returns to IDLE state, barrier passes and proceeds to CMD_COMPLETE
**Use Case**: Insert after DISPATCH commands to ensure DISPATCH operation completes before MATMUL

**Mechanism**: Direct state machine check (not ID comparison) - simplest and most reliable

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

---

## Dispatcher Control (DC)

### FETCH Operation
```
IDLE -> FETCH_INIT -> FETCH_READ -> FETCH_READ_EXP -> FETCH_READ_MAN -> FETCH_DONE -> IDLE
```

**Trigger**: `i_fetch_en == 1`
**State Flow**:
- FETCH_INIT: Initialize operation
- FETCH_READ: Issue AXI AR (address read) requests, wait for arvalid && arready handshake
- FETCH_READ_EXP: Receive exponent data (16 lines), loop back to FETCH_READ for next burst
- FETCH_READ_MAN: Receive mantissa data (512 lines), loop back to FETCH_READ for next burst
- FETCH_DONE: All data received, signal completion
**Done Signal**: `o_fetch_done = 1` (1 cycle pulse)
**AXI Reads**: 528 lines total (16 exponent + 512 mantissa via 16-beat bursts)
**BRAM Write**: Left buffers (exp_left_packed, man_left) OR Right buffers (exp_right_packed, man_right) depending on fetch_right flag

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

### Top Level
```
IDLE -> COMP_BUSY -> COMP_DONE -> IDLE
```

**Trigger**: `i_tile_en == 1`
**Processing**: BCV controller executes B×C×V loops
**Done Signal**: `o_tile_done = 1`

### BCV Controller (Internal)
```
IDLE -> B_LOOP -> C_LOOP -> V_LOOP -> ACCUMULATE -> OUTPUT -> (next B/C) -> BCV_DONE -> IDLE
```

**Nested Loops**: for b in [0:B), for c in [0:C), for v in [0:V)
**BRAM Reads**: Dual-port (left + right) per V iteration
**Output**: FP16 result per (b,c) pair

---

## Synchronization Points

### FETCH Handshake
```
MC: dc_fetch_en=1 ────────────────┐
                                  ▼
DC:                   FETCH_INIT → FETCH_READ → FETCH_READ_EXP → FETCH_READ → FETCH_READ_MAN → FETCH_READ → FETCH_DONE
                                  │            ↑______________|              ↑______________|
                                  │         (loop for 16 exp bursts)      (loop for 32 man bursts)
                                  │
                                  │ (~528 lines via AXI bursts)
                                  │
DC: o_fetch_done=1 ───────────────┤
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
MC:                   Checks: i_dc_state == IDLE ?
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