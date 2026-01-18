# AMD GEMM Reference Manual

This document analyzes the AMD GEMM implementation as a reference design for the Achronix multi-row GEMM engine. It covers the AMD design architecture, hardware differences, reusable components, handshake patterns, and coding style conventions.

**Source Location:** `/home/dev/Dev/elastix_gemm/amd_gemm/ip/`

---

## 1. AMD GEMM Architecture Overview

### 1.1 Design Parameters

From `gemm_pkg.sv`:

| Parameter | Value | Description |
|-----------|-------|-------------|
| `gemm_num_rows_gp` | 16 | Number of rows (V dimension partitions) |
| `gemm_num_cols_gp` | 13 | Number of columns (C dimension partitions) |
| `gemm_num_axi_gp` | 4 | AXI masters per row for HBM access |
| `tile_num_dots_gp` | 128 | Dot products per tile |
| `tile_num_groups_gp` | 4 | GFP groups per tile |
| `gemm_data_width_gp` | 256 | Memory data width (bits) |
| `gfp_group_size_gp` | 32 | Elements per GFP group |
| `gfp_mant_width_gp` | 8 | GFP mantissa width |
| `gfp_exp_width_gp` | 5 | GFP exponent width |

### 1.2 Module Hierarchy

```
gemm_top_wrapper
└── gemm_top
    ├── gemm_control          (Master control FSM, command parsing, V distribution)
    │   └── two_fifo          (Command buffering)
    │
    ├── gemm_row [0:15]       (Per-row processing, C distribution)
    │   ├── gemm_dispatch     (Data fetching, exp/mant separation)
    │   │   ├── two_fifo      (Command pipeline)
    │   │   ├── fifo          (Exponent FIFO)
    │   │   └── adapter       (Mantissa width conversion)
    │   │
    │   └── gemm_tile [0:12]  (Compute tiles)
    │       ├── vbram_nr1w    (Left matrix BRAM - virtualized)
    │       ├── vbram_nr1w    (Right matrix BRAM - virtualized)
    │       └── gfp_dotp      (GFP dot product unit)
    │
    ├── gemm_col_adder [0:12] (Column reduction across rows)
    │   ├── two_fifo          (Tile output buffering per row)
    │   └── fp_adder_tree     (Row reduction tree)
    │
    └── gemm_obuff            (Output buffer, column synchronization)
        ├── two_fifo          (Command FIFO)
        ├── two_fifo          (Tile output transpose)
        └── fifo              (Output FIFO)
```

### 1.3 Command Set

Commands are encoded as 128-bit microcode words:

| Opcode | Name | Description |
|--------|------|-------------|
| `0xF0` | FETCH | Fetch data from HBM to dispatcher |
| `0xF1` | DISPATCH | Distribute data to tile BRAMs |
| `0xF2` | MATMUL | Execute matrix multiplication |
| `0xF3` | WAIT_DISPATCH | Wait for dispatch completion |
| `0xF4` | WAIT_MATMUL | Wait for matmul completion |
| `0xF5` | OBUF | Output buffer command (readout) |

**Command Encoding (from `gemm_pkg.sv`):**

```systemverilog
typedef struct packed {
    logic [3:0]  opcode;
    logic [11:0] reserved;
    logic [15:0] addr;          // Memory address
    logic [15:0] left_ugd_len;  // B dimension (rows of left matrix)
    logic [15:0] right_ugd_len; // C dimension (cols of right matrix)
    logic [15:0] ugd_vec_len;   // V dimension (inner dimension)
    logic [31:0] padding;
} gemm_uc_s;
```

### 1.4 Data Flow

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                              HOST (PCIe)                                    │
└─────────────────────────────────────────────────────────────────────────────┘
                                    │
                                    ▼ Commands (128-bit uCode)
┌─────────────────────────────────────────────────────────────────────────────┐
│                            gemm_control                                      │
│  - Parses uCode commands                                                    │
│  - Distributes V dimension across 16 rows                                   │
│  - First (V % 16) rows get (V/16 + 1) vectors                              │
└─────────────────────────────────────────────────────────────────────────────┘
                                    │
                    ┌───────────────┼───────────────┐
                    ▼               ▼               ▼
            ┌───────────┐   ┌───────────┐   ┌───────────┐
            │  Row 0    │   │  Row 1    │...│  Row 15   │
            │           │   │           │   │           │
            │ dispatch  │   │ dispatch  │   │ dispatch  │
            │     │     │   │     │     │   │     │     │
            │  ┌──┴──┐  │   │  ┌──┴──┐  │   │  ┌──┴──┐  │
            │  │tiles│  │   │  │tiles│  │   │  │tiles│  │
            │  │0..12│  │   │  │0..12│  │   │  │0..12│  │
            │  └──┬──┘  │   │  └──┬──┘  │   │  └──┬──┘  │
            └─────┼─────┘   └─────┼─────┘   └─────┼─────┘
                  │               │               │
                  ▼               ▼               ▼
            ┌─────────────────────────────────────────────┐
            │              gemm_col_adder [0:12]          │
            │  - Sums partial results from all 16 rows   │
            │  - fp_adder_tree for row reduction         │
            └─────────────────────────────────────────────┘
                                    │
                                    ▼
            ┌─────────────────────────────────────────────┐
            │                 gemm_obuff                   │
            │  - Synchronizes outputs from 13 columns     │
            │  - Handles partial column masking           │
            │  - Outputs to host via FIFO                 │
            └─────────────────────────────────────────────┘
                                    │
                                    ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                              HOST (PCIe)                                    │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 1.5 Key Module Descriptions

#### gemm_control.sv (Master Control)
- **Purpose**: Top-level command orchestration
- **States**: `e_idle`, `e_fetch`, `e_dispatch`, `e_matmul`, `e_wait_dispatch`, `e_wait_matmul`, `e_obuf`
- **Key Logic**: V distribution to rows (line 187):
  ```systemverilog
  // Row i gets base + 1 if i < remainder
  assign disp_cmd_lo[i].ugd_len = (disp_uc.ugd_len >> 4) + (i < disp_uc.ugd_len[3:0]);
  ```

#### gemm_row.sv (Row Processing)
- **Purpose**: Per-row data distribution and tile management
- **Key Logic**: C distribution to tiles (lines 113-117):
  ```systemverilog
  // Round-robin: tile i gets +1 if remaining > i
  for (int i = 0; i < 13; i++) begin
      tile_right_len_n[i] = tile_right_len_r[i] + (right_len_r > i);
  end
  right_len_n = right_len_r - 13;
  ```

#### gemm_dispatch.sv (Data Dispatcher)
- **Purpose**: Fetch from HBM, separate exp/mant, distribute to tiles
- **States**: `e_idle`, `e_exp`, `e_mant`, `e_wait`
- **Modes**:
  - `disp_mode == 0`: Broadcast (left matrix to all tiles)
  - `disp_mode == 1`: Distribute (right matrix round-robin)

#### gemm_tile.sv (Compute Tile)
- **Purpose**: Store matrices in BRAM, compute dot products
- **Components**:
  - `vbram_nr1w` for left matrix (mantissa + exponent)
  - `vbram_nr1w` for right matrix (mantissa + exponent)
  - `gfp_dotp` for GFP dot product computation
- **Address Generation**: `matmul_ptr` tracks B×V iteration

#### gemm_col_adder.sv (Column Adder)
- **Purpose**: Sum partial results from all 16 rows per column
- **Key Logic**: Feed zeros for inactive rows:
  ```systemverilog
  assign tree_mant_li[r] = tile_valid[r] ? tile_mant_li[r] : '0;
  assign tree_exp_li[r] = tile_valid[r] ? tile_exp_li[r] : '0;
  ```

#### gemm_obuff.sv (Output Buffer)
- **Purpose**: Synchronize results from 13 columns, output to host
- **Key Logic**: Wait for all active columns (line 105):
  ```systemverilog
  obuf_v_li = &(cadd_v_lo | ~col_en_lo);  // Valid when all active cols ready
  ```

### 1.6 Memory Layout

**Tile BRAM Organization:**
- Left BRAM: 128 addresses × (mantissa_width + exp_width)
- Right BRAM: 128 addresses × (mantissa_width + exp_width)
- Virtualized with `virt_factor_p = 4` for time-multiplexed reads

**HBM Data Format:**
- 256-bit words containing GFP8 data
- Exponent sent first, then mantissa (in `gemm_dispatch.sv`)
- 4 lines of exponents, then 128 lines of mantissa per memory block

---

## 2. Hardware-Specific Differences (AMD vs Achronix)

### 2.1 Memory Interface

| Aspect | AMD FPGA | Achronix Speedster7t |
|--------|----------|---------------------|
| **Memory Type** | HBM (High Bandwidth Memory) | GDDR6 |
| **Interface Protocol** | AXI4 (standard master port) | NAP (Network Access Point) |
| **Data Width** | 256-bit per AXI port | 256-bit per NAP |
| **Channels per Row** | 4 AXI masters per row | 1 NAP per row (via NoC) |
| **Address Width** | 32-bit | NAP-specific addressing |

**Implications:**
- AMD uses standard AXI4 protocol with arvalid/arready/rvalid/rready handshakes
- Achronix uses NAP with `nap_axi4_master` wrapper, but NoC handles arbitration
- We need `nap_initiator_wrapper` instead of direct AXI instantiation
- NAP placement constraints are critical on Achronix (row/column position)

### 2.2 BRAM Primitives

| Aspect | AMD FPGA | Achronix Speedster7t |
|--------|----------|---------------------|
| **BRAM Primitive** | RAMB18E2, RAMB36E2 | ACX_BRAM72K |
| **Wrapper Module** | `bram18_1r1w`, `bram36_1r1w` | Need custom wrapper |
| **Virtual BRAM** | `vbram_nr1w` (time-multiplexed) | Can borrow pattern |
| **Addressing** | Separate read/write clocks supported | Single-clock typical |

**Implications:**
- Cannot directly use AMD's `bram18_1r1w` and `bram36_1r1w` modules
- The `vbram_nr1w` pattern (virtualized time-multiplexed BRAM) is portable with new BRAM primitive
- ACX_BRAM72K has asymmetric port widths which AMD doesn't have

### 2.3 Compute Resources

| Aspect | AMD FPGA | Achronix Speedster7t |
|--------|----------|---------------------|
| **DSP Primitive** | DSP48E2 (27x18 multiply) | ACX_MLP72 (72-bit MAC) |
| **GFP Dot Product** | `gfp_dotp` (custom logic) | MLP-based `gfp8_nv_dot` |
| **FP Addition** | `fp_add` (custom pipelined) | `fp24_add` (similar pattern) |
| **Adder Tree** | `fp_adder_tree` | `int_adder_tree`, `fp24_adder_tree` |

**Implications:**
- AMD's `gfp_dotp` is fully custom logic, not using DSPs efficiently
- Our MLP-based design leverages ACX_MLP72's native BFP8 support
- Row reduction adder trees are portable concepts

### 2.4 Array Configuration

| Aspect | AMD GEMM | Achronix GEMM |
|--------|----------|---------------|
| **Rows** | 16 | 16 |
| **Columns** | 13 | 16 |
| **Tile Capacity** | 128 dot products | 128 NVs per tile |
| **UGD Vector Size** | 4 | 4 |

**Implications:**
- Distribution algorithms are nearly identical
- Column count difference (13 vs 16) affects edge-case handling
- Same V/C partitioning algorithm applies

---

## 3. Reusable Design Components

### 3.1 From `ip/common/` (Portable with Adaptation)

| Module | Purpose | Adaptation Required |
|--------|---------|---------------------|
| **`fifo.sv`** | General synchronous FIFO | Direct port (uses register array) |
| **`two_fifo.sv`** | 2-entry FIFO for decoupling | Direct port |
| **`one_fifo.sv`** | 1-entry bypass FIFO | Direct port |
| **`adapter.sv`** | Width conversion (PISO/SIPO) | Direct port |
| **`piso.sv`** | Parallel-In Serial-Out | Direct port |
| **`sipo.sv`** | Serial-In Parallel-Out | Direct port |
| **`fp_adder_tree.sv`** | FP reduction tree | Adapt for FP24 format |
| **`adder_tree.sv`** | Integer adder tree | Direct port |
| **`vbram_nr1w.sv`** | Virtualized multi-read BRAM | Replace BRAM primitive |

### 3.2 From `ip/gemm/` (Structural Patterns to Mimic)

| Module | Pattern to Borrow |
|--------|-------------------|
| **`gemm_control.sv`** | Master control FSM structure, V distribution logic |
| **`gemm_row.sv`** | Row-level C distribution, tile instantiation pattern |
| **`gemm_dispatch.sv`** | Exponent/mantissa separation, broadcast/distribute modes |
| **`gemm_tile.sv`** | Dual BRAM (left/right), matmul pointer generation |
| **`gemm_col_adder.sv`** | Row reduction with inactive row handling |
| **`gemm_obuff.sv`** | Output buffer synchronization across columns |

### 3.3 Key Algorithm Implementations

#### V Distribution (gemm_control.sv:187)
```systemverilog
// First (V % num_rows) rows get (V // num_rows + 1) vectors
assign disp_cmd_lo[i].ugd_len = (disp_uc.ugd_len >> gemm_row_addr_width_gp)
    + (i < disp_uc.ugd_len[0+:gemm_row_addr_width_gp] ? 1'b1 : 1'b0);
```

#### C Distribution (gemm_row.sv:113-117)
```systemverilog
// Round-robin distribution to tiles
for (int i = 0; i < gemm_num_cols_gp; i++) begin
    tile_right_len_n[i] = tile_right_len_r[i] + (right_len_r > i);
end
right_len_n = right_len_r - gemm_num_cols_gp;
```

#### Column Enable Generation (gemm_obuff.sv:78)
```systemverilog
// Active column mask based on remaining count
assign col_en_lo[c] = (c < right_len_r);
```

---

## 4. Ready-Valid Synchronization and FIFO Patterns

### 4.1 Universal Handshake Protocol

AMD GEMM uses consistent ready/valid handshake throughout:

```
Producer Interface:          Consumer Interface:
  ready_o  <── ready_i        ready_o  ──> ready_i
  v_i      ──> v_o            v_i      <── v_o
  data_i   ──> data_o         data_i   <── data_o
```

**Data Transfer Rule:**
```systemverilog
wire transfer = v_i & ready_o;  // Data moves when both asserted
```

### 4.2 FIFO Hierarchy

```
┌─────────────────────────────────────────────────────────────┐
│ one_fifo (1 entry)                                          │
│ - Zero-latency passthrough when empty                       │
│ - ready_o = ~v_r | ready_i  (accepts while being read)      │
│ - Minimal area, good for pipeline registers                 │
└─────────────────────────────────────────────────────────────┘
           │
           ▼
┌─────────────────────────────────────────────────────────────┐
│ two_fifo (2 entries)                                        │
│ - Decouples producer/consumer timing                        │
│ - ready_o = ~valid[wr_ptr]  (accepts when slot available)   │
│ - Good for crossing module boundaries                       │
└─────────────────────────────────────────────────────────────┘
           │
           ▼
┌─────────────────────────────────────────────────────────────┐
│ fifo (N entries)                                            │
│ - Deep buffering for rate matching                          │
│ - ready_o = (count < els_p)                                 │
│ - Has output register (1-cycle read latency)                │
└─────────────────────────────────────────────────────────────┘
```

### 4.3 Key Synchronization Patterns

#### Pattern 1: Multi-Source Synchronization (gemm_obuff.sv:105)
```systemverilog
// Wait for ALL active columns before outputting
obuf_v_li = &(cadd_v_lo | ~col_en_lo);  // v_lo OR not-enabled
```

#### Pattern 2: Conditional Ready (gemm_obuff.sv:109)
```systemverilog
// Only signal ready to active columns when output accepts
cadd_ready_li[c] = col_en_lo[c] ? (obuf_v_li & obuf_ready_lo) : 1'b0;
```

#### Pattern 3: Command FIFO with FSM (gemm_control.sv)
```systemverilog
// FSM reads from command FIFO
always_comb begin
    cmd_ready_li = 1'b0;  // Default: not consuming command

    case (state_r)
        e_idle: begin
            // Command available? Start processing
            if (cmd_v_lo) state_n = e_process;
        end
        e_process: begin
            // Processing done? Consume command
            if (done_condition) begin
                cmd_ready_li = 1'b1;
                state_n = e_idle;
            end
        end
    endcase
end
```

#### Pattern 4: FIFO Chain for Pipeline Stages (gemm_dispatch.sv)
```systemverilog
// Command flows through multiple FIFOs matching pipeline depth
two_fifo cmd_fifo_0 (.v_i(cmd_v_i), .v_o(stage1_v), ...);
two_fifo cmd_fifo_1 (.v_i(stage1_v), .v_o(stage2_v), ...);
```

### 4.4 Data Flow Through FIFOs

```
Host → cmd_fifo → gemm_control → disp_cmd_fifo → gemm_row
                                                      │
                 ┌────────────────────────────────────┘
                 ▼
         tile_fifo → gemm_tile → result_fifo → gemm_col_adder
                                                      │
                 ┌────────────────────────────────────┘
                 ▼
          obuf_cmd_fifo → gemm_obuff → output_fifo → Host
```

---

## 5. Coding Style Conventions

### 5.1 Signal Naming

| Suffix | Meaning | Example |
|--------|---------|---------|
| `_i` | Input port | `clk_i`, `data_i` |
| `_o` | Output port | `ready_o`, `v_o` |
| `_r` | Registered signal | `state_r`, `count_r` |
| `_n` | Next-state combinational | `state_n`, `count_n` |
| `_li` | Local input (from internal logic) | `cmd_v_li` |
| `_lo` | Local output (to internal logic) | `data_lo` |
| `_p` | Parameter | `width_p`, `els_p` |
| `_lp` | Local parameter | `addr_width_lp` |
| `_gp` | Global parameter (from package) | `gemm_num_rows_gp` |

### 5.2 FSM Pattern (Two-Process Style)

```systemverilog
// State enum with explicit encoding
typedef enum logic [1:0] {
    e_idle,
    e_process,
    e_wait
} state_e;

state_e state_r, state_n;

// Combinational next-state logic
always_comb begin
    // Default assignments (CRITICAL: prevents latches)
    state_n = state_r;
    output_signal = 1'b0;

    case (state_r)
        e_idle: begin
            if (trigger) state_n = e_process;
        end
        e_process: begin
            output_signal = 1'b1;
            if (done) state_n = e_idle;
        end
    endcase
end

// Sequential state register
always_ff @(posedge clk_i) begin
    if (reset_i) begin
        state_r <= e_idle;
    end else begin
        state_r <= state_n;
    end
end
```

### 5.3 Generate Block Naming

```systemverilog
// Use descriptive genvar names
for (genvar r = 0; r < gemm_num_rows_gp; r++) begin: rof_row
    for (genvar c = 0; c < gemm_num_cols_gp; c++) begin: rof_col
        // Module instantiation
    end
end

// Conditional generation
if (condition) begin: gen_feature_enabled
    // Feature logic
end else begin: gen_feature_disabled
    // Alternative logic
end
```

### 5.4 Module Port Declaration

```systemverilog
module example #(
    parameter width_p,                    // Required parameter
    parameter depth_p = 16,               // Optional with default

    localparam addr_width_lp = $clog2(depth_p)  // Derived parameter
) (
    input logic clk_i,
    input logic reset_i,

    // Producer interface (grouped)
    output logic ready_o,
    input logic v_i,
    input logic [width_p-1:0] data_i,

    // Consumer interface (grouped)
    input logic ready_i,
    output logic v_o,
    output logic [width_p-1:0] data_o
);
```

### 5.5 Reset Convention

```systemverilog
// Synchronous active-high reset (preferred)
always_ff @(posedge clk_i) begin
    if (reset_i) begin
        reg_r <= '0;          // Use '0 for all-zeros
    end else begin
        reg_r <= reg_n;
    end
end
```

### 5.6 Assertions and Initial Blocks

```systemverilog
// Parameter validation at elaboration
initial begin
    assert(width_p > 0) else $error("width_p must be positive");
    assert(depth_p >= 2) else $error("depth_p must be >= 2");
end

// Simulation-only checks
`ifdef SIMULATION
initial begin
    $display("[%m] Configuration: width_p=%0d, depth_p=%0d", width_p, depth_p);
end
`endif
```

### 5.7 Packed Arrays and Structs

```systemverilog
// Prefer packed arrays for port signals
input logic [gemm_num_rows_gp-1:0][data_width_gp-1:0] data_i,

// Use structs for command encoding
typedef struct packed {
    logic [3:0] opcode;
    logic [15:0] left_len;
    logic [15:0] right_len;
} cmd_s;
```

---

## 6. Key Design Patterns to Adopt

### 6.1 Command Processing Pipeline

```
┌──────────────┐    ┌──────────────┐    ┌──────────────┐
│ Host writes  │───>│ cmd_fifo     │───>│ FSM reads    │
│ to CSR       │    │ (decoupling) │    │ and executes │
└──────────────┘    └──────────────┘    └──────────────┘
```

### 6.2 Data Distribution Pattern

```
┌──────────────┐    ┌──────────────┐    ┌──────────────┐
│ Fetcher      │───>│ Dispatcher   │═══>│ Tile BRAMs   │
│ (from DDR)   │    │ (broadcast/  │    │ (parallel)   │
│              │    │  distribute) │    │              │
└──────────────┘    └──────────────┘    └──────────────┘
```

### 6.3 Result Collection Pattern

```
┌──────────────┐    ┌──────────────┐    ┌──────────────┐
│ Tile outputs │───>│ Column adder │───>│ Output buffer│
│ (per column) │    │ (row reduce) │    │ (sync cols)  │
└──────────────┘    └──────────────┘    └──────────────┘
```

---

## 7. Recommended Adoption Strategy

### Phase 1: Common Components
1. Port `fifo.sv`, `two_fifo.sv`, `one_fifo.sv` directly
2. Port `adapter.sv`, `piso.sv`, `sipo.sv` for width conversion
3. Adapt `fp_adder_tree.sv` for FP24 format

### Phase 2: Control Structure
1. Implement `gemm_control` pattern for master control
2. Adopt V distribution algorithm exactly
3. Implement per-row C distribution in dispatcher

### Phase 3: Compute Path
1. Keep existing MLP-based dot product (superior to AMD's)
2. Adopt tile structure with dual BRAM pattern
3. Implement column adder with row reduction

### Phase 4: Output Path
1. Implement output buffer synchronization pattern
2. Add column enable masking for partial results
3. Integrate with existing result FIFO infrastructure

---
