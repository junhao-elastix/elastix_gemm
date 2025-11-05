# Interface Mismatches - Fetcher Testbench vs Actual RTL

## Fetcher Module (`fetcher.sv`)

| Testbench Used (WRONG) | Actual RTL (CORRECT) | Type | Notes |
|------------------------|----------------------|------|-------|
| `i_fetch_start_addr` | `i_fetch_addr` | Input [25:0] | Command address input |
| `i_fetch_num_lines` | `i_fetch_len` | Input [15:0] | Number of lines to fetch |
| `o_nap_ar_valid` | `axi_ddr_if.arvalid` | AXI AR | AXI uses interface, not individual signals |
| `i_nap_ar_ready` | `axi_ddr_if.arready` | AXI AR | Part of t_AXI4.initiator interface |
| `o_nap_ar_addr` | `axi_ddr_if.araddr` | AXI AR | Part of t_AXI4.initiator interface |
| `o_nap_ar_id` | `axi_ddr_if.arid` | AXI AR | Part of t_AXI4.initiator interface |
| `o_nap_ar_len` | `axi_ddr_if.arlen` | AXI AR | Part of t_AXI4.initiator interface |
| `o_nap_ar_size` | `axi_ddr_if.arsize` | AXI AR | Part of t_AXI4.initiator interface |
| `o_nap_ar_burst` | `axi_ddr_if.arburst` | AXI AR | Part of t_AXI4.initiator interface |
| `i_nap_r_valid` | `axi_ddr_if.rvalid` | AXI R | Part of t_AXI4.initiator interface |
| `o_nap_r_ready` | `axi_ddr_if.rready` | AXI R | Part of t_AXI4.initiator interface |
| `i_nap_r_data` | `axi_ddr_if.rdata` | AXI R | Part of t_AXI4.initiator interface |
| `i_nap_r_last` | `axi_ddr_if.rlast` | AXI R | Part of t_AXI4.initiator interface |
| `i_nap_r_id` | `axi_ddr_if.rid` | AXI R | Part of t_AXI4.initiator interface |
| `i_nap_r_resp` | `axi_ddr_if.rresp` | AXI R | Part of t_AXI4.initiator interface |
| `o_wr_data` | `o_bram_wr_data` | Output [255:0] | BRAM write data |
| `o_wr_addr` | `o_bram_wr_addr` | Output [10:0] | BRAM write address (11-bit for 0-527) |
| `o_wr_en` | `o_bram_wr_en` | Output | BRAM write enable |
| `o_wr_target` | `o_bram_wr_target` | Output | BRAM target (0=left, 1=right) |

### Critical Fix: AXI Interface

**WRONG (in testbench):**
```systemverilog
// Individual AXI signals
output logic        o_nap_ar_valid,
input  logic        i_nap_ar_ready,
output logic [41:0] o_nap_ar_addr,
// ... etc
```

**CORRECT (actual RTL):**
```systemverilog
// AXI4 interface
t_AXI4.initiator axi_ddr_if
```

## Dispatcher BRAM Module (`dispatcher_bram.sv`)

| Testbench Used (WRONG) | Actual RTL (CORRECT) | Type | Notes |
|------------------------|----------------------|------|-------|
| `i_rd_addr_left_exp` | `i_exp_left_rd_addr` | Input [8:0] | Left exp read address |
| `i_rd_addr_left_man` | `i_man_left_rd_addr` | Input [8:0] | Left mantissa read address |
| `i_rd_addr_right_exp` | `i_exp_right_rd_addr` | Input [8:0] | Right exp read address |
| `i_rd_addr_right_man` | `i_man_right_rd_addr` | Input [8:0] | Right mantissa read address |
| `o_rd_data_left_exp` | `o_exp_left_rd_data` | Output [7:0] | Left exp read data |
| `o_rd_data_left_man` | `o_man_left_rd_data` | Output [255:0] | Left mantissa read data |
| `o_rd_data_right_exp` | `o_exp_right_rd_data` | Output [7:0] | Right exp read data |
| `o_rd_data_right_man` | `o_man_right_rd_data` | Output [255:0] | Right mantissa read data |
| Parameter: `DATA_WIDTH` | No such parameter | - | dispatcher_bram uses `MAN_WIDTH` instead |

### Naming Convention Pattern

**Actual RTL follows this pattern:**
- **Mantissa**: `i_man_{left|right}_rd_{addr|en}`, `o_man_{left|right}_rd_data`
- **Exponent**: `i_exp_{left|right}_rd_{addr|en}`, `o_exp_{left|right}_rd_data`

**Format**: `{direction}_{type}_{side}_rd_{signal}`
- direction: `i` (input) or `o` (output)
- type: `man` (mantissa) or `exp` (exponent)
- side: `left` or `right`
- signal: `addr`, `en`, or `data`

## Dispatcher BRAM Missing Read Enable Signals

The testbench is **missing** these required signals:

| Signal | Type | Purpose |
|--------|------|---------|
| `i_man_left_rd_en` | Input | Left mantissa read enable |
| `i_exp_left_rd_en` | Input | Left exponent read enable |
| `i_man_right_rd_en` | Input | Right mantissa read enable |
| `i_exp_right_rd_en` | Input | Right exponent read enable |

## Summary of Required Changes

### 1. Fetcher Instantiation
```systemverilog
// WRONG:
fetcher #(...) u_fetcher (
    .i_fetch_start_addr(fetch_start_addr),   // WRONG NAME
    .i_fetch_num_lines(fetch_num_lines),     // WRONG NAME
    .o_nap_ar_valid(axi_nap.arvalid),        // WRONG - individual signals
    // ...
);

// CORRECT:
fetcher #(...) u_fetcher (
    .i_fetch_addr(fetch_addr),               // CORRECT
    .i_fetch_len(fetch_len),                 // CORRECT
    .axi_ddr_if(axi_nap.initiator),         // CORRECT - use interface
    // ...
);
```

### 2. Dispatcher BRAM Instantiation
```systemverilog
// WRONG:
dispatcher_bram #(
    .DATA_WIDTH(256)                         // WRONG - no such parameter
) u_dispatcher_bram (
    .i_rd_addr_left_exp(bram_rd_addr_left_exp),   // WRONG NAME
    .o_rd_data_left_exp(bram_rd_data_left_exp),   // WRONG NAME
    // ...
);

// CORRECT:
dispatcher_bram #(
    .MAN_WIDTH(256)                          // CORRECT parameter name
) u_dispatcher_bram (
    .i_exp_left_rd_addr(bram_rd_addr_left_exp),   // CORRECT
    .i_exp_left_rd_en(bram_rd_en_left_exp),       // ADDED - was missing
    .o_exp_left_rd_data(bram_rd_data_left_exp),   // CORRECT
    // ...
);
```

### 3. Signal Declarations
```systemverilog
// ADD these missing signals:
logic         bram_rd_en_left_exp;
logic         bram_rd_en_left_man;
logic         bram_rd_en_right_exp;
logic         bram_rd_en_right_man;

// RENAME these:
logic [25:0]  fetch_addr;          // was: fetch_start_addr
logic [15:0]  fetch_len;           // was: fetch_num_lines
```

## Complete Correct Port Mapping

### Fetcher (from actual RTL line 32-83):
```systemverilog
module fetcher #(...) (
    input  logic                         i_clk,
    input  logic                         i_reset_n,
    
    // Master Control Interface
    input  logic                         i_fetch_en,
    input  logic [link_addr_width_gp-1:0] i_fetch_addr,      // ← CORRECT NAME
    input  logic [link_len_width_gp-1:0]  i_fetch_len,       // ← CORRECT NAME
    input  logic                         i_fetch_target,
    output logic                         o_fetch_done,
    
    // BRAM Write Interface
    output logic [MAN_WIDTH-1:0]         o_bram_wr_data,     // ← CORRECT NAME
    output logic [BRAM_ADDR_WIDTH+2:0]   o_bram_wr_addr,     // ← CORRECT NAME (11-bit)
    output logic                         o_bram_wr_en,       // ← CORRECT NAME
    output logic                         o_bram_wr_target,   // ← CORRECT NAME
    
    // Exponent aligned write
    output logic [TILE_ADDR_WIDTH-1:0]   o_exp_left_wr_addr,
    output logic                         o_exp_left_wr_en,
    output logic [EXP_WIDTH-1:0]         o_exp_left_wr_data,
    output logic [TILE_ADDR_WIDTH-1:0]   o_exp_right_wr_addr,
    output logic                         o_exp_right_wr_en,
    output logic [EXP_WIDTH-1:0]         o_exp_right_wr_data,
    
    // Unpacking read interface
    output logic [3:0]                   o_exp_packed_rd_addr,
    output logic                         o_exp_packed_rd_target,
    input  logic [MAN_WIDTH-1:0]         i_exp_packed_rd_data,
    
    // AXI Interface
    t_AXI4.initiator                     axi_ddr_if,         // ← CORRECT (interface, not signals)
    
    // Debug
    output logic [3:0]                   o_fetcher_state,
    output logic [10:0]                  o_wr_addr,
    output logic                         o_wr_en
);
```

### Dispatcher BRAM (from actual RTL line 33-93):
```systemverilog
module dispatcher_bram #(...) (
    input  logic                            i_clk,
    input  logic                            i_reset_n,
    
    // Write ports
    input  logic [MAN_WIDTH-1:0]            i_wr_data,
    input  logic [WR_ADDR_WIDTH-1:0]        i_wr_addr,
    input  logic                            i_wr_en,
    input  logic                            i_wr_target,
    
    // Exp aligned write
    input  logic [RD_ADDR_WIDTH-1:0]        i_exp_left_wr_addr,
    input  logic                            i_exp_left_wr_en,
    input  logic [EXP_WIDTH-1:0]            i_exp_left_wr_data,
    input  logic [RD_ADDR_WIDTH-1:0]        i_exp_right_wr_addr,
    input  logic                            i_exp_right_wr_en,
    input  logic [EXP_WIDTH-1:0]            i_exp_right_wr_data,
    
    // Read ports
    input  logic [RD_ADDR_WIDTH-1:0]        i_man_left_rd_addr,    // ← CORRECT NAME
    input  logic                            i_man_left_rd_en,      // ← WAS MISSING
    output logic [MAN_WIDTH-1:0]            o_man_left_rd_data,    // ← CORRECT NAME
    
    input  logic [RD_ADDR_WIDTH-1:0]        i_exp_left_rd_addr,    // ← CORRECT NAME
    input  logic                            i_exp_left_rd_en,      // ← WAS MISSING
    output logic [EXP_WIDTH-1:0]            o_exp_left_rd_data,    // ← CORRECT NAME
    
    input  logic [RD_ADDR_WIDTH-1:0]        i_man_right_rd_addr,   // ← CORRECT NAME
    input  logic                            i_man_right_rd_en,     // ← WAS MISSING
    output logic [MAN_WIDTH-1:0]            o_man_right_rd_data,   // ← CORRECT NAME
    
    input  logic [RD_ADDR_WIDTH-1:0]        i_exp_right_rd_addr,   // ← CORRECT NAME
    input  logic                            i_exp_right_rd_en,     // ← WAS MISSING
    output logic [EXP_WIDTH-1:0]            o_exp_right_rd_data,   // ← CORRECT NAME
    
    // Unpacking interface
    input  logic [EXP_PACKED_ADDR_WIDTH-1:0] i_exp_packed_rd_addr,
    input  logic                              i_exp_packed_rd_target,
    output logic [MAN_WIDTH-1:0]              o_exp_packed_rd_data
);
```
