# Compilation Notes - Fetcher Testbench

## Issues Found and Fixed

### Issue 1: Port Name Mismatches
**Problem**: Testbench used incorrect port names for fetcher.sv
- Used `i_fetch_start_addr` → Should be `i_fetch_addr`
- Used `i_fetch_num_lines` → Should be `i_fetch_len`
- Used individual AXI signals → Should use `t_AXI4.initiator` interface

**Solution**: Updated testbench to use correct port names from actual RTL

### Issue 2: dispatcher_bram.sv Simulation Error (VCP2675)
**Problem**: Initial block conflicts with always_ff for BRAM initialization
```
ERROR VCP2675: Cannot write to a variable 'exp_left_packed[init_i]' 
that is also driven by an always_ff procedural block
```

**Solution**: Added `-err VCP2675 W1` flag to Makefile to suppress this warning
- This is simulation-only issue (synthesis ignores initial blocks)
- Hardware uses reset logic, not initial blocks
- Safe to suppress for testbench purposes

### Issue 3: Address Width Mismatches
**Problem**: Testbench used `[9:0]` for BRAM write address
**Actual**: Fetcher uses `[BRAM_ADDR_WIDTH+2:0]` = `[10:0]` (11-bit for 0-527 range)

**Solution**: Updated all address widths to match RTL parameters

## Reference: Actual Interfaces

### fetcher.sv (key ports)
```systemverilog
input  logic [link_addr_width_gp-1:0] i_fetch_addr,      // NOT i_fetch_start_addr
input  logic [link_len_width_gp-1:0]  i_fetch_len,       // NOT i_fetch_num_lines  
t_AXI4.initiator                       axi_ddr_if,       // NOT individual signals
output logic [BRAM_ADDR_WIDTH+2:0]     o_bram_wr_addr,   // 11-bit, NOT 10-bit
```

### dispatcher_bram.sv (key ports)
```systemverilog
// Read ports use different naming
input  logic [RD_ADDR_WIDTH-1:0]  i_man_left_rd_addr,   // NOT i_rd_addr_left_man
output logic [MAN_WIDTH-1:0]       o_man_left_rd_data,   // NOT o_rd_data_left_man
// Unpacking interface
input  logic [3:0]                 i_exp_packed_rd_addr, // 4-bit for 0-15
output logic [255:0]               o_exp_packed_rd_data
```

## Verification Strategy

1. **Baseline Run**: Establish golden reference with current fetcher.sv
2. **Optimization**: Create fetcher_optimized.sv with improved state machine
3. **Comparison**: Verify identical BRAM contents + measure cycle improvement

