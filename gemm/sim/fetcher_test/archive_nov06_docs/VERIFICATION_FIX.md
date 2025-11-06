# Verification Issue - BRAM Read Timing

## Problem
```
# KERNEL: Error: LEFT man[0]: mismatch
# KERNEL: Error: RIGHT man[0]: mismatch
```

Only mantissa[0] fails, not exp[0] or other indices.

## Root Cause

BRAM reads are registered (1-cycle latency):

```systemverilog
// dispatcher_bram.sv
always_ff @(posedge i_clk) begin
    if (i_man_left_rd_en) begin
        man_left_rd_data_reg <= man_left[i_man_left_rd_addr];
    end
end
assign o_man_left_rd_data = man_left_rd_data_reg;
```

Current verification loop:
```systemverilog
for (i = 0; i < 512; i++) begin
    dispatcher_man_left_rd_addr = i[8:0];
    dispatcher_man_left_rd_en = 1'b1;
    @(posedge clk);  // Wait 1 cycle
    golden_left_man[i] = dispatcher_bram_man_left_rd_data;  // TOO EARLY!
end
```

Timeline:
- Cycle 0: addr=0, en=1
- Cycle 1: BRAM reads man[0] internally
- Cycle 2: man[0] appears on output ← We read at cycle 1 instead!

## Solution

Add initial dummy read cycle:

```systemverilog
for (i = 0; i < 512; i++) begin
    dispatcher_man_left_rd_addr = i[8:0];
    dispatcher_man_left_rd_en = 1'b1;
    @(posedge clk);
    @(posedge clk);  // ADD: Extra cycle for registered output
    golden_left_man[i] = dispatcher_bram_man_left_rd_data;
end
```

OR use pipelined reads (better performance):

```systemverilog
// Issue first read
dispatcher_man_left_rd_addr = 0;
dispatcher_man_left_rd_en = 1'b1;
@(posedge clk);

for (i = 0; i < 512; i++) begin
    // Issue next read while capturing previous
    if (i < 511) begin
        dispatcher_man_left_rd_addr = (i+1)[8:0];
        dispatcher_man_left_rd_en = 1'b1;
    end
    @(posedge clk);
    golden_left_man[i] = dispatcher_bram_man_left_rd_data;
end
```

## Why exp[0] works but man[0] fails?

Need to check exp read logic - it might be combinational or have different timing.
