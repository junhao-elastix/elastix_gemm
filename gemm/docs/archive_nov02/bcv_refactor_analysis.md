# BCV Controller Refactoring Analysis

## Current Inefficiencies

### 1. BRAM Read Latency Misconception
**Problem**: Code assumes 2-cycle BRAM latency, but actual latency is **1 cycle**

**Evidence from tile_bram.sv**:
```systemverilog
// BRAM read logic - REGISTERED OUTPUT
always_ff @(posedge i_clk) begin
    if (i_man_left_rd_en) begin
        man_left_rd_data_reg <= man_left[i_man_left_rd_addr];  // 1-cycle latency
    end
end
```

**Current behavior** (WASTEFUL):
```
Cycle 0: Present address, rd_en=1
Cycle 1: Wait (unnecessary!)
Cycle 2: Capture data
```

**Optimal behavior**:
```
Cycle 0: Present address, rd_en=1
Cycle 1: Capture data (ready!)
```

### 2. Fill Buffer Timing

**Current**: 9 cycles for 4 groups
- Group 0: Cycles 0-2 (3 cycles)
- Group 1: Cycles 3-4 (2 cycles) 
- Group 2: Cycles 5-6 (2 cycles)
- Group 3: Cycles 7-8 (2 cycles)

**Optimal**: 5 cycles for 4 groups
- Group 0: Cycles 0-1 (2 cycles: issue + capture)
- Group 1: Cycles 1-2 (2 cycles: issue + capture, overlaps!)
- Group 2: Cycles 2-3 (2 cycles: issue + capture, overlaps!)
- Group 3: Cycles 3-4 (2 cycles: issue + capture, overlaps!)
- Cycle 4: Transition

**Savings**: 4 cycles per V iteration!

### 3. Code Structure Issues

**Problems**:
1. Massive if-else chain for fill_cycle (lines 269-334, 401-467)
2. Repetitive address calculation per group
3. Unclear datapath (exp + man handled separately but identically)
4. Excessive debug prints in critical path

**Solution**: Clean FSM with:
- Unified address generation
- Pipelined read/capture
- Clear separation of address/data stages

## Proposed Refactoring

### Architecture
```
State: FILL_BUFFER
├─ Cycle 0: Issue addr[0], rd_en=1
├─ Cycle 1: Issue addr[1], rd_en=1 | Capture data[0]
├─ Cycle 2: Issue addr[2], rd_en=1 | Capture data[1]
├─ Cycle 3: Issue addr[3], rd_en=1 | Capture data[2]
├─ Cycle 4: Capture data[3] → Transition to COMPUTE_NV
```

### Benefits
1. **Performance**: 5 cycles vs 9 cycles (44% faster fill!)
2. **Clarity**: Simple counter-based addressing
3. **Correctness**: Matches actual BRAM latency
4. **Maintainability**: 50% less code, cleaner logic

### Total System Impact
**Per V iteration**: 13 cycles → 9 cycles
- Fill: 9→5 cycles
- Compute: 3 cycles (unchanged)
- Accum: 1 cycle (unchanged)

**For V=128**: 1664 cycles → 1152 cycles (**31% faster!**)



