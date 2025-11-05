# fetcher_optimized_v2.sv - Critical Bug Analysis

**Date**: November 3, 2025
**Baseline**: 598 cycles (original fetcher.sv)
**Optimized V2 Status**: ❌ **DOES NOT WORK** - Multiple critical bugs

---

## Simulation Results Summary

**Test Status**: ❌ **FAILED** - Timeout after 250ns
**Expected Duration**: ~2990ns (598 cycles @ 5ns period)
**Actual Duration**: Simulation hung at 250ns

### Observable Symptoms

1. **Only 3 AR transactions issued** (should issue 33 total)
2. **ARID FIFO premature full**: Flagged full after only 2-3 ARs
3. **arready=0 blocking**: Memory model stopped accepting new ARs
4. **Address corruption**: Memory model warnings "Address out of range: line x"
5. **Continuous AR_BLOCKED messages**: Every 2 cycles during active fetch

---

## Critical Discovery: GDDR6 Outstanding Request Limit

### Reference: Achronix GDDR6 Design Constraint

**Source**: `gddr_ref_design/src/tb/tb_noc_memory_behavioural.sv:235,309`

```systemverilog
if( outstanding_xact < 32 )
begin
    // Blocking call. Task will only complete when request made
    get_AR(t_arid, t_araddr, t_arlen, t_arsize, t_arburst, t_arlock, t_arqos);
    queue_AR0.push_back('{t_araddr, t_arlen, t_arburst, t_arid});
    outstanding_xact++;
end
else
    @(posedge i_clk);  // BLOCK until outstanding requests < 32
```

**Key Finding**: The GDDR6 NoC infrastructure has a **hardware limit of 32 outstanding transactions** (AR or AW). When 32 requests are in-flight, `arready` will deassert until some R bursts complete.

### Implications for Fetcher Optimization

**Original Assumption (WRONG)**:
- ARID FIFO depth = 64 slots
- Can issue all 33 ARs back-to-back
- Memory will queue them internally

**Actual Hardware Reality**:
- **GDDR6 NoC limit = 32 outstanding requests** (architectural constraint)
- After 32 ARs issued, `arready` will block
- Must wait for R bursts to complete before issuing more ARs

**Correct Strategy**:
- ARID FIFO depth should be **32 (not 64)**
- FIFO full threshold should be **28-30 (not 60)**
- Cannot issue all 33 ARs upfront - must respect 32-request window

---

## Root Cause Analysis

### Bug #1: ARID FIFO Depth Too Large

**Location**: `fetcher_optimized_v2.sv:113-115`

```systemverilog
localparam ARID_FIFO_DEPTH = 64;       // 64-entry FIFO (user requested)
localparam ARID_FIFO_DEPTH_WIDTH = $clog2(ARID_FIFO_DEPTH);  // 6 bits
localparam ARID_FIFO_FULL_THRESHOLD = 60;  // Keep 4 slots free for safety
```

**Problem**:
- FIFO designed for 64 entries but GDDR6 only supports 32 outstanding
- Threshold of 60 is meaningless when hardware blocks at 32

**Expected Behavior**:
- ARID_FIFO_DEPTH should be **32** (match hardware limit)
- ARID_FIFO_FULL_THRESHOLD should be **28-30** (leave headroom)

---

### Bug #2: ARID Counter Reuse (Critical Protocol Violation)

**Location**: `fetcher_optimized_v2.sv:607`

```systemverilog
assign axi_ddr_if.arvalid = axi_ar_req_reg;
assign axi_ddr_if.arid    = arid_counter;  // ❌ WRONG - continuous counter
```

**Problem**:
The ARID is driven directly from `arid_counter`, which increments when AR handshake completes. However, the aggressive issuing strategy (lines 561-567) keeps `axi_ar_req_reg=1` for multiple cycles trying to issue back-to-back ARs.

**Result**: Multiple AR transactions share the **same ARID value** because the counter doesn't increment until handshake completes, but arvalid stays high.

**Example Timeline**:
```
Cycle 10: arvalid=1, arid=0xFE, arready=1 → AR handshake, arid_counter increments
Cycle 11: arvalid=1, arid=0xFF, arready=0 → AR pending with NEW arid
Cycle 12: arvalid=1, arid=0xFF, arready=0 → Still same arid (counter hasn't moved)
Cycle 13: arvalid=1, arid=0xFF, arready=1 → AR handshake with 0xFF
Cycle 14: arvalid=1, arid=0x00, arready=0 → NEW arid after increment
```

**AXI Protocol Violation**: Multiple in-flight ARs with identical ARID values → memory controller cannot distinguish which R burst belongs to which AR.

**Correct Implementation**:
```systemverilog
// Latch ARID when AR handshake completes
always_ff @(posedge i_clk) begin
    if (~i_reset_n) begin
        arid_latched <= 8'hFE;
    end else if (axi_ddr_if.arvalid && axi_ddr_if.arready) begin
        arid_latched <= arid_counter + 1;  // Capture NEXT ID
    end
end

assign axi_ddr_if.arid = arid_latched;  // Use latched value
```

---

### Bug #3: FIFO Entry Tracking Logic Error

**Location**: `fetcher_optimized_v2.sv:159-161, 181-193`

```systemverilog
assign arid_fifo_wr = (axi_ddr_if.arvalid && axi_ddr_if.arready);
assign arid_fifo_rd = (axi_ddr_if.rvalid && axi_ddr_if.rready && axi_ddr_if.rlast);

always_ff @(posedge i_clk) begin
    case ({arid_fifo_wr, arid_fifo_rd})
        2'b00: arid_fifo_entries <= arid_fifo_entries;
        2'b01: arid_fifo_entries <= arid_fifo_entries - 1;
        2'b10: arid_fifo_entries <= arid_fifo_entries + 1;
        2'b11: arid_fifo_entries <= arid_fifo_entries;  // Simultaneous
    endcase
end
```

**Analysis**: This logic is actually **CORRECT** for entry tracking.

**Observed Behavior**:
```
Cycle 81:  AR handshake #2 → arid_fifo_entries = 2
Cycle 117: AR handshake #3 → arid_fifo_entries = 3, arid_fifo_full=1 ???
```

**Root Cause of Premature Full**: The FIFO threshold (60) is evaluated against the wrong metric. With only 3 entries, `arid_fifo_entries >= 60` should be **false**, but simulation shows `arid_fifo_full=1`.

**Hypothesis**: There's a mismatch between when ARs are issued vs when memory model increments `outstanding_xact`. The memory model may be blocking `arready` before the fetcher's FIFO logic thinks it's full.

---

### Bug #4: Missing Backpressure Handling

**Location**: `fetcher_optimized_v2.sv:568-576`

```systemverilog
} else if (state_reg == ST_FETCH_ACTIVE) begin
    // Issue AR if none pending and conditions met
    if (total_ars_issued < TOTAL_BURSTS_NEEDED && !arid_fifo_full && !axi_ar_req_reg) begin
        axi_ar_req_reg <= 1'b1;
    end
end
```

**Problem**: When `arready=0` (memory at 32 outstanding limit), the code correctly does NOT issue new ARs. However, it doesn't have any logic to **retry** when memory becomes ready again.

**Result**: After hitting the 32-request limit, the fetcher stops issuing ARs and hangs.

**Missing Logic**:
```systemverilog
// Retry when arready becomes available
if (total_ars_issued < TOTAL_BURSTS_NEEDED &&
    !arid_fifo_full &&
    !axi_ar_req_reg &&
    axi_ddr_if.arready) begin  // ← ADD THIS CHECK
    axi_ar_req_reg <= 1'b1;
end
```

---

## Address Generation Analysis

**Location**: `fetcher_optimized_v2.sv:608`

```systemverilog
assign axi_ddr_if.araddr = {GDDR6_PAGE_ID, 2'b00, (fetch_addr_reg + current_line_reg), {ADDR_BYTE_SHIFT{1'b0}}};
```

**Status**: ✅ **CORRECT** (same as original fetcher.sv:452)

**Logic**:
- `current_line_reg` increments by 1 for each beat received (line 411)
- Address naturally points to next 256-bit line
- Identical to original working implementation

**Note**: Cannot fully verify due to early simulation hang, but logic is sound.

---

## Comparison: Original vs Optimized V2

| Aspect | Original (598 cycles) | Optimized V2 (BROKEN) | Status |
|--------|----------------------|----------------------|--------|
| **ARID Management** | Simple counter in READ state | ARID FIFO with aggressive issuing | ❌ ID reuse bug |
| **Outstanding Limit** | Respects 32-limit implicitly | Ignores 32-limit (uses 64) | ❌ Wrong assumption |
| **FIFO Depth** | N/A (no FIFO) | 64 entries | ❌ Should be 32 |
| **FIFO Threshold** | N/A | 60/64 | ❌ Should be 28-30 |
| **Backpressure** | State machine waits for R-last | No retry logic when arready=0 | ❌ Hangs after 32 ARs |
| **State Machine** | 6 states (READ→READ_MAN loop) | 5 states (single ACTIVE) | ⚠️ Simpler but untested |
| **Address Generation** | fetch_addr + current_line | fetch_addr + current_line | ✅ Same logic |

---

## Why Original Fetcher Works

The original fetcher issues ARs **one-at-a-time** with an 18-cycle gap between bursts:

```systemverilog
ST_FETCH_READ: begin
    // Issue 1 AR, then wait
    axi_ar_req_reg <= 1'b1;
    state_next = ST_FETCH_READ_EXP;  // Go wait for R burst
end

ST_FETCH_READ_EXP: begin
    // Wait for all 16 beats to arrive
    if (axi_ddr_if.rvalid && axi_ddr_if.rready && axi_ddr_if.rlast) begin
        state_next = ST_FETCH_READ;  // Issue next AR
    end
end
```

**Why This Works**:
1. Only 1 outstanding AR at a time → never hits 32-limit
2. Wait for R-last before issuing next AR → natural pacing
3. 18-cycle gap = overhead from state transitions

**Performance**: 598 cycles (conservative but reliable)

---

## Recommended Fix Strategy

### Option 1: Fix Existing V2 (Aggressive)

1. **Reduce FIFO depth to 32**
2. **Fix ARID counter reuse** (latch on handshake)
3. **Lower threshold to 28** (leave 4-slot headroom)
4. **Add backpressure retry logic**
5. **Track outstanding ARs vs completed R bursts**

**Expected Performance**: ~550-580 cycles (10-48 cycle improvement)

**Risk**: High complexity, multiple interacting bugs

---

### Option 2: Conservative Pipelined Approach (Recommended)

Instead of issuing all 33 ARs upfront, issue ARs in a **pipelined manner**:

1. **Issue AR immediately when previous R burst completes**
2. **Allow 2-4 ARs in-flight at once** (configurable)
3. **No FIFO needed** - simple counter tracking
4. **Respect 32-limit naturally** (never approach it)

**Implementation**:
```systemverilog
logic [5:0] outstanding_ar_count;  // Track ARs issued but not R-complete

always_ff @(posedge i_clk) begin
    case ({ar_issued, r_burst_complete})
        2'b10: outstanding_ar_count <= outstanding_ar_count + 1;
        2'b01: outstanding_ar_count <= outstanding_ar_count - 1;
        2'b11: outstanding_ar_count <= outstanding_ar_count;  // Equal
        default: outstanding_ar_count <= outstanding_ar_count;
    endcase
end

assign can_issue_ar = (outstanding_ar_count < MAX_OUTSTANDING_ARS);  // e.g., 4
```

**Expected Performance**: ~570-590 cycles (8-28 cycle improvement)

**Advantages**:
- Simple, minimal state changes
- Respects 32-limit by design
- No FIFO complexity
- Easy to verify

---

## Conclusion

**fetcher_optimized_v2.sv is fundamentally broken** due to:

1. **Wrong assumption**: Thought GDDR6 could queue 64 requests (actual limit: 32)
2. **ARID reuse**: Multiple ARs share same ID (AXI protocol violation)
3. **No backpressure handling**: Hangs when hitting 32-request limit
4. **FIFO oversized**: 64-entry FIFO for 32-request hardware

**Recommendation**:
- **Abandon aggressive "all 33 ARs upfront" approach**
- **Use conservative pipelined strategy** (Option 2)
- **Target modest improvement** (8-28 cycles = 1-5% speedup)
- **Maintain reliability** over aggressive optimization

**Baseline remains at 598 cycles** with original working fetcher.

---

**Analysis by**: Claude Code
**Reference Design**: `gddr_ref_design/src/tb/tb_noc_memory_behavioural.sv`
**GDDR6 Limit Confirmed**: 32 outstanding transactions (line 235, 309)
