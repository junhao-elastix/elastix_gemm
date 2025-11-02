# Circular Buffer Reset Simplification Proposal

**Date**: November 1, 2025
**Issue**: Redundant reset signals for circular buffer
**Proposal**: Remove `i_write_top_reset`, simplify to single reset path

---

## Current Implementation (Redundant)

### Two Reset Paths to result_fifo_to_simple_bram

**Path 1: Async Reset (`i_reset_n`)**
```systemverilog
// elastix_gemm_top.sv line 568
assign engine_reset_n = nap_rstn & ~engine_soft_reset;

// Line 661 - Module instantiation
result_fifo_to_simple_bram i_result_adapter (
    .i_reset_n(engine_reset_n),  // ✅ Resets wr_ptr when soft reset
    ...
);

// result_fifo_to_simple_bram.sv lines 96-97
always_ff @(posedge i_clk or negedge i_reset_n) begin
    if (!i_reset_n) begin
        wr_ptr <= 13'd0;  // ✅ Reset on soft reset
    end
```

**Path 2: Sync Reset (`i_write_top_reset`)**
```systemverilog
// elastix_gemm_top.sv lines 709-710
assign result_write_top_reset = engine_soft_reset ||  // ⚠️ REDUNDANT!
                                (write_strobes[ENGINE_WRITE_TOP] && 
                                 (user_regs_write[ENGINE_WRITE_TOP] == 32'h0));

// Line 677 - Module instantiation
result_fifo_to_simple_bram i_result_adapter (
    .i_write_top_reset(result_write_top_reset),  // ⚠️ REDUNDANT for soft reset
    ...
);

// result_fifo_to_simple_bram.sv lines 98-99
always_ff @(posedge i_clk or negedge i_reset_n) begin
    ...
    end else if (i_write_top_reset) begin
        wr_ptr <= 13'd0;  // ⚠️ REDUNDANT for soft reset
    end
```

### Result: Double Reset on Soft Reset!

When software does `soft_reset()`:
1. Control[1] = 1 → `engine_soft_reset = 1`
2. `engine_reset_n = 0` → **wr_ptr resets (async)**
3. `result_write_top_reset = 1` → **wr_ptr resets (sync)** ← Redundant!

---

## Proposed Simplification

### Option A: Remove `i_write_top_reset` Completely (RECOMMENDED)

**Rationale:**
- Soft reset already resets circular buffer via `i_reset_n`
- No real use case for resetting buffer independently of engine
- Simpler hardware with single reset path
- Less confusing for software developers

**Changes Required:**

#### 1. Remove port from `result_fifo_to_simple_bram.sv`
```systemverilog
module result_fifo_to_simple_bram (
    input  logic        i_clk,
    input  logic        i_reset_n,
    ...
    // REMOVED: input  logic        i_write_top_reset,
    output logic        o_almost_full
);
```

#### 2. Simplify wr_ptr reset logic
```systemverilog
always_ff @(posedge i_clk or negedge i_reset_n) begin
    if (!i_reset_n) begin
        wr_ptr <= 13'd0;
    // REMOVED: end else if (i_write_top_reset) begin
    // REMOVED:     wr_ptr <= 13'd0;
    end else if (fifo_rd_valid) begin
        ...
    end
end

// Also remove from first_four_count logic (line 173)
if (i_write_top_reset) begin  // ← REMOVE THIS BLOCK
    first_four_count <= 13'd0;
end
```

#### 3. Remove signal from top-level
```systemverilog
// elastix_gemm_top.sv - REMOVE these lines:
// logic result_write_top_reset;
// assign result_write_top_reset = engine_soft_reset || ...;

// Simplify rd_ptr reset
always_ff @(posedge i_reg_clk or negedge nap_rstn) begin
    if (!nap_rstn) begin
        result_rd_ptr_reg <= 13'd0;
    end else if (engine_soft_reset) begin  // ✅ Just use soft reset directly
        result_rd_ptr_reg <= 13'd0;
    end else if (write_strobes[REG_RD_PTR]) begin
        result_rd_ptr_reg <= user_regs_write[REG_RD_PTR][12:0];
    end
end
```

#### 4. Remove register 0x22C write functionality (or make it read-only)
```systemverilog
// Register 0x22C (ENGINE_WRITE_TOP) becomes read-only
assign user_regs_read[ENGINE_WRITE_TOP] = {19'h0, result_wr_ptr};  // RO
// No write handler needed
```

---

### Option B: Keep for Independent Buffer Clear (Current)

**Rationale:**
- Allows clearing buffer without resetting engine FSMs
- Useful for debugging or mid-operation buffer management
- More flexible but more complex

**Use Case Example:**
```cpp
// Clear buffer without resetting engine state
gemm_device.mmio_write32(0, 0x22C, 0x0);  // Clear buffer
// Engine FSMs (MC, DC, CE) remain in their current states
```

**Downside:** Adds complexity and potential for confusion

---

## Recommendation

**✅ REMOVE `i_write_top_reset` (Option A)**

**Reasoning:**
1. **Simpler is Better**: Single reset path is easier to understand and debug
2. **No Real Use Case**: Always want to reset engine AND buffer together
3. **Prevents Confusion**: One reset mechanism, not two
4. **Software Pattern**: All existing code does `soft_reset()` which resets everything
5. **Hardware Efficiency**: Fewer gates, simpler timing

**Migration Path:**
1. Remove `i_write_top_reset` port from `result_fifo_to_simple_bram.sv`
2. Remove `result_write_top_reset` signal from `elastix_gemm_top.sv`
3. Make register 0x22C read-only (just exposes `wr_ptr`)
4. rd_ptr resets directly from `engine_soft_reset`
5. Update software to only use `soft_reset()` (already the case!)

---

## Impact Analysis

### Hardware Changes
- **Files Modified**: 2 (result_fifo_to_simple_bram.sv, elastix_gemm_top.sv)
- **Lines Changed**: ~15 lines
- **Complexity**: Reduced (1 reset path instead of 2)

### Software Changes
- **Files Modified**: None! (Software already uses soft_reset())
- **Breaking Changes**: None! (Register 0x22C still readable)

### Testing Changes
- **Existing Tests**: No changes needed
- **New Tests**: Verify soft reset clears buffer (already tested)

---

## Implementation

Would you like me to implement Option A (remove `i_write_top_reset`)?

This will:
1. Simplify RTL (remove redundant reset path)
2. Make register 0x22C read-only (wr_ptr exposure)
3. Keep existing software working without changes
4. Reduce confusion about when to use which reset

---

**Recommendation**: ✅ **REMOVE** - Simplify to single reset path
**Risk**: Low - Software already uses soft_reset() exclusively
**Benefit**: Cleaner, simpler, less confusing hardware



