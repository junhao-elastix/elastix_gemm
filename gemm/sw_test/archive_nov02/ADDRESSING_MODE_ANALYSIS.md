# DMA Bridge Addressing Mode Analysis

**Date**: October 31, 2025
**Issue**: Mismatch between circular buffer addressing (2-byte FP16 granularity) and DMA bridge (32-byte line alignment)
**Options**: Keep line padding vs. implement byte-level addressing

---

## 1. Current Architecture (Baseline)

### 1.1 Circular Buffer Pointer System
```
ptr[12:0]        = FP16 index (0-8191)
Byte Address     = {ptr[12:0], 1'b0} = ptr * 2  (2-byte aligned)
BRAM Line Addr   = ptr[12:4]                    (divide by 16)
Position in Line = ptr[3:0]                     (mod 16)
```

### 1.2 DMA Bridge Current Implementation
```systemverilog
// dma_bram_bridge.sv lines 239, 243
.wraddr ({actual_wr_addr, 5'h00}),  // Forces 32-byte alignment
.rdaddr ({actual_rd_addr, 5'h00}),  // Forces 32-byte alignment
```

**Problem**: Software must provide line-aligned addresses (multiples of 32), but circular buffer uses FP16 indices.

### 1.3 Software Complexity (Current)
```cpp
// Reading results from circular buffer
uint32_t rd_ptr = read_reg(REG_RD_PTR);          // FP16 index 0-8191
uint32_t result_count = 17;                       // Example: 17 FP16 results

// Step 1: Convert FP16 index → BRAM line address
uint32_t start_line = rd_ptr >> 4;                // Divide by 16
uint32_t num_lines = (rd_ptr + result_count + 15) >> 4) - start_line;

// Step 2: Calculate byte address (32-byte aligned)
uint32_t byte_addr = start_line * 32;

// Step 3: DMA read (always full 32-byte lines)
dma_read(BRAM_BASE + byte_addr, num_lines * 32, buffer);

// Step 4: Extract FP16 values from packed lines
uint32_t offset_in_first_line = (rd_ptr & 0xF) * 2;  // Byte offset
for (int i = 0; i < result_count; i++) {
    uint32_t byte_idx = offset_in_first_line + i * 2;
    uint32_t line_idx = byte_idx / 32;
    uint32_t offset = byte_idx % 32;
    results[i] = extract_fp16(buffer[line_idx * 32 + offset]);
}

// Step 5: Update read pointer
uint32_t new_rd_ptr = (rd_ptr + result_count) & 0x1FFF;  // Wrap at 8192
write_reg(REG_RD_PTR, new_rd_ptr);
```

**Complexity**: 5 steps, multiple address translations, complex unpacking logic.

---

## 2. Option A: Keep Line Padding, Fix Software

### 2.1 RTL Changes
**NONE** - No hardware modifications required.

### 2.2 Software Changes
```cpp
// Reading results from circular buffer (Option A - simplified)
uint32_t rd_ptr = read_reg(REG_RD_PTR);          // FP16 index 0-8191
uint32_t result_count = 17;

// Convert FP16 index → byte address → line address
uint32_t byte_addr = rd_ptr * 2;                 // 2-byte aligned address
uint32_t line_addr = (byte_addr >> 5) << 5;      // Round down to 32-byte boundary
uint32_t num_lines = ((rd_ptr + result_count + 15) >> 4) - (rd_ptr >> 4);

// DMA read (still line-aligned)
dma_read(BRAM_BASE + line_addr, num_lines * 32, buffer);

// Extract FP16 (same complex unpacking as before)
// ... (same as current implementation)
```

### 2.3 Pros
✅ **Zero RTL changes** - No hardware modifications
✅ **Zero risk** - Existing hardware continues working
✅ **Fast implementation** - Only software changes

### 2.4 Cons
❌ **Same complexity** - Still needs line address calculations
❌ **Same unpacking logic** - Still complex FP16 extraction
❌ **Flushing remains error-prone** - See Section 4
❌ **Inconsistent addressing** - Pointers are FP16, DMA needs lines
❌ **Hard to debug** - Multiple address translations obscure bugs

### 2.5 Flushing Impact (Option A)
**No improvement**. Partial line handling remains complex:
```cpp
// Flushing partial results (e.g., 1 FP16 from B1_C1_V1)
uint32_t wr_ptr_before = read_reg(REG_WR_PTR);   // e.g., 1
write_reg(ENGINE_WRITE_TOP, 0x0);                 // Trigger flush → wr_ptr=0!

// BUG SCENARIO:
// - Before flush: wr_ptr=1, BRAM line 0 has 1 valid FP16
// - After flush: wr_ptr=0, BRAM line 0 written with partial data
// - Software must remember pre-flush wr_ptr to know line has only 1 FP16
// - If using post-flush wr_ptr=0, calculation breaks!

uint32_t complete_lines = (wr_ptr_before + 15) / 16;  // MUST use saved value!
```

**Key Issue**: Software must save wr_ptr **before** flush, then use that value for address calculation. Easy to introduce bugs.

---

## 3. Option B: Remove Padding, Internal Translation

### 3.1 RTL Changes

**File**: `dma_bram_bridge.sv`

**Before** (lines 239, 243):
```systemverilog
.wraddr ({actual_wr_addr, 5'h00}),  // Forces 32-byte line alignment
.rdaddr ({actual_rd_addr, 5'h00}),  // Forces 32-byte line alignment
```

**After**:
```systemverilog
// Internal address translation: byte address → BRAM line
logic [8:0] bram_wr_line_addr;
logic [8:0] bram_rd_line_addr;

assign bram_wr_line_addr = actual_wr_addr[12:4];  // Divide by 16 (256-bit lines)
assign bram_rd_line_addr = actual_rd_addr[12:4];  // Divide by 16

.wraddr ({bram_wr_line_addr, 5'h00}),  // Line address with padding
.rdaddr ({bram_rd_line_addr, 5'h00}),  // Line address with padding
```

**Additional Enhancement** (optional, future):
```systemverilog
// Support byte-granular reads by tracking valid bytes per line
// This would completely solve the flushing issue
```

### 3.2 Software Changes (Simplified!)
```cpp
// Reading results from circular buffer (Option B - CLEAN)
uint32_t rd_ptr = read_reg(REG_RD_PTR);          // FP16 index 0-8191
uint32_t result_count = 17;

// Convert FP16 index → byte address (DONE!)
uint32_t byte_addr = rd_ptr * 2;                 // 2-byte aligned address
uint32_t byte_count = result_count * 2;          // Number of bytes to read

// DMA read (byte-addressed!)
dma_read(BRAM_BASE + byte_addr, byte_count, buffer);

// Extract FP16 (SIMPLIFIED - sequential unpacking)
for (int i = 0; i < result_count; i++) {
    results[i] = extract_fp16(buffer + i * 2);
}

// Update read pointer
uint32_t new_rd_ptr = (rd_ptr + result_count) & 0x1FFF;
write_reg(REG_RD_PTR, new_rd_ptr);
```

### 3.3 Pros
✅ **Clean addressing** - Byte address = FP16 index × 2 (simple!)
✅ **Simplified software** - No line calculations, no complex unpacking
✅ **Unified semantics** - All addresses are 2-byte aligned throughout
✅ **Better encapsulation** - dma_bram_bridge handles BRAM details internally
✅ **Flushing simplified** - See Section 4
✅ **Easier debugging** - Direct mapping: address ↔ FP16 index
✅ **Future-proof** - Enables byte-granular DMA (solve flushing completely)

### 3.4 Cons
❌ **RTL changes required** - Modify dma_bram_bridge.sv (small, localized)
❌ **Requires rebuild** - ~6 minute bitstream generation
❌ **Needs validation** - Must test existing BRAM functionality

### 3.5 Flushing Impact (Option B)
**MAJOR IMPROVEMENT**:
```cpp
// Flushing partial results (Option B - CLEAN)
uint32_t result_count = 1;                        // B1_C1_V1
uint32_t rd_ptr = 0;
write_reg(ENGINE_WRITE_TOP, 0x0);                 // Trigger flush

// Calculate byte address AFTER flush (no pre-save needed!)
uint32_t byte_addr = rd_ptr * 2;                  // = 0
uint32_t byte_count = result_count * 2;           // = 2 bytes

// DMA read - dma_bram_bridge handles line translation internally
dma_read(BRAM_BASE + byte_addr, byte_count, buffer);

// Extract (trivial)
result = extract_fp16(buffer);
```

**Key Benefit**: No need to save wr_ptr before flush! Byte addressing is flush-independent.

---

## 4. Flushing Mechanism Deep Dive

### 4.1 The Flushing Problem (Current)

**Scenario**: B1_C1_V1 produces 1 FP16 result
```
Initial state:     wr_ptr=0, pack_position=0
After result:      wr_ptr=1, pack_position=1 (partial line, NOT written to BRAM)
Host triggers flush: write(0x22C, 0) → write_top_reset=1
Hardware flushes:  Writes BRAM[0] with [FP16_0, zeros...], wr_ptr→0
Host must read:    1 FP16 from BRAM[0]
```

**Critical Issue**: After flush, `wr_ptr=0`, but software needs to know "line 0 has 1 valid FP16, not 16".

### 4.2 Option A Flushing (COMPLEX)
```cpp
bool run_single_test(...) {
    // BEFORE running test, save initial state
    uint32_t wr_ptr_before_test = read_reg(REG_WR_PTR);

    // Run GEMM operation...

    // AFTER GEMM, calculate expected results
    uint32_t result_count_expected = B * C;

    // If partial line, need flush
    if ((result_count_expected % 16) != 0) {
        // CRITICAL: Must save wr_ptr BEFORE flush!
        uint32_t wr_ptr_before_flush = read_reg(REG_WR_PTR);

        write_reg(ENGINE_WRITE_TOP, 0x0);  // Flush → wr_ptr becomes 0!

        // Must use SAVED value for calculation
        uint32_t complete_lines = (wr_ptr_before_flush + 15) / 16;
        uint32_t byte_addr = 0;  // Always start at line 0
        dma_read(BRAM_BASE + byte_addr, complete_lines * 32, buffer);

        // Complex unpacking to extract only valid FP16s...
    }
}
```

**Bug-Prone Points**:
1. Must save wr_ptr before flush (easy to forget)
2. Must use saved value, not post-flush value (easy to mix up)
3. Complex line calculation and unpacking
4. Different code path for flushed vs. non-flushed

### 4.3 Option B Flushing (CLEAN)
```cpp
bool run_single_test(...) {
    // Run GEMM operation...

    // Calculate expected results
    uint32_t result_count_expected = B * C;

    // If partial line, flush
    if ((result_count_expected % 16) != 0) {
        write_reg(ENGINE_WRITE_TOP, 0x0);  // Flush
        // No need to save wr_ptr!
    }

    // Read using byte addressing (SAME CODE PATH!)
    uint32_t rd_ptr = read_reg(REG_RD_PTR);
    uint32_t byte_addr = rd_ptr * 2;
    uint32_t byte_count = result_count_expected * 2;

    dma_read(BRAM_BASE + byte_addr, byte_count, buffer);

    // Simple sequential extraction
    for (int i = 0; i < result_count_expected; i++) {
        results[i] = extract_fp16(buffer + i * 2);
    }
}
```

**Benefits**:
1. No need to save/restore wr_ptr
2. Flush is transparent to read logic
3. Single code path for all cases
4. Flush-independent addressing

---

## 5. Implementation Complexity

### 5.1 Option A Implementation
**RTL Changes**: NONE
**Software Changes**: MODERATE
- Refactor existing address calculations
- Ensure wr_ptr saved before flush in all locations
- Test all 10 test cases

**Estimated Effort**: 1-2 hours
**Risk Level**: LOW (no hardware changes)

### 5.2 Option B Implementation
**RTL Changes**: SMALL (localized to dma_bram_bridge.sv)
- Modify lines 239, 243 (address translation)
- Add internal line address calculation
- Update any related addressing logic

**Software Changes**: MODERATE
- Simplify address calculations (remove line math)
- Unified read logic (no separate flush path)
- Test all 10 test cases

**Build Time**: ~6 minutes (bitstream generation)
**Estimated Effort**: 2-3 hours (including build + test)
**Risk Level**: LOW-MODERATE (localized RTL change, well-defined interface)

---

## 6. Testing Requirements

### 6.1 Option A Testing
- [ ] Verify all 10 test cases pass (Stage 1)
- [ ] Verify batched tests (Stage 2)
- [ ] Verify partial line handling (B1_C1_V1, B2_C2_V2)
- [ ] Verify wr_ptr saving/restore logic
- [ ] Stress test: repeated flush operations

### 6.2 Option B Testing
- [ ] Verify all 10 test cases pass (Stage 1)
- [ ] Verify batched tests (Stage 2)
- [ ] Verify partial line handling (transparent)
- [ ] Verify existing BRAM functionality (test_bram.cpp)
- [ ] Verify byte-aligned addressing throughout
- [ ] Regression test: existing DMA operations

---

## 7. Recommendation

### 7.1 Short Answer
**Option B** is strongly recommended.

### 7.2 Detailed Reasoning

**Primary Concern (Flushing Bugs)**: Option B **eliminates** the root cause by decoupling byte addressing from line alignment. Flush becomes transparent to software.

**Long-Term Benefits**:
- Cleaner architecture (unified 2-byte addressing)
- Easier to maintain (simpler software logic)
- Future-proof (enables byte-granular DMA)
- Better debugging (direct address ↔ FP16 index mapping)

**Risk Assessment**:
- RTL changes are **small and localized** (2 lines)
- Change is **well-defined** (address translation)
- Existing BRAM read/write functionality **unchanged**
- Can be **thoroughly tested** with existing test suite

**Cost-Benefit**:
- Extra 6 minutes build time
- 2-3 hours total effort
- **Eliminates entire class of flushing bugs**
- **Simplifies all future software development**

### 7.3 Implementation Plan

**Phase 1: RTL Modification**
1. Modify `dma_bram_bridge.sv` lines 239, 243
2. Add internal address translation logic
3. Build bitstream (~6 minutes)

**Phase 2: Validation**
1. Run `test_registers` (device health)
2. Run `test_bram` (verify existing BRAM functionality)
3. Run `test_gemm` Stage 1 (individual tests with reset)
4. Run `test_gemm` Stage 2 (batched tests without reset)

**Phase 3: Software Simplification**
1. Refactor `test_gemm.cpp` with byte addressing
2. Remove complex line calculations
3. Unify flush and non-flush code paths

**Rollback Plan**: If issues arise, revert to previous bitstream (backup exists).

---

## 8. Alternative: Hybrid Approach (Not Recommended)

**Concept**: Add dedicated result-specific DMA path separate from main BRAM bridge.

**Pros**: Clean separation, optimized for FP16 format
**Cons**: Much larger effort, duplicates DMA logic, overkill for current problem

**Verdict**: Not justified for current scope. Option B achieves 90% of benefits with 10% of effort.

---

## 9. Conclusion

**Recommendation**: **Implement Option B**

**Key Decision Factors**:
1. ✅ **Solves flushing bugs** - Primary concern addressed
2. ✅ **Simplifies software** - Long-term maintenance benefit
3. ✅ **Low risk** - Small, localized RTL change
4. ✅ **Future-proof** - Enables byte-granular DMA
5. ✅ **Matches design intent** - RESULT_BUFFER_REFERENCE already specifies 2-byte addressing

**Next Steps**: Proceed with Option B implementation if user approves.
