# CRITICAL: Architecture Confusion - Need Clarification

**Date**: October 13, 2025  
**Status**: CONFUSED - NEED USER CONFIRMATION

---

## The Mess I Created

I've been implementing changes without a clear documented plan, and now there are multiple inconsistencies.

### Current State (BROKEN)

**Dispatcher BRAM (`dispatcher_bram.sv`):**
```systemverilog
// I just changed to:
left_mantissa_mem[512]   // 256-bit x 512
right_mantissa_mem[512]  // 256-bit x 512
left_exp_mem[512]        // 8-bit x 512
right_exp_mem[512]       // 8-bit x 512

// Write decode:
[0-511] → left_mantissa_mem
[512-1023] → right_mantissa_mem
```

**Dispatcher Control (writes):**
```
FETCH 1: Writes to BRAM [0-527]
  Lines [0-15]: Exponents (unpacked to left_exp_mem)
  Lines [16-527]: LEFT MANTISSAS

FETCH 2: Writes to BRAM [528-1055]
  Lines [528-543]: Exponents (unpacked to right_exp_mem)
  Lines [544-1055]: RIGHT MANTISSAS
```

**BCV Controller (reads):**
```systemverilog
// Mantissa address = (nv_idx * 4 + g_idx) + 16
// Uses left_base=0, right_base=0
// BOTH read from address 16+ in their respective BRAMs
```

**MISMATCH:**
- Write: Left mantissas go to BRAM [16-527]
- Decode: [16-527] doesn't map cleanly to [0-511]!
- Read: BCV reads from address 16+, but in separate BRAMs

---

## What I THINK We Discussed (But I'm Not Sure)

**Option A: Single BRAM with Base Addresses**
```
Single BRAM[2048]:
  [0-15]:    Left exponents (unpacked to left_exp_mem)
  [16-527]:  Left mantissas  
  [528-543]: Right exponents (unpacked to right_exp_mem)
  [544-1055]: Right mantissas

BCV uses:
  left_base = 16
  right_base = 544
  address = base + (nv_idx * 4 + g_idx)
```

**Option B: Separate BRAMs, No Offset**
```
Separate BRAMs:
  left_mantissa_mem[512]: Lines [0-511]
  right_mantissa_mem[512]: Lines [0-511]

Dispatcher writes:
  Left:  [0-511] → left_mantissa_mem
  Right: [0-511] → right_mantissa_mem

BCV reads:
  address = nv_idx * 4 + g_idx (NO +16 offset!)
  left_base = 0
  right_base = 0
```

---

## Questions for User

1. **Which architecture did we agree on?**
   - Single BRAM with base addresses?
   - Separate BRAMs?

2. **If separate BRAMs:**
   - Should dispatcher_control write mantissas starting at address 0 (not 16)?
   - Should BCV controller remove the +16 offset?

3. **Where is the original plan documented?**
   - I cannot find a clear document with our agreed architecture

---

## What I Need From You

Please confirm:
1. The EXACT BRAM organization you want
2. The EXACT address mappings for write and read
3. Whether I should revert my changes and start over with a clear plan

I apologize for creating this confusion. I should have documented the plan BEFORE implementing.


