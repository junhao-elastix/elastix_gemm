# Software-Only Investigation Plan
**No RTL changes or bitstream rebuild required**

## Test 1: FETCH @ 0x4200 as FIRST Command ⭐ **CRITICAL**
**Purpose**: Determine if problem is "sequential FETCH" vs "address 0x4200"

**Test**: `./test_fetch_4200` (after system reboot)

**Expected Results**:
- **If it works (528 lines)**: Problem is "second FETCH state" or BRAM write collision
- **If it fails (16 lines)**: Problem is address 0x4200 specifically

**Why important**: This tells us whether to focus on:
- Sequential FETCH logic (state machine bug)
- GDDR6 address mapping (NoC/NAP routing)

---

## Test 2: Check Reference Design GDDR6 Usage
**Purpose**: See what addresses working code uses

**Commands**:
```bash
cd ~/Dev/elastix_gemm/llm_vp_demo_pcie_orig
grep -r "0x[0-9a-fA-F]\{4,\}" software/ | grep -i gddr
grep -r "dmaWrite.*0x" software/ | head -20
```

**Look for**:
- What GDDR6 addresses are known-good?
- Are there alignment requirements?
- Max tested offset?

---

## Test 3: Check GDDR6 Register Status
**Purpose**: See if GDDR6 has errors or constraints

**Test**:
```bash
cd ~/Dev/elastix_gemm/gemm/sw_test
./test_gddr6  # Check channel 0 status
./scan_registers | grep -E "0x[5-9]" | head -20  # GDDR6 registers
```

**Look for**:
- Error flags in GDDR6 control registers
- Status bits indicating problems
- Performance counters showing stalls

---

## Test 4: Vary FETCH Size (After Reboot)
**Purpose**: Test if it's size-dependent

**Create simple tests**:
```cpp
// Test 16 lines (1 burst) - should always work
word2 = (16 << 16);

// Test 32 lines (2 bursts) - does second burst succeed?
word2 = (32 << 16);

// Test 256 lines (16 bursts)
word2 = (256 << 16);
```

**If only 1 burst works**: Problem is with burst continuation logic
**If 256 works but 528 fails**: Problem is specific to 33-burst sequences

---

## Test 5: Check NoC Configuration (Documentation)
**Purpose**: Verify address routing

**Check files**:
```bash
cat ~/Dev/elastix_gemm/gemm/src/constraints/ace_placements.pdc | grep -i nap
cat ~/Dev/elastix_gemm/doc/2D_Network_on_Chip/*.html  # Search for address mapping
```

**Look for**:
- NAP placement for Channel 0
- Page ID configuration (should be 10 = 0x0A)
- Address range limits

---

## Test 6: Examine AXI Burst Parameters
**Purpose**: Check if burst size/length is issue

**From code**:
```systemverilog
// dispatcher_control.sv uses:
axi_ddr_if.arlen = 8'd15;  // 16 beats
axi_ddr_if.arsize = 3'd5;  // 32 bytes per beat
```

**Questions**:
- Does NAP support 16-beat bursts?
- Is there a max total transfer size?
- Does second burst in same transaction fail?

---

## Test 7: Single Large DMA vs Multiple Small
**Purpose**: Test if GDDR6 has transaction limits

**Test**:
```bash
# Current: Write 16896 bytes in one DMA
device->dmaWrite(0x4200, 16896, data);

# Try: Write as 4 smaller DMAs
for (int i = 0; i < 4; i++) {
    device->dmaWrite(0x4200 + i*4224, 4224, &data[i*4224]);
}
```

**If multiple small work**: GDDR6 has per-transaction size limit

---

## Test 8: Check Timing Between Commands
**Purpose**: See if commands need spacing

**Test**:
```cpp
// Issue first FETCH
device->mmioWrite32(0, 0x38, 1);
sleep(1);  // Wait 1 second

// Read status
uint32_t status;
device->mmioRead32(0, 0x1C, status);
if (status & 0x80) {  // fetch_done
    // Issue second FETCH
    ...
}
```

**If this helps**: Commands need synchronization gap

---

## Test 9: Inspect Current `wr_addr` Behavior
**Purpose**: Understand the "544 lines" anomaly

**Current observation**: 
- wr_addr = 543 = 544 lines total
- Expected: 528 lines (first FETCH)

**Hypothesis to test**:
- Is 544 from BOTH FETCHes combined (528 + 16)?
- Or is first FETCH writing 544 alone (off-by-one)?

**Test** (after reboot):
```bash
./test_single_fetch  # Fresh system, one FETCH only
# If wr_addr = 527: Correct (528 lines, 0-indexed)
# If wr_addr = 543: Bug in first FETCH (writes extra burst)
```

---

## Test 10: Check for BRAM Write Conflicts
**Purpose**: See if writing BRAM[528+] causes issues

**Theory**: 
- BRAM depth = 2048
- First FETCH writes [0-527] ✅
- Second FETCH starts at [528] but maybe BRAM has region restriction?

**Test**: Skip first FETCH, start second FETCH at BRAM[0]
```cpp
// Modify dispatcher to start at BRAM[0] for "second" FETCH
// This requires current_line_reg reset between FETCHes
// Can't do without RTL change... skip this one
```

---

## Prioritized Test Order

1. **HIGHEST PRIORITY**: `./test_fetch_4200` (after reboot)
   - Answers: Sequential issue vs address issue

2. **Check reference designs**: What addresses does working code use?
   - Quick grep, no hardware needed

3. **Test GDDR6 status**: Are there hardware errors?
   - `./test_gddr6` and scan_registers

4. **Vary FETCH sizes**: 16, 32, 64, 128, 256 lines
   - Test burst continuation logic

5. **Check NoC routing**: Verify address mapping
   - Documentation review

All these can be done **without RTL changes or rebuild**!
