# Software Test Reference Results - Circular Buffer Bug

**Generated**: November 14, 2025
**Source**: test_gemm_full.cpp Stage 2 testing
**Purpose**: Reference data for simulation verification

---

## Mismatch Summary by Tile Count

| Tiles (col_en) | Mismatches | Percentage | Pattern Characteristic |
|----------------|------------|------------|------------------------|
| n=1 (0x000001) | 617/618    | 99.8%      | Simple +1 shift        |
| n=2 (0x000003) | 384/618    | 62.1%      | Periodic realignment   |
| n=4 (0x00000F) | 253/618    | 40.9%      | Frequent realignment   |
| n=8 (0x0000FF) | 197/618    | 31.9%      | Maximum realignment    |

---

## Test Configuration Sequence

| Test | Name       | B   | C   | V   | Results | Cumulative | col_en (all) |
|------|------------|-----|-----|-----|---------|------------|--------------|
| 1    | B1_C1_V1   | 1   | 1   | 1   | 1       | 1          | Variable     |
| 2    | B2_C2_V2   | 2   | 2   | 2   | 4       | 5          | Variable     |
| 3    | B4_C4_V4   | 4   | 4   | 4   | 16      | 21         | Variable     |
| 4    | B2_C2_V64  | 2   | 2   | 64  | 4       | 25         | Variable     |
| 5    | B4_C4_V32  | 4   | 4   | 32  | 16      | 41         | Variable     |
| 6    | B8_C8_V16  | 8   | 8   | 16  | 64      | 105        | Variable     |
| 7    | B16_C16_V8 | 16  | 16  | 8   | 256     | 361        | Variable     |
| 8    | B1_C128_V1 | 1   | 128 | 1   | 128     | 489        | Variable     |
| 9    | B128_C1_V1 | 128 | 1   | 1   | 128     | 617        | Variable     |
| 10   | B1_C1_V128 | 1   | 1   | 128 | 1       | 618        | Variable     |

---

## wr_ptr Progression

| Test | Expected | n=1 (wr/used) | n=2 (wr/used) | n=4 (wr/used) | n=8 (wr/used) |
|------|----------|---------------|---------------|---------------|---------------|
| 1    | 1        | 1/1           | 1/1           | 1/1           | 1/1           |
| 2    | 5        | 5/5           | 5/5           | 5/5           | 5/5           |
| 3    | 21       | 21/21         | 21/21         | 21/21         | 21/21         |
| 4    | 25       | 25/25         | 25/25         | 25/25         | 25/25         |
| 5    | 41       | 41/41         | 41/41         | 41/41         | 41/41         |
| 6    | 105      | 105/105       | 105/105       | 95/105        | 91/105        |
| 7    | 361      | 311/333       | 260/282       | 251/273       | 227/249       |
| 8    | 489      | 482/489       | 461/483       | 461/484       | 430/453       |
| 9    | 617      | 600/617       | 589/611       | 617/617       | 617/617       |
| 10   | 618      | 618/618       | 618/618       | 618/618       | 618/618       |

**Note:** Test 7 shows (used - wr_ptr) = 22 for ALL tile counts ("magic number 22")

---

## Golden Results (First 20 positions from stage1_golden.hex)

```
Position | Value  | Test | Description
---------|--------|------|----------------------------------
0        | 0x253e | T1   | Test 1 single result
1        | 0x22f7 | T2   | Test 2 result 0/4
2        | 0x25b7 | T2   | Test 2 result 1/4
3        | 0xa390 | T2   | Test 2 result 2/4
4        | 0xa40a | T2   | Test 2 result 3/4
5        | 0x9873 | T3   | Test 3 result 0/16
6        | 0xa03c | T3   | Test 3 result 1/16
7        | 0x21c5 | T3   | Test 3 result 2/16
8        | 0xa29b | T3   | Test 3 result 3/16
9        | 0xa7c8 | T3   | Test 3 result 4/16
10       | 0x263e | T3   | Test 3 result 5/16
11       | 0x254c | T3   | Test 3 result 6/16
12       | 0x29db | T3   | Test 3 result 7/16
13       | 0xa6dc | T3   | Test 3 result 8/16
14       | 0x27d7 | T3   | Test 3 result 9/16
15       | 0x27fe | T3   | Test 3 result 10/16
16       | 0x2532 | T3   | Test 3 result 11/16
17       | 0xa751 | T3   | Test 3 result 12/16
18       | 0x27e8 | T3   | Test 3 result 13/16
19       | 0x2705 | T3   | Test 3 result 14/16
```

---

## Match/Mismatch Patterns (First 10 positions)

### n=1 (Single Tile - 0x000001)
```
[0] MATCH   - 0x253e (Test 1, correct)
[1] MISMATCH - 0x253e (DUPLICATE! Should be 0x22f7)
[2] MISMATCH - 0x22f7 (shifted from pos 1)
[3] MISMATCH - 0x25b7 (shifted from pos 2)
[4] MISMATCH - 0xa390 (shifted from pos 3)
[5] MISMATCH - 0xa40a (shifted from pos 4)
[6] MISMATCH - 0x9873 (shifted from pos 5)
[7] MISMATCH - 0xa03c (shifted from pos 6)
[8] MISMATCH - 0x21c5 (shifted from pos 7)
[9] MISMATCH - 0xa29b (shifted from pos 8)

Pattern: Everything shifted +1 after duplicate at position 1
```

### n=2 (Two Tiles - 0x000003)
```
[0] MATCH    - 0x253e
[1] MISMATCH - 0x253e (DUPLICATE!)
[2] MATCH    - 0x25b7 (lucky realignment)
[3] MISMATCH - 0x22f7
[4] MISMATCH - 0xa390
[5] MATCH    - 0x9873 (periodic realignment)
[6] MISMATCH - 0xa40a
[7] MATCH    - 0x21c5
[8] MISMATCH - 0xa03c
[9] MATCH    - 0xa7c8

Pattern: Odd/even interleaving creates periodic matches
```

### n=4 (Four Tiles - 0x00000F)
```
[0] MATCH    - 0x253e
[1] MISMATCH - 0x253e (DUPLICATE!)
[2] MATCH    - 0x25b7
[3] MISMATCH - 0x22f7
[4] MATCH    - 0xa40a (more frequent realignment)
[5] MISMATCH - 0xa390
[6] MATCH    - 0xa03c
[7] MATCH    - 0x21c5
[8] MATCH    - 0xa29b
[9] MISMATCH - 0x9873

Pattern: 4-way interleaving → more matches
```

### n=8 (Eight Tiles - 0x0000FF)
```
[0] MATCH    - 0x253e
[1] MISMATCH - 0x253e (DUPLICATE!)
[2] MATCH    - 0x25b7
[3] MISMATCH - 0x22f7
[4] MATCH    - 0xa40a
[5] MISMATCH - 0xa390
[6] MATCH    - 0xa03c
[7] MATCH    - 0x21c5
[8] MATCH    - 0xa29b
[9] MISMATCH - 0x9873

Pattern: Similar to n=4 for early tests (not enough results to use 8 tiles)
```

---

## Critical Bug Signature

**What to Look For in Simulation:**

1. **After Test 1 READOUT:**
   ```
   BRAM position 0 = 0x253e  ✓
   BRAM position 1 = 0x0000  ✓ (empty)
   wr_ptr = 1                ✓
   ```

2. **After Test 2 READOUT (BUG):**
   ```
   BRAM position 0 = 0x253e  ✓ (unchanged)
   BRAM position 1 = 0x253e  ✗ DUPLICATE! (should be 0x22f7)
   BRAM position 2 = 0x22f7  ✗ (shifted +1)
   BRAM position 3 = 0x25b7  ✗ (shifted +1)
   BRAM position 4 = 0xa390  ✗ (shifted +1)
   wr_ptr = 5                ✓ (pointer correct, but 5 values written!)
   ```

3. **Expected After Fix:**
   ```
   BRAM position 0 = 0x253e  ✓
   BRAM position 1 = 0x22f7  ✓ FIX! (no duplicate)
   BRAM position 2 = 0x25b7  ✓
   BRAM position 3 = 0xa390  ✓
   BRAM position 4 = 0xa40a  ✓
   wr_ptr = 5                ✓
   ```

---

## Simulation Verification Checklist

- [ ] Position 1 contains duplicate 0x253e after Test 2
- [ ] wr_ptr progression matches table above
- [ ] Total 618 results collected at end
- [ ] n=1: 617 mismatches (99.8%)
- [ ] n=2: ~384 mismatches (62.1%)
- [ ] n=4: ~253 mismatches (40.9%)
- [ ] n=8: ~197 mismatches (31.9%)
- [ ] Test 7 shows (used - wr_ptr) = 22 for all tile counts
- [ ] After fix: ALL 618 results match golden for all tile counts

---

## Files Generated From Software Testing

- `/gemm/sw_test/stage1_golden.hex` - 618 FP16 golden results (one per line)
- `/gemm/sw_test/CIRCULAR_BUFFER_BUG_ANALYSIS.md` - Comprehensive bug analysis
- `/gemm/sw_test/CIRCULAR_BUFFER_FIX_SUMMARY.md` - Quick reference summary

---

**End of Software Reference Data**
