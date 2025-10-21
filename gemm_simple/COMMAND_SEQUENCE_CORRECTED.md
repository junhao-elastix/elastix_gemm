# Command Sequencing for MS2.0 GEMM Engine

**Last Updated**: Sun Oct 12 01:43:44 PDT 2025  
**Status**: Corrected sequence documentation based on hardware architecture

---

## Overview

The MS2.0 GEMM engine uses a **microcode-based command architecture** with strict sequencing rules. The key distinction is between **FETCH** (load entire memory block) and **DISP** (extract portion for computation).

---

## Command Types (from MS2.0_uCode-Single_Tile.csv)

| Opcode | Name | Purpose | Payload |
|--------|------|---------|---------|
| `0xF0` | **FETCH** | Load 128x128 memory block from GDDR6 | addr, len |
| `0xF1` | **DISP** | Extract BxV (left) or CxV (right) portion to BRAM | addr, len, flags |
| `0xF2` | **TILE** | Execute matrix multiplication | left_addr, right_addr, B, C, V, flags |
| `0xF3` | **WAIT_DISP** | Wait for DISP to complete | wait_id |
| `0xF4` | **WAIT_TILE** | Wait for TILE to complete | wait_id |

---

## Critical Sequencing Rules

### Rule 1: FETCH Before DISP
- **FETCH** must occur before any **DISP** for that matrix
- FETCH loads entire 128x128 block into dispatcher buffer
- DISP extracts portions from this buffer

### Rule 2: Paired Commands
- **DISP** + **WAIT_DISP**: Always together, never separated
- **TILE** + **WAIT_TILE**: Always together, never separated

### Rule 3: FETCH Happens Once
- One FETCH per 128x128 memory block
- Multiple DISPs can extract different portions from one FETCH

### Rule 4: Independent Left/Right
- Left and right matrices have independent FETCH/DISP sequences
- DISP left and DISP right don't need to be symmetric

---

## Single-Tile Sequence (Baseline)

**Example**: B=4, C=4, V=32

```
1. FETCH left          Load 128x128 left matrix block
2. DISP left           Extract 4x32 = 4 rows x 4096 columns
3. WAIT_DISP           Ensure left extraction complete
4. FETCH right         Load 128x128 right matrix block
5. DISP right          Extract 32x4 = 4096 rows x 4 columns
6. WAIT_DISP           Ensure right extraction complete
7. TILE                Compute 4x4 output
8. WAIT_TILE           Ensure computation complete
```

**Result**: 16 FP16 values (4x4 matrix)

---

## Multi-Tile Sequences

### Case 1: Sequential Fetch-Disp-Tile

**Example**: B=1, C=1, V=64 (two tiles from one memory block)

```
FETCH left             Load 128x128 left block
DISP left 1            Extract rows 0 (V=64 → 64x128 = 8192 elements)
WAIT_DISP
FETCH right            Load 128x128 right block
DISP right 1           Extract cols 0 (V=64)
WAIT_DISP
TILE 1                 Compute result[0,0]
WAIT_TILE

DISP left 2            Extract rows 1 (next V=64 portion)
WAIT_DISP
DISP right 2           Extract cols 1
WAIT_DISP
TILE 2                 Compute result[0,1]
WAIT_TILE
```

**Key**: Both FETCH commands executed first, then multiple DISP+TILE pairs

### Case 2: Fetch-All-First Pattern

**Example**: Same B=1, C=1, V=64

```
FETCH left             Load entire left block
FETCH right            Load entire right block

DISP left 1            Extract first portion
WAIT_DISP
DISP right 1           Extract first portion
WAIT_DISP
TILE 1                 Compute
WAIT_TILE

DISP left 2            Extract second portion
WAIT_DISP
DISP right 2           Extract second portion
WAIT_DISP
TILE 2                 Compute
WAIT_TILE
```

**Key**: Both matrices fetched upfront, then alternating DISP/TILE

### Case 3: Asymmetric Dispatch (Reuse Left, Multiple Right)

**Example**: B=4, C=2, V=16 (4 left rows, 2 right columns)

**Capacity Check**:
- Left needs: B x V = 4 x 16 = 64 NVs ✅ (fits in one 128 NV block)
- Right needs: C x V = 2 x 16 = 32 NVs ✅ (fits in one 128 NV block)

```
FETCH left             Load 128 NVs
DISP left 1            Extract rows 0-1 (2 x 16 = 32 NVs)
WAIT_DISP
FETCH right            Load 128 NVs
DISP right 1           Extract col 0 (16 NVs)
WAIT_DISP
TILE 1                 Compute [0-1, 0] → 2 results
WAIT_TILE

DISP right 2           Extract col 1 (16 NVs)
WAIT_DISP
TILE 2                 Compute [0-1, 1] → 2 results (reusing left 1)
WAIT_TILE

DISP left 2            Extract rows 2-3 (next 32 NVs)
WAIT_DISP
DISP right 1           Reuse col 0 (already in BRAM)
WAIT_DISP
TILE 3                 Compute [2-3, 0] → 2 results
WAIT_TILE

DISP right 2           Reuse col 1 (already in BRAM)
WAIT_DISP
TILE 4                 Compute [2-3, 1] → 2 results
WAIT_TILE
```

**Key**: 
- DISP left: 2 times (2 row pairs from left block)
- DISP right: 2 times initially, then reused (2 columns from right block)
- TILE: 4 times (2x2 grid)
- Total output: 8 FP16 results (4 tiles x 2 results each)

### Extreme Case: B=128, C=1, V=1

**Scenario**: Compute full 128x128 matrix with 128 tiles

**Capacity Check**:
- Left needs: B x V = 128 x 1 = 128 NVs ✅ (exactly one full 128 NV block)
- Right needs: C x V = 1 x 1 = 1 NV ✅ (fits in one 128 NV block)

**Key Insight**: Each TILE computes BxC = 128x1 = **128 results** (not just 1!)

```
FETCH left             Load 128 NVs (entire left block)
DISP left 1            Extract ALL 128 rows (BxV = 128 NVs)
WAIT_DISP
FETCH right            Load 128 NVs (entire right block)

DISP right 1           Extract col 0 (CxV = 1 NV)
WAIT_DISP
TILE 1                 Compute 128x1 → 128 results (rows 0-127, col 0)
WAIT_TILE

DISP right 2           Extract col 1 (CxV = 1 NV)
WAIT_DISP
TILE 2                 Compute 128x1 → 128 results (rows 0-127, col 1, reusing left)
WAIT_TILE

DISP right 3           Extract col 2 (CxV = 1 NV)
WAIT_DISP
TILE 3                 Compute 128x1 → 128 results (rows 0-127, col 2, reusing left)
WAIT_TILE

... (repeat 128 times total)

DISP right 128         Extract col 127 (CxV = 1 NV)
WAIT_DISP
TILE 128               Compute 128x1 → 128 results (rows 0-127, col 127, reusing left)
WAIT_TILE
```

**Key**: 
- **DISP left**: 1 time only (extracts ALL 128 rows at once, entire left block)
- **DISP right**: 128 times (one per column, each extracts 1 NV from right block)
- **TILE**: 128 times (each computes BxC = 128x1 = 128 results)
- **Total commands**: 2 FETCH + 1 DISP left + 128 DISP right + 128 TILE = 131 commands + 258 WAIT = 389 total
- **Total output**: 128 tiles x 128 results = **16,384 FP16 results** (full 128x128 matrix!)

---

## Memory Block Capacity

One 128x128 memory block contains:
- **128 Native Vectors** (each NV = 128 elements)
- **Total**: 128 x 128 = 16,384 elements

### Core Formula (CRITICAL!)

For a given (B, C, V) configuration:

**Number of tiles in one memory block:**
```
N = (128/B) x (128/C)  [when V=1]
N = (128/(BxV)) x (128/(CxV))  [general case]
```

**Results per tile:**
```
One TILE computes: B x C results
```

**Total results from one memory block:**
```
Total = N x B x C = (128/B) x (128/C) x B x C = 128 x 128 = 16,384 results (always!)
```

**Verification Examples:**

| B | C | V | N (tiles) | Results/tile | Total Results |
|---|---|---|-----------|--------------|---------------|
| 1 | 1 | 1 | 128x128 = 16,384 | 1x1 = 1 | 16,384x1 = 16,384 ✓ |
| 4 | 4 | 1 | 32x32 = 1,024 | 4x4 = 16 | 1,024x16 = 16,384 ✓ |
| 128 | 1 | 1 | 1x128 = 128 | 128x1 = 128 | 128x128 = 16,384 ✓ |
| 1 | 128 | 1 | 128x1 = 128 | 1x128 = 128 | 128x128 = 16,384 ✓ |
| 2 | 2 | 2 | 32x32 = 1,024 | 2x2 = 4 | 1,024x4 = 4,096 ✓ |

### Dispatching for One Memory Block

For a single memory block:
- **Left dispatches**: **128/(BxV)** times (each extracts BxV NVs = one "row group")
- **Right dispatches**: **128/(CxV)** times (each extracts CxV NVs = one "column group")
- **TILE commands**: **N = (128/(BxV)) x (128/(CxV))** times (one per tile)

**Key insight**: You dispatch left 128/(BxV) times and right 128/(CxV) times, creating N=128/(BxV) x 128/(CxV) tiles.

### Capacity Constraint (Critical!)

**Rule**: For any single FETCH, all extracted portions must fit within 128 NVs

**Left matrix extraction**: B x V ≤ 128
**Right matrix extraction**: C x V ≤ 128

### Valid Examples

| B | C | V | Left NVs | Right NVs | Valid? |
|---|---|---|----------|-----------|--------|
| 1 | 1 | 64 | 64 | 64 | ✅ Both fit |
| 4 | 4 | 32 | 128 | 128 | ✅ Both fit (maximum) |
| 128 | 1 | 1 | 128 | 1 | ✅ Both fit |
| 1 | 128 | 1 | 1 | 128 | ✅ Both fit |
| 8 | 8 | 16 | 128 | 128 | ✅ Both fit |
| 2 | 64 | 1 | 2 | 64 | ✅ Both fit |

### Invalid Examples (Exceed Block Capacity)

| B | C | V | Left NVs | Right NVs | Why Invalid? |
|---|---|---|----------|-----------|--------------|
| 2 | 4 | 64 | 128 | **256** | ❌ Right exceeds 128 NVs (need 2 FETCHes) |
| 4 | 2 | 64 | **256** | 128 | ❌ Left exceeds 128 NVs (need 2 FETCHes) |
| 8 | 8 | 32 | **256** | **256** | ❌ Both exceed (need 4 FETCHes total) |
| 128 | 128 | 1 | 128 | 128 | ✅ **BUT** produces 16,384 results (FIFO overflow risk) |

**Critical**: If BxV > 128 or CxV > 128, you need **multiple FETCH commands** to load additional memory blocks!

---

## Microcode Format (from MS2.0_uCode-Single_Tile.csv)

All commands follow the same header structure, followed by command-specific payload.

### Common Header Format

**All Commands** (32 bits, 1 word):
```
[31:24]  reserved     (unused, typically 0x00)
[23:16]  len          (total command length in bytes)
[15:8]   id           (command identifier for tracking)
[7:0]    opcode       (0xF0-0xF4)
```

---

### FETCH (0xF0) - Load Memory Block from GDDR6

**Total Length**: 12 bytes (3 words)

**Header** (Word 0):
```
[31:24]  0x00         (reserved)
[23:16]  0x0C         (len = 12 bytes)
[15:8]   id           (command ID)
[7:0]    0xF0         (FETCH opcode)
```

**Payload** (2 words = 64 bits):

**Word 1** [31:0]:
```
start_addr[31:0]     External memory relative address (divided by 8)
```

**Word 2** [31:0]:
```
[31:24]  reserved     (padding)
[23:16]  reserved     (padding)
[15:0]   length       Number of 128B chunks to read
```

**Purpose**: Transfer data from GDDR6 to dispatcher's internal buffer  
**Notes**: 
- Address is byte address divided by 8
- Length specifies number of 128-byte chunks
- One 128x128 matrix = 528 chunks (16 exponent + 512 mantissa lines)

---

### DISP (0xF1) - Vector Dispatch (Extract to BRAM)

**Total Length**: 8 bytes (2 words)

**Header** (Word 0):
```
[31:24]  0x00         (reserved)
[23:16]  0x08         (len = 8 bytes)
[15:8]   id           (command ID)
[7:0]    0xF1         (DISP opcode)
```

**Payload** (1 word = 32 bits):

**Word 1** [31:0]:
```
[31:24]  reserved     (padding)
[23:16]  flags[7:0]   Configuration flags
         [7:1]       reserved
         [0]         Mantissa format: 0=8-bit, 1=4-bit
[15:0]   tile_dest_addr  Destination BRAM start address
```

**CSV Field Mapping**:
- **Mantissa NV cnt**: Implicitly BxV (left) or CxV (right), not in command
- **Tile destination address**: BRAM write start (0 for left, 528 for right typically)
- **Flags[0]**: Mantissa width selector

**Purpose**: Convert GFP8 to BFP and write to BRAM  
**Notes**:
- Extracts BxV Native Vectors (left) or CxV NVs (right) from fetched buffer
- Multiple DISP commands can extract different portions from one FETCH
- Address specifies where in BRAM to write (allows non-overlapping regions)

---

### TILE (0xF2) - Matrix Multiplication

**Total Length**: 12 bytes (3 words)

**Header** (Word 0):
```
[31:24]  0x00         (reserved)
[23:16]  0x0C         (len = 12 bytes)
[15:8]   id           (command ID)
[7:0]    0xF2         (TILE opcode)
```

**Payload** (3 words = 96 bits):

**Word 1** [31:0]:
```
[31:16]  right_addr   Right matrix start address in BRAM (16 bits)
[15:0]   left_addr    Left matrix start address in BRAM (16 bits)
```

**Word 2** [31:0]:
```
[31:24]  ugd_vec_size UGD vector size = V (8 bits)
[23:16]  right_ugd    Right UGD vectors = C (8 bits)
[15:8]   left_ugd     Left UGD vectors = B (8 bits)
[7:0]    reserved     (padding)
```

**Word 3** [31:0]:
```
[31:8]   reserved     (padding, 24 bits)
[7:0]    flags        Configuration flags
         [7:3]       reserved
         [2]         Main loop over left (0=over right, 1=over left)
         [1]         Right mantissa: 0=8-bit, 1=4-bit
         [0]         Left mantissa: 0=8-bit, 1=4-bit
```

**CSV Field Mapping**:
- **Left start address**: BRAM address for left matrix data
- **Right start address**: BRAM address for right matrix data
- **Left UGD vectors**: B = number of output rows
- **Right UGD vectors**: C = number of output columns
- **UGD vector size**: V = Native Vectors per dot product (accumulation depth)

**Terminology**:
- **UGD**: Unspecified Group Descriptor (essentially means Native Vector in this context)
- **Native Vector (NV)**: 128 elements (4 groups x 32 elements)
- **Output size**: B x C FP16 results

**Purpose**: Execute Bx(Vx128) @ (Vx128)xC matrix multiplication  
**Notes**:
- Left matrix: B rows x (Vx128) columns
- Right matrix: (Vx128) rows x C columns
- Output: B x C FP16 results
- V-loop: Each output accumulates V dot products

---

### WAIT_DISP (0xF3) - Wait for Dispatch Complete

**Total Length**: 4 bytes (1 word)

**Header** (Word 0):
```
[31:24]  wait_id      ID of DISP command to wait for
[23:16]  0x04         (len = 4 bytes)
[15:8]   id           (command ID)
[7:0]    0xF3         (WAIT_DISP opcode)
```

**Purpose**: Block until specified DISP command completes  
**Notes**:
- Must immediately follow corresponding DISP
- Ensures data is ready in BRAM before TILE accesses it
- wait_id matches the id field of the DISP command to wait for

---

### WAIT_TILE (0xF4) - Wait for Tile Complete

**Total Length**: 4 bytes (1 word)

**Header** (Word 0):
```
[31:24]  wait_id      ID of TILE command to wait for
[23:16]  0x04         (len = 4 bytes)
[15:8]   id           (command ID)
[7:0]    0xF4         (WAIT_TILE opcode)
```

**Purpose**: Block until specified TILE computation completes  
**Notes**:
- Must immediately follow corresponding TILE
- Ensures all BxC results written to result FIFO
- wait_id matches the id field of the TILE command to wait for

---

## Command Size Summary

| Command | Header | Payload | Total | Words |
|---------|--------|---------|-------|-------|
| FETCH | 4 bytes | 8 bytes | 12 bytes | 3 |
| DISP | 4 bytes | 4 bytes | 8 bytes | 2 |
| TILE | 4 bytes | 8 bytes | 12 bytes | 3 |
| WAIT_DISP | 4 bytes | 0 bytes | 4 bytes | 1 |
| WAIT_TILE | 4 bytes | 0 bytes | 4 bytes | 1 |

**Note**: WAIT commands encode wait_id in the header's reserved field [31:24]

---

## Dispatch Address Calculation

**DISP Command** extracts a portion from the fetched 128x128 block:

### Left Matrix (B rows, V NVs per row)
```
disp_addr = row_start_idx x 4
  where row_start_idx is the first Native Vector index to extract
  
Example: Extract rows 0-3 with V=32
  row_start_idx = 0 → disp_addr = 0
  Extracts NVs [0-127] (4 rows x 32 NVs)

Example: Extract rows 64-67 with V=32
  row_start_idx = 64 → disp_addr = 256
  Extracts NVs [64-191]
```

### Right Matrix (C columns, V NVs per column)
```
disp_addr = col_start_idx x 4 + base_offset
  where col_start_idx is the first NV index for this column
  base_offset = 528 (typical separation in BRAM)

Example: Extract col 0 with V=64
  disp_addr = 0 + 528 = 528
  Extracts NVs [0-63]

Example: Extract col 1 with V=64
  disp_addr = 64 + 528 = 592
  Extracts NVs [64-127]
```

---

## Validation Rules

### Must Follow
1. ✅ FETCH left before any DISP left
2. ✅ FETCH right before any DISP right
3. ✅ DISP immediately followed by WAIT_DISP
4. ✅ TILE immediately followed by WAIT_TILE
5. ✅ DISP complete before TILE that uses its data

### Allowed Flexibility
1. ✅ FETCH left and FETCH right can be in any order
2. ✅ Multiple DISP left from one FETCH left
3. ✅ Multiple DISP right from one FETCH right
4. ✅ Asymmetric DISP patterns (e.g., 1 left, 128 right)
5. ✅ TILE can reuse previous DISP results if not overwritten

---

## Typical Patterns

### Pattern A: Balanced Matrix (B=C)
```
FETCH left, FETCH right
FOR i = 0 to N-1:
    DISP left i, WAIT_DISP
    DISP right i, WAIT_DISP
    TILE i, WAIT_TILE
```

### Pattern B: Row Vector (B=1, C=128)
```
FETCH left, FETCH right
DISP left 1, WAIT_DISP
FOR col = 0 to 127:
    DISP right col, WAIT_DISP
    TILE col, WAIT_TILE
```

### Pattern C: Column Vector (B=128, C=1)
```
FETCH left, FETCH right
DISP right 1, WAIT_DISP
FOR row = 0 to 127:
    DISP left row, WAIT_DISP
    TILE row, WAIT_TILE
```

---

## Summary of Changes from Original Documentation

### ❌ Old (Incorrect)
```
FETCH left → FETCH right → DISP left + DISP right → TILE
(Assumed DISP happens in pairs)
```

### ✅ New (Correct)
```
FETCH left → DISP left → WAIT_DISP → 
FETCH right → DISP right → WAIT_DISP → 
TILE → WAIT_TILE

With flexibility for:
- Multiple DISPs per FETCH
- Asymmetric left/right DISP counts
- FETCH ordering flexibility
```

**Key Insight**: DISP is NOT a simple format conversion step - it's a **selective extraction** that enables multi-tile processing from a single FETCH.

---

**References**:
- MS2.0_uCode-Single_Tile.csv: Official microcode format
- master_control.sv: Command processing FSM
- dispatcher_control.sv: FETCH/DISP implementation
- compute_engine_modular.sv: TILE execution

