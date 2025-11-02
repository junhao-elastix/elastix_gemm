# Software Multi-Tile Command Sequencing for MS2.0 GEMM Engine

**Last Updated**: November 1, 2025
**Status**: Multi-tile software orchestration documentation - CORRECTED with actual hardware interface

---

## Overview

The MS2.0 GEMM engine uses a **clean separation** between hardware and software responsibilities for multi-tile matrix multiplication:

- **Hardware**: Provides a generic, address-agnostic matmul primitive
- **Software**: Has **full control** over what data to process via arbitrary addresses and lengths
- **Result**: Maximum flexibility - software orchestrates any tiling pattern

---

## Command Types (from MS2.0_uCode-Single_Tile.csv)

| Opcode | Name | Purpose | Payload |
|--------|------|---------|---------|
| `0xF0` | **FETCH** | Load 128x128 memory block from GDDR6 | addr, len |
| `0xF1` | **DISP** | Extract BxV (left) or CxV (right) portion to BRAM (current forced to be 128x128) | addr, len, flags |
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
- **FETCH** + **DISP** + **WAIT_DISP**: Always together, never separated
- **TILE** + **WAIT_TILE**: Always together, never separated

### Rule 3: FETCH Happens Once
- One FETCH per 128x128 memory block to left or right
- TILE needs both left and right to be fetched and dispatched before it can be executed

### Rule 4: Independent Left/Right
- Left and right matrices have independent FETCH/DISP sequences
- FETCH left + DISP left and FETCH right + DISP right don't need to be symmetric

### Rule 5: Can issue multiple TILE in a row
- TILE + WAIT_TILE can be issued in a row without FETCH + DISP + WAIT_DISP

---

## Hardware's View: Generic Address-Based Matmul Primitive

### Actual Hardware Command Interface

```cpp
uint8_t tile(uint16_t leftAddr, uint16_t rightAddr,
             uint8_t leftUgdLen, uint8_t rightUgdLen, uint8_t vecLen,
             bool leftMan4b = false, bool rightMan4b = false,
             bool mainLoopOverLeft = true, uint32_t col_en = 0x0001);
```

**Hardware parameters**:
- `leftAddr`, `rightAddr`: BRAM line addresses (can be **any** valid address)
- `leftUgdLen`: Number of lines to read from left BRAM (ugd = "upgrade", historical naming)
- `rightUgdLen`: Number of lines to read from right BRAM
- `vecLen`: V-loop depth (Native Vector accumulation count)

**Hardware execution**:
1. Reads `leftUgdLen` lines from BRAM starting at `leftAddr`
2. Reads `rightUgdLen` lines from BRAM starting at `rightAddr`
3. Computes matrix multiplication with `vecLen`-deep V-loop accumulation
4. Outputs FP16 results as a **flat 1D stream**

**Key insights**:
- Hardware is **completely agnostic** to multi-tile concepts
- Software has **full control** over addressing and data selection
- One side may advance faster than the other (asymmetric strides allowed)
- No restrictions on tile patterns - software decides everything

### Result Output Format

Hardware outputs results in **row-major order**:
```
result[0][0], result[0][1], ..., result[0][C-1],
result[1][0], result[1][1], ..., result[1][C-1],
...
result[B-1][0], result[B-1][1], ..., result[B-1][C-1]
```

**Example**: B=2, C=1 produces 2 results: `[result[0][0], result[1][0]]`

---

## Software's View: Multi-Tile Orchestration

### Complete Addressing Freedom

**CRITICAL INSIGHT**: Hardware is completely address-agnostic. Software has **absolute freedom** to:
- Start from **any valid BRAM address** (0-2047 lines)
- Read **any valid length** (1-128 Native Vectors per side)
- Use **any V-loop depth** (1-128)
- Issue commands in **any order**

The hardware is a **generic matmul primitive** - it doesn't know or care about "tiles", "grid patterns", or "sequential processing". It only executes:
```
matmul(leftAddr, rightAddr, leftLen, rightLen, vecLen) → results
```

### Test Case Pattern (Sequential Tiling)

For **systematic testing**, we use a sequential tiling pattern based on available data:

**Bottleneck Principle** (determines how many tiles we can compute):
```python
# Given 128 Native Vectors total in reference matrices
max_left_tiles = 128 // (B × V)   # How many left chunks available
max_right_tiles = 128 // (C × V)  # How many right chunks available
num_tiles = min(max_left_tiles, max_right_tiles)  # Limited by bottleneck
```

**Sequential addressing pattern**:
```python
left_stride = (B × V) × 4   # Lines per left tile
right_stride = (C × V) × 4  # Lines per right tile

FOR tile_idx = 0 to num_tiles-1:
    left_addr = tile_idx × left_stride
    right_addr = tile_idx × right_stride
    TILE(left_addr, right_addr, B, C, V)
    # Produces B×C results
```

**Key points**:
- This is **our test pattern choice**, not a hardware requirement
- Both sides advance together (lockstep) with potentially different strides
- We stop when the limiting side runs out of data (bottleneck principle)
- In production, you can use **any addressing pattern you want**

### Test Case Examples (Bottleneck Principle)

**Example 1: Symmetric** (B=2, C=2, V=32):
```
max_left_tiles  = 128 / (2×32) = 2
max_right_tiles = 128 / (2×32) = 2
num_tiles = min(2, 2) = 2 tiles
total_results = 2 × (2×2) = 8 results ✓
```

**Example 2: Asymmetric - right bottleneck** (B=2, C=4, V=16):
```
max_left_tiles  = 128 / (2×16) = 4
max_right_tiles = 128 / (4×16) = 2  ← bottleneck
num_tiles = min(4, 2) = 2 tiles
total_results = 2 × (2×4) = 16 results ✓
```

**Example 3: Maximum tiles** (B=1, C=1, V=1):
```
max_left_tiles  = 128 / (1×1) = 128
max_right_tiles = 128 / (1×1) = 128
num_tiles = min(128, 128) = 128 tiles
total_results = 128 × (1×1) = 128 results ✓
```

### Result Assembly

Software collects results from each TILE command:
- Each TILE produces `B × C` results (where B,C derived from ugd_len parameters)
- Total results = `num_tiles × (B × C)`
- Hardware delivers as flat 1D stream
- Software interprets structure based on chosen tiling pattern

---

## Concrete Example: Simple Tiling Test Case

### Configuration

Testing parameters:
- `B=2, C=1, V=32` (2×1 output per tile, 32 Native Vectors accumulated)
- Left matrix: Uses `B*V = 2*32 = 64` Native Vectors per tile
- Right matrix: Uses `C*V = 1*32 = 32` Native Vectors per tile

Available BRAM:
- 128 Native Vectors total (512 lines @ 4 lines/NV)
- Can fit 2 left chunks (64 NVs each = 128 total)
- Can fit 4 right chunks (32 NVs each = 128 total)

**Bottleneck principle**:
```
max_left_tiles  = 128 / (2*32) = 2
max_right_tiles = 128 / (1*32) = 4
num_tiles = min(2, 4) = 2 (left is bottleneck)
```

**Lockstep advancement strategy**:
```
left_stride  = (2 * 32) * 4 = 256 lines
right_stride = (1 * 32) * 4 = 128 lines
Both sides advance together, stop when left runs out
```

### Actual Hardware Commands (Corrected with Bottleneck Principle)

**Configuration**: B=2, C=1, V=32

**Bottleneck calculation**:
```
max_left_tiles  = 128 / (2×32) = 2
max_right_tiles = 128 / (1×32) = 4
num_tiles = min(2, 4) = 2 tiles (left is bottleneck!)
```

**Lockstep addressing**:
```
left_stride  = (2×32) × 4 = 256 lines
right_stride = (1×32) × 4 = 128 lines
```

| Tile | left_addr | right_addr | leftUgdLen | rightUgdLen | vecLen | Results |
|------|-----------|------------|------------|-------------|--------|---------|
| 0 | 0×256=0 | 0×128=0 | 2 | 1 | 32 | 2 results |
| 1 | 1×256=256 | 1×128=128 | 2 | 1 | 32 | 2 results |

**Note**:
- Both sides advance together (lockstep)
- Left runs out after 2 tiles (bottleneck)
- Right has 4 tiles available but only 2 are used

### Hardware Output (Flat 1D Stream)

```
Index 0-1: result from tile 0 (left @ addr 0, right @ addr 0)
Index 2-3: result from tile 1 (left @ addr 256, right @ addr 128)
```

**Total**: 4 FP16 values (2 tiles × 2 results/tile)

---

## Memory Layout and Addressing

### BRAM Structure

Dispatcher BRAM holds pre-fetched matrix data:
- **128 Native Vectors capacity** (each NV = 4 lines)
- **Line address units**: Hardware addresses are in BRAM line units (0-512)

**Native Vector to Line mapping**:
```
NV_0:  lines 0-3    (4 lines, one per group: exp + 32 mantissas each)
NV_1:  lines 4-7
NV_2:  lines 8-11
...
NV_127: lines 508-511
```

### Address Calculation for Tiles

**Software controls addressing** - hardware just reads lines starting at given address:

```cpp
// For a tile processing B Native Vectors from left, C from right, V-deep accumulation:
left_addr = nv_start_left * 4;           // Convert NV index to line address
right_addr = nv_start_right * 4;         // Convert NV index to line address
leftUgdLen = B;                          // Read B Native Vectors (B*4 lines)
rightUgdLen = C;                         // Read C Native Vectors (C*4 lines)
vecLen = V;                              // V-loop accumulation depth
```

---

## References

- **Hardware Interface**: [vp815_gemm_device.hpp](../gemm/sw_test/vp815_gemm_device.hpp) - Actual command API
- **Test Data Generation**: [generate_nv_hex.py](generate_nv_hex.py)
- **Golden Reference**: [hardware_gfp_reference.py](hardware_gfp_reference.py)
- **RTL Implementation**: [gfp8_bcv_controller.sv](../gemm/src/rtl/gfp8_bcv_controller.sv)
- **Compute Engine**: [compute_engine_modular.sv](../gemm/src/rtl/compute_engine_modular.sv)

---

**Maintained by**: Claude Code (claude.ai/code)
**Project**: Elastix GEMM Engine - MS2.0 Multi-Tile Software Orchestration
**Last Updated**: November 1, 2025 - Corrected to reflect actual hardware interface

