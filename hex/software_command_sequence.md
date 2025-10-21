# Software Multi-Tile Command Sequencing for MS2.0 GEMM Engine

**Last Updated**: October 15, 2025  
**Status**: Multi-tile software orchestration documentation

---

## Overview

The MS2.0 GEMM engine uses a **clean separation** between hardware and software responsibilities for multi-tile matrix multiplication:

- **Hardware**: Provides a simple, stateless B×C matmul primitive
- **Software**: Orchestrates multiple TILE commands to implement multi-tile operations
- **Result**: Flexible, scalable matrix multiplication without hardware complexity

---

## Hardware's View: Simple B×C Matmul Primitive

### Single TILE Command Behavior

The hardware receives **one TILE command** with parameters:
- `left_addr`, `right_addr`: BRAM addresses for matrix data
- `B`, `C`, `V`: Matrix dimensions and V-loop depth

**Hardware execution**:
1. Reads B×V Native Vectors from left BRAM (starting at `left_addr`)
2. Reads C×V Native Vectors from right BRAM (starting at `right_addr`)  
3. Computes B×C matrix multiplication with V-loop accumulation
4. Outputs **B×C FP16 results** as a **flat 1D stream**

**Key insight**: Hardware is **completely agnostic** to multi-tile concepts. It just performs one B×C matmul per command.

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

### 4D Tensor Structure

For a given (B, C, V) configuration, the logical result structure is:
```
[num_left_tile, num_right_tile, B, C]
```

Where:
- `num_left_tile = 128 / (B×V)` - Number of left tile groups
- `num_right_tile = 128 / (C×V)` - Number of right tile groups  
- `B`, `C` - Actual matrix dimensions per tile

### Multi-Tile Command Sequence

Software issues **multiple sequential TILE commands** to cover all tile combinations:

```
FOR left_tile_idx = 0 to num_left_tile-1:
    FOR right_tile_idx = 0 to num_right_tile-1:
        left_addr = (left_tile_idx * B * V) * 4
        right_addr = (right_tile_idx * C * V) * 4
        Issue TILE command with (left_addr, right_addr, B, C, V)
        Collect B×C results from hardware
        Append to flat result array
```

### Result Assembly

Software collects results from each TILE command and assembles them into the 4D tensor:
- Each TILE produces B×C results
- Total results = `num_left_tile × num_right_tile × B × C`
- Hardware delivers as flat 1D stream
- Software interprets as 4D tensor based on tile ordering

---

## Concrete Example: B=2, C=1, V=32

### Configuration Analysis

- `num_left_tile = 128 / (2×32) = 128 / 64 = 2`
- `num_right_tile = 128 / (1×32) = 128 / 32 = 4`
- **Total tiles**: 2 × 4 = 8 tiles
- **Total results**: 8 tiles × 2 results/tile = 16 FP16 values

### Command Sequence

| Tile | left_tile | right_tile | left_addr | right_addr | Results |
|------|-----------|------------|-----------|------------|---------|
| 0 | 0 | 0 | 0 | 0 | 2 results |
| 1 | 0 | 1 | 0 | 128 | 2 results |
| 2 | 0 | 2 | 0 | 256 | 2 results |
| 3 | 0 | 3 | 0 | 384 | 2 results |
| 4 | 1 | 0 | 256 | 0 | 2 results |
| 5 | 1 | 1 | 256 | 128 | 2 results |
| 6 | 1 | 2 | 256 | 256 | 2 results |
| 7 | 1 | 3 | 256 | 384 | 2 results |

### Hardware Output (Flat 1D Stream)

```
Index 0:  result[0][0][0][0]  (from tile 0)
Index 1:  result[0][0][1][0]  (from tile 0)
Index 2:  result[0][1][0][0]  (from tile 1)
Index 3:  result[0][1][1][0]  (from tile 1)
Index 4:  result[0][2][0][0]  (from tile 2)
Index 5:  result[0][2][1][0]  (from tile 2)
Index 6:  result[0][3][0][0]  (from tile 3)
Index 7:  result[0][3][1][0]  (from tile 3)
Index 8:  result[1][0][0][0]  (from tile 4)
Index 9:  result[1][0][1][0]  (from tile 4)
Index 10: result[1][1][0][0]  (from tile 5)
Index 11: result[1][1][1][0]  (from tile 5)
Index 12: result[1][2][0][0]  (from tile 6)
Index 13: result[1][2][1][0]  (from tile 6)
Index 14: result[1][3][0][0]  (from tile 7)
Index 15: result[1][3][1][0]  (from tile 7)
```

### 4D Tensor Interpretation

When reshaped as `[2, 4, 2, 1]`:
```
result[0][0] = [result[0][0][0][0], result[0][0][1][0]]  # Left tile 0, Right tile 0
result[0][1] = [result[0][1][0][0], result[0][1][1][0]]  # Left tile 0, Right tile 1
result[0][2] = [result[0][2][0][0], result[0][2][1][0]]  # Left tile 0, Right tile 2
result[0][3] = [result[0][3][0][0], result[0][3][1][0]]  # Left tile 0, Right tile 3
result[1][0] = [result[1][0][0][0], result[1][0][1][0]]  # Left tile 1, Right tile 0
result[1][1] = [result[1][1][0][0], result[1][1][1][0]]  # Left tile 1, Right tile 1
result[1][2] = [result[1][2][0][0], result[1][2][1][0]]  # Left tile 1, Right tile 2
result[1][3] = [result[1][3][0][0], result[1][3][1][0]]  # Left tile 1, Right tile 3
```

---

## Memory Layout and Addressing

### BRAM Structure

Each memory block contains:
- **512 lines total** (0-511)
- **128 Native Vectors** (each NV = 128 elements)
- **4 lines per Native Vector** (128 elements ÷ 32 elements/line = 4 lines)

### Address Calculation

For a tile at `(left_tile_idx, right_tile_idx)`:

**Left matrix address**:
```
left_addr = (left_tile_idx * B * V) * 4
```

**Right matrix address**:
```
right_addr = (right_tile_idx * C * V) * 4
```

**Example**: B=2, C=1, V=32
- Left tile 1: `left_addr = (1 * 2 * 32) * 4 = 256`
- Right tile 2: `right_addr = (2 * 1 * 32) * 4 = 256`

### Native Vector Access

Within each tile, Native Vectors are accessed as:
```
nv_idx = addr / 4
nv_line = nv_idx * 4 + group_idx  (where group_idx = 0,1,2,3)
```

---

## Command Sequencing Patterns

### Pattern 1: Sequential Tile Processing

```
FETCH left_block
FETCH right_block
FOR each tile:
    DISP left (tile_addr)
    WAIT_DISP
    DISP right (tile_addr)  
    WAIT_DISP
    TILE (left_addr, right_addr, B, C, V)
    WAIT_TILE
    Collect B×C results
```

### Pattern 2: Optimized (Reuse FETCH)

```
FETCH left_block
FETCH right_block
FOR left_tile_idx = 0 to num_left_tile-1:
    FOR right_tile_idx = 0 to num_right_tile-1:
        TILE (left_addr, right_addr, B, C, V)
        WAIT_TILE
        Collect B×C results
```

---

## Key Benefits

### Hardware Simplicity
- **Stateless**: No multi-tile coordination logic
- **Fast**: Optimized for single B×C matmul
- **Flexible**: Works with any valid (B, C, V) configuration

### Software Control
- **Full orchestration**: Software controls tiling strategy
- **Optimization**: Can optimize for different matrix sizes
- **Scalability**: Same hardware works for any tile count

### Clean Separation
- **Hardware**: "I compute B×C matmul, here are the results"
- **Software**: "I'll call you multiple times with different addresses"
- **Result**: Complex multi-tile operations from simple hardware

---

## References

- **Hardware Command Format**: [COMMAND_SEQUENCE_CORRECTED.md](../gemm/COMMAND_SEQUENCE_CORRECTED.md)
- **Test Data Generation**: [generate_nv_hex.py](generate_nv_hex.py)
- **Golden Reference**: [hardware_gfp_reference.py](hardware_gfp_reference.py)
- **RTL Implementation**: [gfp8_bcv_controller.sv](../gemm/src/rtl/gfp8_bcv_controller.sv)

---

**Maintained by**: Claude Code (claude.ai/code)  
**Project**: Elastix GEMM Engine - MS2.0 Multi-Tile Software Orchestration

