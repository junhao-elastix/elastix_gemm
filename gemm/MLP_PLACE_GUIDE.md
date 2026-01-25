# MLP and BRAM Placement Guide

## Overview

This document describes the placement strategy for MLP (Machine Learning Processor) and BRAM (Block RAM) resources on the Achronix Speedster7t FPGA, based on analysis of the `acx_gemm_ref_design` tensor core reference design.

## BMLP Block Architecture

The Speedster7t FPGA organizes MLPs and BRAMs into **BMLP blocks**. Each BMLP block contains:
- Multiple MLP units (ACX_MLP72)
- Multiple BRAM units (ACX_BRAM72K)
- Co-located for optimal data flow between computation and storage

### BMLP Coordinate System

BMLP blocks are addressed using a 2D coordinate system:
```
x_core.BMLP[x][y].logic.bmlp.mlp[n]   - MLP at BMLP block (x,y), unit n
x_core.BMLP[x][y].logic.bmlp.bram[n]  - BRAM at BMLP block (x,y), unit n
```

Where:
- **x**: Horizontal BMLP column index (observed range: 0-18 in west half, 20-38 in east half)
- **y**: Vertical BMLP row index (observed values: 0, 4, 8, 12, 16, 20, 24, 28 - increments of 4)
- **n**: Unit index within the BMLP block (typically 0)

## RTL Architecture Hierarchy

The tensor core reference design follows this hierarchy for matrix computation:

```
tc_ref_design_top.sv
 |
 +-- tc_quad.sv (4 quadrants: Q0=SW, Q1=NW, Q2=NE, Q3=SE)
      |
      +-- tc_core.sv (16 Tensor Cores per quadrant = 64 total)
           |
           +-- engine.sv (instantiated as "i_matrix_mult_fp" - note confusing naming!)
                |
                +-- stack.sv (4 parallel stacks, instantiated as "stack_X__u_stack")
                     |
                     +-- stack_stage_fp.sv (8 cascaded MLPs, instantiated as "stage_X__u_stack_stage_fp")
                     |    |
                     |    +-- ACX_MLP72 (instantiated as "u_acx_mlp72")
                     |
                     +-- weight_bram.sv (ACX_BRAM72K for B matrix)
```

> **Note:** In `tc_core.sv`, the `engine` module is instantiated with the name `i_matrix_mult_fp`. This naming can be confusing since there is also a separate `matrix_mult_fp.sv` file with a different architecture. The PDC placement paths follow the instance names, hence paths like `i_matrix_mult_fp.stack_0__u_stack`.

### Key Parameters

| Parameter | Value | Description |
|-----------|-------|-------------|
| `num_mlp` | 8 | MLPs per stack (cascaded vertically) |
| `num_stacks` | 4 | Parallel stacks per engine |
| `TC_PER_QUAD` | 16 | Tensor Cores per quadrant |
| `NUM_TC_QUAD` | 4 | Number of quadrants |

**Total MLP count:** 4 quadrants x 16 TCs x 4 stacks x 8 MLPs = **2048 MLPs**
**Explicitly placed:** 256 MLP/BRAM pairs (first stage of each stack)

## Placement Strategy

### Co-location Principle

MLPs and their associated weight BRAMs are placed at the **same BMLP block** for optimal data path:

```tcl
# MLP placement
set_placement -fixed -batch {i:..stack_0__u_stack.stage_0__u_stack_stage_fp.u_acx_mlp72} {s:x_core.BMLP[0][0].logic.bmlp.mlp[0]}

# Weight BRAM placement (same BMLP block)
set_placement -fixed -batch {i:..stack_0__u_stack.u_weight_bram...ACX_BRAM72K_single} {s:x_core.BMLP[0][0].logic.bmlp.bram[0]}
```

### Cascading Within Stack

Only **stage_0** (first MLP in each stack) is explicitly placed. The remaining 7 MLPs in the cascade are automatically placed by the tool due to their cascading connections:

```
stack_stage_fp[0] -> stage_0 (EXPLICITLY PLACED at BMLP[x][y])
    |
    v (cascade: a_d, b, results flow down)
stack_stage_fp[1] -> stage_1 (auto-placed)
    |
    v
...
stack_stage_fp[7] -> stage_7 (auto-placed)
```

### Quadrant-Based Distribution

Each quadrant's 16 Tensor Cores have their 4 stacks mapped to consecutive BMLP x-coordinates:

**Quadrant 0 (SW) - BMLP y=0 and y=4:**
```
TC 0:  stacks 0-3 -> BMLP[0][0], BMLP[1][0], BMLP[2][0], BMLP[3][0]
TC 1:  stacks 0-3 -> BMLP[5][0], BMLP[6][0], BMLP[7][0], BMLP[8][0]
TC 2:  stacks 0-3 -> BMLP[10][0], BMLP[11][0], BMLP[12][0], BMLP[13][0]
TC 3:  stacks 0-3 -> BMLP[15][0], BMLP[16][0], BMLP[17][0], BMLP[18][0]
TC 4:  stacks 0-3 -> BMLP[0][4], BMLP[1][4], BMLP[2][4], BMLP[3][4]
...
```

**Pattern Observations:**
- Each TC uses 4 consecutive x-coordinates for its 4 stacks
- TCs are grouped in blocks of 4, with 1 x-coordinate gap between groups
- y-coordinate increments by 4 for every 4 TCs (rows of TCs)

### Quadrant BMLP Regions

| Quadrant | BMLP X Range | BMLP Y Values | Physical Location |
|----------|-------------|---------------|-------------------|
| Q0 (SW) | 0-18 | 0, 4, 8, 12 (ascending) | Southwest |
| Q1 (NW) | 0-18 | 28, 24, 20, 16 (descending) | Northwest |
| Q2 (NE) | 20-38 | 28, 24, 20, 16 (descending) | Northeast |
| Q3 (SE) | 20-38 | 0, 4, 8, 12 (ascending) | Southeast |

> **Note:** North quadrants (NW, NE) use descending y-values starting from y=28 at TC row 0, while south quadrants (SW, SE) use ascending y-values starting from y=0. East-side quadrants (NE, SE) use x=20-38 with TCs placed in decreasing x order (TC0 at highest x).

## PDC Syntax Reference

### Fixed Placement Commands

```tcl
# Basic syntax
set_placement -fixed -batch {i:<hierarchical_instance_path>} {s:x_core.BMLP[x][y].logic.bmlp.<type>[n]}

# Where:
#   -fixed   : Prevents the placer from moving this instance
#   -batch   : Processes placement in batch mode for efficiency
#   i:       : Instance path prefix
#   s:       : Site path prefix
#   <type>   : Either 'mlp' or 'bram'
#   [n]      : Unit index within the BMLP block
```

### Example Placements from ace_placements.pdc.4q

```tcl
# Quadrant 0, TC 0, Stack 0 - MLP at BMLP[0][0]
set_placement -fixed -batch {i:tc_gen_quad_0__i_tc_quad.tc_gen_noc_0__i_tc_core.i_matrix_mult_fp.stack_0__u_stack.stage_0__u_stack_stage_fp.u_acx_mlp72} {s:x_core.BMLP[0][0].logic.bmlp.mlp[0]}

# Quadrant 0, TC 0, Stack 0 - Weight BRAM at BMLP[0][0]
set_placement -fixed -batch {i:tc_gen_quad_0__i_tc_quad.tc_gen_noc_0__i_tc_core.i_matrix_mult_fp.stack_0__u_stack.u_weight_bram.x_bram.stack_brams_0__u_bram_u_bram_u_bram_acx_bram72k_U_ACX_BRAM72K_single} {s:x_core.BMLP[0][0].logic.bmlp.bram[0]}

# Quadrant 0, TC 0, Stack 1 - MLP at BMLP[1][0]
set_placement -fixed -batch {i:tc_gen_quad_0__i_tc_quad.tc_gen_noc_0__i_tc_core.i_matrix_mult_fp.stack_1__u_stack.stage_0__u_stack_stage_fp.u_acx_mlp72} {s:x_core.BMLP[1][0].logic.bmlp.mlp[0]}

# Quadrant 0, TC 1, Stack 0 - MLP at BMLP[5][0] (gap of 1 x-coordinate)
set_placement -fixed -batch {i:tc_gen_quad_0__i_tc_quad.tc_gen_noc_1__i_tc_core.i_matrix_mult_fp.stack_0__u_stack.stage_0__u_stack_stage_fp.u_acx_mlp72} {s:x_core.BMLP[5][0].logic.bmlp.mlp[0]}
```

## GDDR6 Reference Design Note

The `gddr_ref_design` does **NOT** include MLP or BRAM placements as it is a pure memory test design. The placement file contains only:
- NAP placements for GDDR6 interfaces
- Soft placement regions for NAP-related logic

Example from gddr_ref_design (no MLP/BRAM):
```tcl
# Example of how to fix the location of an MLP and a BRAM
# set_placement -fixed {i:<my_hierarchical_path>.i_bram} {s:x_core.BMLP[29][5].logic.bmlp.bram[0]}
# set_placement -fixed {i:<my_hierarchical_path>.i_mlp}  {s:x_core.BMLP[29][5].logic.bmlp.mlp[0]}
```

This commented example suggests BMLP[29][5] as a possible placement location.

## Placement Guidelines

### 1. Co-locate MLP and Weight BRAM
Always place the weight BRAM at the same BMLP block as its associated MLP to minimize routing delay:
```tcl
set_placement -fixed {i:..u_mlp}  {s:x_core.BMLP[x][y].logic.bmlp.mlp[0]}
set_placement -fixed {i:..u_bram} {s:x_core.BMLP[x][y].logic.bmlp.bram[0]}
```

### 2. Place Only Cascade Entry Points
When using cascaded MLPs (like in stack_stage_fp), only place the first stage. The cascade connection will guide automatic placement of subsequent stages.

### 3. Align with NAP Proximity
Place MLPs near their associated NAPs to minimize data transfer latency:
- West-side MLPs (BMLP x = 0-18) for west NAPs (columns 1-5)
- East-side MLPs (BMLP x = 20-38) for east NAPs (columns 6-10)

### 4. Use Consistent Y-Coordinate Spacing
The reference design uses y-coordinate increments of 4 (0, 4, 8, 12, ...). This appears to align with physical BMLP row boundaries.

### 5. Leave Gaps Between TC Groups
The reference design leaves a 1 x-coordinate gap between TC stack groups (e.g., TC0 uses x=0-3, TC1 uses x=5-8). This may help with routing congestion.

## Related Documents

- [GDDR6_NAP_GUIDE.md](GDDR6_NAP_GUIDE.md) - NAP placement and GDDR6 target ID mapping
- [Speedster7t Component Library User Guide (UG086)](https://www.achronix.com/documentation/speedster7t-component-library-user-guide-ug086) - ACX_MLP72 and ACX_BRAM72K documentation

## Document History

| Date | Version | Description |
|------|---------|-------------|
| 2026-01-24 | 1.2 | Fixed RTL hierarchy: tc_core.sv instantiates engine.sv (not matrix_mult_fp.sv) as "i_matrix_mult_fp" - verified against actual PDC paths |
| 2026-01-24 | 1.1 | Corrected Quadrant BMLP Regions table: fixed east-side x-range (20-38, not 50-68), added ascending/descending notation for y-values |
| 2026-01-24 | 1.0 | Initial documentation of MLP and BRAM placement from acx_gemm_ref_design analysis |
