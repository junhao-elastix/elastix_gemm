# GDDR6 NAP Placement and Target ID Guide

## Overview

This document describes the mapping between NAP (Network Access Point) locations and GDDR6 memory channels on the Achronix Speedster7t FPGA (AC7t1400/AC7t1500). Understanding this mapping is essential for optimal memory bandwidth and latency when designing systems that access GDDR6 via the 2D NoC.

## Speedster7t GDDR6 Architecture

The Speedster7t device has:
- **8 GDDR6 controllers**: GDDR0 through GDDR7
- **2 channels per controller**: CH0 and CH1
- **16 total GDDR6 channels** accessible via the 2D NoC
- **GDDR0-3** located on the **West side** of the device
- **GDDR4-7** located on the **East side** of the device

## GDDR6 Target ID Table

Each GDDR6 channel is addressed using a 9-bit NOC Target ID embedded in the AXI address. The upper 4 bits (address bits [36:33]) contain the Control ID.

| GDDR6 Controller | Channel | Control ID (Binary) | Control ID (Decimal) | 9-bit NOC Target ID |
|------------------|---------|---------------------|----------------------|---------------------|
| GDDR0 | CH0 | 4'b1100 | 12 | 9'd12 |
| GDDR0 | CH1 | 4'b1101 | 13 | 9'd13 |
| GDDR1 | CH0 | 4'b0100 | 4 | 9'd4 |
| GDDR1 | CH1 | 4'b0101 | 5 | 9'd5 |
| GDDR2 | CH0 | 4'b0000 | 0 | 9'd0 |
| GDDR2 | CH1 | 4'b0001 | 1 | 9'd1 |
| GDDR3 | CH0 | 4'b1000 | 8 | 9'd8 |
| GDDR3 | CH1 | 4'b1001 | 9 | 9'd9 |
| GDDR4 | CH0 | 4'b1111 | 15 | 9'd15 |
| GDDR4 | CH1 | 4'b1110 | 14 | 9'd14 |
| GDDR5 | CH0 | 4'b0111 | 7 | 9'd7 |
| GDDR5 | CH1 | 4'b0110 | 6 | 9'd6 |
| GDDR6 | CH0 | 4'b0011 | 3 | 9'd3 |
| GDDR6 | CH1 | 4'b0010 | 2 | 9'd2 |
| GDDR7 | CH0 | 4'b1011 | 11 | 9'd11 |
| GDDR7 | CH1 | 4'b1010 | 10 | 9'd10 |

### Channel Addressing Note

- **West-side GDDR (0-3)**: Uses **odd** target IDs for CH1
- **East-side GDDR (4-7)**: Uses **even** target IDs for CH1

## Physical Layout

The 2D NoC uses a row/column coordinate system for NAP placement:
- **Columns 1-5**: West side of device (closer to GDDR0-3)
- **Columns 6-10**: East side of device (closer to GDDR4-7)
- **Rows 1-8**: Vertical position within the fabric

**Sources:**
- NAP Row range (1–8) and Column range (1–10): Speedster7t Soft IP User Guide (UG103), "Device Manager" chapter, Configuration section
- GDDR0-3 on West side, GDDR4-7 on East side: Speedster7t GDDR6 Reference Design Guide (RD017)

```
Device Layout (Speedster7t AC7t1500):

         WEST SIDE                              EAST SIDE
         (GDDR0-3)                              (GDDR4-7)
         
         Col:  1    2    4    5         6    7    9   10
Row 8:       [1,8][2,8][4,8][5,8] ... [6,8][7,8][9,8][10,8]
Row 7:       [1,7][2,7][4,7][5,7] ... [6,7][7,7][9,7][10,7]
Row 6:       [1,6][2,6][4,6][5,6] ... [6,6][7,6][9,6][10,6]
Row 5:       [1,5][2,5][4,5][5,5] ... [6,5][7,5][9,5][10,5]
Row 4:       [1,4][2,4][4,4][5,4] ... [6,4][7,4][9,4][10,4]
Row 3:       [1,3][2,3][4,3][5,3] ... [6,3][7,3][9,3][10,3]
Row 2:       [1,2][2,2][4,2][5,2] ... [6,2][7,2][9,2][10,2]
Row 1:       [1,1][2,1][4,1][5,1] ... [6,1][7,1][9,1][10,1]
```

> **Note:** This diagram is **inferred** from PDC placement patterns observed in the tensor core reference design (`ace_placements.pdc.4q`). The division between west-side columns (1-5) and east-side columns (6-10) is approximate. The actual physical floorplan and optimal column boundaries may differ. Consult official Achronix floorplan documentation for precise device layout.

## Optimal Placement Guidelines

### Key Principle

> **"The NAP locations should be chosen to be adjacent to the target GDDR6 subsystem on the east or west side of the FPGA depending on which side is closest to the target GDDR6 subsystem. The locality should be selected to reduce latency between the NAP and the GDDR6 controller."**
> — Speedster7t GDDR6 Reference Design Guide (RD017)

### Placement Rules

1. **West-side NAPs (Columns 1-5)** should target:
   - GDDR0 (Target IDs 12, 13)
   - GDDR1 (Target IDs 4, 5)
   - GDDR2 (Target IDs 0, 1)
   - GDDR3 (Target IDs 8, 9)

2. **East-side NAPs (Columns 6-10)** should target:
   - GDDR4 (Target IDs 15, 14)
   - GDDR5 (Target IDs 7, 6)
   - GDDR6 (Target IDs 3, 2)
   - GDDR7 (Target IDs 11, 10)

### Latency Considerations

- Transactions from a NAP travel **east or west** along the row until reaching the peripheral portion of the 2D NoC
- Shorter distance = lower latency
- Cross-chip traffic (west NAP → east GDDR or vice versa) incurs higher latency

## Example: tc_ref_design Quadrant Mapping

The tensor core reference design uses 4 quadrants with 16 NAPs each, optimally mapped to adjacent GDDR controllers:

| Quadrant | Location | NAP Columns | GDDR_ID_NOC Assignment | Target GDDR Channels |
|----------|----------|-------------|------------------------|----------------------|
| **SW** (quad 0) | Southwest | 1, 2, 4, 5 | {9'd4, 9'd5, 9'd12, 9'd13} | GDDR1 CH0, GDDR1 CH1, GDDR0 CH0, GDDR0 CH1 |
| **NW** (quad 1) | Northwest | 1, 2, 4, 5 | {9'd1, 9'd0, 9'd9, 9'd8} | GDDR2 CH1, GDDR2 CH0, GDDR3 CH1, GDDR3 CH0 |
| **NE** (quad 2) | Northeast | 6, 7, 9, 10 | {9'd2, 9'd3, 9'd10, 9'd11} | GDDR6 CH1, GDDR6 CH0, GDDR7 CH1, GDDR7 CH0 |
| **SE** (quad 3) | Southeast | 6, 7, 9, 10 | {9'd7, 9'd6, 9'd15, 9'd14} | GDDR5 CH0, GDDR5 CH1, GDDR4 CH0, GDDR4 CH1 |

### RTL Example (from tc_ref_design_top.sv)

```systemverilog
// GDDR6 target address ID for each quadrant
// 9th bit (LSB) controls channel selection
localparam [35:0] GDDR_ID_NOC_SW = {9'd4, 9'd5, 9'd12, 9'd13};   // GDDR1 CH0, GDDR1 CH1, GDDR0 CH0, GDDR0 CH1
localparam [35:0] GDDR_ID_NOC_NW = {9'd1, 9'd0, 9'd9, 9'd8};     // GDDR2 CH1, GDDR2 CH0, GDDR3 CH1, GDDR3 CH0
localparam [35:0] GDDR_ID_NOC_NE = {9'd2, 9'd3, 9'd10, 9'd11};   // GDDR6 CH1, GDDR6 CH0, GDDR7 CH1, GDDR7 CH0
localparam [35:0] GDDR_ID_NOC_SE = {9'd7, 9'd6, 9'd15, 9'd14};   // GDDR5 CH0, GDDR5 CH1, GDDR4 CH0, GDDR4 CH1

// Concatenate for parameter passing to quadrants
localparam [143:0] GDDR_ID_NOC = {GDDR_ID_NOC_SE, GDDR_ID_NOC_NE, GDDR_ID_NOC_NW, GDDR_ID_NOC_SW};
```

### PDC Placement Example (from ace_placements.pdc)

```tcl
# Southwest quadrant - uses west-side NAPs (columns 1-5)
set_placement -fixed [find -insts {tc_gen_quad_0__i_tc_quad.tc_gen_noc_0__i_axi_slave_wrapper.i_axi_slave}] {s:x_core.NOC[1][1].logic.noc.nap_s}

# Northeast quadrant - uses east-side NAPs (columns 6-10)
set_placement -fixed [find -insts {tc_gen_quad_2__i_tc_quad.tc_gen_noc_0__i_axi_slave_wrapper.i_axi_slave}] {s:x_core.NOC[10][8].logic.noc.nap_s}
```

## Address Construction

The NoC address format for GDDR6 access:

```
Bit Position: [41:37] [36:33]      [32:0]
              ┌─────┬──────────┬────────────┐
              │Rsvd │Target ID │Memory Addr │
              └─────┴──────────┴────────────┘
```

The `get_tgt_addr_id` function in `tc_core.sv` extracts the appropriate 9-bit target ID based on a 2-bit channel mapping input:

```systemverilog
function automatic [8:0] get_tgt_addr_id(
    input [1:0] i_tc_chmap,
    input [35:0] gddr_tgt_id
);
    case (i_tc_chmap)
        2'd0: get_tgt_addr_id = gddr_tgt_id[8:0];
        2'd1: get_tgt_addr_id = gddr_tgt_id[17:9];
        2'd2: get_tgt_addr_id = gddr_tgt_id[26:18];
        2'd3: get_tgt_addr_id = gddr_tgt_id[35:27];
    endcase
endfunction
```

## Elastix GEMM 2D Engine - Actual Hardware Mapping

This section documents the actual NAP-to-GDDR6 mapping implemented in the elastix_gemm 2D engine. Use this as a reference for debugging or optimization.

### Configuration Sources

The mapping is defined across three files that must stay synchronized:

| Configuration | File | Key Lines |
|---------------|------|-----------|
| GDDR6 Control IDs | `src/rtl/engine_top_2d.sv` | Lines 82-91: `GDDR6_CTRL_ID[0:15]` |
| NAP Placement (RTL) | `src/rtl/elastix_gemm_top.sv` | Lines 512-513: `NAP_COL[0:15]`, `NAP_ROW[0:15]` |
| NAP Placement (PDC) | `src/constraints/ace_placements.pdc` | Lines 51-113: `gen_gddr_nap_*` placements |

### Connection Chain

```
engine_top_2d                      elastix_gemm_top                    ace_placements.pdc
─────────────                      ────────────────                    ──────────────────
gen_row[r]:                        gen_gddr_nap[r]:
  GDDR6_CTRL_ID[r]                   NAP_COL[r], NAP_ROW[r]            gen_gddr_nap_[r]
  axi_ddr_if[r]      ←────────────→  gddr_nap_if[r]      ←──────────→  NOC[col][row]
```

### Complete Row-to-GDDR6 Mapping Table

**NOTE:** NoC rows 9-10 do NOT exist on the AC7t1500 device. Valid NoC rows are 1-8.

**OPTIMIZATION (Jan 2026):** NAPs moved to columns 1 (west) and 10 (east) for minimum latency to GDDR controllers. See RD017 "NAP Locations" section.

| Row Index | GDDR6_CTRL_ID | Target GDDR | NAP Column | NAP Row | NOC Location | Side |
|-----------|---------------|-------------|------------|---------|--------------|------|
| 0 | 0xC (12) | GDDR0 CH0 | 1 | 1 | NOC[1][1] | West |
| 1 | 0xD (13) | GDDR0 CH1 | 1 | 2 | NOC[1][2] | West |
| 2 | 0x4 (4) | GDDR1 CH0 | 1 | 3 | NOC[1][3] | West |
| 3 | 0x5 (5) | GDDR1 CH1 | 1 | 4 | NOC[1][4] | West |
| 4 | 0x0 (0) | GDDR2 CH0 | 1 | 5 | NOC[1][5] | West |
| 5 | 0x1 (1) | GDDR2 CH1 | 1 | 6 | NOC[1][6] | West |
| 6 | 0x8 (8) | GDDR3 CH0 | 1 | 7 | NOC[1][7] | West |
| 7 | 0x9 (9) | GDDR3 CH1 | 1 | 8 | NOC[1][8] | West |
| 8 | 0xF (15) | GDDR4 CH0 | 10 | 1 | NOC[10][1] | East |
| 9 | 0xE (14) | GDDR4 CH1 | 10 | 2 | NOC[10][2] | East |
| 10 | 0x7 (7) | GDDR5 CH0 | 10 | 3 | NOC[10][3] | East |
| 11 | 0x6 (6) | GDDR5 CH1 | 10 | 4 | NOC[10][4] | East |
| 12 | 0x3 (3) | GDDR6 CH0 | 10 | 5 | NOC[10][5] | East |
| 13 | 0x2 (2) | GDDR6 CH1 | 10 | 6 | NOC[10][6] | East |
| 14 | 0xB (11) | GDDR7 CH0 | 10 | 7 | NOC[10][7] | East |
| 15 | 0xA (10) | GDDR7 CH1 | 10 | 8 | NOC[10][8] | East |

### RTL Code References

**engine_top_2d.sv - Control ID Array:**
```systemverilog
localparam [8:0] GDDR6_CTRL_ID [0:NUM_ROWS-1] = '{
    9'hC, 9'hD,   // Controller 0: Ch0=0xC, Ch1=0xD (West)
    9'h4, 9'h5,   // Controller 1: Ch0=0x4, Ch1=0x5 (West)
    9'h0, 9'h1,   // Controller 2: Ch0=0x0, Ch1=0x1 (West)
    9'h8, 9'h9,   // Controller 3: Ch0=0x8, Ch1=0x9 (West)
    9'hF, 9'hE,   // Controller 4: Ch0=0xF, Ch1=0xE (East, reversed)
    9'h7, 9'h6,   // Controller 5: Ch0=0x7, Ch1=0x6 (East, reversed)
    9'h3, 9'h2,   // Controller 6: Ch0=0x3, Ch1=0x2 (East, reversed)
    9'hB, 9'hA    // Controller 7: Ch0=0xB, Ch1=0xA (East, reversed)
};
```

**elastix_gemm_top.sv - NAP Placement Arrays:**
```systemverilog
// OPTIMIZATION: Place NAPs closest to target GDDR controllers for lowest latency
//   - West side (rows 0-7): NOC column 1 (closest to west-edge GDDR0-3)
//   - East side (rows 8-15): NOC column 10 (closest to east-edge GDDR4-7)
// Reference: RD017 "NAP Locations" - "adjacent to the target GDDR6 subsystem"
// NOTE: NOC rows 9-10 do NOT exist on AC7t1500 - valid range is 1-8
localparam int NAP_COL [0:15] = '{1, 1, 1, 1, 1, 1, 1, 1, 10, 10, 10, 10, 10, 10, 10, 10};
localparam int NAP_ROW [0:15] = '{1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 8};
```

**fetcher_2d.sv - AXI Address Construction:**
```systemverilog
// Address format: {GDDR6_CTRL_ID[8:0], 2'b00, line_addr[25:0], 5'b00000}
// Bits [41:37] = 0 (reserved), Bits [36:33] = Control ID, Bits [32:0] = Memory address
assign axi_ddr_if.araddr = {GDDR6_CTRL_ID, 2'b00, line_addr_26bit, {5{1'b0}}};
```

### Latency Optimization Status

| Rows | NAP Column | Target GDDR | Optimization | Status |
|------|------------|-------------|--------------|--------|
| 0-7 | 1 (westernmost) | GDDR0-3 (west edge) | Minimum latency | OPTIMAL |
| 8-15 | 10 (easternmost) | GDDR4-7 (east edge) | Minimum latency | OPTIMAL |

### Change History

- **2026-01-25**: Optimized NAP columns for minimum GDDR latency:
  - West: Column 3 -> Column 1 (closest to GDDR0-3)
  - East: Column 8 -> Column 10 (closest to GDDR4-7)
  - Reference: RD017 "NAP locations should be adjacent to target GDDR6 subsystem"
- **2026-01-23**: Fixed invalid NOC row range. Original mapping used rows 3-10, but AC7t1500 only supports NOC rows 1-8.

### Verification Checklist

When modifying the NAP-GDDR6 mapping, verify:

- [ ] `GDDR6_CTRL_ID` array in `engine_top_2d.sv` matches intended GDDR channels
- [ ] `NAP_COL`/`NAP_ROW` arrays in `elastix_gemm_top.sv` match PDC constraints
- [ ] PDC `set_placement` commands in `ace_placements.pdc` use correct NOC coordinates
- [ ] West rows (0-7) target west GDDR (0-3) via west NAPs (column 1 = closest)
- [ ] East rows (8-15) target east GDDR (4-7) via east NAPs (column 10 = closest)
- [ ] All three files use consistent indexing (row index `r` maps to same GDDR channel)
- [ ] MLP/BRAM placements align with NAP locations (west: BMLP x=0-3, east: BMLP x=35-38)

## Reference Design Comparison

This section compares NAP-to-GDDR6 mapping strategies across Achronix reference designs.

### gddr_ref_design (GDDR6 Reference Design)

**Source:** `gddr_ref_design/src/constraints/ace_placements.pdc`

**Purpose:** Simple GDDR6 memory test/validation design with 8 NAP interfaces.

**NAP Placement Pattern:**
- Uses **columns 3 and 8** (closest to GDDR6 controllers)
- Uses **rows 3, 4, 5, 6** (center of device)
- 8 total NAPs (one per GDDR6 controller)

| NAP Index | Column | Rows | Target GDDR | Side |
|-----------|--------|------|-------------|------|
| 0-3 | 3 | 3, 4, 5, 6 | GDDR0-3 | West |
| 4-7 | 8 | 3, 4, 5, 6 | GDDR4-7 | East |

**PDC Pattern:**
```tcl
# Loop places NAPs at columns 3 (west) and 8 (east), rows 3-6
for {set ii 0} {$ii < 8} {incr ii} {
    if {$ii < 4} { set col 3 }  # West-side NAPs
    if {$ii > 3} { set col 8 }  # East-side NAPs
    set_placement -fixed [find -insts "gddr_gen_noc_$ii*i_axi_responder"] "s:x_core.NOC[$col][$row].logic.noc.nap_s"
}
```

**Soft Placement Regions:**
- West regions: x1=55, x2=81 (fabric cluster coordinates)
- East regions: x1=185, x2=212

**Key Observations:**
- Minimal design: 8 NAPs for basic GDDR6 access
- No MLP/BRAM placements (pure memory test design)
- Uses `nap_s` (slave NAP) for memory responder interface
- One `nap_m` (master NAP) at NOC[5][5] for register control

---

### acx_gemm_ref_design (Tensor Core Reference Design)

**Source:** `acx_gemm_ref_design/src/constraints/ace_placements.pdc.4q`

**Purpose:** Full 64-Tensor-Core GEMM accelerator with 4 quadrants.

**NAP Placement Pattern:**
- Uses **columns 1, 2, 4, 5** (west) and **6, 7, 9, 10** (east)
- Uses **all 8 rows** (1-8) per quadrant
- 64 slave NAPs + 64 master NAPs = 128 total NAPs
- Each Tensor Core has its own NAP pair (slave + master)

**Quadrant Layout:**

| Quadrant | Location | NAP Columns | NAP Rows | Target GDDR |
|----------|----------|-------------|----------|-------------|
| Q0 (SW) | Southwest | 1, 2, 4, 5 | 1-4 | GDDR0, GDDR1 |
| Q1 (NW) | Northwest | 1, 2, 4, 5 | 5-8 | GDDR2, GDDR3 |
| Q2 (NE) | Northeast | 6, 7, 9, 10 | 5-8 | GDDR6, GDDR7 |
| Q3 (SE) | Southeast | 6, 7, 9, 10 | 1-4 | GDDR4, GDDR5 |

**NAP Distribution per Quadrant (16 NAPs each):**

```
Quadrant 0 (SW) - Columns 1,2,4,5 x Rows 1-4:
  Row 1: NOC[1][1], NOC[2][1], NOC[4][1], NOC[5][1]  -> TC 0-3
  Row 2: NOC[1][2], NOC[2][2], NOC[4][2], NOC[5][2]  -> TC 4-7
  Row 3: NOC[1][3], NOC[2][3], NOC[4][3], NOC[5][3]  -> TC 8-11
  Row 4: NOC[1][4], NOC[2][4], NOC[4][4], NOC[5][4]  -> TC 12-15

Quadrant 1 (NW) - Columns 1,2,4,5 x Rows 5-8:
  Row 8: NOC[1][8], NOC[2][8], NOC[4][8], NOC[5][8]  -> TC 0-3
  Row 7: NOC[1][7], NOC[2][7], NOC[4][7], NOC[5][7]  -> TC 4-7
  Row 6: NOC[1][6], NOC[2][6], NOC[4][6], NOC[5][6]  -> TC 8-11
  Row 5: NOC[1][5], NOC[2][5], NOC[4][5], NOC[5][5]  -> TC 12-15

Quadrant 2 (NE) - Columns 6,7,9,10 x Rows 5-8:
  Row 8: NOC[10][8], NOC[9][8], NOC[7][8], NOC[6][8] -> TC 0-3
  Row 7: NOC[10][7], NOC[9][7], NOC[7][7], NOC[6][7] -> TC 4-7
  Row 6: NOC[10][6], NOC[9][6], NOC[7][6], NOC[6][6] -> TC 8-11
  Row 5: NOC[10][5], NOC[9][5], NOC[7][5], NOC[6][5] -> TC 12-15

Quadrant 3 (SE) - Columns 6,7,9,10 x Rows 1-4:
  Row 1: NOC[10][1], NOC[9][1], NOC[7][1], NOC[6][1] -> TC 0-3
  Row 2: NOC[10][2], NOC[9][2], NOC[7][2], NOC[6][2] -> TC 4-7
  Row 3: NOC[10][3], NOC[9][3], NOC[7][3], NOC[6][3] -> TC 8-11
  Row 4: NOC[10][4], NOC[9][4], NOC[7][4], NOC[6][4] -> TC 12-15
```

**Key Observations:**
- Uses both `nap_s` (for GDDR6 data) and `nap_m` (for register access) per TC
- Avoids columns 3 and 8 (reserved for other uses or optimal GDDR proximity)
- East quadrants use **reversed column order** (10,9,7,6 instead of 6,7,9,10) for symmetry
- NW and NE quadrants use **reversed row order** (8,7,6,5 instead of 5,6,7,8) for physical layout

---

### Design Strategy Comparison

| Aspect | gddr_ref_design | acx_gemm_ref_design |
|--------|-----------------|---------------------|
| **Total NAPs** | 9 (8 slave + 1 master) | 128 (64 slave + 64 master) |
| **NAP Columns** | 3, 8 only | 1,2,4,5 (W) and 6,7,9,10 (E) |
| **NAP Rows** | 3-6 | 1-8 (all rows) |
| **MLP Placement** | None | Fixed placement for 256 MLPs |
| **BRAM Placement** | None | Fixed placement for 256 BRAMs |
| **Use Case** | Memory validation | Production GEMM accelerator |

---

### Lessons for Custom Designs

1. **Simple GDDR6 access**: Use columns 3 (west) and 8 (east) for lowest latency
2. **High-throughput designs**: Spread NAPs across multiple columns to increase parallelism
3. **Quadrant-based designs**: Mirror NAP patterns for symmetric physical layout
4. **MLP integration**: Co-locate NAPs with associated MLP/BRAM resources (see MLP_PLACE_GUIDE.md)

## References

1. **Speedster7t 2D Network on Chip User Guide (UG089)**
   - Chapter: "FPGA Fabric Logic to GDDR6 or DDR4 Subsystems"
   - Chapter: "Modes of Operation"
   - [Achronix Documentation](https://www.achronix.com/documentation/speedster7t-2d-network-chip-user-guide-ug089)

2. **Speedster7t GDDR6 Reference Design Guide (RD017)**
   - Section: "NAP Locations" (part5.htm)
   - Section: "GDDR6 Subsystem Control IDs" (part38.htm)
   - Section: "Test Structure Using the 2D NoC-GDDR6 Interface" (part37.htm)
   - [Achronix Documentation](https://www.achronix.com/documentation/speedster7t-gddr6-reference-design-rd017)

3. **Speedster7t GDDR6 User Guide (UG091)**
   - Details on GDDR6 controller configuration and DC interface
   - [Achronix Documentation](https://www.achronix.com/documentation/speedster7t-gddr6-user-guide-ug091)

4. **Speedster7t Component Library User Guide (UG086)**
   - NAP primitive documentation and parameters
   - [Achronix Documentation](https://www.achronix.com/documentation/speedster7t-component-library-user-guide-ug086)

## Document History

| Date | Version | Description |
|------|---------|-------------|
| 2026-01-25 | 1.3 | Optimized NAP columns: West 3->1, East 8->10 for minimum GDDR latency per RD017 guidance |
| 2026-01-24 | 1.2 | Added "Reference Design Comparison" section with gddr_ref_design and acx_gemm_ref_design NAP placement analysis |
| 2026-01-23 | 1.1 | Added "Elastix GEMM 2D Engine - Actual Hardware Mapping" section with complete row-to-GDDR6 mapping table, RTL code references, and verification checklist |
| 2026-01-23 | 1.0 | Initial documentation of NAP-GDDR6 mapping |
