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
| 2026-01-23 | 1.0 | Initial documentation of NAP-GDDR6 mapping |
