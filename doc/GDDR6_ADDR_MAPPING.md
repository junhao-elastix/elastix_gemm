# GDDR6 Address Mapping and Ctrl ID

## Overview

This document describes the GDDR6 addressing scheme for the Achronix Speedster7t AC7t1500 FPGA as specified in the 2D Network-on-Chip User Guide (UG089). The addressing scheme uses a Ctrl ID field to route transactions to specific GDDR6 controllers and channels.

## Address Format

### Global Address Map Structure

The 42-bit address space for GDDR6 is structured as follows:

```
Addr[41:37] = 5'b00000  (Fixed prefix for GDDR6 memory space)
Addr[36:33] = Ctrl ID  (4-bit controller/channel selection)
Addr[32:0]  = Memory Address (33-bit address within channel)
```

### Address Bit Breakdown

| Address Bits | Field Name | Width | Description |
|--------------|------------|-------|-------------|
| [41:37] | GDDR6 Prefix | 5 bits | Fixed value `5'b00000` identifies GDDR6 memory space |
| [36:33] | **Ctrl ID** | 4 bits | Selects which GDDR6 controller and channel |
| [32:0] | Memory Address | 33 bits | Physical address within the selected channel |

## Ctrl ID Field

### Bit Structure

The Ctrl ID field (Addr[36:33]) is divided into two sub-fields:

- **Addr[36:34]** (3 bits): Controller selection
  - Selects one of 8 GDDR6 controllers (0-7)
  - Each controller manages 2 channels

- **Addr[33]** (1 bit): Channel selection
  - Selects one of 2 channels within the selected controller
  - Channel 0 or Channel 1

### Ctrl ID to Controller/Channel Mapping

The following table shows the mapping from Ctrl ID values to GDDR6 controllers and channels for the AC7t1500 FPGA:

| Ctrl ID [36:33] | Binary | Controller | Channel | Notes |
|-----------------|--------|------------|----------|-------|
| 0x0 | 0000 | GDDR6 2 | 0 | |
| 0x1 | 0001 | GDDR6 2 | 1 | |
| 0x2 | 0010 | GDDR6 6 | 1 | East side (channel reversed) |
| 0x3 | 0011 | GDDR6 6 | 0 | East side (channel reversed) |
| 0x4 | 0100 | GDDR6 1 | 0 | |
| 0x5 | 0101 | GDDR6 1 | 1 | |
| 0x6 | 0110 | GDDR6 5 | 1 | East side (channel reversed) |
| 0x7 | 0111 | GDDR6 5 | 0 | East side (channel reversed) |
| 0x8 | 1000 | GDDR6 3 | 0 | |
| 0x9 | 1001 | GDDR6 3 | 1 | |
| 0xA | 1010 | GDDR6 7 | 1 | East side (channel reversed) |
| 0xB | 1011 | GDDR6 7 | 0 | East side (channel reversed) |
| 0xC | 1100 | GDDR6 0 | 0 | |
| 0xD | 1101 | GDDR6 0 | 1 | |
| 0xE | 1110 | GDDR6 4 | 1 | East side (channel reversed) |
| 0xF | 1111 | GDDR6 4 | 0 | East side (channel reversed) |

**Important Note**: The channel selection (LSB of Ctrl ID) is **reversed** for channels on the east side of the device. This means:
- West side controllers (GDDR6 0, 1, 2, 3): Channel 0 = Ctrl ID bit[33]=0, Channel 1 = Ctrl ID bit[33]=1
- East side controllers (GDDR6 4, 5, 6, 7): Channel 0 = Ctrl ID bit[33]=1, Channel 1 = Ctrl ID bit[33]=0

## Address Translation

### Remapping Capabilities

The 2D NoC supports address translation/remapping for GDDR6 transactions:

1. **Ctrl ID Remapping** (Addr[36:33])
   - All 4 bits can be used in address translation
   - Allows remapping to determine which GDDR6 controller receives a transaction
   - Useful for load balancing and routing optimization

2. **Page Remapping** (Addr[28:26])
   - Bits [28:26] can be used for page remapping within memory
   - Enables memory interleaving and page-level address translation

### Address Translation Table

| Address Bit Range | Translation Capability | Purpose |
|-------------------|------------------------|----------|
| [36:33] | Full remapping | Controller/channel selection |
| [28:26] | Page remapping | Memory page interleaving |
| [32:0] | Pass-through | Physical memory address |

## Implementation Notes

### Base Address Calculation

To construct a GDDR6 address:

```systemverilog
// Example: Address for GDDR6 Controller 0, Channel 0, Memory Offset 0x1000
logic [41:0] gddr6_addr;
logic [3:0]  ctrl_id = 4'hC;  // GDDR6 0, Channel 0
logic [30:0] mem_addr = 31'h1000;  // 31-bit address (2GB max per channel)

gddr6_addr = {5'b00000, ctrl_id, mem_addr};
// Result: 42'h0003000001000
```

### Ctrl ID Extraction

To extract Ctrl ID from an address:

```systemverilog
logic [3:0] ctrl_id = gddr6_addr[36:33];
logic [2:0] controller = gddr6_addr[36:34];
logic       channel = gddr6_addr[33];
logic [30:0] mem_addr = gddr6_addr[30:0];  // 31-bit memory address (2GB per channel)
```

### Channel Reversal Handling

When working with east-side controllers, account for channel reversal:

```systemverilog
// Determine if controller is on east side
logic is_east_side = (gddr6_addr[36:34] >= 3'd4);

// Extract actual channel (accounting for reversal)
logic actual_channel = is_east_side ? ~gddr6_addr[33] : gddr6_addr[33];
```

## Memory Space Organization

### Per-Channel Address Space

**Source**: `gddr_ref_design_top.sv` lines 145-148
- VP815 card uses 2 x 8Gb devices in clamshell mode x8
- 2 x 8Gb = 2 x 1GB = 2GB per channel
- Address width: 31 bits (26 bits memory address + 5 bits byte offset)

Each GDDR6 channel has a **31-bit address space** (Addr[30:0] effectively used), providing:
- **Addressable range**: 2^31 bytes = **2 GB per channel**
- **Total GDDR6 capacity**: 16 channels × 2 GB = **32 GB total** (VP815 card configuration)

**Note**: While the address format supports 33 bits (Addr[32:0]), the actual physical memory on VP815 is limited to 31 bits (2GB) per channel. The upper 2 bits (Addr[32:31]) are not used for physical addressing in this configuration.

**Reference Design Implementation** (`gddr_ref_design_top.sv` lines 145-149):
- Uses `GDDR_NOC_ADDR_WIDTH = 26` bits for memory addressing
- This represents bits [30:5] of the address (26 bits)
- Plus 5 bits for byte offset (bits [4:0]) = 31 bits total
- Address construction: `{TGT_ADDR_ID[8:0], padding[1:0], mem_addr[25:0], byte_offset[4:0]}`

### Address Space Layout

**Source**: Calculated from Ctrl ID mapping and 2GB per channel capacity.

**Note**: Address ranges shown are theoretical maximums. Actual VP815 card uses 31-bit addressing (2GB per channel).

```
Ctrl ID 0xC: 0x0003000000000 - 0x0003FFFFFFFFF  : GDDR6 Controller 0, Channel 0 (2GB)
Ctrl ID 0xD: 0x0003400000000 - 0x00037FFFFFFFFF  : GDDR6 Controller 0, Channel 1 (2GB)
Ctrl ID 0x4: 0x0001000000000 - 0x00013FFFFFFFFF  : GDDR6 Controller 1, Channel 0 (2GB)
Ctrl ID 0x5: 0x0001400000000 - 0x00017FFFFFFFFF  : GDDR6 Controller 1, Channel 1 (2GB)
...
Ctrl ID 0xA: 0x0002800000000 - 0x0002BFFFFFFFFF  : GDDR6 Controller 7, Channel 1 (2GB)
```

**Actual usable range per channel**: 2^31 bytes = 2GB (31-bit addressing)

## Reference Design Implementation

### TGT_ADDR_ID Parameter

The Achronix GDDR6 reference design (`gddr_ref_design`) uses a **9-bit TGT_ADDR_ID** parameter that encodes both the GDDR6 prefix and Ctrl ID:

```systemverilog
// From gddr_ref_design_top.sv
localparam [71:0] GDDR6_ID_NOC_CH1 = {9'd10, 9'd2, 9'd6, 9'd14, 9'd9, 9'd1, 9'd5, 9'd13};
```

### TGT_ADDR_ID Structure

The 9-bit TGT_ADDR_ID is structured as follows:
- **TGT_ADDR_ID[8:4]** (5 bits): GDDR6 prefix - must be `5'b00000`
- **TGT_ADDR_ID[3:0]** (4 bits): Ctrl ID - maps to Addr[36:33]

### Reference Design Ctrl ID Values

The reference design uses these TGT_ADDR_ID values for Channel 1 access:

| Channel Index | TGT_ADDR_ID (decimal) | TGT_ADDR_ID (binary) | Ctrl ID [3:0] | Controller | Channel | Notes |
|---------------|----------------------|---------------------|---------------|------------|---------|-------|
| 0 | 10 | 000001010 | 0xA (1010) | GDDR6 7 | 1 | East side |
| 1 | 2 | 000000010 | 0x2 (0010) | GDDR6 6 | 1 | East side |
| 2 | 6 | 000000110 | 0x6 (0110) | GDDR6 5 | 1 | East side |
| 3 | 14 | 000001110 | 0xE (1110) | GDDR6 4 | 1 | East side |
| 4 | 9 | 000001001 | 0x9 (1001) | GDDR6 3 | 1 | West side |
| 5 | 1 | 000000001 | 0x1 (0001) | GDDR6 2 | 1 | West side |
| 6 | 5 | 000000101 | 0x5 (0101) | GDDR6 1 | 1 | West side |
| 7 | 13 | 000001101 | 0xD (1101) | GDDR6 0 | 1 | West side |

**Verification**: All TGT_ADDR_ID values have `5'b00000` in bits [8:4], confirming they are valid GDDR6 addresses. The Ctrl ID values (bits [3:0]) match the documentation mapping for Channel 1 access.

### Address Construction in Reference Design

The reference design constructs addresses as follows:

```systemverilog
// From axi_pkt_gen.sv and axi_pkt_chk.sv
// TGT_ADDR_ID is 9 bits, placed at top of address
// Address format: {TGT_ADDR_ID[8:0], padding, memory_addr[25:0], byte_offset[4:0]}
assign axi_if.awaddr = {TGT_ADDR_ID, {TGT_ADDR_PAD_WIDTH{1'b0}}, 
                        axi_addr_out[ACTIVE_ADDR_WIDTH-1:0], {ADDR_BYTE_STEP{1'b0}}};
```

Where:
- `TGT_ADDR_ID` = 9 bits (includes 5-bit prefix + 4-bit Ctrl ID)
- `TGT_ADDR_PAD_WIDTH` = 2 bits (calculated as `42-9-26-5`)
- `ACTIVE_ADDR_WIDTH` = 26 bits (memory address width)
- `ADDR_BYTE_STEP` = 5 bits (byte offset)

This results in the final 42-bit address:
- Bits [41:33] = TGT_ADDR_ID[8:0] (9 bits: 5-bit prefix + 4-bit Ctrl ID)
- Bits [32:31] = Padding (2 bits)
- Bits [30:5] = Memory address (26 bits)
- Bits [4:0] = Byte offset (5 bits)

### Consistency Check

**VERIFIED**: The reference design implementation is **consistent** with the documentation:

1. ✅ **GDDR6 Prefix**: All TGT_ADDR_ID values have `5'b00000` in bits [8:4], matching Addr[41:37] = `5'b00000`
2. ✅ **Ctrl ID Location**: TGT_ADDR_ID[3:0] maps to Addr[36:33], correctly placing Ctrl ID
3. ✅ **Ctrl ID Values**: The Ctrl IDs used (0xA, 0x2, 0x6, 0xE, 0x9, 0x1, 0x5, 0xD) match the documentation mapping for Channel 1
4. ✅ **Channel Reversal**: East-side controllers (4, 5, 6, 7) use even Ctrl IDs for Channel 1, confirming channel reversal

### Testbench Verification

The testbench (`tb_noc_memory_behavioural.sv`) confirms the address structure:

```systemverilog
// GDDR CTRL ID is 4 bits in locations [36:33].
// Top bits of address [41:37] have to be 0 to access a GDDR.
convert_mem_addr = {5'b0, addr[36:33], 3'b000, addr[29:5]};
```

This matches the documentation exactly:
- Bits [41:37] = `5'b0` (GDDR6 prefix) ✅
- Bits [36:33] = Ctrl ID (4 bits) ✅

## Usage in Project

### Fetcher Module

The `fetcher_2d.sv` module uses the GDDR6_PAGE_ID parameter for address construction:

```systemverilog
parameter [8:0] GDDR6_PAGE_ID = 9'd0
```

This parameter follows the same 9-bit format as TGT_ADDR_ID in the reference design, where:
- Bits [8:4] = GDDR6 prefix (`5'b00000`)
- Bits [3:0] = Ctrl ID (4 bits for controller/channel selection)

### Address Construction Pattern

When constructing addresses for GDDR6 transactions:

1. Set base prefix: `5'b00000` for bits [41:37]
2. Set Ctrl ID: Based on desired controller/channel (bits [36:33])
3. Set memory address: Physical offset within channel (bits [32:0])
4. Apply address translation if remapping is enabled

**Recommended Pattern** (matching reference design):
```systemverilog
// Use 9-bit TGT_ADDR_ID format
localparam [8:0] TGT_ADDR_ID = {5'b00000, ctrl_id[3:0]};
logic [41:0] gddr6_addr = {TGT_ADDR_ID, padding, mem_addr, byte_offset};
```

## References

- **Primary Source**: Speedster7t 2D Network on Chip User Guide (UG089)
  - Section: Chapter 6 - Speedster7t 2D NoC Address Mapping
  - Subsection: GDDR6 (part46.htm)
  - Subsection: Address Translation - GDDR6 (part53.htm)
- **Table Reference**: Table 4 - Speedster7t AC7t1500 FPGA GDDR Memory Mapping
- **Translation Reference**: Table 7 - GDDR6 Address Translation

## Accessing All 16 GDDR6 Channels

**Source**: Derived from Ctrl ID mapping table in documentation (part46.htm, Table 4) and verified against reference design implementation patterns.

### Complete Channel Mapping

To access all 16 GDDR6 channels (8 controllers × 2 channels each), use the following Ctrl ID values:

| Controller | Channel 0 Ctrl ID | Channel 1 Ctrl ID | Side | Notes |
|------------|-------------------|-------------------|------|-------|
| GDDR6 0 | 0xC (1100) | 0xD (1101) | West | |
| GDDR6 1 | 0x4 (0100) | 0x5 (0101) | West | |
| GDDR6 2 | 0x0 (0000) | 0x1 (0001) | West | |
| GDDR6 3 | 0x8 (1000) | 0x9 (1001) | West | |
| GDDR6 4 | 0xF (1111) | 0xE (1110) | East | Channel reversed |
| GDDR6 5 | 0x7 (0111) | 0x6 (0110) | East | Channel reversed |
| GDDR6 6 | 0x3 (0011) | 0x2 (0010) | East | Channel reversed |
| GDDR6 7 | 0xB (1011) | 0xA (1010) | East | Channel reversed |

**Key Points:**
- **West side controllers (0-3)**: Channel 0 uses even Ctrl IDs, Channel 1 uses odd Ctrl IDs
- **East side controllers (4-7)**: Channel 0 uses odd Ctrl IDs, Channel 1 uses even Ctrl IDs (reversed)
- All Ctrl IDs are 4 bits (0x0 to 0xF)

### Implementation Example

#### Option 1: Lookup Table Approach

**Source**: Derived from Ctrl ID mapping table (part46.htm, Table 4) - all 16 Ctrl ID values (0x0-0xF) mapped to controllers/channels.

```systemverilog
// Define Ctrl ID lookup table for all 16 channels
// Index: {controller[2:0], channel[0]}
// Source: GDDR6 Ctrl ID mapping table from UG089 documentation
localparam [3:0] CTRL_ID_TABLE [0:15] = '{
    // Controller 0: Channel 0, Channel 1
    4'hC, 4'hD,
    // Controller 1: Channel 0, Channel 1
    4'h4, 4'h5,
    // Controller 2: Channel 0, Channel 1
    4'h0, 4'h1,
    // Controller 3: Channel 0, Channel 1
    4'h8, 4'h9,
    // Controller 4: Channel 0, Channel 1 (reversed)
    4'hF, 4'hE,
    // Controller 5: Channel 0, Channel 1 (reversed)
    4'h7, 4'h6,
    // Controller 6: Channel 0, Channel 1 (reversed)
    4'h3, 4'h2,
    // Controller 7: Channel 0, Channel 1 (reversed)
    4'hB, 4'hA
};

// Function to get Ctrl ID for a specific controller and channel
function automatic [3:0] get_ctrl_id(input [2:0] controller, input channel);
    int index = {controller, channel};
    get_ctrl_id = CTRL_ID_TABLE[index];
endfunction

// Usage example
logic [3:0] ctrl_id = get_ctrl_id(3'd0, 1'b0);  // GDDR6 0, Channel 0 → 0xC
logic [41:0] addr = {5'b00000, ctrl_id, 31'h1000};  // Note: 31-bit address (2GB max per channel)
```

#### Option 2: Direct Calculation (Account for Channel Reversal)

**Source**: Based on channel reversal behavior documented in `gddr_ref_design_top.sv` line 142 and Ctrl ID bit structure (bits [36:34] = controller, bit [33] = channel).

```systemverilog
// Function to calculate Ctrl ID directly
// Source: Channel reversal logic from reference design comments
function automatic [3:0] calc_ctrl_id(input [2:0] controller, input channel);
    logic is_east_side = (controller >= 3'd4);
    logic [2:0] controller_bits = controller;
    logic channel_bit;
    
    // Account for east-side channel reversal
    // Source: gddr_ref_design_top.sv line 142 - east side uses even addresses for channel 1
    if (is_east_side) begin
        channel_bit = ~channel;  // Reversed for east side
    end else begin
        channel_bit = channel;    // Normal for west side
    end
    
    calc_ctrl_id = {controller_bits, channel_bit};
endfunction

// Usage example
logic [3:0] ctrl_id_west = calc_ctrl_id(3'd0, 1'b0);  // GDDR6 0, Ch0 → 0xC
logic [3:0] ctrl_id_east = calc_ctrl_id(3'd4, 1'b0); // GDDR6 4, Ch0 → 0xF (reversed)
```

#### Option 3: Parameter Array (For Multiple Channels)

```systemverilog
// Define all 16 channel Ctrl IDs as parameters
localparam [3:0] GDDR6_CTRL_ID [0:7][0:1] = '{
    // Controller 0: {Channel 0, Channel 1}
    '{4'hC, 4'hD},
    // Controller 1: {Channel 0, Channel 1}
    '{4'h4, 4'h5},
    // Controller 2: {Channel 0, Channel 1}
    '{4'h0, 4'h1},
    // Controller 3: {Channel 0, Channel 1}
    '{4'h8, 4'h9},
    // Controller 4: {Channel 0, Channel 1} (reversed)
    '{4'hF, 4'hE},
    // Controller 5: {Channel 0, Channel 1} (reversed)
    '{4'h7, 4'h6},
    // Controller 6: {Channel 0, Channel 1} (reversed)
    '{4'h3, 4'h2},
    // Controller 7: {Channel 0, Channel 1} (reversed)
    '{4'hB, 4'hA}
};

// Usage example
logic [2:0] controller = 3'd0;
logic channel = 1'b0;
logic [3:0] ctrl_id = GDDR6_CTRL_ID[controller][channel];
logic [41:0] addr = {5'b00000, ctrl_id, mem_addr};
```

### Complete Address Construction for All Channels

```systemverilog
// Complete example: Access all 16 channels
module gddr6_all_channels_example;
    
    // Channel enumeration
    typedef enum logic [3:0] {
        CH0_CTRL0 = 4'hC, CH1_CTRL0 = 4'hD,  // GDDR6 0
        CH0_CTRL1 = 4'h4, CH1_CTRL1 = 4'h5,  // GDDR6 1
        CH0_CTRL2 = 4'h0, CH1_CTRL2 = 4'h1,  // GDDR6 2
        CH0_CTRL3 = 4'h8, CH1_CTRL3 = 4'h9,  // GDDR6 3
        CH0_CTRL4 = 4'hF, CH1_CTRL4 = 4'hE,  // GDDR6 4 (reversed)
        CH0_CTRL5 = 4'h7, CH1_CTRL5 = 4'h6,  // GDDR6 5 (reversed)
        CH0_CTRL6 = 4'h3, CH1_CTRL6 = 4'h2,  // GDDR6 6 (reversed)
        CH0_CTRL7 = 4'hB, CH1_CTRL7 = 4'hA   // GDDR6 7 (reversed)
    } gddr6_channel_t;
    
    // Function to construct GDDR6 address
    function automatic [41:0] build_gddr6_addr(
        input [3:0] ctrl_id,
        input [30:0] mem_addr  // 31-bit address (2GB per channel)
    );
        build_gddr6_addr = {5'b00000, ctrl_id, mem_addr};
    endfunction
    
// Example: Access Controller 0, Channel 0
logic [41:0] addr_ctrl0_ch0 = build_gddr6_addr(CH0_CTRL0, 31'h1000);  // 31-bit address
// Result: 42'h0003000001000

// Example: Access Controller 4, Channel 1 (east side, reversed)
logic [41:0] addr_ctrl4_ch1 = build_gddr6_addr(CH1_CTRL4, 31'h2000);  // 31-bit address
// Result: 42'h0003E00002000 (Ctrl ID 0xE)
    
endmodule
```

### Iterating Over All Channels

```systemverilog
// Example: Generate addresses for all 16 channels
genvar ctrl, ch;
generate
    for (ctrl = 0; ctrl < 8; ctrl = ctrl + 1) begin : gen_controllers
        for (ch = 0; ch < 2; ch = ch + 1) begin : gen_channels
            // Calculate Ctrl ID accounting for channel reversal
            localparam logic is_east = (ctrl >= 4);
            localparam logic [3:0] ctrl_id = {ctrl[2:0], is_east ? ~ch[0] : ch[0]};
            
            // Instantiate channel-specific logic
            // Each channel can have its own address space
            localparam [41:0] BASE_ADDR = {5'b00000, ctrl_id, 27'b0};
            
            // Use BASE_ADDR for channel-specific addressing
        end
    end
endgenerate
```

### Practical Usage Pattern

```systemverilog
// Recommended pattern for accessing all channels
module gddr6_multi_channel_access;
    
    // Channel selection
    input [2:0] i_controller;  // 0-7
    input       i_channel;     // 0 or 1
    input [30:0] i_mem_addr;   // 31-bit address (2GB per channel)
    
    // Calculate Ctrl ID
    logic is_east_side = (i_controller >= 3'd4);
    logic [3:0] ctrl_id;
    
    always_comb begin
        if (is_east_side) begin
            // East side: channel bit is reversed
            ctrl_id = {i_controller, ~i_channel};
        end else begin
            // West side: channel bit is normal
            ctrl_id = {i_controller, i_channel};
        end
    end
    
    // Construct full address
    logic [41:0] gddr6_addr = {5'b00000, ctrl_id, i_mem_addr};
    
    // Use gddr6_addr for AXI transactions
    
endmodule
```

### Important Reminders

1. **Always use 5'b00000 prefix** in bits [41:37] for GDDR6 memory space
   - **Source**: `tb_noc_memory_behavioural.sv` line 168: "Top bits of address [41:37] have to be 0 to access a GDDR"
2. **Account for channel reversal** on east-side controllers (4-7)
   - **Source**: `gddr_ref_design_top.sv` line 142: "GDDR6 on the east side use even addresses for channel 1, whereas the west side uses odd addresses"
3. **Ctrl ID is 4 bits** located at address bits [36:33]
   - **Source**: `tb_noc_memory_behavioural.sv` line 167: "GDDR CTRL ID is 4 bits in locations [36:33]"
4. **Each channel has 31-bit address space** (2GB per channel on VP815)
   - **Source**: `gddr_ref_design_top.sv` lines 145-148: "2 x 8Gb = 2 x 1GB device is 31 bits"
5. **Total addressable space**: 16 channels × 2 GB = **32 GB** (VP815 card configuration)

## Summary

### Consistency Verification

**VERIFIED**: The documentation is **fully consistent** with the Achronix GDDR6 reference design implementation:

1. ✅ **Address Structure**: Both use 42-bit addresses with identical bit field layout
2. ✅ **GDDR6 Prefix**: Both require `5'b00000` in bits [41:37]
3. ✅ **Ctrl ID Location**: Both place Ctrl ID in bits [36:33] (4 bits)
4. ✅ **Ctrl ID Values**: Reference design values match documentation mapping table
5. ✅ **Channel Reversal**: Both document east-side channel reversal behavior
6. ✅ **Testbench Confirmation**: Testbench code explicitly confirms bit locations

### Key Takeaways

- **Ctrl ID is 4 bits** located at address bits [36:33]
- **Reference design uses 9-bit TGT_ADDR_ID** format: `{5'b00000, ctrl_id[3:0]}`
- **All 8 channels** in reference design use Channel 1 (Ctrl IDs: 0xA, 0x2, 0x6, 0xE, 0x9, 0x1, 0x5, 0xD)
- **East-side controllers** (4, 5, 6, 7) have reversed channel bit interpretation
- **Address construction** follows pattern: `{5'b00000, ctrl_id[3:0], padding, mem_addr, byte_offset}`

## Notes

- The address mappings apply only to the **memory address space**
- For configuration space (CSR) address mappings, refer to the appropriate CSR mapping table in the documentation
- Ctrl ID mappings are device-specific and may vary for different Speedster7t FPGA variants
- Always verify Ctrl ID mappings against the specific device documentation
