# NAP Architecture Analysis for GDDR6 Access
**Date**: Mon Oct 6 08:46:55 AM PDT 2025
**Author**: FPGA Architect

## Critical Architectural Finding

### The Problem
The G2B processor was unable to initiate AXI read transactions to GDDR6 memory when using a NAP responder.

### Root Cause Analysis

#### NAP Responder vs NAP Initiator Architecture

1. **NAP Responders (`ACX_NAP_AXI_SLAVE`)**:
   - Are **endpoints** that receive and respond to AXI transactions
   - Cannot initiate new transactions to other NAPs
   - Used by GDDR6 packet generators as memory endpoints
   - Support full 42-bit addressing (no truncation)
   - Placement: `nap_s` in NoC fabric

2. **NAP Initiators (`ACX_NAP_AXI_MASTER`)**:
   - Can **initiate** AXI transactions on the NoC
   - Send read/write requests to NAP responders (including GDDR6)
   - Address limited to 28-bit at primitive level
   - Upper address bits used for NoC routing (page ID)
   - Placement: `nap_m` in NoC fabric

### The Solution

#### Correct Architecture for G2B Processor
To read from GDDR6, the G2B processor must use a **NAP initiator**, not a responder:

```systemverilog
// CORRECT: NAP initiator for reading from GDDR6
nap_initiator_wrapper i_nap_initiator (
    .i_clk          (i_nap_clk),
    .i_reset_n      (i_nap_reset_n),
    .nap            (axi_if),
    .o_output_rstn  (nap_output_rstn),
    .o_error_valid  (nap_error_valid),
    .o_error_info   (nap_error_info)
);
```

#### Address Construction for GDDR6 Access
Even though the NAP initiator primitive only accepts 28-bit addresses, the full 42-bit address is constructed:

```systemverilog
// Full 42-bit GDDR6 address construction
logic [41:0] gddr_addr_constructed;
assign gddr_addr_constructed = {
    GDDR6_CH0_PAGE_ID,  // [41:33] 9-bit page ID for channel routing
    GDDR6_ADDR_PAD,     // [32:31] 2-bit padding
    word_addr_26bit,    // [30:5]  26-bit local address
    5'b00000            // [4:0]   5-bit byte alignment
};
```

The NoC fabric uses the upper bits for routing to the correct GDDR6 channel.

### NoC Topology

```
User Logic (NAP Initiator @ NOC[4][4])
           ↓
    NoC Fabric (routes based on page ID)
           ↓
GDDR6 NAP Responders:
- West: Ch0-3 @ NOC[3][3-6] (Page IDs: 10,2,6,14)
- East: Ch4-7 @ NOC[8][3-6] (Page IDs: 9,1,5,13)
```

### Key Lessons Learned

1. **NAP Type Determines Transaction Direction**:
   - Initiators → Responders: ✅ Works
   - Responders → Responders: ❌ Not possible

2. **Address Width Handling**:
   - NAP initiator primitive: 28-bit input
   - NoC routing: Uses full 42-bit address
   - Page ID in upper bits determines target

3. **Placement Constraints Matter**:
   - NAP initiators use `nap_m` placement
   - NAP responders use `nap_s` placement
   - Must update both RTL and PDC constraints

### Implementation Changes Made

1. **RTL Changes** (`gddr6_to_bram_processor.sv`):
   - Changed from `nap_responder_wrapper` to `nap_initiator_wrapper`
   - Maintained 42-bit address construction
   - Fixed interface connections

2. **Constraint Changes** (`ace_placements.pdc`):
   - Updated placement from `nap_s` to `nap_m`
   - Changed instance path to match new NAP type

3. **Filelist Update** (`filelist.tcl`):
   - Added `nap_initiator_wrapper_fixed.sv` (initially attempted)
   - Reverted to standard `nap_initiator_wrapper.sv`

### Status
Build in progress with corrected NAP initiator architecture. Synthesis completed successfully, P&R underway.

### Next Steps
1. Complete P&R and generate bitstream
2. Flash FPGA and validate G2B processor can read from GDDR6
3. Test data processing pipeline with various modes
4. Verify BRAM write functionality

## Reference Architecture

### Working GDDR6 Packet Generators
The GDDR6 packet generators in `elastix_gemm_top.sv` (lines 616-644) use NAP responders because they ARE the endpoints - they don't read FROM GDDR6, they implement the GDDR6 interface itself.

### User Logic Accessing GDDR6
Any user logic that needs to READ or WRITE to GDDR6 must use a NAP initiator to send transactions through the NoC to the GDDR6 NAP responders.