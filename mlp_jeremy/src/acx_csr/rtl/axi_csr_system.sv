// ------------------------------------------------------------------
//
// Copyright (c) 2021 Achronix Semiconductor Corp.
// All Rights Reserved.
//
// This Software constitutes an unpublished work and contains
// valuable proprietary information and trade secrets belonging
// to Achronix Semiconductor Corp.
//
// Permission is hereby granted to use this Software including
// without limitation the right to copy, modify, merge or distribute
// copies of the software subject to the following condition:
//
// The above copyright notice and this permission notice shall
// be included in in all copies of the Software.
//
// The Software is provided "as is" without warranty of any kind
// expressed or implied, including  but not limited to the warranties
// of merchantability fitness for a particular purpose and non-infringement.
// In no event shall the copyright holder be liable for any claim,
// damages, or other liability for any damages or other liability,
// whether an action of contract, tort or otherwise, arising from,
// out of, or in connection with the Software
//
// ------------------------------------------------------------------
// Top-level AXI CSR system with NAP components
//      Instantiates reg_control_block with internal AXI initiator NAP
//      Instantiates nap_responder_wrapper for external AXI access
//      NAPs communicate through NoC fabric (no explicit connections needed)
// ------------------------------------------------------------------

`include "nap_interfaces.svh"
`include "reg_control_defines.svh"
`include "version_defines.svh"

// Include the appropriate DSM utility file which defines the appropriate macros
// If unsupported device selected, then compilation will fail
`include "ac7t1500_utils.svh"

module axi_csr_system
#(
    // Parameters for reg_control_block
    parameter   NUM_USER_REGS         = 2,        // Number of user registers
    parameter   IN_REGS_PIPE          = 0,        // Stages of pipeline for input registers
    parameter   OUT_REGS_PIPE         = 0,        // Stages of pipeline for output registers
    parameter   ENABLE_PCIE_DMA_ACCEL = 0,        // When enabled, turns on support for PCIe DMA acceleration

    // Parameters for nap_responder_wrapper
    parameter   CSR_ACCESS_ENABLE     = 1'b1,     // Enable NAP access to CSR space
    parameter   RESPONDER_COLUMN      = 4'hx,     // NAP responder column location
    parameter   RESPONDER_ROW         = 4'hx,     // NAP responder row location
    parameter   E2W_ARB_SCHED         = 32'hffffffff, // east-to-west arbitration schedule
    parameter   W2E_ARB_SCHED         = 32'hffffffff  // west-to-east arbitration schedule
)
(
    // Clock and reset
    input  wire                         i_clk,
    input  wire                         i_reset_n,

    // User register interfaces for reg_control_block
    input  t_ACX_USER_REG               i_user_regs_in[NUM_USER_REGS -1:0],
    output t_ACX_USER_REG               o_user_regs_out[NUM_USER_REGS -1:0],

    // Status outputs from NAP responder
    output wire                         o_responder_rstn,
    output wire                         o_responder_error_valid,
    output wire [2:0]                   o_responder_error_info
);

    //------------------------------------------------------------
    // Register Control Block with Internal NAP Initiator
    //------------------------------------------------------------
    // Contains internal AXI initiator NAP that automatically connects
    // to the NoC fabric for register access operations

    reg_control_block #(
        .NUM_USER_REGS         (NUM_USER_REGS),
        .IN_REGS_PIPE          (IN_REGS_PIPE),
        .OUT_REGS_PIPE         (OUT_REGS_PIPE),
        .ENABLE_PCIE_DMA_ACCEL (ENABLE_PCIE_DMA_ACCEL)
    ) i_reg_control_block (
        .i_clk              (i_clk),
        .i_reset_n          (i_reset_n),
        .i_user_regs_in     (i_user_regs_in),
        .o_user_regs_out    (o_user_regs_out)
    );

    //------------------------------------------------------------
    // NAP Responder Wrapper for External Access
    //------------------------------------------------------------
    // Provides external AXI responder interface that connects to NoC fabric
    // External masters (PCIe, CPU, etc.) can access CSR space through this interface
    t_AXI4 #(
            .DATA_WIDTH (`ACX_NAP_AXI_DATA_WIDTH),
            .ADDR_WIDTH (`ACX_NAP_AXI_RESPONDER_ADDR_WIDTH),
            .LEN_WIDTH  (8),
            .ID_WIDTH   (8))
    ext_axi_if();

    nap_responder_wrapper #(
        .CSR_ACCESS_ENABLE  (CSR_ACCESS_ENABLE),
        .COLUMN             (RESPONDER_COLUMN),
        .ROW                (RESPONDER_ROW),
        .E2W_ARB_SCHED      (E2W_ARB_SCHED),
        .W2E_ARB_SCHED      (W2E_ARB_SCHED)
    ) i_nap_responder_wrapper (
        .i_clk              (i_clk),
        .i_reset_n          (i_reset_n),
        .nap                (ext_axi_if),
        .o_output_rstn      (o_responder_rstn),
        .o_error_valid      (o_responder_error_valid),
        .o_error_info       (o_responder_error_info)
    );

    //------------------------------------------------------------
    // NoC Communication Notes
    //------------------------------------------------------------

    // NETWORK ON CHIP (NoC) CONNECTIVITY:
    // Both NAPs automatically connect to the Speedster7t NoC fabric:
    //
    // 1. reg_control_block's internal NAP initiator:
    //    - Can initiate AXI transactions on the NoC
    //    - Automatically routed through NoC fabric to target responders
    //    - Address-based routing determines destination
    //
    // 2. nap_responder_wrapper:
    //    - Provides AXI responder endpoint accessible via NoC
    //    - External AXI masters connect through ext_axi_responder_if
    //    - Responds to transactions routed by NoC fabric
    //
    // COMMUNICATION FLOW:
    // External Master -> ext_axi_responder_if -> NAP Responder -> NoC -> Target
    // reg_control_block -> Internal NAP Initiator -> NoC -> Target Responder
    //
    // No explicit AXI connections needed - NoC handles all routing automatically


// Instantiate Speedster7t device
// ACX_DEVICE_NAME is defined in the DSM utility file for the selected device
// Connect chip_ready and GDDR ports
`ACX_DEVICE_NAME `ACX_DEVICE_NAME (
            .FCU_CONFIG_USER_MODE (chip_ready)
    );

// NETWORK ON CHIP (NoC) BINDINGS:
`ACX_BIND_NAP_AXI_MASTER(i_reg_control_block.i_axi_initiator.i_axi_initiator,1,1);
`ACX_BIND_NAP_AXI_SLAVE(i_nap_responder_wrapper.i_axi_responder,2,1);



        // Record any errors during configuration and test execution
logic fcu_error;
assign fcu_error = `ACX_DEVICE_NAME.fcu.error;

initial begin
    `ACX_DEVICE_NAME.set_verbosity(2);
    // Ensure correct version of sim package is being used
    // This design requires 8.8 as a minimum
    `ACX_DEVICE_NAME.require_version(8, 8, 0, 0);

    // -------------------------
    // Configure GDDR controllers in RTL mode
    // -------------------------
  //  `include "../../src/ioring/tc_ref_design_top_sim_config.svh"
end

initial begin
    // if (dump_waves) begin
        $dumpfile("axi_csr_waves.vcd");
        $dumpvars(0, axi_csr_system);
//    end
end


endmodule : axi_csr_system
