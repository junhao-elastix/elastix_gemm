// ------------------------------------------------------------------
// Fixed NAP Initiator Wrapper
//
// CRITICAL FIX: The ACX_NAP_AXI_MASTER primitive presents an AXI SLAVE
// interface to the user logic (it receives commands from us), while acting
// as an AXI MASTER on the NoC side. This means we must use the responder
// modport when connecting to it, not the initiator modport.
//
// The confusion arises because:
// - From NoC perspective: NAP is an AXI Master (initiates transactions)
// - From user logic perspective: NAP is an AXI Slave (receives commands)
// ------------------------------------------------------------------

`include "nap_interfaces.svh"

module nap_initiator_wrapper_fixed
  #(
    parameter COLUMN        = 4'hx,
    parameter ROW           = 4'hx,
    parameter N2S_ARB_SCHED = 32'hffffffff,
    parameter S2N_ARB_SCHED = 32'hffffffff
    )
   (
    input wire          i_clk,
    input wire          i_reset_n,
    t_AXI4.responder    nap,                // NAP acts as responder to our logic!

    output wire         o_output_rstn,
    output wire         o_error_valid,
    output wire [2:0]   o_error_info
    );

   // Instantiate NAP with proper signal directions
   // NAP receives our commands (arvalid, araddr, etc.) and sends back responses
   ACX_NAP_AXI_MASTER
     #(.column    (COLUMN),
       .row       (ROW),
       .n2s_arbitration_schedule (N2S_ARB_SCHED),
       .s2n_arbitration_schedule (S2N_ARB_SCHED),
       .must_keep (1)
       )
     i_axi_initiator (
                   .clk         (i_clk),
                   .rstn        (i_reset_n),
                   .output_rstn (o_output_rstn),

                   // Read address channel - NAP receives these
                   .arready     (nap.arready),    // OUTPUT from NAP
                   .arvalid     (nap.arvalid),    // INPUT to NAP
                   .arqos       (nap.arqos),      // INPUT to NAP
                   .arburst     (nap.arburst),    // INPUT to NAP
                   .arlock      (),               // Leave open - NAP handles internally
                   .arsize      (nap.arsize),     // INPUT to NAP
                   .arlen       (nap.arlen),      // INPUT to NAP
                   .arid        (nap.arid),       // INPUT to NAP
                   .araddr      (nap.araddr[27:0]), // INPUT to NAP (28-bit)

                   // Write address channel - NAP receives these
                   .awready     (nap.awready),    // OUTPUT from NAP
                   .awvalid     (nap.awvalid),    // INPUT to NAP
                   .awqos       (nap.awqos),      // INPUT to NAP
                   .awburst     (nap.awburst),    // INPUT to NAP
                   .awlock      (),               // Leave open - NAP handles internally
                   .awsize      (nap.awsize),     // INPUT to NAP
                   .awlen       (nap.awlen),      // INPUT to NAP
                   .awid        (nap.awid),       // INPUT to NAP
                   .awaddr      (nap.awaddr[27:0]), // INPUT to NAP (28-bit)

                   // Write data channel - NAP receives these
                   .wready      (nap.wready),     // OUTPUT from NAP
                   .wvalid      (nap.wvalid),     // INPUT to NAP
                   .wdata       (nap.wdata),      // INPUT to NAP
                   .wstrb       (nap.wstrb),      // INPUT to NAP
                   .wlast       (nap.wlast),      // INPUT to NAP

                   // Read data channel - NAP sends these
                   .rready      (nap.rready),     // INPUT to NAP
                   .rvalid      (nap.rvalid),     // OUTPUT from NAP
                   .rresp       (nap.rresp),      // OUTPUT from NAP
                   .rid         (nap.rid),        // OUTPUT from NAP
                   .rdata       (nap.rdata),      // OUTPUT from NAP
                   .rlast       (nap.rlast),      // OUTPUT from NAP

                   // Write response channel - NAP sends these
                   .bready      (nap.bready),     // INPUT to NAP
                   .bvalid      (nap.bvalid),     // OUTPUT from NAP
                   .bid         (nap.bid),        // OUTPUT from NAP
                   .bresp       (nap.bresp),      // OUTPUT from NAP

                   // Error interface
                   .error_valid (o_error_valid),
                   .error_info  (o_error_info)
                   ) /* synthesis syn_noprune=1 */;

endmodule : nap_initiator_wrapper_fixed