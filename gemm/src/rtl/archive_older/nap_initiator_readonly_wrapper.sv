// ------------------------------------------------------------------
// NAP Initiator Wrapper for Read-Only Masters
//
// This wrapper is specifically designed for NAP initiators that only
// perform read operations (no writes). It properly handles tie-offs
// for unused write channels and optional AXI signals to avoid
// synthesis conflicts with multiple drivers.
//
// Key differences from standard wrapper:
// - Write channels tied off internally (not connected to interface)
// - Optional signals (arlock, awlock, arqos, awqos) tied to constants
// - Prevents GND driver conflicts during synthesis
// ------------------------------------------------------------------

`include "nap_interfaces.svh"

module nap_initiator_readonly_wrapper
  #(
    parameter COLUMN        = 4'hx,
    parameter ROW           = 4'hx,
    parameter N2S_ARB_SCHED = 32'hffffffff, // north-to-south arbitration schedule
    parameter S2N_ARB_SCHED = 32'hffffffff  // south-to-north arbitration schedule
    )
   (
    // Inputs
    input wire          i_clk,
    input wire          i_reset_n,          // Negative synchronous reset
    t_AXI4.initiator    nap,                // Module is an initiator

    output wire         o_output_rstn,
    output wire         o_error_valid,
    output wire [2:0]   o_error_info
    );

   // Instantiate NAP with proper tie-offs for read-only operation
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

                   // Read address channel - connected
                   .arready     (nap.arready),
                   .arvalid     (nap.arvalid),
                   .arqos       (nap.arqos),          // Connect from interface
                   .arburst     (nap.arburst),
                   .arlock      (),                   // Leave unconnected - NAP outputs GND internally
                   .arsize      (nap.arsize),
                   .arlen       (nap.arlen),
                   .arid        (nap.arid),
                   .araddr      (nap.araddr[27:0]),

                   // Write address channel - all tied off
                   .awready     (nap.awready),        // Connect output but don't use
                   .awvalid     (nap.awvalid),        // Connect but should be 0 from G2B
                   .awqos       (nap.awqos),          // Connect from interface (will be 0)
                   .awburst     (nap.awburst),        // Connect from interface (will be 0)
                   .awlock      (),                   // Leave unconnected - NAP outputs GND internally
                   .awsize      (nap.awsize),         // Connect from interface (will be 0)
                   .awlen       (nap.awlen),          // Connect from interface (will be 0)
                   .awid        (nap.awid),           // Connect from interface (will be 0)
                   .awaddr      (nap.awaddr[27:0]),   // Connect from interface (will be 0)

                   // Write data channel - all tied off
                   .wready      (nap.wready),         // Connect output but don't use
                   .wvalid      (nap.wvalid),         // Connect but should be 0 from G2B
                   .wdata       (nap.wdata),          // Connect from interface (will be 0)
                   .wstrb       (nap.wstrb),          // Connect from interface (will be 0)
                   .wlast       (nap.wlast),          // Connect from interface (will be 0)

                   // Read data channel - connected
                   .rready      (nap.rready),
                   .rvalid      (nap.rvalid),
                   .rresp       (nap.rresp),
                   .rid         (nap.rid),
                   .rdata       (nap.rdata),
                   .rlast       (nap.rlast),

                   // Write response channel - tied off
                   .bready      (nap.bready),         // Connect from interface (G2B sets to 1)
                   .bvalid      (nap.bvalid),         // Connect output but don't use
                   .bid         (nap.bid),            // Connect output but don't use
                   .bresp       (nap.bresp),          // Connect output but don't use

                   // Error interface
                   .error_valid (o_error_valid),
                   .error_info  (o_error_info)
                   ) /* synthesis syn_noprune=1 */;

endmodule : nap_initiator_readonly_wrapper