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
// The Software is provided “as is” without warranty of any kind
// expressed or implied, including  but not limited to the warranties
// of merchantability fitness for a particular purpose and non-infringement.
// In no event shall the copyright holder be liable for any claim,
// damages, or other liability for any damages or other liability,
// whether an action of contract, tort or otherwise, arising from, 
// out of, or in connection with the Software
//
// ------------------------------------------------------------------
// AXI register layer to improve timing
//      Requires an a/b pair of registers as handshake response latency
//      is two cycles
//      One cycle for the registered data and data valid
//      One cycle for the registered ready signal.
// ------------------------------------------------------------------

`include "nap_interfaces.svh"

module axi_reg_layer #(
    parameter                           DATA_WIDTH = 0,
    parameter                           ADDR_WIDTH = 0,
    parameter                           LEN_WIDTH  = 0,
    parameter                           ID_WIDTH   = 0
)
(
    // Inputs
    input  wire                         i_clk,              // Clock
    input  wire                         i_reset_n,          // Negative synchronous reset

    // Interfaces
    t_AXI4.initiator                    axi_initiator_if,   // AXI-4 initiator interface.
    t_AXI4.responder                    axi_responder_if    // AXI-4 responder interface.

);

    // In general it is sufficient to insert registers between the majority of the
    // data and control buses.  However in order to assure there are not double
    // transfer pulses, the ready and valid signals need to be properly handshaked.
    axi_reg_layer_handshake  #(
        .DATA_WIDTH     (ADDR_WIDTH + LEN_WIDTH + ID_WIDTH + 4 + 2 + 1 + 3 + 3 + 3 + 4)
    ) i_aw_handshake (
        .i_clk          (i_clk),
        .i_reset_n      (i_reset_n),
        .i_src_valid    (axi_responder_if.awvalid),
        .i_snk_ready    (axi_initiator_if.awready),
        .o_src_ready    (axi_responder_if.awready),
        .o_snk_valid    (axi_initiator_if.awvalid),
        .i_data_in      ({  axi_responder_if.awaddr,
                            axi_responder_if.awlen,
                            axi_responder_if.awid,
                            axi_responder_if.awqos,
                            axi_responder_if.awburst,
                            axi_responder_if.awlock,
                            axi_responder_if.awsize,
                            axi_responder_if.awregion,
                            axi_responder_if.awprot,
                            axi_responder_if.awcache }),

        .o_data_out     ({  axi_initiator_if.awaddr,
                            axi_initiator_if.awlen,
                            axi_initiator_if.awid,
                            axi_initiator_if.awqos,
                            axi_initiator_if.awburst,
                            axi_initiator_if.awlock,
                            axi_initiator_if.awsize,
                            axi_initiator_if.awregion,
                            axi_initiator_if.awprot,
                            axi_initiator_if.awcache })
    );

    axi_reg_layer_handshake #(
        .DATA_WIDTH     (DATA_WIDTH + (DATA_WIDTH/8) + 1)
    ) i_w_handshake (
        .i_clk          (i_clk),
        .i_reset_n      (i_reset_n),
        .i_src_valid    (axi_responder_if.wvalid),
        .i_snk_ready    (axi_initiator_if.wready),
        .o_src_ready    (axi_responder_if.wready),
        .o_snk_valid    (axi_initiator_if.wvalid),
        .i_data_in      ({  axi_responder_if.wdata,
                            axi_responder_if.wstrb,
                            axi_responder_if.wlast }),
        .o_data_out     ({  axi_initiator_if.wdata,
                            axi_initiator_if.wstrb,
                            axi_initiator_if.wlast })
    );

    axi_reg_layer_handshake #(
        .DATA_WIDTH     (ADDR_WIDTH + LEN_WIDTH + ID_WIDTH + 4 + 2 + 1 + 3 + 3 + 3 + 4)
    ) i_ar_handshake (
        .i_clk          (i_clk),
        .i_reset_n      (i_reset_n),
        .i_src_valid    (axi_responder_if.arvalid),
        .i_snk_ready    (axi_initiator_if.arready),
        .o_src_ready    (axi_responder_if.arready),
        .o_snk_valid    (axi_initiator_if.arvalid),
        .i_data_in      ({  axi_responder_if.araddr,
                            axi_responder_if.arlen,
                            axi_responder_if.arid,
                            axi_responder_if.arqos,
                            axi_responder_if.arburst,
                            axi_responder_if.arlock,
                            axi_responder_if.arsize,
                            axi_responder_if.arregion,
                            axi_responder_if.arprot,
                            axi_responder_if.arcache }),

        .o_data_out     ({  axi_initiator_if.araddr,
                            axi_initiator_if.arlen,
                            axi_initiator_if.arid,
                            axi_initiator_if.arqos,
                            axi_initiator_if.arburst,
                            axi_initiator_if.arlock,
                            axi_initiator_if.arsize,
                            axi_initiator_if.arregion,
                            axi_initiator_if.arprot,
                            axi_initiator_if.arcache })
    );

    axi_reg_layer_handshake #(
        .DATA_WIDTH     (DATA_WIDTH + 1 + 2 + ID_WIDTH)
    ) i_r_handshake (
        .i_clk          (i_clk),
        .i_reset_n      (i_reset_n),
        .i_src_valid    (axi_initiator_if.rvalid),
        .i_snk_ready    (axi_responder_if.rready),
        .o_src_ready    (axi_initiator_if.rready),
        .o_snk_valid    (axi_responder_if.rvalid),
        .i_data_in      ({  axi_initiator_if.rdata,
                            axi_initiator_if.rlast,
                            axi_initiator_if.rresp,
                            axi_initiator_if.rid }),
        .o_data_out     ({  axi_responder_if.rdata,
                            axi_responder_if.rlast,
                            axi_responder_if.rresp,
                            axi_responder_if.rid })
    );

    axi_reg_layer_handshake #(
        .DATA_WIDTH     (2 + ID_WIDTH)
    ) i_b_handshake (
        .i_clk          (i_clk),
        .i_reset_n      (i_reset_n),
        .i_src_valid    (axi_initiator_if.bvalid),
        .i_snk_ready    (axi_responder_if.bready),
        .o_src_ready    (axi_initiator_if.bready),
        .o_snk_valid    (axi_responder_if.bvalid),
        .i_data_in      ({  axi_initiator_if.bresp,
                            axi_initiator_if.bid }),
        .o_data_out     ({  axi_responder_if.bresp,
                            axi_responder_if.bid })
    );
endmodule : axi_reg_layer


module axi_reg_layer_handshake #(
    parameter                           DATA_WIDTH = 8
)
(
    // Inputs
    input  wire                         i_clk,              // Clock
    input  wire                         i_reset_n,          // Negative synchronous reset

    input  wire                         i_src_valid,        // Source valid
    input  wire                         i_snk_ready,        // Sink ready
    input  wire [DATA_WIDTH-1:0]        i_data_in,          // Data stream to be registered

    // Outputs
    output reg                          o_src_ready,        // Ready to the source
    output reg                          o_snk_valid,        // Valid to the sink
    output reg  [DATA_WIDTH-1:0]        o_data_out          // Output registered data stream
);

    // A/B register set
    (* must_keep=1 *) logic [DATA_WIDTH-1:0]      reg_a;
    (* must_keep=1 *) logic [DATA_WIDTH-1:0]      reg_b;
    logic                       reg_a_write;
    logic                       reg_b_write;

    always @(posedge i_clk)
        if ( reg_a_write )
            reg_a <= i_data_in;

    always @(posedge i_clk)
        if ( reg_b_write )
            reg_b <= i_data_in;

    // Output mux
    // Need muxing signal derived from handshake sequences.
    // To reduce fanout, limit muxing signal to a fanout of 16
    // Create an independent signal for the handshake logic
    localparam OUT_SEL_B_WIDTH = ((DATA_WIDTH+15)/16);

    (* must_keep=1 *) logic [OUT_SEL_B_WIDTH -1:0] out_sel_b           /* synthesis syn_fanout=16 syn_preserve=1 */;
    (* must_keep=1 *) logic                        out_sel_b_handshake /* synthesis syn_preserve=1 */;

    integer ii;
    always_comb
        for (ii=0; ii<DATA_WIDTH; ii++)
            o_data_out[ii] = (out_sel_b[ii/16]) ? reg_b[ii] : reg_a[ii];

    // Source to sink bi-directional handshake
    // Consider register layer to be a 1-bit deep FIFO.
    // Sink issues ready.  Source issues valid.
    // Note : To avoid deadlock, AXI spec dictates that source can issue valid even when there is no
    // ready.  It does not have to wait.  Equally sink can issue ready ahead of time

    logic a_valid;      // Indicate when a value has been written to reg_a, before being read
    logic b_valid;      // Indicate when a value has been written to reg_b, before being read

    // Define read and write cycles into the registers
    logic  write;
    logic  read;
    logic  read_a;
    logic  read_b;

    assign write  = (i_src_valid & o_src_ready);
    assign read   = (i_snk_ready & o_snk_valid);
    assign read_a = (read & ~out_sel_b_handshake);
    assign read_b = (read &  out_sel_b_handshake);

    // Determine when there is a valid value in the registers
    // The change of state is when there is a write without a read
    // or read without a write.
    always @(posedge i_clk)
        if( ~i_reset_n )
            a_valid <= 1'b0;
        else if (reg_a_write & ~read_a)
            a_valid <= 1'b1;
        else if (~reg_a_write & read_a)
            a_valid <= 1'b0;

    always @(posedge i_clk)
        if( ~i_reset_n )
            b_valid <= 1'b0;
        else if (reg_b_write & ~read_b)
            b_valid <= 1'b1;
        else if (~reg_b_write & read_b)
            b_valid <= 1'b0;

    assign o_snk_valid = (a_valid || b_valid);
    
    always @(posedge i_clk)
        if( ~i_reset_n )
        begin
            out_sel_b_handshake <= 1'b0;
            out_sel_b           <= {OUT_SEL_B_WIDTH{1'b0}};
        end
        else if (read & ~out_sel_b_handshake)
        begin
            out_sel_b_handshake <= 1'b1;
            out_sel_b           <= {OUT_SEL_B_WIDTH{1'b1}};
        end
        else if (read & out_sel_b_handshake)
        begin
            out_sel_b_handshake <= 1'b0;
            out_sel_b           <= {OUT_SEL_B_WIDTH{1'b0}};
        end

    logic in_write_b;
    
    always @(posedge i_clk)
        if( ~i_reset_n )
            in_write_b <= 1'b0;
        else if (reg_a_write)
            in_write_b <= 1'b1;
        else if (reg_b_write)
            in_write_b <= 1'b0;

    // Determine when to write
    // The write signals involve fanning out the valid signal 512 times
    assign reg_a_write = write & ~in_write_b & (~a_valid || (a_valid & read_a));
    assign reg_b_write = write &  in_write_b & (~b_valid || (b_valid & read_b));
        
    // Enhancement : A future version could include times when about to read as well
    assign o_src_ready = (~a_valid || ~b_valid);    
    
endmodule : axi_reg_layer_handshake

