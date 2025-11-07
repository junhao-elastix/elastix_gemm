// ------------------------------------------------------------------
//
// Copyright (c) 2025 Achronix Semiconductor Corp.
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
// FLR Responder logic block  
//      Generate AXI write to CSR register for Function Level Reset (FLR) completion
// ------------------------------------------------------------------
`include "nap_interfaces.svh"

module flr_responder
(
    input  wire         i_clk,
    input  wire         i_reset_n,
    input  wire         i_enable,           // set enable high to send FLR done bits
    input  wire  [3:0]  flr_pf_done,        // bit3 - PF3, bit2 - PF2, bit1 - PF1, bit0 - PF0

    output logic        o_wr_error,         // Asserted if there is an error writing
    output logic        o_written_valid
);

    logic written_valid;
    logic write_error;

    // Assign outputs
    assign o_written_valid  = written_valid;
    assign o_wr_error       = write_error;

    //------------------------------------------------------------
    // AXI responder NAP and interface
    //------------------------------------------------------------
    // Instantiate AXI_4 interfaces for nap
    t_AXI4 #(
            .DATA_WIDTH (`ACX_NAP_AXI_DATA_WIDTH),
            .ADDR_WIDTH (`ACX_NAP_AXI_RESPONDER_ADDR_WIDTH),
            .LEN_WIDTH  (8),
            .ID_WIDTH   (8))
    axi_if();

    // Non AXI signals from AXI NAP
    logic                       nap_output_rstn;
    logic                       nap_error_valid;
    logic [2:0]                 nap_error_info;

    // Set location in pdc file / testbench bind statement
    nap_responder_wrapper #(
        .CSR_ACCESS_ENABLE(1'b1)
    ) i_axi_responder_nap (
        .i_clk              (i_clk),
        .i_reset_n          (i_reset_n),
        .nap                (axi_if),
        .o_output_rstn      (nap_output_rstn),
        .o_error_valid      (nap_error_valid),
        .o_error_info       (nap_error_info)
    );

    localparam TGT_LENGTH_SIZE = 8'h0;      // Use one beat to transfer data
    localparam TGT_BURST_SIZE  = 3'b010;    // Transfer 4-bytes
    
    // -------------------------------------------------------------------------
    // State machine to send AXI write
    // -------------------------------------------------------------------------
    enum {WR_IDLE, WR_VALID, WR_READY} wr_state;

    // Read Channel not used
    assign axi_if.arvalid = 1'b0;
    assign axi_if.rready  = 1'b0;

    // CSR address for FLR done register
    assign axi_if.awaddr = 42'h819100017c;
    
    // 32-bit data data for target address 0x0819100017c is aligned at the 8th doubleword on the 256-bit AXI data bus
    assign axi_if.wdata[(32*7) +: 32] = { {28{1'b0}}, flr_pf_done };

    // enable byte lanes for the 8th doubleword on the 256 bit bus
    assign axi_if.wstrb = 32'hf0000000;

    always_ff @(posedge i_clk)
    begin
        written_valid <= 1'b0;
        if ( ~i_reset_n )
        begin
            wr_state        <= WR_IDLE;
            axi_if.awsize   <= 3'h0;
            axi_if.awburst  <= 2'b00;

            // Not necessary to reset address and data buses
            // Will aid synthesis timing
            axi_if.awlen    <= 'h0;
            axi_if.awlock   <= 1'b0;
            axi_if.awqos    <= 1'b0;
            axi_if.awregion <= 3'h0;
            axi_if.awprot   <= 3'b010;      // Unprivileged, Non-secure, data access
            axi_if.awcache  <= 4'h0;        // Non-bufferable, (i.e. standard memory access)
            axi_if.awid     <= 'h0;

            // Do all handshake signals as non-blocking
            // to prevent simulation race conditions
            axi_if.awvalid  <= 1'b0;
            axi_if.wvalid   <= 1'b0;
            axi_if.wlast    <= 1'b0;

            axi_if.bready   <= 1'b1;
        end
        else
        begin
            // Fixed values that do not change
            axi_if.awlen   <= TGT_LENGTH_SIZE;
            axi_if.awsize  <= TGT_BURST_SIZE;
            axi_if.awburst <= 2'b01;    // Incrementing bursts.  Fixed bursts are not supported

            case (wr_state)
                WR_IDLE :
                begin
                    if( i_enable )
                        wr_state    <= WR_VALID;
                    else
                        wr_state    <= WR_IDLE;
                end

                WR_VALID :
                begin
                    // Set initial address and data valids
                    wr_state       <= WR_READY;

                    axi_if.awid    <= 8'h02;    // Using AWID 2 for all writes
                    axi_if.awvalid <= 1'b1;
                    axi_if.wvalid  <= 1'b1;
                    axi_if.wlast   <= 1'b1;     // Only one beat per transfer
                end

                WR_READY :
                begin
                    // Write the address and data word

                    // AXI spec dicates that valid should be asserted
                    // and should not wait for ready.  This is to prevent deadlocks

                    // Can only have a single cycle of ready & valid for both of address and data cycles.
                    if ( axi_if.awready )
                        axi_if.awvalid <= 1'b0;
                    if ( axi_if.wready )
                    begin
                        axi_if.wvalid <= 1'b0;
                        axi_if.wlast  <= 1'b0;
                    end
                    // Transfer complete
                    if ( (axi_if.awready || ~axi_if.awvalid) && (axi_if.wready || ~axi_if.wvalid) )
                        written_valid <= 1'b1;
                        wr_state      <= WR_IDLE;
                end

                default :
                    wr_state <= WR_IDLE;
            endcase
        end
    end

    // Code up bid errors explicitly and pipeline
    logic   bid_error;
    // Prevent b_xact being merged with axi_reg_layer handshake signals
    logic   b_xact /* synthesis syn_preserve=1 */;

    // Compare 8 bits and 2 bits.
    always @(posedge i_clk)
        bid_error <= (( axi_if.bid != 8'h0 ) || (axi_if.bresp != 0));

    always @(posedge i_clk)
        b_xact <= (axi_if.bready & axi_if.bvalid);

    always @(posedge i_clk)
        if ( ~i_reset_n )
            write_error    <= 1'b0;
        else if (b_xact & bid_error)
            write_error    <= 1'b1;

endmodule : flr_responder
