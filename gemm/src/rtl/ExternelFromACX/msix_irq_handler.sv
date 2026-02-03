// ------------------------------------------------------------------
//
// Copyright (c) 2024 Achronix Semiconductor Corp.
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
// PCIe MSI-X Application block  
//      Generate MSI-X Doorbell requests for multiple (optional) channels
// ------------------------------------------------------------------

`include "nap_interfaces.svh"
`include "reg_control_defines.svh"

module msix_irq_handler
#(
    parameter   NUM_CHANNELS            = 1,                        // Number of interrupt channels
    parameter   NUM_REGS                = 4 + (4 * NUM_CHANNELS)    // Number of read and write registers used by the handler
)
(
    input  wire                         i_clk,
    input  wire                         i_reset_n,
    input  t_ACX_USER_REG               i_regs_write [NUM_REGS -1:0],   // Array of registers to configure channel
    
    output t_ACX_USER_REG               o_regs_read  [NUM_REGS -1:0]    // Array of registers to monitor channel
);

    localparam CHANNEL_POINTER_WIDTH = (NUM_CHANNELS == 1) ? 1 : $clog2(NUM_CHANNELS);

    logic [CHANNEL_POINTER_WIDTH -1:0] ch_ptr;
    logic [NUM_CHANNELS -1:0] interrupt_enable;
    logic [NUM_CHANNELS -1:0] interrupt_enable_d;
    logic [NUM_CHANNELS -1:0] ch_pending_bits;
    logic [NUM_CHANNELS -1:0] clr_ch_pending_mask;

    // Code up bid errors explicitly
    logic   bid_error;
    // Prevent b_xact being merged with axi_reg_layer handshake signals
    logic   b_xact /* synthesis syn_preserve=1 */;

    // mask to clear pending bits for serviced channels
    assign clr_ch_pending_mask = ~(b_xact << ch_ptr);

    // Interrupt triggered on rising edge of interrupt enable
    always_ff @(posedge i_clk)
    begin
        if ( ~i_reset_n )
        begin
            interrupt_enable_d  <= {NUM_CHANNELS{1'b0}};
            ch_pending_bits <= 'h0;
        end
        else
        begin
            interrupt_enable_d <= interrupt_enable;

            if ( (interrupt_enable & ~interrupt_enable_d) || b_xact )
                ch_pending_bits <= (ch_pending_bits & clr_ch_pending_mask) | ( interrupt_enable & ~interrupt_enable_d );
        end
    end

    // Register Interface
    localparam    CH_REGS_NUM       = 4;    // CONTROL, DB_DATA, and DB_CNT_STATUS are registers used for each channel
    localparam    DB_ADDR_LOW       = 0;
    localparam    DB_ADDR_HIGH      = 1;
    localparam    CONTROL           = 4;    // Bit 31 is the interrupt enable signal, rising edge trigger
    localparam    DB_DATA           = 5;
    localparam    DB_CNT_STATUS     = 6;

    logic [NUM_CHANNELS -1:0] count_reset;
    logic [31:0] db_sent_cnt [0:NUM_CHANNELS -1];

    assign o_regs_read[DB_ADDR_LOW]   = i_regs_write[DB_ADDR_LOW];
    assign o_regs_read[DB_ADDR_HIGH]  = {22'h0, i_regs_write[DB_ADDR_HIGH][9:0]};

    genvar i;
    generate
        for (i = 0; i < NUM_CHANNELS; i++) begin : gb_ch_regs
            assign o_regs_read[CONTROL+(CH_REGS_NUM*i)]       = i_regs_write[CONTROL+(CH_REGS_NUM*i)];
            assign o_regs_read[DB_DATA+(CH_REGS_NUM*i)]       = i_regs_write[DB_DATA+(CH_REGS_NUM*i)];
            assign o_regs_read[DB_CNT_STATUS+(CH_REGS_NUM*i)] = db_sent_cnt[i];

            assign interrupt_enable[i] = i_regs_write[CONTROL+(CH_REGS_NUM*i)][31];
            assign count_reset[i]      = i_regs_write[CONTROL+(CH_REGS_NUM*i)][0];

            // Count successful writes sent
            always @(posedge i_clk)
            begin
                if ( ~i_reset_n | count_reset[i] )
                    db_sent_cnt[i] <= 32'h0;
                else if ( b_xact & ~bid_error & (i == ch_ptr) )
                    db_sent_cnt[i] <= db_sent_cnt[i] + 32'h1;
            end
        end
    endgenerate

    // -------------------------------------------------------------------------
    // State machine to service interrupts
    // -------------------------------------------------------------------------
    // Round robin handling of channel interrupts
    enum {POLL_CHANNELS, ISSUE_INTERRUPT} state;
    logic start;
    
    always_ff @(posedge i_clk)
    begin
        start <= 1'b0;
        if ( ~i_reset_n )
        begin
            state  <= POLL_CHANNELS;
            ch_ptr <= 'h0;
        end
        else
        begin
            case (state)
                POLL_CHANNELS:
                begin
                    if ( ch_pending_bits[ch_ptr] )
                    begin
                        start <= 1'b1;
                        
                        state <= ISSUE_INTERRUPT;
                    end
                    else
                    begin
                        if ( ch_ptr == (NUM_CHANNELS-1) )
                            ch_ptr <= {(CHANNEL_POINTER_WIDTH){1'b0}};
                        else
                            ch_ptr <= ch_ptr + {{(CHANNEL_POINTER_WIDTH-1){1'b0}}, 1'b1};
                        
                        state  <= POLL_CHANNELS;
                    end
                end

                ISSUE_INTERRUPT :
                begin
                    if ( b_xact )
                    begin
                        if ( ch_ptr == (NUM_CHANNELS-1) )
                            ch_ptr <= {(CHANNEL_POINTER_WIDTH){1'b0}};
                        else
                            ch_ptr <= ch_ptr + {{(CHANNEL_POINTER_WIDTH-1){1'b0}}, 1'b1};

                        state <= POLL_CHANNELS;
                    end
                    else 
                        state <= ISSUE_INTERRUPT;
                end

                default :
                    state  <= POLL_CHANNELS;
            endcase
        end
    end

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
    nap_responder_wrapper i_axi_responder_nap (
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

    assign axi_if.awaddr = { i_regs_write[DB_ADDR_HIGH][9:0], i_regs_write[DB_ADDR_LOW] };

    always_ff @(posedge i_clk)
    begin
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
                    if( start )
                        wr_state    <= WR_VALID;
                    else
                        wr_state    <= WR_IDLE;
                end

                WR_VALID :
                begin
                    // Set initial address and data valids
                    wr_state       <= WR_READY;

                    axi_if.awid    <= 8'h0;     // Using AWID 0 for all writes
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
                        wr_state            <= WR_IDLE;
                end

                default :
                    wr_state <= WR_IDLE;
            endcase
        end
    end

    // Compare 8 bits and 2 bits.
    always @(posedge i_clk)
        bid_error <= (( axi_if.bid != 8'h0 ) || (axi_if.bresp != 0));

    always @(posedge i_clk)
        b_xact <= (axi_if.bready & axi_if.bvalid);

    // Set 32 bit data at the correct offset on the 256 bit AXI data bus based on address
    always_comb
    begin
        axi_if.wdata = {256{1'b0}};
        case (i_regs_write[DB_ADDR_LOW][4:2])
            3'b000 : axi_if.wdata[(32*0) +: 32] = i_regs_write[DB_DATA+(CH_REGS_NUM*ch_ptr)];
            3'b001 : axi_if.wdata[(32*1) +: 32] = i_regs_write[DB_DATA+(CH_REGS_NUM*ch_ptr)];
            3'b010 : axi_if.wdata[(32*2) +: 32] = i_regs_write[DB_DATA+(CH_REGS_NUM*ch_ptr)];
            3'b011 : axi_if.wdata[(32*3) +: 32] = i_regs_write[DB_DATA+(CH_REGS_NUM*ch_ptr)];
            3'b100 : axi_if.wdata[(32*4) +: 32] = i_regs_write[DB_DATA+(CH_REGS_NUM*ch_ptr)];
            3'b101 : axi_if.wdata[(32*5) +: 32] = i_regs_write[DB_DATA+(CH_REGS_NUM*ch_ptr)];
            3'b110 : axi_if.wdata[(32*6) +: 32] = i_regs_write[DB_DATA+(CH_REGS_NUM*ch_ptr)];
            3'b111 : axi_if.wdata[(32*7) +: 32] = i_regs_write[DB_DATA+(CH_REGS_NUM*ch_ptr)];
        endcase
    end

    // Set the appropriate write strobe signals based on address
    always_comb
    begin
        axi_if.wstrb = {32{1'b0}};
        case (i_regs_write[DB_ADDR_LOW][4:2])
            3'b000 : axi_if.wstrb[(4*0) +: 4] = {4{axi_if.wvalid}};
            3'b001 : axi_if.wstrb[(4*1) +: 4] = {4{axi_if.wvalid}};
            3'b010 : axi_if.wstrb[(4*2) +: 4] = {4{axi_if.wvalid}};
            3'b011 : axi_if.wstrb[(4*3) +: 4] = {4{axi_if.wvalid}};
            3'b100 : axi_if.wstrb[(4*4) +: 4] = {4{axi_if.wvalid}};
            3'b101 : axi_if.wstrb[(4*5) +: 4] = {4{axi_if.wvalid}};
            3'b110 : axi_if.wstrb[(4*6) +: 4] = {4{axi_if.wvalid}};
            3'b111 : axi_if.wstrb[(4*7) +: 4] = {4{axi_if.wvalid}};
        endcase
    end

endmodule : msix_irq_handler