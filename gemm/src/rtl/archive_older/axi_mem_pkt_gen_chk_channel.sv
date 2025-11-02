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
//      Memory test channel incorporating an axi_pkt_gen and axi_pkt_chk
//      All inputs and outputs pipelined to support placement on the die
// ------------------------------------------------------------------

`include "nap_interfaces.svh"
`include "reg_control_defines.svh"

module axi_mem_pkt_gen_chk_channel
#(
    parameter   AXI_DATA_WIDTH          = 256,      // AXI interface data width
    parameter   AXI_ADDR_WIDTH          = 42,       // AXI interface address width

    parameter   LINEAR_PKTS             = 0,        // Set to 1 to make packets have linear counts
    parameter   LINEAR_ADDR             = 0,        // Set to 1 to have linear addresses
    parameter   MAX_BURST_LEN           = 0,        // Maximum number of AXI beats in a burst

    parameter   TGT_ADDR_WIDTH          = 0,        // Target address width.  This is less than the full NAP address width
                                                    // The full address is the concatenation of this address, and the TARGET_ID_ADDR
    parameter   TGT_ADDR_PAD_WIDTH      = 0,        // Target address padding.  Placed between target address and id
    parameter   TGT_ADDR_ID             = 0,        // Target address ID.  Page in NoC address mapping
                                                    // Width of this value + TGT_ADDR_PAD_WIDTH + TGT_ADDR_WIDTH = NAP_AXI_ADDR_WIDTH
    
    parameter logic [AXI_DATA_WIDTH-1:0] RAND_DATA_INIT = {AXI_DATA_WIDTH{1'b0}},
                                                    // Random value to start the data at
                                                    // Can be used to uniqify each axi_pkt_gen instance
    parameter   NO_AR_LIMIT             = 0,        // By default, AR's have a minimum gap to prevent GDDR/DDR pipeline reordering
                                                    // However, if this checker is used for just NAP to NAP communication, then this limit
                                                    // can be removed
    parameter   NUM_REGS                = 8,        // Number of read and write registers used by this channel
    parameter   CHANNEL_CLK_FREQ        = 400,      // Frequency of the channel clock.  Used to calibrate the performance monitor
    parameter   OUTPUT_PIPELINE_LENGTH  = 4         // Length of the done output pipeline
)
(
   
     // Inputs
    input  wire                         i_ch_clk,           // Channel clock
    input  wire                         i_reg_clk,          // Register clock
    input  wire                         i_ch_reset_n,       // Negative synchronous reset on channel clock
    input  t_ACX_USER_REG               i_regs_write [NUM_REGS -1:0],   // Array of registers to configure channel

    t_AXI4.initiator                    axi_if,             // AXI interface

    output t_ACX_USER_REG               o_regs_read  [NUM_REGS -1:0],   // Array of registers to monitor channel
    output wire                         o_running,          // Test is running.  Primarily for LED outputs
    output wire                         o_done,             // Test complete.  Primarily for LED outputs
    output wire                         o_fail              // Test failed.  Primarily for LED outputs
);

    // NOTE : It is the responsibility of the controlling block, (i.e. reg_control_block)
    //        to ensure that the channel is ready to transmit and receive data
    //        In practice, this means that DDR4 or GDDR6 training should be complete before
    //        this channel is activated.
    logic   gen_rstn_pre;
    logic   chk_rstn_pre;
    logic   fifo_rstn_pre;
    logic   mon_rstn_pre;
    logic   fifo_flush_pre;
    logic   gen_start_pre;
    logic   max_bursts_pre;
    logic   gen_stop_pre;
    logic   gen_rstn_q;
    logic   chk_rstn_q;
    logic   fifo_rstn_q;
    logic   mon_rstn_q;
    logic   mon_rstn_qq;
    logic   fifo_flush_q;
    logic   gen_start_q;
    logic   max_bursts_q;
    logic   gen_stop_q;
    logic   gen_rstn;
    logic   chk_rstn;
    logic   fifo_rstn;
    logic   mon_rstn;
    logic   fifo_flush;
    logic   gen_start;
    logic   max_bursts;
    logic   gen_stop;


    logic   test_running;
    logic   test_done;
    logic   gen_running;
    logic   gen_done;
    logic   pkt_error;
    logic   wr_error;

    logic [32 -1:0] test_gen_count;
    logic [8  -1:0] outstanding_compares;

    //------------------------------------------------
    // Registers
    //------------------------------------------------

    t_ACX_USER_REG control_reg;
    t_ACX_USER_REG status_reg;
    t_ACX_USER_REG num_transfers_reg;

    // Control register
    assign control_reg    = i_regs_write[0];
    assign o_regs_read[0] = control_reg;

    // As reg clock is normally slower than the channel clock, 
    // pipeline the control signals in the reg clock domain, then clock cross
    shift_reg #(.LENGTH(3), .WIDTH(1)) x_shift_gen_rstn
        (.i_clk (i_reg_clk), .i_rstn (1'b1), .i_din (control_reg[0]), .o_dout (gen_rstn_pre));
    shift_reg #(.LENGTH(3), .WIDTH(1)) x_shift_chk_rstn
        (.i_clk (i_reg_clk), .i_rstn (1'b1), .i_din (control_reg[1]), .o_dout (chk_rstn_pre));
    shift_reg #(.LENGTH(3), .WIDTH(1)) x_shift_fifo_rstn
        (.i_clk (i_reg_clk), .i_rstn (1'b1), .i_din (control_reg[2]), .o_dout (fifo_rstn_pre));
    shift_reg #(.LENGTH(3), .WIDTH(1)) x_shift_mon_rstn
        (.i_clk (i_reg_clk), .i_rstn (1'b1), .i_din (control_reg[3]), .o_dout (mon_rstn_pre));
    shift_reg #(.LENGTH(3), .WIDTH(1)) x_shift_fifo_flush
        (.i_clk (i_reg_clk), .i_rstn (1'b1), .i_din (control_reg[4]), .o_dout (fifo_flush_pre));
    shift_reg #(.LENGTH(3), .WIDTH(1)) x_shift_max_bursts
        (.i_clk (i_reg_clk), .i_rstn (1'b1), .i_din (control_reg[5]), .o_dout (max_bursts_pre));
    shift_reg #(.LENGTH(3), .WIDTH(1)) x_shift_gen_start
        (.i_clk (i_reg_clk), .i_rstn (1'b1), .i_din (control_reg[6]), .o_dout (gen_start_pre));
    shift_reg #(.LENGTH(3), .WIDTH(1)) x_shift_gen_stop
        (.i_clk (i_reg_clk), .i_rstn (1'b1), .i_din (control_reg[7]), .o_dout (gen_stop_pre));

    // Synchronize from control register to channel_clk
    ACX_SYNCHRONIZER x_sync_gen_rstn   (.din(gen_rstn_pre),   .dout(gen_rstn_q),   .clk(i_ch_clk), .rstn(i_ch_reset_n));
    ACX_SYNCHRONIZER x_sync_chk_rstn   (.din(chk_rstn_pre),   .dout(chk_rstn_q),   .clk(i_ch_clk), .rstn(i_ch_reset_n));
    ACX_SYNCHRONIZER x_sync_fifo_rstn  (.din(fifo_rstn_pre),  .dout(fifo_rstn_q),  .clk(i_ch_clk), .rstn(i_ch_reset_n));
    ACX_SYNCHRONIZER x_sync_mon_rstn   (.din(mon_rstn_pre),   .dout(mon_rstn_q),   .clk(i_ch_clk), .rstn(i_ch_reset_n));
    ACX_SYNCHRONIZER x_sync_fifo_flush (.din(fifo_flush_pre), .dout(fifo_flush_q), .clk(i_ch_clk), .rstn(i_ch_reset_n));
    ACX_SYNCHRONIZER x_sync_max_bursts (.din(max_bursts_pre), .dout(max_bursts_q), .clk(i_ch_clk), .rstn(i_ch_reset_n));
    ACX_SYNCHRONIZER x_sync_gen_start  (.din(gen_start_pre),  .dout(gen_start_q),  .clk(i_ch_clk), .rstn(i_ch_reset_n));
    ACX_SYNCHRONIZER x_sync_gen_stop   (.din(gen_stop_pre),   .dout(gen_stop_q),   .clk(i_ch_clk), .rstn(i_ch_reset_n));

    // Add additional flop after synchronizing, to allow for easier fanout and duplication
    always @(posedge i_ch_clk)
    begin
        gen_rstn   <= gen_rstn_q;
        chk_rstn   <= chk_rstn_q;
        fifo_rstn  <= fifo_rstn_q;
        mon_rstn_qq <= mon_rstn_q;
        mon_rstn   <= mon_rstn_qq;
        fifo_flush <= fifo_flush_q;
        max_bursts <= max_bursts_q;
        gen_start  <= gen_start_q;
        gen_stop   <= gen_stop_q;
    end

    // Status register
    assign o_regs_read[1] = status_reg;
    assign status_reg     = {16'b0, outstanding_compares, 2'b00, wr_error, pkt_error, gen_done, gen_running, test_done, test_running};

    // Number of transfers register
    assign num_transfers_reg = i_regs_write[2];
    assign o_regs_read[2]    = num_transfers_reg;

    // Outstanding transfers register
    assign o_regs_read[3]    = test_gen_count;

    // Transacton FIFO parameters
    localparam MAX_FIFO_WIDTH    = 72;     // Fixed port widths of 72
    localparam FIFO_WIDTH        = 72;     // Address width are 42 or 33, + 8 for len.  So 72 required

    // Values passed from writing block
    logic [TGT_ADDR_WIDTH-1:0]  wr_addr;
    logic [TGT_ADDR_WIDTH-1:0]  rd_addr;
    logic [7:0]                 wr_len;
    logic [7:0]                 rd_len;
    logic                       written_valid;
    logic                       pkt_compared;
    logic                       continuous_test;
    logic                       axi_wr_enable;

    // Values to pass through FIFO
    logic [MAX_FIFO_WIDTH -1:0] fifo_data_in;
    logic [MAX_FIFO_WIDTH -1:0] fifo_data_out;
    // FIFO control
    logic                       fifo_rden;
    logic                       fifo_empty;
    logic                       fifo_full;

    // Assign values to and from FIFO
    // Structures would be ideal here, except cannot be used as ports to FIFO
    // Do in the one block so that they can be checked for consistency
    assign fifo_data_in     = {{(MAX_FIFO_WIDTH-$bits(wr_len)-$bits(wr_addr)){1'b0}}, wr_len, wr_addr};
    assign rd_addr          = fifo_data_out[$bits(rd_addr)-1:0];
    assign rd_len           = fifo_data_out[$bits(rd_addr)+$bits(rd_len)-1:$bits(rd_addr)];

    // Hold off writing transactions if transfer FIFO fills up        
    assign axi_wr_enable    = (gen_running & ~fifo_full & ~gen_stop);

    // This will cross clock domains, however continuous test is only used
    // once the test is running, and so num_transactions should be stable during
    // the test run.  Therefore continuous_test should not toggle during the test
    always @(posedge i_ch_clk)
        continuous_test <= (num_transfers_reg == 32'h0) & ~gen_stop;

    // Create a signal to indicate the test is running
    // Reset with generator reset as this starts and stops test
    logic gen_start_d;
    logic gen_start_2d;
    logic gen_start_3d;
    always @(posedge i_ch_clk)
    begin
        gen_start_d  <= gen_start;
        gen_start_2d <= gen_start_d;
        gen_start_3d <= gen_start_2d;
        if( ~gen_rstn ) 
            gen_running <= 1'b0;
        else 
        begin
            // Test starts on rising edge of delayed start signal
            // when test is not yet running
            // Need delay to allow test_gen_counter to be loaded
            if ( gen_start_2d & ~gen_start_3d & ~gen_running)
                gen_running <= 1'b1;
            else if (gen_done)
                gen_running <= 1'b0;
        end
    end

    //------------------------------------------------
    // Transmit counter
    //------------------------------------------------

    // Create test counter as a 24-bit counter, composed of 3x 8-bit counters for speed.
    // Decrement the generate counter each time we write a transaction
    logic [9 -1:0]  test_gen_count_lsb;     // Includes carry bit
    logic [8 -1:0]  test_gen_count_lsb_d;
    logic [8 -1:0]  test_gen_count_lsb_2d;
    logic [8 -1:0]  test_gen_count_lsb_3d;
    logic [9 -1:0]  test_gen_count_1;       // Includes carry bit
    logic [8 -1:0]  test_gen_count_1_d;
    logic [8 -1:0]  test_gen_count_1_2d;
    logic [9 -1:0]  test_gen_count_2;       // Includes carry bit
    logic [8 -1:0]  test_gen_count_2_d;
    logic [8 -1:0]  test_gen_count_msb;
    logic           test_gen_msb_zero;
    logic           test_gen_1_zero;
    logic           test_gen_2_zero;
    logic           test_count_dec;
    logic           test_count_dec_d;
    logic           test_count_dec_2d;
    logic           test_count_dec_3d;
    logic           test_count_load;

    always @(posedge i_ch_clk)
    begin
        test_gen_count_lsb_d  <= test_gen_count_lsb[7:0];
        test_gen_count_lsb_2d <= test_gen_count_lsb_d;
        test_gen_count_lsb_3d <= test_gen_count_lsb_2d;
        test_gen_count_1_d    <= test_gen_count_1[7:0];
        test_gen_count_1_2d   <= test_gen_count_1_d;
        test_gen_count_2_d    <= test_gen_count_2[7:0];
        test_gen_count <= {test_gen_count_msb, test_gen_count_2_d, test_gen_count_1_2d, test_gen_count_lsb_3d};
    end

    assign test_count_dec  = (written_valid && ~continuous_test && ~gen_done);

    always @(posedge i_ch_clk)
        test_count_load <= (gen_start & ~gen_start_d & ~gen_running) || gen_stop;

    always @(posedge i_ch_clk)
    begin
        test_count_dec_d  <= test_count_dec;
        test_count_dec_2d <= test_count_dec_d;
        test_count_dec_3d <= test_count_dec_2d;
    end

    always @(posedge i_ch_clk)
    begin
        if( ~gen_rstn ) 
        begin
            test_gen_count_lsb <= 9'h0;
            test_gen_count_1   <= 9'h0;
            test_gen_count_2   <= 9'h0;
            test_gen_count_msb <= 8'h0;
        end
        else 
        begin
            // The load phase will cross clock domains
            // However num_transfer_reg will be stable at this point
            if (test_count_load)
                test_gen_count_lsb <= {1'b0, num_transfers_reg[7:0]};
            else if (test_count_dec)
                test_gen_count_lsb <= {1'b0, test_gen_count_lsb[7:0]} - 9'h1;
            else
                test_gen_count_lsb <= {1'b0, test_gen_count_lsb[7:0]};

            if (test_count_load)
                test_gen_count_1   <= {1'b0, num_transfers_reg[15:8]};
            else if (test_gen_count_lsb[8] & test_count_dec_d)
                test_gen_count_1   <= {1'b0, test_gen_count_1[7:0]} - 9'h1;
            else
                test_gen_count_1   <= {1'b0, test_gen_count_1[7:0]};

            if (test_count_load)
                test_gen_count_2   <= {1'b0, num_transfers_reg[23:16]};
            else if (test_gen_count_1[8] & test_count_dec_2d)
                test_gen_count_2   <= {1'b0, test_gen_count_2[7:0]} - 9'h1;
            else
                test_gen_count_2   <= {1'b0, test_gen_count_2[7:0]};

            if (test_count_load)
                test_gen_count_msb <= num_transfers_reg[31:24];
            else if (test_gen_count_2[8] & test_count_dec_3d)
                test_gen_count_msb <= test_gen_count_msb[7:0] - 8'h1;
            else
                test_gen_count_msb <= test_gen_count_msb[7:0];

        end
    end

    // Pre-calculate when the higher order counters have got to 0
    always @(posedge i_ch_clk)
        test_gen_msb_zero <= (test_gen_count_msb == 8'h0);

    always @(posedge i_ch_clk)
        test_gen_1_zero   <= (test_gen_count_1[7:0] == 8'h0);

    always @(posedge i_ch_clk)
        test_gen_2_zero   <= (test_gen_count_2[7:0] == 8'h0);

    // Generate done signal.  Reset with checker reset
    always @(posedge i_ch_clk)
    begin
        if( ~gen_rstn )
            gen_done <= 1'b0;
        else if ((test_gen_count_lsb[7:0] == 8'h0) & test_gen_1_zero & test_gen_2_zero & test_gen_msb_zero & ~continuous_test & gen_running)
            gen_done <= 1'b1;
    end

    // Compare the transactions read against the packets compared
    // Will always be positive, not going to exceed an 8-bit count
    always @(posedge i_ch_clk)
    begin
        if( ~chk_rstn )
            outstanding_compares <= 8'h0;
        else 
            case ({pkt_compared, fifo_rden})
                2'b00 : outstanding_compares <= outstanding_compares;
                2'b01 : outstanding_compares <= outstanding_compares + 8'h1;
                2'b10 : outstanding_compares <= outstanding_compares - 8'h1;
                2'b11 : outstanding_compares <= outstanding_compares;
            endcase
    end

    always @(posedge i_ch_clk)
    begin
        if( ~chk_rstn )
            test_done <= 1'b0;
        else if (gen_done & fifo_empty & (outstanding_compares == 8'h0))
            // Test is complete once the last entry has been read and compared
            test_done <= 1'b1;
    end

    always @(posedge i_ch_clk)
    begin
        if( ~chk_rstn )
            test_running <= 1'b0;
        else if (gen_running)
            test_running <= 1'b1;
        else if (test_done)
            test_running <= 1'b0;
    end

    // Stop the performance monitor block measurements 
    logic test_done_d;
    logic mon_measurement_stop;

    always@(posedge i_ch_clk)
    begin
        test_done_d <= test_done;
        if(test_done && !test_done_d) // Edge detect end of test
            mon_measurement_stop <= 1'b1;
        else
            mon_measurement_stop <= 1'b0;
    end

    // Instantiate AXI transaction generator
    axi_pkt_gen #(
        .LINEAR_PKTS                    (LINEAR_PKTS),
        .LINEAR_ADDR                    (LINEAR_ADDR),
        .TGT_ADDR_WIDTH                 (TGT_ADDR_WIDTH),
        .TGT_ADDR_PAD_WIDTH             (TGT_ADDR_PAD_WIDTH),
        .TGT_ADDR_ID                    (TGT_ADDR_ID),
        .TGT_DATA_WIDTH                 (AXI_DATA_WIDTH),
        .MAX_BURST_LEN                  (MAX_BURST_LEN),
        .AXI_ADDR_WIDTH                 (AXI_ADDR_WIDTH),
        .RAND_DATA_INIT                 (RAND_DATA_INIT)
    ) i_axi_pkt_gen (
        // Inputs
        .i_clk                          (i_ch_clk),
        .i_reset_n                      (gen_rstn),
        .i_start                        (gen_running),
        .i_enable                       (axi_wr_enable),
        .i_max_bursts                   (max_bursts),
        // Interfaces
        .axi_if                         (axi_if),
        // Outputs
        .o_addr_written                 (wr_addr),
        .o_len_written                  (wr_len),
        .o_written_valid                (written_valid),
        .o_wr_error                     (wr_error)
    );

    // FIFO the address and length written, and then read out into the checker
    // FIFO is 72-bits wide by 32-words deep
    ACX_LRAM2K_FIFO #(
        .aempty_threshold               (6'h4),
        .afull_threshold                (6'h4),
        .fwft_mode                      (1'b0),     
        .outreg_enable                  (1'b1),
        .rdclk_polarity                 ("rise"),
        .read_width                     (FIFO_WIDTH),
        .sync_mode                      (1'b1),
        .wrclk_polarity                 ("rise"),
        .write_width                    (FIFO_WIDTH)
    ) i_xact_fifo ( 
        .din                            (fifo_data_in),
        .rstn                           (fifo_rstn),
        .wrclk                          (i_ch_clk),
        .rdclk                          (i_ch_clk),
        .wren                           (written_valid),
        .rden                           (fifo_rden | fifo_flush),
        .outreg_rstn                    (fifo_rstn),
        .outreg_ce                      (1'b1),
        .dout                           (fifo_data_out),
        .almost_full                    (),
        .full                           (fifo_full),
        .almost_empty                   (),
        .empty                          (fifo_empty),
        .write_error                    (),
        .read_error                     ()
    );

    // With overlapping writes from axi_pkt_gen, must ensure that a relevant bresp
    // has been received before reading from the channel
    // Count reads and bresp, and only issue a valid read when greater than zero
    // Note : This will not support out of order bresp.  However the current external
    // memories and NoC maintain bresp ordering
    logic [6 -1:0]  valid_bresp_count;
    logic           b_xact;
    logic           valid_write_xact;

    always @(posedge i_ch_clk)
        b_xact <= (axi_if.bready & axi_if.bvalid);

    always @(posedge i_ch_clk)
        if (~fifo_rstn)
            valid_bresp_count <= 6'b0;
        else case ({fifo_rden, b_xact})
            2'b00 : valid_bresp_count <= valid_bresp_count;
            2'b01 : valid_bresp_count <= valid_bresp_count + 6'b1;
            2'b10 : valid_bresp_count <= valid_bresp_count - 6'b1;
            2'b11 : valid_bresp_count <= valid_bresp_count;
        endcase

    always @(posedge i_ch_clk)
        valid_write_xact <= (valid_bresp_count > 6'b0);

    // Instantiate AXI transaction checker
    // Must have the same configuration as the generator
    axi_pkt_chk #(
        .LINEAR_PKTS                    (LINEAR_PKTS),
        .TGT_ADDR_WIDTH                 (TGT_ADDR_WIDTH),
        .TGT_ADDR_PAD_WIDTH             (TGT_ADDR_PAD_WIDTH),
        .TGT_ADDR_ID                    (TGT_ADDR_ID),
        .TGT_DATA_WIDTH                 (AXI_DATA_WIDTH),
        .AXI_ADDR_WIDTH                 (AXI_ADDR_WIDTH),
        .RAND_DATA_INIT                 (RAND_DATA_INIT),
        .NO_AR_LIMIT                    (NO_AR_LIMIT)
    ) i_axi_pkt_chk (
        // Inputs
        .i_clk                          (i_ch_clk),
        .i_reset_n                      (chk_rstn),
        .i_xact_avail                   (~fifo_empty & valid_write_xact),
        .i_xact_addr                    (rd_addr),
        .i_xact_len                     (rd_len),

        // Interfaces
        .axi_if                         (axi_if),
        // Outputs
        .o_xact_read                    (fifo_rden),
        .o_pkt_compared                 (pkt_compared),
        .o_pkt_error                    (pkt_error)
    );

    // Pipeline outputs
    shift_reg #(.LENGTH(OUTPUT_PIPELINE_LENGTH),  .WIDTH(1)) x_shift_reg_fail 
        (.i_clk (i_ch_clk), .i_rstn (1'b1), .i_din (pkt_error | wr_error), .o_dout (o_fail));
    shift_reg #(.LENGTH(OUTPUT_PIPELINE_LENGTH),  .WIDTH(1)) x_shift_reg_done
        (.i_clk (i_ch_clk), .i_rstn (1'b1), .i_din (test_done), .o_dout (o_done));
    shift_reg #(.LENGTH(OUTPUT_PIPELINE_LENGTH),  .WIDTH(1)) x_shift_reg_running
        (.i_clk (i_ch_clk), .i_rstn (1'b1), .i_din (test_running), .o_dout (o_running));


    // Need to create an instance of the AXI4 port for the performance monitor.
    // This is because the performance monitor is a monitor port, but this
    // module has an initiator port.  So purely a directional mapping
    // Instantiate AXI_4 interfaces for nap
    t_AXI4 #(
        .DATA_WIDTH (AXI_DATA_WIDTH),
        .ADDR_WIDTH (AXI_ADDR_WIDTH),
        .LEN_WIDTH  (8),
        .ID_WIDTH   (8) )
    mon_if();

    // Assign signals from input initiator interface to local, monitor, interface
    assign mon_if.awvalid  = axi_if.awvalid;
    assign mon_if.awready  = axi_if.awready;
    assign mon_if.awaddr   = axi_if.awaddr;
    assign mon_if.awlen    = axi_if.awlen;
    assign mon_if.awid     = axi_if.awid;
    assign mon_if.awqos    = axi_if.awqos;
    assign mon_if.awburst  = axi_if.awburst;
    assign mon_if.awlock   = axi_if.awlock;
    assign mon_if.awsize   = axi_if.awsize;
    assign mon_if.awregion = axi_if.awregion;
    assign mon_if.awprot   = axi_if.awprot;
    assign mon_if.awcache  = axi_if.awcache;
    assign mon_if.wvalid   = axi_if.wvalid;
    assign mon_if.wready   = axi_if.wready;
    assign mon_if.wdata    = axi_if.wdata;
    assign mon_if.wstrb    = axi_if.wstrb;
    assign mon_if.wlast    = axi_if.wlast;
    assign mon_if.arready  = axi_if.arready;
    assign mon_if.rdata    = axi_if.rdata;
    assign mon_if.rlast    = axi_if.rlast;
    assign mon_if.rresp    = axi_if.rresp;
    assign mon_if.rvalid   = axi_if.rvalid;
    assign mon_if.rid      = axi_if.rid;
    assign mon_if.araddr   = axi_if.araddr;
    assign mon_if.arlen    = axi_if.arlen;
    assign mon_if.arid     = axi_if.arid;
    assign mon_if.arqos    = axi_if.arqos;
    assign mon_if.arburst  = axi_if.arburst;
    assign mon_if.arlock   = axi_if.arlock;
    assign mon_if.arsize   = axi_if.arsize;
    assign mon_if.arvalid  = axi_if.arvalid;
    assign mon_if.arregion = axi_if.arregion;
    assign mon_if.arprot   = axi_if.arprot;
    assign mon_if.arcache  = axi_if.arcache;
    assign mon_if.rready   = axi_if.rready;
    assign mon_if.bvalid   = axi_if.bvalid;
    assign mon_if.bready   = axi_if.bready;
    assign mon_if.bresp    = axi_if.bresp;
    assign mon_if.bid      = axi_if.bid;

    // Instantiate NAP AXI performance monitor
    // Reset whenever generator or checker resets are asserted
    axi_performance_monitor #(
        .BW_WINDOW_SIZE            (2048),
        .CLOCK_FREQ                (CHANNEL_CLK_FREQ),
        .DATA_WIDTH                (AXI_DATA_WIDTH),
        .INPUT_REG_STAGES          (2)  
    ) i_axi_performance_monitor (
        // Inputs
        .i_clk                     (i_ch_clk),
        .i_reset_n                 (mon_rstn),
        .i_start                   (gen_start),
        .i_stop                    (mon_measurement_stop),
        .i_counter_reset           (~mon_rstn),

        // Interfaces
        .axi_if                    (mon_if),

        // Outputs
        .o_bw_results_rd           (o_regs_read[4]),
        .o_bw_results_wr           (o_regs_read[5]),
        .o_latency_results_current (o_regs_read[6]),
        .o_latency_results_avg     (o_regs_read[7]),
        .o_latency_results_max     (o_regs_read[8]),
        .o_latency_results_min     (o_regs_read[9]),
        .o_clock_freq_data_width   (o_regs_read[10])
    );

endmodule : axi_mem_pkt_gen_chk_channel
