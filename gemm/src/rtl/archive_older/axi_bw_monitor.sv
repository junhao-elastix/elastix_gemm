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
// Monitors packets received from AXI bus for bandwith performance
//      Designed to read from NAPs, will monitor the amount of
//      written or read data over a window of user definable clock cycles.
//      Per default the window size is set to 2048.
// ------------------------------------------------------------------

`include "nap_interfaces.svh"
`include "reg_control_defines.svh"

module axi_bw_monitor
#(
    parameter BW_WINDOW_SIZE    = 2048,     // Size of the moving window, maximum of 2048 used as default
    parameter STOP_COUNT        = 0,        // If non-zero, stop measuring on this number of cycles
                                            // Ignore i_stop
    parameter AUTO_START        = 0,        // If enabled, start counting when first read word is received
                                            // Ignore i_start
    parameter CLOCK_FREQ        = 500,      // holds the operating clock frequency of the AXI interface in MHz
    parameter DATA_WIDTH        = 32,       // holds the data width of the AXI interface in bytes
    parameter INPUT_REG_STAGES  = 0         // Add register stages, (up to 2), to the inputs.  
                                            // To allow greater placement flexibiltiy
)
(
    // Inputs
    input  wire                         i_clk,
    input  wire                         i_reset_n,      // Negative synchronous reset
    input  wire                         i_start,
    input  wire                         i_stop,
    input  wire                         i_counter_reset,

    // Interfaces
    t_AXI4.monitor                      axi_if,         // AXI-4 interface.  This is a monitor port

    // Outputs
    // bw_results_XX is to return the bw measurements for the register interface
    // there are 2 32bit registers with the following content:
    // o_bw_results_rd = 2'b NC, 10'b BW read  average norm , 10'b BW read  max norm , 10'b BW read  min norm 
    // o_bw_results_wr = 2'b NC, 10'b BW write average norm , 10'b BW write max norm , 10'b BW write min norm 
    output t_ACX_USER_REG  o_bw_results_rd,
    output t_ACX_USER_REG  o_bw_results_wr,
    output t_ACX_USER_REG  o_clock_freq_data_width
);

    localparam int    WINDOW_SIZE_WIDTH      = $clog2(BW_WINDOW_SIZE);
    localparam int    NORM_SIZE_WIDTH        = 10;

    logic                       new_data_read_q;
    logic                       new_data_write_q;
    logic                       new_data_read;
    logic                       new_data_write;
    logic                       new_data_read_d;
    logic                       new_data_write_d;
    logic                       new_data_read_2d;
    logic                       new_data_write_2d;
    logic                       new_data_read_3d;
    logic                       new_data_write_3d;
    logic                       new_data_read_4d;
    logic                       new_data_write_4d;
    logic [10:0]                window_counter;         // Counter up to the defined window size and then starts to read back from the FIFO
    logic                       window_complete;        // Indicates that the sampling window is completed
    logic                       window_complete_d;
    logic [15:0]                stop_counter;           // Counts cycles before stopping measurement
    logic                       start_int;              // Starts the BW calculation process
    logic                       stop_int;               // Stops the BW calculation process
    logic                       start_d;
    logic                       stop_d;
    logic                       counter_reset_d;
    logic                       test_state;             // Indicates the measurement is started
    logic                       test_ran;

    logic [10:0]                rd_sum;
    logic [10:0]                wr_sum;
    logic [10:0]                rd_bw;
    logic [10:0]                wr_bw;
    logic [10:0]                next_rd_bw;
    logic [10:0]                next_wr_bw;
    logic [10:0]                rd_bw_valid;
    logic [10:0]                wr_bw_valid;
    logic [10:0]                rd_bw_valid_d;
    logic [10:0]                wr_bw_valid_d;
    logic [10:0]                rd_bw_max;
    logic [10:0]                wr_bw_max;
    logic [10:0]                rd_bw_min;
    logic [10:0]                wr_bw_min;
    logic                       rd_gt_max;
    logic                       rd_ls_min;
    logic                       wr_gt_max;
    logic                       wr_ls_min;
    logic [NORM_SIZE_WIDTH-1:0] rd_bw_norm;
    logic [NORM_SIZE_WIDTH-1:0] wr_bw_norm;
    logic [NORM_SIZE_WIDTH-1:0] rd_bw_max_norm;
    logic [NORM_SIZE_WIDTH-1:0] wr_bw_max_norm;
    logic [NORM_SIZE_WIDTH-1:0] rd_bw_min_norm;
    logic [NORM_SIZE_WIDTH-1:0] wr_bw_min_norm;

    // FIFO primitive is 144-bits wide, we are only configuring for 36-bits
    localparam MAX_FIFO_WIDTH = 144;
    localparam FIFO_WIDTH     = 36;

    logic [MAX_FIFO_WIDTH -1:0] fifo_din;
    logic [MAX_FIFO_WIDTH -1:0] fifo_dout;

    // Start/stop signal handling
    always @(posedge i_clk)
    begin
        if(~i_reset_n)
        begin
            start_d             <= 1'b0;
            stop_d              <= 1'b0;
            counter_reset_d     <= 1'b0;
        end
        else
        begin
            start_d             <= i_start;
            stop_d              <= i_stop;
            counter_reset_d     <= i_counter_reset;
        end
    end
    
    always @(posedge i_clk)
        if( ~i_reset_n || stop_int)
            test_state <= 1'b0;
        else if (start_int)
            test_state <= 1'b1;
    
    always @(posedge i_clk)
        if( ~i_reset_n)
            test_ran <= 1'b0;
        else if (start_int)
            test_ran <= 1'b1;
            
    assign stop_int  = (STOP_COUNT != 0) ? (stop_counter==STOP_COUNT) : stop_d;
    // Auto start on first write data seen
    assign start_int = (AUTO_START != 0) ? (new_data_write & ~test_state & ~test_ran) : start_d;

    // Assign BW registers
    assign rd_bw_norm     = rd_bw_valid[WINDOW_SIZE_WIDTH-1:(WINDOW_SIZE_WIDTH-NORM_SIZE_WIDTH)];
    assign rd_bw_max_norm = rd_bw_max  [WINDOW_SIZE_WIDTH-1:(WINDOW_SIZE_WIDTH-NORM_SIZE_WIDTH)];
    assign rd_bw_min_norm = rd_bw_min  [WINDOW_SIZE_WIDTH-1:(WINDOW_SIZE_WIDTH-NORM_SIZE_WIDTH)];
    assign wr_bw_norm     = wr_bw_valid[WINDOW_SIZE_WIDTH-1:(WINDOW_SIZE_WIDTH-NORM_SIZE_WIDTH)];
    assign wr_bw_max_norm = wr_bw_max  [WINDOW_SIZE_WIDTH-1:(WINDOW_SIZE_WIDTH-NORM_SIZE_WIDTH)];
    assign wr_bw_min_norm = wr_bw_min  [WINDOW_SIZE_WIDTH-1:(WINDOW_SIZE_WIDTH-NORM_SIZE_WIDTH)];

    assign o_bw_results_rd = {2'b0, rd_bw_norm, rd_bw_max_norm, rd_bw_min_norm};
    assign o_bw_results_wr = {2'b0, wr_bw_norm, wr_bw_max_norm, wr_bw_min_norm};
    // Set to 4'h1 to indicate this is the AXI BW monitor, also used for overall AXI performance monitor
    assign o_clock_freq_data_width = {4'h1, CLOCK_FREQ[11:0], DATA_WIDTH[15:0]};

    // Support extra pipeline stage if required
    generate if (INPUT_REG_STAGES > 0) begin : gb_1_in_del
        always @(posedge i_clk)
        begin
            new_data_read_q  <= ( axi_if.rvalid && axi_if.rready );
            new_data_write_q <= ( axi_if.wvalid && axi_if.wready );
        end
    end
    else
    begin : gb_0_in_del
        always_comb
        begin
            new_data_read_q  = ( axi_if.rvalid && axi_if.rready );
            new_data_write_q = ( axi_if.wvalid && axi_if.wready );
        end
    end
    endgenerate

    // Signal when new data has been received
    // Flop signals to improve overall timing
    always @(posedge i_clk)
    begin
        new_data_read_d   <= new_data_read;
        new_data_write_d  <= new_data_write;
        new_data_read_2d  <= new_data_read_d;
        new_data_write_2d <= new_data_write_d;
        new_data_read_3d  <= new_data_read_2d;
        new_data_write_3d <= new_data_write_2d;
        new_data_read_4d  <= new_data_read_3d;
        new_data_write_4d <= new_data_write_3d;
        new_data_read     <= new_data_read_q;
        new_data_write    <= new_data_write_q;
    end

    // Pipeline lower sum
    // new_data_read and fifo_dout[35] must be exactly 2^WINDOW_SIZE_WIDTH apart
    always @(posedge i_clk)
    begin
        case ({new_data_read, (fifo_dout[35] & window_complete_d)})
            2'b00 : rd_sum <= 11'd0;
            2'b01 : rd_sum <= -11'd1;
            2'b10 : rd_sum <= 11'd1;
            2'b11 : rd_sum <= 11'd0;
        endcase
    end

    // new_data_write and fifo_dout[17] must be exactly 2^WINDOW_SIZE_WIDTH apart
    always @(posedge i_clk)
    begin
        case ({new_data_write, (fifo_dout[17] & window_complete_d)})
            2'b00 : wr_sum <= 11'd0;
            2'b01 : wr_sum <= -11'd1;
            2'b10 : wr_sum <= 11'd1;
            2'b11 : wr_sum <= 11'd0;
        endcase
    end

    // Bring out sum for explicit inference
    assign next_rd_bw = rd_bw + rd_sum;
    assign next_wr_bw = wr_bw + wr_sum;

    // Calculate the BW for data
    // Add additional pipelining to allow for synthesis retiming
    always @(posedge i_clk)
    begin
        if(~i_reset_n || counter_reset_d)
        begin
            rd_bw <= 11'd0;
            wr_bw <= 11'd0;
        end
        // Start accumulating values from same cycle that first write to FIFO occurs
        else if(test_state)
        begin
            rd_bw <= next_rd_bw;
            wr_bw <= next_wr_bw;
        end
    end

    // Calculate the BW for data
    always @(posedge i_clk)
    begin
        if (new_data_write_2d)
            wr_bw_valid <= wr_bw;
        if (new_data_read_2d)
            rd_bw_valid <= rd_bw;
    end

    // Calculate the max and min BW for data
    // this can only be done reliable if sample window is completed
    // Register comparisions to ease timing
    // ENHANCE - due to the 2 cycle latencies introduced by registering the comparison
    // signals, the min and max calculations can be out by one sample
    // This is not considered crucial at this time as they are only used for feedback in the terminal
    // and the reported error is usually less than 1%
    // A future enhancement will be to create a module to do comparisons, using 2 streams to account
    // for the 2 cycle delay stage.
    always @(posedge i_clk)
    begin
        rd_gt_max <= (rd_bw_valid > rd_bw_max);
        rd_ls_min <= (rd_bw_valid < rd_bw_min);
        wr_gt_max <= (wr_bw_valid > wr_bw_max);
        wr_ls_min <= (wr_bw_valid < wr_bw_min);
    end

    always @(posedge i_clk)
    begin
        rd_bw_valid_d <= rd_bw_valid;
        if(~i_reset_n || counter_reset_d)
        begin
            rd_bw_max <= 11'd0;
            rd_bw_min <= {11{1'b1}};
        end
        else if(window_complete & test_state)
        begin
            if ( new_data_read_4d )
            begin
                if(rd_gt_max)
                   rd_bw_max <= rd_bw_valid_d;
                if(rd_ls_min)
                   rd_bw_min <= rd_bw_valid_d;
            end
            
            // synthesis synthesis_off
            /* Disable debug messages, otherwise they fill the transcript
            if(new_data_read_4d)
            begin
               $display($time, ", %m: rd_bw_max = %d  in percentage %d", rd_bw_max, (100*rd_bw_max)/window_counter);
               $display($time, ", %m: rd_bw_max = %d  in percentage %d", rd_bw_max, (100*rd_bw_max)/window_counter);
               $display($time, ", %m: rd_bw     = %d  in percentage %d", rd_bw, (100*rd_bw)/window_counter);
            end
            */
            // synthesis synthesis_on
        end
    end

    always @(posedge i_clk)
    begin
        wr_bw_valid_d <= wr_bw_valid;
        if(~i_reset_n || counter_reset_d)
        begin
            wr_bw_max <= 11'd0;
            wr_bw_min <= {11{1'b1}};
        end
        else if(window_complete & test_state)
        begin
            if ( new_data_write_4d )
            begin
                if(wr_gt_max)
                   wr_bw_max <= wr_bw_valid_d;
                if(wr_ls_min)
                   wr_bw_min <= wr_bw_valid_d;
            end
            
            // synthesis synthesis_off
            /* Disable debug messages, otherwise they fill the transcript
            if(new_data_write_4d)
            begin
                $display($time, ", %m: wr_bw_min = %d  in percentage %d", wr_bw_min, (100*wr_bw_min)/window_counter);
                $display($time, ", %m: wr_bw_min = %d  in percentage %d", wr_bw_min, (100*wr_bw_min)/window_counter);
                $display($time, ", %m: wr_bw     = %d  in percentage %d", wr_bw, (100*wr_bw)/window_counter);
            end
            */
            // synthesis synthesis_on
        end
    end

    // Counter for the window size that BW is averaged on
    always @(posedge i_clk)
    begin
        if(~i_reset_n || counter_reset_d)
            window_counter <= 11'd0;
        else if(test_state && (window_counter < (BW_WINDOW_SIZE-1)))
            window_counter <= window_counter + 11'd1;
    end

    always @(posedge i_clk)
    begin
        window_complete_d <= window_complete;
        if(~i_reset_n || counter_reset_d)
            window_complete <= 1'b0;
        // Assert window_complete one cycle early as FIFO has one cycle delay on output
        else if (window_counter == (BW_WINDOW_SIZE -2))
            window_complete <= 1'b1;
    end

    // Counter for the stop counter
    always @(posedge i_clk)
    begin
        if(~i_reset_n  || counter_reset_d)
        begin
            stop_counter <= 16'd0;
        end
        else if(test_state)
        begin
            stop_counter <= stop_counter + 16'd1;
        end
    end

    // FIFO primitive is 144-bits data ports.  Need to pad data
    assign fifo_din = {{(MAX_FIFO_WIDTH-FIFO_WIDTH){1'b0}}, {new_data_read, 17'b0, new_data_write, 17'b0}};

    ACX_BRAM72K_FIFO #(
        .aempty_threshold   (14'h10),                      // default 
        .afull_threshold    (14'h1),                       // default
        .ecc_decoder_enable (1'b0),                        // default
        .ecc_encoder_enable (1'b0),                        // default
        .fwft_mode          (1'b0),
        .outreg_enable      (1'b1),
        .rdclk_polarity     ("rise"),                      // default
        .read_width         (FIFO_WIDTH),
        .sync_mode          (1'b1),
        .wrclk_polarity     ("rise"),                      // default
        .write_width        (FIFO_WIDTH)
    ) i_performance_data_fifo ( 
        .din                (fifo_din),
        .wrclk              (i_clk),
        .rdclk              (i_clk),
        .wren               (test_state),                  // Fifo written during test_state
        .rden               (window_complete),             // Read operates once initial window completed
        .rstn               (i_reset_n),
        .dout               (fifo_dout),
        .sbit_error         (),
        .dbit_error         (),
        .almost_full        (),
        .full               (),
        .almost_empty       (),
        .empty              (),
        .write_error        (),
        .read_error         ()
    );

endmodule : axi_bw_monitor

