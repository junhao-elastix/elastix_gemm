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
//      Designed to read from NAPs, it will monitor the latency of
//      write or read transactions.
//      The module reports back the average, min and max latencies encountered.
//      The measurement can be started and stopped automatically or from external signals
// ------------------------------------------------------------------

`include "nap_interfaces.svh"
`include "reg_control_defines.svh"

`define ACX_PERFORMANCE_MONITOR_FIFO_WIDTH 36

module axi_latency_monitor
#(
    parameter LAT_AVERAGE_SIZE_EXP    = 5,      // Size of the averaging batch size; this batch is in power of 2;
                                                // the parameter spezifies the exponent ==> 2^LAT_AVERAGE_SIZE_EXP
                                                // should not exceed 10    
    parameter STOP_COUNT              = 0,      // If non-zero, stop measuring on this number of cycles
                                                // Ignore i_stop
    parameter AUTO_START              = 0,      // If enabled, start counting when first read word is received
                                                // Ignore i_start
    parameter CLOCK_FREQ              = 500,    // holds the operating clock frequency of the AXI interface in MHz
    parameter DATA_WIDTH              = 32,     // holds the data width of the AXI interface in bytes
    parameter INPUT_REG_STAGES        = 0       // Add register stages, (up to 2), to the inputs.  
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
    // latency_results_XX is to return the latency measurements for the register interface
    // there are 2 32bit registers with the following content:
    // latency_results_rd = 2'b NC, 10'b latency read  average norm , 10'b latency read  max norm , 10'b latency read  min norm 
    // latency_results_wr = 2'b NC, 10'b latency write average norm , 10'b latency write max norm , 10'b latency write min norm 
    output t_ACX_USER_REG  o_latency_results_current,
    output t_ACX_USER_REG  o_latency_results_avg,
    output t_ACX_USER_REG  o_latency_results_max,
    output t_ACX_USER_REG  o_latency_results_min,
    output t_ACX_USER_REG  o_clock_freq_data_width
);

    
    logic                       new_xact_read;
    logic                       new_xact_write;
    logic                       new_resp_read;
    logic                       new_resp_write;
    
    // start/stop related signals
    logic [15:0]                stop_counter;         // counter up to the defined window size and then starts
                                                      // to read back from the FIFO
    logic                       start_int;            // starts the BW calculation process
    logic                       stop_int;             // stops the BW calculation process
    logic                       start_d;
    logic                       stop_d;
    logic                       counter_reset_d;
    logic                       test_state;           // indicates the measurement is started
    logic                       test_ran;
    
    logic                       measurement_active_read;
    logic                       measurement_active_write;
    logic [11:0]                latency_counter_read;
    logic [11:0]                latency_counter_read_d;
    logic [11:0]                latency_counter_read_2d;
    logic [11:0]                latency_counter_write;
    logic [11:0]                latency_counter_write_d;
    logic                       latency_gt_max;
    logic                       latency_ls_min;
    logic [11:0]                rd_lat_max;
    logic [11:0]                rd_lat_min;
    logic [11:0]                rd_lat_avg;
    logic [11:0]                wr_lat_max;
    logic [11:0]                wr_lat_min;
    logic [11:0]                wr_lat_avg;
    logic [15:0]                latency_read;
    logic [15:0]                latency_write;
    logic [11:0]                latency_read_counts;
    logic [11:0]                latency_write_counts;
    logic                       latency_write_compute;

    // Latched IDs
    logic [7:0]                 arid_latch;
    logic [7:0]                 awid_latch;

    // Delayed versions of AXI signals
    logic [7:0]                 arid_d;
    logic [7:0]                 awid_d;
    logic [7:0]                 rid_d;
    logic [7:0]                 bid_d;
    logic                       arvalid_d;
    logic                       arready_d;
    logic                       awvalid_d;
    logic                       awready_d;
    logic                       rlast_d;
    logic                       rvalid_d;
    logic                       rready_d;
    logic                       bvalid_d;
    logic                       bready_d;
    
    logic [7:0]                 arid_2d;
    logic [7:0]                 awid_2d;
    logic [7:0]                 rid_2d;
    logic [7:0]                 bid_2d;
    logic                       arvalid_2d;
    logic                       arready_2d;
    logic                       awvalid_2d;
    logic                       awready_2d;
    logic                       rlast_2d;
    logic                       rvalid_2d;
    logic                       rready_2d;
    logic                       bvalid_2d;
    logic                       bready_2d;

    logic [7:0]                 arid_3d;
    logic [7:0]                 awid_3d;
    logic [7:0]                 rid_3d;
    logic [7:0]                 bid_3d;
    logic                       arvalid_3d;
    logic                       arready_3d;
    logic                       awvalid_3d;
    logic                       awready_3d;
    logic                       rlast_3d;
    logic                       rvalid_3d;
    logic                       rready_3d;
    logic                       bvalid_3d;
    logic                       bready_3d;

    logic [7:0]                 arid;
    logic [7:0]                 awid;
    logic [7:0]                 rid;
    logic [7:0]                 bid;
    logic                       arvalid;
    logic                       arready;
    logic                       awvalid;
    logic                       awready;
    logic                       rlast;
    logic                       rvalid;
    logic                       rready;
    logic                       bvalid;
    logic                       bready;

    // Pipeline the axi interface signals
    always @(posedge i_clk)
    begin
        if(~i_reset_n)
        begin
            arvalid_d <= 1'b0;
            arready_d <= 1'b0;
            awvalid_d <= 1'b0;
            awready_d <= 1'b0;
            rlast_d   <= 1'b0;
            rvalid_d  <= 1'b0;
            rready_d  <= 1'b0;
            bvalid_d  <= 1'b0;
            bready_d  <= 1'b0;
            arid_d    <= 'h0;
            awid_d    <= 'h0;
            rid_d     <= 'h0;
            bid_d     <= 'h0;
        end
        else
        begin
            // Existing delay
            arvalid_d <= axi_if.arvalid;
            arready_d <= axi_if.arready;
            awvalid_d <= axi_if.awvalid;
            awready_d <= axi_if.awready;
            rlast_d   <= axi_if.rlast;
            rvalid_d  <= axi_if.rvalid;
            rready_d  <= axi_if.rready;
            bvalid_d  <= axi_if.bvalid;
            bready_d  <= axi_if.bready;
            arid_d    <= axi_if.arid;
            awid_d    <= axi_if.awid;
            rid_d     <= axi_if.rid;
            bid_d     <= axi_if.bid;
        end

        // No reset on extra stages, pipelines will clear during reset
        // One stage delay
        arvalid_2d <= arvalid_d;
        arready_2d <= arready_d;
        awvalid_2d <= awvalid_d;
        awready_2d <= awready_d;
        rlast_2d   <= rlast_d;
        rvalid_2d  <= rvalid_d;
        rready_2d  <= rready_d;
        bvalid_2d  <= bvalid_d;
        bready_2d  <= bready_d;
        arid_2d    <= arid_d;
        awid_2d    <= awid_d;
        rid_2d     <= rid_d;
        bid_2d     <= bid_d;

        // Two stage delay
        arvalid_3d <= arvalid_2d;
        arready_3d <= arready_2d;
        awvalid_3d <= awvalid_2d;
        awready_3d <= awready_2d;
        rlast_3d   <= rlast_2d;
        rvalid_3d  <= rvalid_2d;
        rready_3d  <= rready_2d;
        bvalid_3d  <= bvalid_2d;
        bready_3d  <= bready_2d;
        arid_3d    <= arid_2d;
        awid_3d    <= awid_2d;
        rid_3d     <= rid_2d;
        bid_3d     <= bid_2d;
    end

    // Add delay dependant upon parameter
    always_comb
    begin
        case (INPUT_REG_STAGES)
            // Existing default delay
            0 : begin
                    arid    = arid_d;
                    awid    = awid_d;
                    rid     = rid_d;
                    bid     = bid_d;
                    arvalid = arvalid_d;
                    arready = arready_d;
                    awvalid = awvalid_d;
                    awready = awready_d;
                    rlast   = rlast_d;
                    rvalid  = rvalid_d;
                    rready  = rready_d;
                    bvalid  = bvalid_d;
                    bready  = bready_d;
                end

            // Single delay
            1 : begin
                    arid    = arid_2d;
                    awid    = awid_2d;
                    rid     = rid_2d;
                    bid     = bid_2d;
                    arvalid = arvalid_2d;
                    arready = arready_2d;
                    awvalid = awvalid_2d;
                    awready = awready_2d;
                    rlast   = rlast_2d;
                    rvalid  = rvalid_2d;
                    rready  = rready_2d;
                    bvalid  = bvalid_2d;
                    bready  = bready_2d;
                end

            // Two stage delay
            2 : begin
                    arid    = arid_3d;
                    awid    = awid_3d;
                    rid     = rid_3d;
                    bid     = bid_3d;
                    arvalid = arvalid_3d;
                    arready = arready_3d;
                    awvalid = awvalid_3d;
                    awready = awready_3d;
                    rlast   = rlast_3d;
                    rvalid  = rvalid_3d;
                    rready  = rready_3d;
                    bvalid  = bvalid_3d;
                    bready  = bready_3d;
                end
//            default : error ERROR_illegal_value_of_INPUT_REG_STAGES();
        endcase
    end


    assign o_latency_results_current = {4'b0, latency_counter_read, 4'b0, latency_counter_write};
    assign o_latency_results_avg     = {4'b0, rd_lat_avg, 4'b0, wr_lat_avg};
    assign o_latency_results_max     = {4'b0, rd_lat_max, 4'b0, wr_lat_max};
    assign o_latency_results_min     = {4'b0, rd_lat_min, 4'b0, wr_lat_min};
    // Set to 4'h2 to indicate AXI latency monitor
    assign o_clock_freq_data_width   = {4'h2, CLOCK_FREQ[11:0], DATA_WIDTH[15:0]};

    // start/stop signal handling
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
            
    assign stop_int  = (STOP_COUNT != 0) ? (stop_counter==STOP_COUNT) : stop_d;
    assign start_int = (AUTO_START != 0) ? (new_xact_write & ~test_state & ~test_ran) : start_d;
    // Auto start on first write transaction request seen


    // Signal when new xact has been received
    assign new_xact_read  = ( arvalid && arready && ~measurement_active_read);
    assign new_xact_write = ( awvalid && awready && ~measurement_active_write);
    // Signal when new response has been received
    assign new_resp_read  = (rvalid && rready && rlast);
    assign new_resp_write = (bvalid && bready);


    logic read_end;
    logic read_end_d;
    logic read_end_2d;
    assign read_end = (new_resp_read && (rid == arid_latch));

    always @(posedge i_clk)
    begin
        read_end_d  <= read_end;
        read_end_2d <= read_end_d;
    end

    // Start/stop the read measurement
    always @(posedge i_clk)
    begin
        if(~i_reset_n || counter_reset_d)
        begin
            arid_latch              <= 8'b0;
            measurement_active_read <= 1'b0;
            latency_read            <= 16'd0;
            latency_read_counts     <= 12'd0;
        end
        else if(new_xact_read & test_state)
        begin
            arid_latch              <= arid;
            measurement_active_read <= 1'b1;
        end
        else if(read_end)
        begin
            measurement_active_read <= 1'b0;
            latency_read            <= latency_read + {4'd0, latency_counter_read};
            latency_read_counts     <= latency_read_counts + 12'd1;
            if(latency_read_counts == {1'b1, {LAT_AVERAGE_SIZE_EXP{1'b0}}})
            begin
               latency_read        <= 16'd0;
               latency_read_counts <= 12'd0;
               // synthesis synthesis_off
               // $display($time, ", %m: NEW read latency total = %d count = %d   average = %d", latency_read, latency_read_counts, rd_lat_avg);
               // synthesis synthesis_on
            end
            // Turn off messages to clean up simulation logs
            /*
            // synthesis synthesis_off
            $display($time, ", %m: arid = %d latency = %d", arid_latch, latency_counter_read);
            $display($time, ", %m: read latency total = %d count = %d   average = %d", latency_read, latency_read_counts, latency_read/latency_read_counts);
            $display($time, ", %m: read latency max   = %d   min = %d", rd_lat_max, rd_lat_min);
            // synthesis synthesis_on
            */
        end
    end

    always @(posedge i_clk)
        latency_gt_max <= (latency_counter_read_d > rd_lat_max);

    always @(posedge i_clk)
        latency_ls_min <= (latency_counter_read_d < rd_lat_min);

    always @(posedge i_clk)
    begin
        latency_counter_read_d  <= latency_counter_read;
        latency_counter_read_2d <= latency_counter_read_d;
        if(~i_reset_n || counter_reset_d)
        begin
            rd_lat_max <= 12'd0;
            rd_lat_min <= {12{1'b1}};
        end
        else if(read_end_2d)
        begin
            if(latency_gt_max)
               rd_lat_max <= latency_counter_read_2d;        

            if(latency_ls_min)
               rd_lat_min <= latency_counter_read_2d;
        end
    end

    always @(posedge i_clk)
    begin
        if(~i_reset_n || counter_reset_d)
            rd_lat_avg <= 12'd0;
        else if(read_end_d)
            if(latency_read_counts == {1'b1, {LAT_AVERAGE_SIZE_EXP{1'b0}}})
               rd_lat_avg <= latency_read[15:LAT_AVERAGE_SIZE_EXP];
    end

    logic write_end;
    logic write_end_d;
    assign write_end = (new_resp_write && (bid == awid_latch));

    always @(posedge i_clk)
        write_end_d <= write_end;

    // Capture the write xact
    always @(posedge i_clk)
    begin
        if(~i_reset_n || counter_reset_d)
        begin
            awid_latch            <= 8'b0;
            measurement_active_write <= 1'b0;
            latency_write         <= 16'd0;
            latency_write_counts  <= 12'd0;
            latency_write_compute <= 1'b0;
        end
        else if(new_xact_write & test_state)
        begin
            awid_latch               <= awid;
            measurement_active_write <= 1'b1;
        end
        else if(write_end & test_state)
        begin
            measurement_active_write <= 1'b0;
            latency_write <= latency_write + {4'd0, latency_counter_write};
            latency_write_counts <= latency_write_counts + 12'd1;
            if(latency_write_counts == {1'b1, {LAT_AVERAGE_SIZE_EXP{1'b0}}})
            begin
               latency_write_compute <= 1'b1;
            end
            if(latency_write_compute)
            begin
               latency_write         <= 16'd0;
               latency_write_counts  <= 12'd0;
               latency_write_compute <= 1'b0;
               // synthesis synthesis_off
               // $display($time, ", %m: NEW write latency total = %d count = %d   average = %d", latency_write, latency_write_counts, wr_lat_avg);
               // synthesis synthesis_on
            end
            /* Turn off messages
            // synthesis synthesis_off
            $display($time, ", %m: awid = %d latency = %d", awid_latch, latency_counter_write);
            $display($time, ", %m: write latency total = %d count = %d   average = %d", latency_write, latency_write_counts, latency_write/latency_write_counts);
            $display($time, ", %m: write latency max   = %d   min = %d", wr_lat_max, wr_lat_min);
            // synthesis synthesis_on
            */
        end
      
    end
    always @(posedge i_clk)
    begin
        latency_counter_write_d <= latency_counter_write;
        if(~i_reset_n || counter_reset_d)
        begin
            wr_lat_max <= 12'd0;
            wr_lat_min <= {12{1'b1}};
            wr_lat_avg <= 12'd0;
        end
        else if(write_end_d & test_state)
        begin
            if(latency_counter_write_d > wr_lat_max)
               wr_lat_max <= latency_counter_write_d;
            if(latency_counter_write_d < wr_lat_min)
               wr_lat_min <= latency_counter_write_d;
            if(latency_write_compute)
               wr_lat_avg <= latency_write[15:LAT_AVERAGE_SIZE_EXP];
        end
      
    end
    
    // Run the latency read counter
    always @(posedge i_clk)
    begin
        if(~i_reset_n || ~measurement_active_read)
        begin
            latency_counter_read <= 12'd0;
        end
        else if(measurement_active_read & test_state)
        begin
            latency_counter_read <= latency_counter_read + 12'd1;
        end
    end
    
    // run the latency write counter
    always @(posedge i_clk)
    begin
        if(~i_reset_n || ~measurement_active_write)
        begin
            latency_counter_write <= 12'd0;
        end
        else if(measurement_active_write & test_state)
        begin
            latency_counter_write <= latency_counter_write + 12'd1;
        end
    end

endmodule : axi_latency_monitor

