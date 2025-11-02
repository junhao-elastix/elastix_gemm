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
// Monitors packets received from AXI bus for bandwith performance and latency
//      Top level which instantiates the axi_bw_monitor and the axi_latency_monitor. 
// ------------------------------------------------------------------

`include "nap_interfaces.svh"
`include "reg_control_defines.svh"


module axi_performance_monitor
#(
    parameter BW_WINDOW_SIZE       = 2048,      // Size of the moving window, maximum of 2048 used as default
    parameter LAT_AVERAGE_SIZE_EXP = 5,         // Size of the averaging batch size; this batch is in power of 2; the parameter spezifies the exponent ==> 2^AVERAGE_SIZE
                                                // should not exceed 10
    parameter STOP_COUNT           = 0,         // If non-zero, stop measuring on this number of cycles
                                                // Ignore i_stop
    parameter AUTO_START           = 0,         // If enabled, start counting when first read word is received
                                                // Ignore i_start
    parameter CLOCK_FREQ           = 500,       // Operating clock frequency of the AXI interface in MHz
    parameter DATA_WIDTH           = 32,        // Data width of the AXI interface in bytes
    parameter INPUT_REG_STAGES     = 0          // Add register stages, (up to 2), to the inputs.  
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
    t_AXI4.monitor                      axi_if,          // AXI-4 interface.  This is a monitor, all signals are inputs

    // Outputs
    // bw_results_XX is to return the bw measurements for the register interface
    // there are 2 32bit registers with the following content:
    // o_bw_results_rd = 2'b NC, 10'b BW read  average norm , 10'b BW read  max norm , 10'b BW read  min norm 
    // o_bw_results_wr = 2'b NC, 10'b BW write average norm , 10'b BW write max norm , 10'b BW write min norm 
    output t_ACX_USER_REG  o_bw_results_rd,
    output t_ACX_USER_REG  o_bw_results_wr,
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

    // Set to 4'h0 to indicate AXI performance monitor
    assign o_clock_freq_data_width   = {4'h0, CLOCK_FREQ[11:0], DATA_WIDTH[15:0]};

    // Instantiate AXI performance monitor
    axi_bw_monitor #(
        .BW_WINDOW_SIZE                  (BW_WINDOW_SIZE),
        .STOP_COUNT                      (STOP_COUNT),
        .AUTO_START                      (AUTO_START),
        .CLOCK_FREQ                      (CLOCK_FREQ),
        .DATA_WIDTH                      (DATA_WIDTH),
        .INPUT_REG_STAGES                (INPUT_REG_STAGES)
    ) i_axi_bw_monitor (
        // Inputs
        .i_clk                           (i_clk),
        .i_reset_n                       (i_reset_n),
        .i_start                         (i_start),
        .i_stop                          (i_stop),
        .i_counter_reset                 (i_counter_reset),

        // Interfaces
        .axi_if                          (axi_if),
        // Outputs
        .o_bw_results_rd                 (o_bw_results_rd),
        .o_bw_results_wr                 (o_bw_results_wr),
        .o_clock_freq_data_width         ()
    );
    // Instantiate AXI performance monitor
    axi_latency_monitor #(
        .LAT_AVERAGE_SIZE_EXP            (LAT_AVERAGE_SIZE_EXP),
        .STOP_COUNT                      (STOP_COUNT),
        .AUTO_START                      (AUTO_START),
        .CLOCK_FREQ                      (CLOCK_FREQ),
        .DATA_WIDTH                      (DATA_WIDTH),
        .INPUT_REG_STAGES                (INPUT_REG_STAGES)
    ) i_axi_latency_monitor (
        // Inputs
        .i_clk                           (i_clk),
        .i_reset_n                       (i_reset_n),
        .i_start                         (i_start),
        .i_stop                          (i_stop),
        .i_counter_reset                 (i_counter_reset),

        // Interfaces
        .axi_if                          (axi_if),
        // Outputs
        .o_latency_results_current       (o_latency_results_current),
        .o_latency_results_avg           (o_latency_results_avg),
        .o_latency_results_max           (o_latency_results_max),
        .o_latency_results_min           (o_latency_results_min),
        .o_clock_freq_data_width         ()
    );   

endmodule : axi_performance_monitor

