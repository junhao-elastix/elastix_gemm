// ------------------------------------------------------------------
// Dispatcher Control Module (Simplified) - Direct FETCH to row_bram
//
// Purpose: Wrapper module that connects fetcher directly to compute_engine row_bram
// Architecture:
//  - fetcher: Handles FETCH operations (GDDR6 → row_bram directly)
//  - No intermediate dispatcher_bram layer
//  - DISPATCH command is passed through to compute_engine
//
// Author: Junhao Pan
// Date: Dec 2025 - Refactored to remove dispatcher_bram layer
// ------------------------------------------------------------------

`include "nap_interfaces.svh"

module dispatcher_control
import gemm_pkg::*;
#(
    parameter MAN_WIDTH = 256,         // Mantissa data width
    parameter EXP_WIDTH = 8,           // Exponent data width
    parameter BRAM_DEPTH = 512,        // row_bram depth
    parameter AXI_ADDR_WIDTH = 42,     // AXI address width
    parameter BRAM_ADDR_WIDTH = $clog2(BRAM_DEPTH),
    parameter TILE_ADDR_WIDTH = $clog2(BRAM_DEPTH),
    parameter [8:0] GDDR6_PAGE_ID = 9'd0  // GDDR6 Page ID for NoC routing
)
(
    // Clock and Reset
    input  logic                         i_clk,
    input  logic                         i_reset_n,

    // ====================================================================
    // Master Control Interface (FETCH/DISPATCH commands)
    // ====================================================================
    input  logic                         i_fetch_en,
    input  logic [link_addr_width_gp-1:0] i_fetch_addr,
    input  logic [link_len_width_gp-1:0]  i_fetch_len,
    input  logic                         i_fetch_target, // 0=left, 1=right
    output logic                         o_fetch_done,

    input  logic                         i_disp_en,
    input  logic [15:0]                  i_disp_tile_addr,    // Tile destination address (unused)
    input  logic [7:0]                   i_disp_man_nv_cnt,   // Total NVs to dispatch (unused)
    input  logic [7:0]                   i_disp_ugd_vec_size, // NVs per UGD vector (unused)
    input  logic                         i_disp_man_4b,       // Mantissa width (unused)
    input  logic [23:0]                  i_disp_col_en,       // Column enable mask (unused)
    input  logic [4:0]                   i_disp_col_start,    // Distribution start column (unused)
    input  logic                         i_disp_right,        // Dispatch side (0=left NO-OP, 1=right triggers ST_FILL)
    input  logic                         i_disp_broadcast,    // Distribution mode (unused)
    output logic                         o_disp_done,

    // ====================================================================
    // row_bram Write Ports (Direct connection to compute_engine)
    // FOUR PARALLEL OUTPUTS
    // ====================================================================
    // Left mantissa write
    output logic [TILE_ADDR_WIDTH-1:0]   o_man_left_wr_addr,
    output logic                         o_man_left_wr_en,
    output logic [MAN_WIDTH-1:0]         o_man_left_wr_data,

    // Right mantissa write
    output logic [TILE_ADDR_WIDTH-1:0]   o_man_right_wr_addr,
    output logic                         o_man_right_wr_en,
    output logic [MAN_WIDTH-1:0]         o_man_right_wr_data,

    // Left exponent write
    output logic [TILE_ADDR_WIDTH-1:0]   o_exp_left_wr_addr,
    output logic                         o_exp_left_wr_en,
    output logic [EXP_WIDTH-1:0]         o_exp_left_wr_data,

    // Right exponent write
    output logic [TILE_ADDR_WIDTH-1:0]   o_exp_right_wr_addr,
    output logic                         o_exp_right_wr_en,
    output logic [EXP_WIDTH-1:0]         o_exp_right_wr_data,

    // ====================================================================
    // DISPATCH Start Signal (passed through to compute_engine)
    // ====================================================================
    output logic                         o_disp_start,        // Pulse to trigger ST_FILL
    input  logic                         i_disp_done_ce,      // From compute_engine o_disp_done

    // ====================================================================
    // AXI-4 Initiator Interface for DDR access
    // ====================================================================
    t_AXI4.initiator                     axi_ddr_if,

    // ====================================================================
    // Debug Interface
    // ====================================================================
    output logic [3:0]                   o_dc_state,
    output logic [9:0]                   o_disp_wr_count,
    output logic [10:0]                  o_disp_wr_addr,    // Debug: BRAM write address
    output logic                         o_disp_wr_en,      // Debug: BRAM write enable
    output logic [8:0]                   o_disp_rd_addr,    // DISPATCH read address (debug, unused)
    output logic                         o_disp_rd_en,      // DISPATCH read enable (debug, unused)
    
    // Probe Interface (first 16 bits of fetcher data when valid)
    output logic [15:0]                  o_probe_disp_data,
    output logic                         o_probe_disp_valid
);

    // ====================================================================
    // Fetcher Module Instantiation
    // ====================================================================
    fetcher #(
        .MAN_WIDTH      (MAN_WIDTH),
        .EXP_WIDTH      (EXP_WIDTH),
        .BRAM_DEPTH     (BRAM_DEPTH),
        .AXI_ADDR_WIDTH (AXI_ADDR_WIDTH),
        .BRAM_ADDR_WIDTH(BRAM_ADDR_WIDTH),
        .TILE_ADDR_WIDTH(TILE_ADDR_WIDTH),
        .GDDR6_PAGE_ID  (GDDR6_PAGE_ID)
    ) u_fetcher (
        .i_clk                      (i_clk),
        .i_reset_n                  (i_reset_n),
        .i_fetch_en                 (i_fetch_en),
        .i_fetch_addr               (i_fetch_addr),
        .i_fetch_len                (i_fetch_len),
        .i_fetch_target             (i_fetch_target),
        .o_fetch_done               (o_fetch_done),
        
        // Direct row_bram write ports
        .o_man_left_wr_addr         (o_man_left_wr_addr),
        .o_man_left_wr_en           (o_man_left_wr_en),
        .o_man_left_wr_data         (o_man_left_wr_data),
        
        .o_man_right_wr_addr        (o_man_right_wr_addr),
        .o_man_right_wr_en          (o_man_right_wr_en),
        .o_man_right_wr_data        (o_man_right_wr_data),
        
        .o_exp_left_wr_addr         (o_exp_left_wr_addr),
        .o_exp_left_wr_en           (o_exp_left_wr_en),
        .o_exp_left_wr_data         (o_exp_left_wr_data),
        
        .o_exp_right_wr_addr        (o_exp_right_wr_addr),
        .o_exp_right_wr_en          (o_exp_right_wr_en),
        .o_exp_right_wr_data        (o_exp_right_wr_data),
        
        .axi_ddr_if                 (axi_ddr_if)
    );

    // ====================================================================
    // DISPATCH Command Handling
    // ====================================================================
    // DISPATCH LEFT (disp_right=0): NO-OP (immediate done)
    // DISPATCH RIGHT (disp_right=1): Trigger ST_FILL in compute_engine
    
    logic disp_en_prev;
    logic disp_done_reg;       // Unified done flag (stays high until next DISPATCH)
    logic disp_right_pending;  // Track if DISPATCH RIGHT is waiting for ST_FILL
    
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            disp_en_prev <= 1'b0;
            disp_done_reg <= 1'b0;
            disp_right_pending <= 1'b0;
        end else begin
            // Track previous disp_en for edge detection
            disp_en_prev <= i_disp_en;
            
            // DISPATCH command processing
            if (i_disp_en && !disp_en_prev) begin
                if (!i_disp_right) begin
                    // DISPATCH LEFT: Set done immediately (NO-OP)
                    // Note: This clears previous done first, then sets new done
                    disp_done_reg <= 1'b1;
                    disp_right_pending <= 1'b0;
                end else begin
                    // DISPATCH RIGHT: Clear done, wait for compute_engine
                    disp_done_reg <= 1'b0;
                    disp_right_pending <= 1'b1;
                end
            end
            // DISPATCH RIGHT completion: Set done when compute_engine finishes
            else if (disp_right_pending && i_disp_done_ce) begin
                disp_done_reg <= 1'b1;
                disp_right_pending <= 1'b0;
            end
            // Done flag stays high until next DISPATCH command
        end
    end
    
    // Pulse o_disp_start on rising edge of i_disp_en when disp_right=1
    assign o_disp_start = (i_disp_en && !disp_en_prev && i_disp_right);
    
    // o_disp_done: Unified done signal
    assign o_disp_done = disp_done_reg;
    
    // `ifdef SIMULATION
    // always @(posedge i_clk) begin
    //     if (i_disp_en && !disp_en_prev) begin
    //         $display("[DC] @%0t DISPATCH triggered: disp_right=%0b, o_disp_start=%0b",
    //                  $time, i_disp_right, o_disp_start);
    //     end
    //     if (disp_done_reg && !disp_right_pending) begin
    //         $display("[DC] @%0t DISPATCH done: o_disp_done=%0b", $time, o_disp_done);
    //     end
    //     if (i_disp_done_ce) begin
    //         $display("[DC] @%0t DISPATCH RIGHT done signal from CE", $time);
    //     end
    // end
    // `endif

    // ====================================================================
    // Debug Outputs
    // ====================================================================
    assign o_dc_state = 4'd0;  // Simplified: no state machine
    assign o_disp_wr_count = 10'd0;
    assign o_disp_rd_addr = 9'd0;
    assign o_disp_rd_en = 1'b0;
    assign o_disp_wr_addr = {2'b0, o_man_left_wr_addr};  // Show left write addr
    assign o_disp_wr_en = o_man_left_wr_en | o_man_right_wr_en;

    // ====================================================================
    // Probe Outputs - Capture first 16 bits of fetcher data when valid
    // ====================================================================
    logic [15:0] probe_disp_data_reg;
    logic        probe_disp_valid_reg;
    
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            probe_disp_data_reg <= 16'd0;
            probe_disp_valid_reg <= 1'b0;
        end else begin
            probe_disp_valid_reg <= o_man_left_wr_en | o_man_right_wr_en;
            if (o_man_left_wr_en) begin
                probe_disp_data_reg <= o_man_left_wr_data[15:0];
            end else if (o_man_right_wr_en) begin
                probe_disp_data_reg <= o_man_right_wr_data[15:0];
            end
        end
    end
    
    assign o_probe_disp_data = probe_disp_data_reg;
    assign o_probe_disp_valid = probe_disp_valid_reg;

endmodule : dispatcher_control
