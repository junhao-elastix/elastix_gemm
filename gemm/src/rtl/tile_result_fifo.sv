// ------------------------------------------------------------------
// Tile Result FIFO Module
//
// Purpose: Per-tile FIFO for buffering compute engine results
// Features:
//  - Parameterizable depth and width (FP16 results)
//  - Simple registered read (1-cycle latency)
//  - Full/empty status flags for flow control
//  - Wrapper around flex_fifo for consistent interface
//
// Author: Junhao Pan
// Date: 10/28/2025
// Updated: 11/13/2025 - Refactored to use flex_fifo
// ------------------------------------------------------------------

module tile_result_fifo #(
    parameter DEPTH = 128,
    parameter DATA_WIDTH = 16
)(
    input  logic                    i_clk,
    input  logic                    i_reset_n,

    // Write Interface (from compute engine)
    input  logic [DATA_WIDTH-1:0]   i_wr_data,
    input  logic                    i_wr_en,
    output logic                    o_full,
    output logic                    o_afull,

    // Read Interface (to arbiter)
    output logic [DATA_WIDTH-1:0]   o_rd_data,
    input  logic                    i_rd_en,
    output logic                    o_empty,

    // Status
    output logic [$clog2(DEPTH):0]  o_count   // 0 to DEPTH
);

    // ===================================================================
    // Instantiate Flexible FIFO
    // ===================================================================
    flex_fifo #(
        .DATA_WIDTH (DATA_WIDTH),
        .DEPTH      (DEPTH)
    ) u_flex_fifo (
        .i_clk      (i_clk),
        .i_reset_n  (i_reset_n),

        // Write Interface
        .i_wr_data  (i_wr_data),
        .i_wr_en    (i_wr_en),
        .o_full     (o_full),
        .o_afull    (o_afull),

        // Read Interface
        .o_rd_data  (o_rd_data),
        .i_rd_en    (i_rd_en),
        .o_empty    (o_empty),

        // Status
        .o_count    (o_count)
    );

endmodule : tile_result_fifo
