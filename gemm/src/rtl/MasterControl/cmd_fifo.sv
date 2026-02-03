// ------------------------------------------------------------------
// Command FIFO Module (Wrapper)
//
// Purpose: 128-bit wide command FIFO wrapper around flex_fifo
// Features:
//  - 512 entries deep, 128-bit wide
//  - Single 128-bit command per entry (header + 3 payload words)
//  - 1-cycle read latency (standard synchronous BRAM read)
//  - Full/empty/almost-full status flags
//
// Author: Junhao Pan
// Date: 01/24/2026
// ------------------------------------------------------------------

module cmd_fifo
import gemm_pkg::*;
(
    input  logic                        i_clk,
    input  logic                        i_reset_n,

    // Write Interface - 128-bit
    input  logic [cmd_buf_width_gp-1:0] i_wr_data,
    input  logic                        i_wr_en,
    output logic                        o_full,
    output logic                        o_afull,

    // Read Interface - 128-bit
    output logic [cmd_buf_width_gp-1:0] o_rd_data,
    input  logic                        i_rd_en,
    output logic                        o_empty,

    // Status
    output logic [12:0]                 o_count,

    // Debug
    output logic [15:0]                 o_total_writes
);

    // ===================================================================
    // Internal Signals
    // ===================================================================
    localparam DEPTH = cmd_buf_els_gp;  // 512
    localparam DATA_WIDTH = cmd_buf_width_gp;  // 128
    localparam ADDR_WIDTH = $clog2(DEPTH);  // 9 bits for 512 depth

    logic [ADDR_WIDTH:0] fifo_count;

    // Debug counter
    logic [15:0] total_writes_reg;

    // ===================================================================
    // flex_fifo Instance
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
        .o_count    (fifo_count)
    );

    // ===================================================================
    // Count Output (zero-extended to 13 bits for interface compatibility)
    // ===================================================================
    assign o_count = {3'b0, fifo_count};

    // ===================================================================
    // Debug: Total Writes Counter
    // ===================================================================
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            total_writes_reg <= 16'd0;
        end else if (i_wr_en && !o_full) begin
            total_writes_reg <= total_writes_reg + 1'd1;
        end
    end

    assign o_total_writes = total_writes_reg;

endmodule : cmd_fifo
