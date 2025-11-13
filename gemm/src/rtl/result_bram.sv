// ------------------------------------------------------------------
// Result BRAM Module
//
// Purpose: BRAM-based buffer for FP16 computation results
// Features:
//  - Drop-in replacement for result_fifo with identical interface
//  - Dual-port BRAM for independent read/write access
//  - FIFO-compatible read/write semantics
//  - Full/empty status flags
//  - Count output for monitoring
//  - Wrapper around flex_fifo for consistent implementation
//
// Author: Junhao Pan
// Date: 10/03/2025
// Updated: 11/13/2025 - Refactored to use flex_fifo
// ------------------------------------------------------------------

module result_bram
import gemm_pkg::*;
(
    input  logic        i_clk,
    input  logic        i_reset_n,

    // Write Interface (from Compute Engine)
    input  logic [15:0] i_wr_data,     // FP16: [15]=sign, [14:10]=exp, [9:0]=mantissa
    input  logic        i_wr_en,
    output logic        o_full,
    output logic        o_afull,       // Almost full (back-pressure)

    // Read Interface (to Testbench/Host)
    output logic [15:0] o_rd_data,
    input  logic        i_rd_en,
    output logic        o_empty,

    // Status
    output logic [14:0] o_count
);

    // ===================================================================
    // Parameters
    // ===================================================================
    localparam DEPTH      = tile_out_fifo_els_gp;
    localparam DATA_WIDTH = 16;
    localparam ADDR_WIDTH = $clog2(DEPTH);

    // ===================================================================
    // Internal Signals
    // ===================================================================
    logic [ADDR_WIDTH:0] fifo_count;  // Internal count from flex_fifo

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
        .o_count    (fifo_count)
    );

    // ===================================================================
    // Zero-extend count to 15 bits for interface compatibility
    // ===================================================================
    assign o_count = {{(15-ADDR_WIDTH-1){1'b0}}, fifo_count};

    // ===================================================================
    // Debug Display (for simulation)
    // ===================================================================
    `ifdef SIMULATION
    initial begin
        $display("[RESULT_BRAM] Using flex_fifo with DEPTH=%0d", DEPTH);
        $display("[RESULT_BRAM] Data width: 16-bit FP16 format");
    end

    always @(posedge i_clk) begin
        if (i_wr_en && !o_full) begin
            $display("[RESULT_BRAM] Write: data=0x%04x, count=%0d", i_wr_data, fifo_count+1);
        end
        if (i_rd_en && !o_empty) begin
            $display("[RESULT_BRAM] Read: data=0x%04x, count=%0d", o_rd_data, fifo_count-1);
        end
        if (o_full && i_wr_en) begin
            $warning("[RESULT_BRAM] Buffer full! count=%0d", fifo_count);
        end
    end
    `endif

endmodule : result_bram
