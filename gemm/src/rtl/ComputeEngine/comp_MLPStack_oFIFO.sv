// ------------------------------------------------------------------
// MLPStack Output FIFO Wrapper
//
// Purpose: Contains 16 flex_fifos that receive FP16 results from
//          comp_MLPStack and provide buffered read interface for
//          downstream consumers.
//
// Architecture:
//   - 16 parallel FIFOs, one per logical column
//   - Column mapping: col0, col1, col2, ..., col15
//   - All FIFOs written simultaneously when i_result_push asserts
//   - Per-column read enable for flexible consumption
//
// Flow Control:
//   - o_result_fifo_full: OR of all FIFO full flags (feedback to MLPStack)
//   - o_result_afull: OR of all FIFO almost-full flags (early warning)
//   - o_result_empty[c]: Per-column empty flag for read gating
//
// Author: Compute Engine Refactoring
// Date: Jan 21, 2026
// ------------------------------------------------------------------

`timescale 1ps / 1ps
`default_nettype none

module comp_MLPStack_oFIFO #(
    parameter int NUM_COLS = 16,    // 16 logical columns (8 MLPs x 2 banks)
    parameter int FIFO_DEPTH  = 512    // Entries per FIFO (increased for large batch support)
) (
    input  logic        clk,
    input  logic        rstn,

    // =========================================================================
    // Input from MLPStack (16 FP16 results in parallel)
    // =========================================================================
    input  logic [15:0] i_result_fp16 [NUM_COLS-1:0],  // 16 x FP16 results
    input  logic        i_result_push,                     // Push enable (all 16 FIFOs)
    input  logic [NUM_COLS-1:0] i_valid_cols_mask,         // Per-column valid mask (1=write, 0=skip)
    output logic        o_result_fifo_full,                // Feedback: any FIFO full

    // =========================================================================
    // Output FIFO Read Interface (16 columns)
    // Using unpacked arrays for compatibility with parent module wiring
    // =========================================================================
    output logic [15:0] o_result_data [NUM_COLS-1:0],   // FP16 per column
    input  logic        i_result_rd_en [NUM_COLS-1:0],  // Per-column read enable
    output logic        o_result_empty [NUM_COLS-1:0],  // Per-column empty flag
    output logic        o_result_afull                     // OR of all FIFO afull flags
);

    // =========================================================================
    // Internal Signals
    // =========================================================================
    logic [NUM_COLS-1:0] fifo_full;
    logic [NUM_COLS-1:0] fifo_afull;

    // =========================================================================
    // Generate 16 flex_fifos
    // =========================================================================
    generate
        for (genvar c = 0; c < NUM_COLS; c++) begin : gen_result_fifo
            flex_fifo #(
                .DATA_WIDTH(16),
                .DEPTH(FIFO_DEPTH)
            ) u_result_fifo (
                .i_clk(clk),
                .i_reset_n(rstn),

                // Write Interface
                // Only write to FIFO if column is valid (handles C % NUM_COLS != 0)
                .i_wr_data(i_result_fp16[c]),
                .i_wr_en(i_result_push && !fifo_full[c] && i_valid_cols_mask[c]),
                .o_full(fifo_full[c]),
                .o_afull(fifo_afull[c]),

                // Read Interface
                .o_rd_data(o_result_data[c]),
                .i_rd_en(i_result_rd_en[c]),
                .o_empty(o_result_empty[c]),

                // Status (unused)
                .o_count()
            );
        end
    endgenerate

    // =========================================================================
    // Aggregate Status Flags
    // =========================================================================
    assign o_result_fifo_full = |fifo_full;
    assign o_result_afull     = |fifo_afull;

    // =========================================================================
    // Debug Output
    // =========================================================================
    // synthesis translate_off
    `ifdef DEBUG_MLPSTACK
    always @(posedge clk) begin
        if (rstn && i_result_push) begin
            $display("[OFIFO] @%0t PUSH: col0=0x%04x col1=0x%04x col2=0x%04x col3=0x%04x any_full=%b",
                     $time, i_result_fp16[0], i_result_fp16[1], i_result_fp16[2], i_result_fp16[3],
                     o_result_fifo_full);
        end
    end
    `endif
    // synthesis translate_on

endmodule : comp_MLPStack_oFIFO

`default_nettype wire
