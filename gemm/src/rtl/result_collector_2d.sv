// ------------------------------------------------------------------
// 2-D Multi-Row GEMM Result Collector (Auto-Drain, Always-Ready Downstream)
//
// Purpose: Collects and reduces partial results from all compute engine rows
// Refactored for auto-drain with always-ready downstream (result_to_dma)
//
// Architecture:
//  - Receives FP16 results from NUM_ROWS x NUM_COLS CE FIFOs
//  - Processes column-by-column: for each column, read from all rows and reduce
//  - Uses comp_fp_adder_pipeline for FP16 row reduction (16 inputs -> 1 output)
//  - Serializes reduced results into 256-bit output lines (16 x FP16)
//
// Auto-Drain Behavior:
//  - Drains CE FIFOs when col_fifos_ready (all rows have data for column)
//  - Output FIFO drained continuously (downstream always ready)
//  - No READOUT command needed, no backpressure from downstream
//  - Completion detected via i_ce_results_ready signal from CEs
//  - Packs partial line when results_ready_seen AND all FIFOs empty
//
// Output Interface:
//  - Simplified: downstream always accepts (i_output_ready = 1)
//  - Each line = 16 FP16 values (256 bits)
//  - Keep mask indicates valid positions in partial last line
//  - Last signal asserts on final partial line
//
// Author: Junhao Pan
// Date: 01/29/2026 (Simplified for always-ready downstream)
// ------------------------------------------------------------------

`timescale 1ps / 1ps
`default_nettype none

module result_collector_2d
import gemm_pkg::*;
#(
    parameter int NUM_ROWS = 16,              // Number of compute rows to reduce
    parameter int NUM_COLS = 16,              // Number of columns per CE (flexible)
    parameter int ADDER_SEG_LEN = 2,          // Adder pipeline segment length
    parameter int OUTPUT_FIFO_DEPTH = 256     // Depth of final output FIFO
)
(
    input  logic                         i_clk,
    input  logic                         i_reset_n,

    // ====================================================================
    // Results Ready Signal (from CEs via engine_top_2d)
    // Indicates CEs have completed computation and FIFOs have expected data
    // ====================================================================
    input  logic                         i_ce_results_ready,

    // ====================================================================
    // Command Interface (kept for compatibility, not used for flow control)
    // ====================================================================
    input  logic [7:0]                   i_mc_cmd_op,          // Opcode from MC
    input  logic [7:0]                   i_mc_cmd_id,          // Command ID from MC
    input  logic [31:0]                  i_cmd_payload_word1,  // {left_len[15:0], right_len[15:0]}
    input  logic [31:0]                  i_cmd_payload_word2,  // Reserved
    input  logic [31:0]                  i_cmd_payload_word3,  // Reserved

    // Acknowledge: kept for compatibility
    output logic                         o_rc_ack_readout,

    // ====================================================================
    // Compute Engine FIFO Interface (from all CEs)
    // Each CE has NUM_COLS FIFOs outputting FP16 results
    // ====================================================================
    input  logic [15:0] i_ce_result_data [NUM_ROWS-1:0][NUM_COLS-1:0],
    input  logic        i_ce_result_empty [NUM_ROWS-1:0][NUM_COLS-1:0],
    output logic        o_ce_result_rd_en [NUM_ROWS-1:0][NUM_COLS-1:0],

    // ====================================================================
    // Output Interface (to Host DMA)
    // Output is packed 256-bit lines (16 x FP16)
    // ====================================================================
    input  logic                         i_output_ready,
    output logic                         o_output_valid,
    output logic                         o_output_last,       // Last result in sequence
    output logic [15:0]                  o_output_keep,       // Valid mask (16 bits)
    output logic [255:0]                 o_output_data,       // 16 x FP16 packed

    // ====================================================================
    // Status Interface
    // ====================================================================
    output logic [3:0]                   o_rc_state,
    output logic                         o_rc_busy,
    output logic [7:0]                   o_rc_cmd_id,         // Current command ID being processed
    output logic                         o_output_fifo_afull  // Output FIFO almost-full for debug
);

    // ===================================================================
    // Local Parameters
    // ===================================================================
    localparam int COL_IDX_WIDTH = $clog2(NUM_COLS);
    localparam int SERIAL_IDX_WIDTH = 4;  // For 16-slot serialization buffer

    // Adder pipeline latency
    localparam int ADDER_STAGES = $clog2(NUM_ROWS);
    localparam int ADDER_LATENCY = 1 + ((ADDER_STAGES + ADDER_SEG_LEN - 1) / ADDER_SEG_LEN) + 2;

    // ===================================================================
    // FSM States (Simplified for auto-drain)
    // ===================================================================
    typedef enum logic [3:0] {
        ST_IDLE         = 4'd0,    // Wait for data in any FIFO
        ST_DRAIN_COL    = 4'd1,    // Assert FIFO read enable when ready
        ST_FIFO_LATENCY = 4'd2,    // Wait 1 cycle for FIFO data
        ST_WAIT_REDUCE  = 4'd3,    // Wait for adder pipeline
        ST_SERIALIZE    = 4'd4,    // Collect reduced result
        ST_PACK_OUTPUT  = 4'd5,    // Write 256-bit line to output FIFO
        ST_FLUSH_PARTIAL= 4'd6     // Flush partial buffer on completion
    } state_t;

    state_t state_reg, state_next;

    // ===================================================================
    // Column Index and Serialization
    // ===================================================================
    logic [COL_IDX_WIDTH-1:0] col_idx;       // Current column being drained
    logic [SERIAL_IDX_WIDTH-1:0] serial_idx; // Current position in buffer (0..15)
    logic [15:0] serial_keep;                // Valid mask
    logic [15:0] serial_buffer [0:15];       // 16 FP16 values

    // ===================================================================
    // Completion Detection
    // ===================================================================
    logic results_ready_seen;    // Sticky: i_ce_results_ready was seen
    logic all_fifos_empty;       // All row/col FIFOs are empty
    logic any_fifo_has_data;     // At least one FIFO has data

    // Check if ALL FIFOs across all rows and columns are empty
    always_comb begin
        all_fifos_empty = 1'b1;
        any_fifo_has_data = 1'b0;
        for (int r = 0; r < NUM_ROWS; r++) begin
            for (int c = 0; c < NUM_COLS; c++) begin
                if (!i_ce_result_empty[r][c]) begin
                    all_fifos_empty = 1'b0;
                    any_fifo_has_data = 1'b1;
                end
            end
        end
    end

    // ===================================================================
    // Column FIFO Ready Check
    // ===================================================================
    // Check if all rows have data for current column
    logic col_fifos_ready;
    always_comb begin
        col_fifos_ready = 1'b1;
        for (int r = 0; r < NUM_ROWS; r++) begin
            col_fifos_ready = col_fifos_ready && !i_ce_result_empty[r][col_idx];
        end
    end

    // ===================================================================
    // Drain Condition
    // ===================================================================
    // Can drain when: in drain state, column ready, output not backpressured
    logic drain_enable;
    logic can_start_drain;

    assign drain_enable = (state_reg == ST_DRAIN_COL) && col_fifos_ready && !obuf_afull;
    assign can_start_drain = any_fifo_has_data && !obuf_afull;

    // ===================================================================
    // CE FIFO Read Enable Generation
    // ===================================================================
    always_comb begin
        for (int r = 0; r < NUM_ROWS; r++) begin
            for (int c = 0; c < NUM_COLS; c++) begin
                o_ce_result_rd_en[r][c] = drain_enable && (c[COL_IDX_WIDTH-1:0] == col_idx);
            end
        end
    end

    // ===================================================================
    // FP16 Adder Pipeline - Reduces NUM_ROWS to 1 FP16
    // ===================================================================
    logic [NUM_ROWS-1:0][15:0] adder_inputs;
    logic                      adder_valid_in;
    logic [15:0]               adder_result;
    logic                      adder_valid_out;

    // Transpose: extract column col_idx from all rows
    always_comb begin
        for (int r = 0; r < NUM_ROWS; r++) begin
            adder_inputs[r] = i_ce_result_data[r][col_idx];
        end
    end

    // Valid input when FIFO data is ready
    assign adder_valid_in = (state_reg == ST_FIFO_LATENCY);

    // Instantiate FP16 adder pipeline
    comp_fp_adder_pipeline #(
        .NUM_INPUTS   (NUM_ROWS),
        .FP_IN_WIDTH  (16),
        .FP_OUT_WIDTH (16),
        .INT_WIDTH    (128),
        .FRAC_BITS    (48),
        .SEG_LEN      (ADDER_SEG_LEN)
    ) u_row_reducer (
        .clk      (i_clk),
        .rst_n    (i_reset_n),
        .en       (1'b1),
        .i_fp     (adder_inputs),
        .i_valid  (adder_valid_in),
        .o_fp     (adder_result),
        .o_valid  (adder_valid_out)
    );

    // ===================================================================
    // Output Buffer FIFO
    // ===================================================================
    localparam OBUF_DATA_WIDTH = 1 + 16 + 256;  // {last, keep, data}

    logic                         obuf_wr_en;
    logic                         obuf_rd_en;
    logic                         obuf_empty;
    logic                         obuf_full;
    logic                         obuf_afull;
    logic [OBUF_DATA_WIDTH-1:0]   obuf_wr_data;
    logic [OBUF_DATA_WIDTH-1:0]   obuf_rd_data;

    flex_fifo #(
        .DATA_WIDTH(OBUF_DATA_WIDTH),
        .DEPTH(OUTPUT_FIFO_DEPTH)
    ) u_output_fifo (
        .i_clk      (i_clk),
        .i_reset_n  (i_reset_n),
        .i_wr_data  (obuf_wr_data),
        .i_wr_en    (obuf_wr_en),
        .o_full     (obuf_full),
        .o_afull    (obuf_afull),
        .o_rd_data  (obuf_rd_data),
        .i_rd_en    (obuf_rd_en),
        .o_empty    (obuf_empty),
        .o_count    ()
    );

    // ===================================================================
    // Simplified Output FIFO Read Logic (Always-Drain Mode)
    // ===================================================================
    // Downstream (result_to_dma) is always ready, so we continuously
    // drain the output FIFO whenever it has data. No FWFT complexity needed.
    logic obuf_data_valid;

    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (~i_reset_n) begin
            obuf_data_valid <= 1'b0;
        end else begin
            // Data valid 1 cycle after read (FIFO read latency)
            obuf_data_valid <= obuf_rd_en;
        end
    end

    // Always read when FIFO has data (downstream always ready)
    assign obuf_rd_en = ~obuf_empty;

    // Unpack output FIFO
    assign o_output_last = obuf_rd_data[OBUF_DATA_WIDTH-1];
    assign o_output_keep = obuf_rd_data[256 +: 16];
    assign o_output_data = obuf_rd_data[255:0];
    assign o_output_valid = obuf_data_valid;

    // ===================================================================
    // Pack Serialization Buffer to Output
    // ===================================================================
    logic [255:0] packed_data;
    logic         is_last_output;
    logic         should_pack_partial;

    always_comb begin
        for (int i = 0; i < 16; i++) begin
            packed_data[i*16 +: 16] = serial_buffer[i];
        end
    end

    // Pack partial line when: results_ready was seen, all FIFOs empty, buffer has data
    assign should_pack_partial = results_ready_seen && all_fifos_empty && (serial_idx > 0);

    // Last output when:
    // 1. Flushing partial buffer (ST_FLUSH_PARTIAL), OR
    // 2. Packing full buffer (ST_PACK_OUTPUT) AND results complete AND no more data
    assign is_last_output = (state_reg == ST_FLUSH_PARTIAL) ||
                            (state_reg == ST_PACK_OUTPUT && results_ready_seen && !any_fifo_has_data);

    // ===================================================================
    // FSM: State Transition Logic
    // ===================================================================
    always_comb begin
        state_next = state_reg;

        case (state_reg)
            ST_IDLE: begin
                // Start draining when any FIFO has data and output not backpressured
                if (can_start_drain) begin
                    state_next = ST_DRAIN_COL;
                end
                // Flush partial buffer if results complete and buffer has data
                else if (should_pack_partial) begin
                    state_next = ST_FLUSH_PARTIAL;
                end
            end

            ST_DRAIN_COL: begin
                // Wait for current column to be ready, then drain
                if (col_fifos_ready && !obuf_afull) begin
                    state_next = ST_FIFO_LATENCY;
                end
                // If no data available for this column, try next or go idle
                else if (all_fifos_empty) begin
                    if (should_pack_partial) begin
                        state_next = ST_FLUSH_PARTIAL;
                    end else begin
                        state_next = ST_IDLE;
                    end
                end
                // Backpressure: wait
            end

            ST_FIFO_LATENCY: begin
                // 1-cycle wait for FIFO read data
                state_next = ST_WAIT_REDUCE;
            end

            ST_WAIT_REDUCE: begin
                // Wait for adder pipeline
                if (adder_valid_out) begin
                    state_next = ST_SERIALIZE;
                end
            end

            ST_SERIALIZE: begin
                // Check if buffer is full (16 results)
                if (serial_idx == 4'd15) begin
                    state_next = ST_PACK_OUTPUT;
                end else begin
                    // Continue draining
                    state_next = ST_DRAIN_COL;
                end
            end

            ST_PACK_OUTPUT: begin
                // Write to output FIFO when not full
                if (~obuf_full) begin
                    // Continue draining if more data available
                    if (any_fifo_has_data && !obuf_afull) begin
                        state_next = ST_DRAIN_COL;
                    end else begin
                        state_next = ST_IDLE;
                    end
                end
            end

            ST_FLUSH_PARTIAL: begin
                // Flush partial buffer (last line)
                if (~obuf_full) begin
                    state_next = ST_IDLE;
                end
            end

            default: state_next = ST_IDLE;
        endcase
    end

    // ===================================================================
    // FSM: Sequential Logic
    // ===================================================================
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (~i_reset_n) begin
            state_reg          <= ST_IDLE;
            col_idx            <= '0;
            serial_idx         <= 4'h0;
            serial_keep        <= 16'h0;
            results_ready_seen <= 1'b0;
            for (int i = 0; i < 16; i++) begin
                serial_buffer[i] <= 16'h0;
            end
        end else begin
            state_reg <= state_next;

            // Latch results_ready (sticky until reset or completion flush)
            if (i_ce_results_ready) begin
                results_ready_seen <= 1'b1;
            end

            case (state_reg)
                ST_IDLE: begin
                    // Nothing special
                end

                ST_DRAIN_COL: begin
                    // Move to next column if current is empty but others have data
                    if (!col_fifos_ready && !all_fifos_empty) begin
                        if (col_idx == NUM_COLS - 1) begin
                            col_idx <= '0;
                        end else begin
                            col_idx <= col_idx + 1;
                        end
                    end
                end

                ST_SERIALIZE: begin
                    // Store reduced result in serialization buffer
                    serial_buffer[serial_idx] <= adder_result;
                    serial_keep[serial_idx]   <= 1'b1;
                    serial_idx <= serial_idx + 4'd1;

                    // Advance to next column (round-robin)
                    if (col_idx == NUM_COLS - 1) begin
                        col_idx <= '0;
                    end else begin
                        col_idx <= col_idx + 1;
                    end
                end

                ST_PACK_OUTPUT: begin
                    if (~obuf_full) begin
                        // Reset serialization buffer
                        serial_idx  <= 4'h0;
                        serial_keep <= 16'h0;
                        for (int i = 0; i < 16; i++) begin
                            serial_buffer[i] <= 16'h0;
                        end
                        // Clear results_ready_seen if this was the last output (full buffer, no more data)
                        if (results_ready_seen && !any_fifo_has_data) begin
                            results_ready_seen <= 1'b0;
                        end
                    end
                end

                ST_FLUSH_PARTIAL: begin
                    if (~obuf_full) begin
                        // Reset after flush
                        serial_idx         <= 4'h0;
                        serial_keep        <= 16'h0;
                        results_ready_seen <= 1'b0;  // Clear sticky flag
                        for (int i = 0; i < 16; i++) begin
                            serial_buffer[i] <= 16'h0;
                        end
                    end
                end

                default: ;
            endcase
        end
    end

    // ===================================================================
    // Output FIFO Write Logic
    // ===================================================================
    always_comb begin
        obuf_wr_en = 1'b0;
        obuf_wr_data = '0;

        if ((state_reg == ST_PACK_OUTPUT || state_reg == ST_FLUSH_PARTIAL) && ~obuf_full) begin
            obuf_wr_en = 1'b1;
            obuf_wr_data[OBUF_DATA_WIDTH-1] = is_last_output;
            obuf_wr_data[256 +: 16]         = serial_keep;
            obuf_wr_data[255:0]             = packed_data;
        end
    end

    // ===================================================================
    // Status Outputs
    // ===================================================================
    assign o_rc_ack_readout    = 1'b0;  // Not used in auto-drain mode
    assign o_rc_state          = state_reg;
    assign o_rc_busy           = (state_reg != ST_IDLE) || any_fifo_has_data;
    assign o_rc_cmd_id         = 8'h0;  // Not used in auto-drain mode
    assign o_output_fifo_afull = obuf_afull;

endmodule : result_collector_2d

`default_nettype wire
