// ------------------------------------------------------------------
// 2-D Multi-Row GEMM Result Collector
//
// Purpose: Collects and reduces partial results from all compute engine rows
// Refactored to use FP16 FIFO interface from compute_engine_2d
//
// Architecture:
//  - Receives FP16 results from NUM_ROWS x NUM_COLS CE FIFOs
//  - Processes column-by-column: for each column, read from all rows and reduce
//  - Uses comp_fp_adder_pipeline for FP16 row reduction (16 inputs -> 1 output)
//  - Serializes reduced results into 256-bit output lines (16 x FP16)
//  - Flexible NUM_COLS support via serialization buffer
//
// Data Flow:
//  1. On READOUT, drain CE FIFOs column-by-column (all rows for col c)
//  2. FP16 adder pipeline reduces 16 row values to 1 FP16
//  3. Serialize reduced results into 16-slot buffer
//  4. Pack buffer to 256-bit output when full (or partial on last)
//
// Output Order:
//  - For B batches, C columns: output packed FP16 lines
//  - Each line = 16 FP16 values (256 bits)
//  - Keep mask indicates valid positions in partial last line
//
// Author: Junhao Pan
// Date: 01/22/2026
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
    // Command Interface (snoops MC command bus)
    // RC watches for READOUT opcode and self-triggers
    // ====================================================================
    input  logic [7:0]                   i_mc_cmd_op,          // Opcode from MC
    input  logic [7:0]                   i_mc_cmd_id,          // Command ID from MC
    input  logic [31:0]                  i_cmd_payload_word1,  // {left_len[15:0], right_len[15:0]}
    input  logic [31:0]                  i_cmd_payload_word2,  // Reserved
    input  logic [31:0]                  i_cmd_payload_word3,  // Reserved

    // Acknowledge: asserts after RC sees READOUT and registers payload
    output logic                         o_rc_ack_readout,

    // ====================================================================
    // Compute Engine FIFO Interface (from all CEs)
    // Each CE has NUM_COLS FIFOs outputting FP16 results
    // Using unpacked arrays to match compute_engine_2d ports
    // ====================================================================
    // ce_result_data[row][col] = FP16 data from CE FIFO
    input  logic [15:0] i_ce_result_data [NUM_ROWS-1:0][NUM_COLS-1:0],
    // ce_result_empty[row][col] = 1 when CE FIFO is empty
    input  logic        i_ce_result_empty [NUM_ROWS-1:0][NUM_COLS-1:0],
    // ce_result_rd_en[row][col] = 1 to read from CE FIFO
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
    localparam int COL_IDX_WIDTH = $clog2(NUM_COLS) + 1;
    localparam int SERIAL_IDX_WIDTH = 4;  // For 16-slot serialization buffer

    // Adder pipeline latency: 1 (fp_to_int) + ceil(log2(16)/2) (adder) + 2 (int_to_fp) = ~7 cycles
    localparam int ADDER_STAGES = $clog2(NUM_ROWS);
    localparam int ADDER_LATENCY = 1 + ((ADDER_STAGES + ADDER_SEG_LEN - 1) / ADDER_SEG_LEN) + 2;

    // READOUT opcode constant
    localparam logic [7:0] OPC_READOUT = 8'hF5;

    // ===================================================================
    // FSM States
    // ===================================================================
    typedef enum logic [3:0] {
        ST_IDLE         = 4'd0,
        ST_LATCH_CMD    = 4'd1,    // Latch command and acknowledge
        ST_DRAIN_COL    = 4'd2,    // Assert FIFO read enable
        ST_FIFO_LATENCY = 4'd3,    // Wait 1 cycle for FIFO data (flex_fifo has 1-cycle latency)
        ST_WAIT_REDUCE  = 4'd4,    // Wait for adder pipeline
        ST_SERIALIZE    = 4'd5,    // Collect reduced result
        ST_PACK_OUTPUT  = 4'd6,    // Write 256-bit line to output FIFO
        ST_COMPLETE     = 4'd7
    } state_t;

    state_t state_reg, state_next;

    // ===================================================================
    // Command Detection and Registration
    // ===================================================================
    logic readout_detected;
    assign readout_detected = (state_reg == ST_IDLE) && (i_mc_cmd_op == OPC_READOUT);

    // ===================================================================
    // Command Registers
    // ===================================================================
    logic [7:0]  cmd_id_reg;
    logic [15:0] left_len_reg;       // B: batch dimension
    logic [15:0] right_len_reg;      // C: total columns to process

    // Command unpacking
    logic [15:0] cmd_left_len;
    logic [15:0] cmd_right_len;
    assign cmd_left_len  = i_cmd_payload_word1[31:16];
    assign cmd_right_len = i_cmd_payload_word1[15:0];

    // ===================================================================
    // Iteration Counters
    // ===================================================================
    logic [15:0] batch_cnt;          // Current batch (0..B-1)
    logic [COL_IDX_WIDTH-1:0] col_idx;  // Current column being drained (0..NUM_COLS-1)
    logic [15:0] col_remaining;      // Columns remaining in current batch

    // ===================================================================
    // Adder Pipeline Latency Counter
    // ===================================================================
    logic [3:0] latency_cnt;

    // ===================================================================
    // Serialization Buffer (16 x FP16)
    // ===================================================================
    logic [15:0] serial_buffer [0:15];   // 16 FP16 values
    logic [SERIAL_IDX_WIDTH-1:0] serial_idx;  // Current position (0..15)
    logic [15:0] serial_keep;            // Valid mask

    // ===================================================================
    // Acknowledge Register
    // ===================================================================
    logic ack_readout_reg;
    logic [7:0] completed_id_reg;

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
    // CE FIFO Read Enable Generation
    // ===================================================================
    // Read from column col_idx across all rows when draining
    // Note: flex_fifo has 1-cycle read latency, so we assert rd_en in ST_DRAIN_COL
    // and capture data in ST_FIFO_LATENCY
    logic drain_enable;
    assign drain_enable = (state_reg == ST_DRAIN_COL) && col_fifos_ready;

    always_comb begin
        for (int r = 0; r < NUM_ROWS; r++) begin
            for (int c = 0; c < NUM_COLS; c++) begin
                o_ce_result_rd_en[r][c] = drain_enable && (c == col_idx);
            end
        end
    end

    // ===================================================================
    // FP16 Adder Pipeline - Reduces 16 rows to 1 FP16
    // ===================================================================
    // Collect FP16 values from all rows for current column
    logic [NUM_ROWS-1:0][15:0] adder_inputs;
    logic                      adder_valid_in;
    logic [15:0]               adder_result;
    logic                      adder_valid_out;

    // Transpose: extract column col_idx from all rows
    // Data is valid in ST_FIFO_LATENCY (1 cycle after rd_en was asserted)
    always_comb begin
        for (int r = 0; r < NUM_ROWS; r++) begin
            adder_inputs[r] = i_ce_result_data[r][col_idx];
        end
    end

    // Valid input when FIFO data is ready (in ST_FIFO_LATENCY)
    assign adder_valid_in = (state_reg == ST_FIFO_LATENCY);

    // Instantiate FP16 adder pipeline
    comp_fp_adder_pipeline #(
        .NUM_INPUTS   (NUM_ROWS),     // 16 rows
        .FP_IN_WIDTH  (16),           // FP16 input
        .FP_OUT_WIDTH (16),           // FP16 output
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
    // Entry format: {last[1], keep[16], data[256]}
    localparam OBUF_DATA_WIDTH = 1 + 16 + 256;

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
    // First-Word-Fall-Through (FWFT) Logic for Output FIFO
    // ===================================================================
    // flex_fifo has 1-cycle read latency. We need to pre-fetch the first word
    // so that o_output_valid only asserts when data is actually available.
    //
    // State machine:
    // - When FIFO goes from empty to non-empty, initiate a pre-read
    // - After 1 cycle, data is valid in rd_data_reg
    // - When consumer reads (i_output_ready && o_output_valid), initiate next read
    //
    // CRITICAL: flex_fifo has 1-cycle read latency. Both pre-fetch AND consumer
    // read paths must wait 1 cycle before asserting data_valid.
    //
    logic obuf_data_valid;       // Data in obuf_rd_data is valid
    logic obuf_was_empty;        // Previous cycle empty state
    logic obuf_read_pending;     // Waiting for FIFO read latency (1 cycle)

    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (~i_reset_n) begin
            obuf_data_valid   <= 1'b0;
            obuf_was_empty    <= 1'b1;
            obuf_read_pending <= 1'b0;
        end else begin
            obuf_was_empty <= obuf_empty;

            // Read pending: data arrives 1 cycle after rd_en
            if (obuf_read_pending) begin
                obuf_data_valid   <= 1'b1;
                obuf_read_pending <= 1'b0;
            end
            // Pre-fetch: when FIFO becomes non-empty, start read
            else if (obuf_was_empty && ~obuf_empty) begin
                obuf_read_pending <= 1'b1;  // Wait 1 cycle for data
                obuf_data_valid   <= 1'b0;
            end
            // Consumer read: when data consumed and more available
            else if (o_output_valid && i_output_ready) begin
                obuf_data_valid <= 1'b0;  // Data consumed, not valid yet
                if (~obuf_empty) begin
                    obuf_read_pending <= 1'b1;  // Wait 1 cycle for next data
                end
            end
        end
    end

    // Read enable: pre-fetch OR consumer read (when more data available)
    // Both cases trigger a read, then wait 1 cycle for obuf_read_pending
    assign obuf_rd_en = (obuf_was_empty && ~obuf_empty) ||                  // Pre-fetch
                        (o_output_valid && i_output_ready && ~obuf_empty);  // Consumer read

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

    always_comb begin
        // Pack serial_buffer into 256-bit line
        for (int i = 0; i < 16; i++) begin
            packed_data[i*16 +: 16] = serial_buffer[i];
        end
    end

    // Check if this is the last output (last batch, no more columns)
    assign is_last_output = (batch_cnt == 0) && (col_remaining == 0);

    // ===================================================================
    // FSM: State Transition Logic
    // ===================================================================
    always_comb begin
        state_next = state_reg;

        case (state_reg)
            ST_IDLE: begin
                if (readout_detected) begin
                    state_next = ST_LATCH_CMD;
                end
            end

            ST_LATCH_CMD: begin
                state_next = ST_DRAIN_COL;
            end

            ST_DRAIN_COL: begin
                // Wait for all row FIFOs to have data for current column
                // When ready, assert rd_en (handled by drain_enable) and go to latency wait
                if (col_fifos_ready) begin
                    state_next = ST_FIFO_LATENCY;
                end
            end

            ST_FIFO_LATENCY: begin
                // 1-cycle wait for FIFO read data (flex_fifo has registered output)
                // adder_valid_in is asserted in this state
                state_next = ST_WAIT_REDUCE;
            end

            ST_WAIT_REDUCE: begin
                // Wait for adder pipeline latency
                if (adder_valid_out) begin
                    state_next = ST_SERIALIZE;
                end
            end

            ST_SERIALIZE: begin
                // Check if serialization buffer is full OR this is the very last result
                // Note: col_remaining is decremented AFTER this check, so check for <= 1
                // Pack when: buffer full (16 results) OR last column of last batch
                if ((serial_idx == 4'd15) || (col_remaining <= 16'd1 && batch_cnt == 16'd0)) begin
                    state_next = ST_PACK_OUTPUT;
                end else if (col_remaining <= 16'd1 && batch_cnt > 16'd0) begin
                    // End of current batch, but more batches to come - continue filling buffer
                    state_next = ST_DRAIN_COL;
                end else begin
                    // More columns in current batch
                    state_next = ST_DRAIN_COL;
                end
            end

            ST_PACK_OUTPUT: begin
                // Write to output FIFO when not full
                if (~obuf_full) begin
                    if (is_last_output) begin
                        state_next = ST_COMPLETE;
                    end else if (col_remaining == 16'd0 && batch_cnt > 0) begin
                        // Start next batch
                        state_next = ST_DRAIN_COL;
                    end else begin
                        // Continue current batch
                        state_next = ST_DRAIN_COL;
                    end
                end
            end

            ST_COMPLETE: begin
                state_next = ST_IDLE;
            end

            default: state_next = ST_IDLE;
        endcase
    end

    // ===================================================================
    // FSM: Sequential Logic
    // ===================================================================
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (~i_reset_n) begin
            state_reg        <= ST_IDLE;
            cmd_id_reg       <= 8'h0;
            completed_id_reg <= 8'h0;
            left_len_reg     <= 16'h0;
            right_len_reg    <= 16'h0;
            batch_cnt        <= 16'h0;
            col_idx          <= '0;
            col_remaining    <= 16'h0;
            latency_cnt      <= 4'h0;
            serial_idx       <= 4'h0;
            serial_keep      <= 16'h0;
            ack_readout_reg  <= 1'b0;
            for (int i = 0; i < 16; i++) begin
                serial_buffer[i] <= 16'h0;
            end
        end else begin
            state_reg <= state_next;

            case (state_reg)
                ST_IDLE: begin
                    ack_readout_reg <= 1'b0;
                    if (readout_detected) begin
                        // Latch command parameters
                        cmd_id_reg    <= i_mc_cmd_id;
                        left_len_reg  <= cmd_left_len;
                        right_len_reg <= cmd_right_len;
                        batch_cnt     <= cmd_left_len - 16'd1;  // 0-based counter
                        col_remaining <= cmd_right_len;
                        col_idx       <= '0;
                        serial_idx    <= 4'h0;
                        serial_keep   <= 16'h0;
                    end
                end

                ST_LATCH_CMD: begin
                    ack_readout_reg <= 1'b1;
                end

                ST_DRAIN_COL: begin
                    ack_readout_reg <= 1'b0;
                    // Column drained, wait for pipeline
                    if (col_fifos_ready) begin
                        latency_cnt <= 4'h0;
                    end
                end

                ST_WAIT_REDUCE: begin
                    // Pipeline latency tracking (for debug)
                    latency_cnt <= latency_cnt + 4'h1;
                end

                ST_SERIALIZE: begin
                    // Store reduced result in serialization buffer
                    serial_buffer[serial_idx] <= adder_result;
                    serial_keep[serial_idx]   <= 1'b1;
                    serial_idx <= serial_idx + 4'd1;

                    // Update column tracking
                    if (col_remaining > 16'd1) begin
                        // More columns in this batch
                        col_remaining <= col_remaining - 16'd1;
                        // Advance to next column (wrap at NUM_COLS)
                        if (col_idx == NUM_COLS - 1) begin
                            col_idx <= '0;
                        end else begin
                            col_idx <= col_idx + 1;
                        end
                    end else if (col_remaining == 16'd1 && batch_cnt > 16'd0) begin
                        // Last column of this batch, but more batches to come
                        // Start next batch (col_remaining becomes 0, then reset)
                        col_remaining <= right_len_reg;
                        col_idx <= '0;
                        batch_cnt <= batch_cnt - 16'd1;
                    end else begin
                        // Last column of last batch (col_remaining == 1, batch_cnt == 0)
                        col_remaining <= 16'd0;
                        // Don't advance col_idx, we're done
                    end
                end

                ST_PACK_OUTPUT: begin
                    if (~obuf_full) begin
                        // Reset serialization buffer for next chunk
                        serial_idx  <= 4'h0;
                        serial_keep <= 16'h0;
                        for (int i = 0; i < 16; i++) begin
                            serial_buffer[i] <= 16'h0;
                        end

                        // Handle batch/column transitions
                        if (col_remaining == 16'd0 && batch_cnt > 0) begin
                            // Start next batch
                            batch_cnt     <= batch_cnt - 16'd1;
                            col_remaining <= right_len_reg;
                            col_idx       <= '0;
                        end
                    end
                end

                ST_COMPLETE: begin
                    completed_id_reg <= cmd_id_reg;
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

        if (state_reg == ST_PACK_OUTPUT && ~obuf_full) begin
            obuf_wr_en = 1'b1;
            // Pack: {last[1], keep[16], data[256]}
            obuf_wr_data[OBUF_DATA_WIDTH-1]   = is_last_output;
            obuf_wr_data[256 +: 16]           = serial_keep;
            obuf_wr_data[255:0]               = packed_data;
        end
    end

    // ===================================================================
    // Status Outputs
    // ===================================================================
    assign o_rc_ack_readout    = ack_readout_reg;
    assign o_rc_state          = state_reg;
    assign o_rc_busy           = (state_reg != ST_IDLE);
    assign o_rc_cmd_id         = completed_id_reg;
    assign o_output_fifo_afull = obuf_afull;

endmodule : result_collector_2d

`default_nettype wire
