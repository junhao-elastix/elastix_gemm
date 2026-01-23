// ------------------------------------------------------------------
// MLP Column Compute Controller
//
// Purpose: Controls activation streaming and compute operations for MLP columns
// Architecture:
//   - FSM-based controller for sequential activation processing
//   - Handles batch processing (B batches × V NVs per batch)
//   - Manages handshaking with comp_MLPStack
//
// Operation:
//   - Reads activations from row_bram (left side)
//   - Streams activations to MLP BRAM columns via comp_MLPStack
//   - Processes one NV at a time, one batch at a time
//   - Tracks dot product boundaries (new_dot, last_nv)
//
// Author: Refactored from compute_engine_mlp.sv
// Date: Dec 16, 2025
// ------------------------------------------------------------------

`timescale 1ps / 1ps
`default_nettype none

module comp_mlp_col_ctrl #(
    parameter int MAX_BATCHES = 256,  // Maximum number of batches (B)
    parameter int MAX_VEC_LEN = 128   // Maximum vector length (V)
) (
    input  logic                     i_clk,
    input  logic                     i_reset_n,

    // Control interface
    input  logic                     i_compute_start,      // Pulse to start compute operation
    output logic                     o_compute_done,       // Compute operation complete

    // Configuration parameters
    input  logic [7:0]               i_vec_len,            // V: Number of NVs per batch
    input  logic [7:0]               i_left_ugd_len,       // B: Number of batches

    // Interface to comp_MLPStack
    output logic [6:0]               o_nv_left_rd_idx,     // row_bram read address
    output logic                     o_act_valid,          // Activation data valid
    input  logic                     i_act_ready,          // Ready to accept activation data
    output logic                     o_new_dot,            // Start new dot product (reset accumulator)
    output logic                     o_last_nv             // Last NV of current batch
);

    // =========================================================================
    // State Machine Definition
    // =========================================================================
    // Simplified, handshake-driven controller:
    // - STREAM: o_act_valid held high, advance NV counter on i_act_ready
    // - WAIT_FINISH: o_act_valid low, wait for wrapper to return to IDLE (i_act_ready high)
    typedef enum logic [1:0] {
        COMP_IDLE        = 2'b00,
        COMP_STREAM      = 2'b01,
        COMP_WAIT_FINISH = 2'b10,
        COMP_DONE        = 2'b11
    } comp_ctrl_state_t;

    comp_ctrl_state_t comp_ctrl_state_reg, comp_ctrl_state_next;

    // =========================================================================
    // Internal Signals
    // =========================================================================
    logic [7:0] comp_nv_cnt;      // NV counter within batch (0 to vec_len-1)
    logic [7:0] comp_batch_cnt;   // Batch counter (0 to left_ugd_len-1)
    logic [13:0] comp_nv_idx_full;
    logic [6:0]  comp_nv_idx;

    // =========================================================================
    // State Transition Logic
    // =========================================================================
    always_comb begin
        comp_ctrl_state_next = comp_ctrl_state_reg;

        case (comp_ctrl_state_reg)
            COMP_IDLE: begin
                if (i_compute_start) begin
                    comp_ctrl_state_next = COMP_STREAM;
                end
            end

            COMP_STREAM: begin
                // Advance NVs based on READY handshakes; when we handshake the last NV of a batch,
                // pause and wait for the wrapper to finish its drain/output pipeline.
                if (i_act_ready && (comp_nv_cnt == (i_vec_len - 1))) begin
                    comp_ctrl_state_next = COMP_WAIT_FINISH;
                end
            end

            COMP_WAIT_FINISH: begin
                // Wrapper returns to IDLE after it completes drain; it asserts READY in IDLE.
                if (i_act_ready) begin
                    if (comp_batch_cnt == (i_left_ugd_len - 1)) begin
                        comp_ctrl_state_next = COMP_DONE;
                    end else begin
                        comp_ctrl_state_next = COMP_STREAM;
                    end
                end
            end

            COMP_DONE: begin
                comp_ctrl_state_next = COMP_IDLE;
            end

            default: begin
                comp_ctrl_state_next = COMP_IDLE;
            end
        endcase
    end

    // =========================================================================
    // Sequential State Update
    // =========================================================================
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            comp_ctrl_state_reg <= COMP_IDLE;
            comp_nv_cnt         <= 8'd0;
            comp_batch_cnt      <= 8'd0;
        end else begin
            comp_ctrl_state_reg <= comp_ctrl_state_next;

            case (comp_ctrl_state_reg)
                COMP_IDLE: begin
                    comp_nv_cnt    <= 8'd0;
                    comp_batch_cnt <= 8'd0;
                end

                COMP_STREAM: begin
                    if (i_act_ready) begin
                        if (comp_nv_cnt == (i_vec_len - 1)) begin
                            comp_nv_cnt <= 8'd0;
                        end else begin
                            comp_nv_cnt <= comp_nv_cnt + 8'd1;
                        end
                    end
                end

                COMP_WAIT_FINISH: begin
                    if (i_act_ready) begin
                        if (comp_batch_cnt != (i_left_ugd_len - 1)) begin
                            comp_batch_cnt <= comp_batch_cnt + 8'd1;
                            comp_nv_cnt    <= 8'd0;
                        end
                    end
                end

                default: begin
                    // No counter updates in other states
                end
            endcase
        end
    end

    // =========================================================================
    // Address Calculation
    // =========================================================================
    always_comb begin
        // Calculate: batch_cnt * vec_len + nv_cnt
        comp_nv_idx_full = (comp_batch_cnt * i_vec_len) + comp_nv_cnt;
        comp_nv_idx = comp_nv_idx_full[6:0];
    end

    // =========================================================================
    // Control Signal Generation
    // =========================================================================
    // List ALL control signals explicitly in EACH state for clear debugging
    always_comb begin
        // Default assignments
        o_nv_left_rd_idx = 7'd0;
        o_act_valid      = 1'b0;
        o_new_dot        = 1'b0;
        o_last_nv        = 1'b0;

        case (comp_ctrl_state_reg)
            COMP_IDLE: begin
                o_nv_left_rd_idx = 7'd0;
                o_act_valid      = 1'b0;
                o_new_dot        = 1'b0;
                o_last_nv        = 1'b0;
            end

            COMP_STREAM: begin
                o_nv_left_rd_idx = comp_nv_idx;
                o_act_valid      = 1'b1;
                o_new_dot        = (comp_nv_cnt == 8'd0);
                o_last_nv        = (comp_nv_cnt == (i_vec_len - 1));
            end

            COMP_WAIT_FINISH: begin
                o_nv_left_rd_idx = comp_nv_idx;
                o_act_valid      = 1'b0;
                o_new_dot        = 1'b0;
                o_last_nv        = 1'b0;
            end


            COMP_DONE: begin
                o_nv_left_rd_idx = 7'd0;
                o_act_valid      = 1'b0;
                o_new_dot        = 1'b0;
                o_last_nv        = 1'b0;
            end

            default: begin
                o_nv_left_rd_idx = 7'd0;
                o_act_valid      = 1'b0;
                o_new_dot        = 1'b0;
                o_last_nv        = 1'b0;
            end
        endcase
    end

    // =========================================================================
    // Output Assignment
    // =========================================================================
    assign o_compute_done = (comp_ctrl_state_reg == COMP_DONE);

    // =========================================================================
    // Debug Output
    // =========================================================================
    // synthesis translate_off
    logic [1:0] comp_state_prev;
    always @(posedge i_clk) begin
        comp_state_prev <= comp_ctrl_state_reg;
        if (comp_ctrl_state_reg != comp_state_prev) begin
            $display("[COMP_MLP_COL_CTRL] @%0t state=%0d->%0d, batch=%0d, nv=%0d, act_ready=%b, compute_start=%b",
                     $time, comp_state_prev, comp_ctrl_state_reg, comp_batch_cnt, comp_nv_cnt, i_act_ready, i_compute_start);
        end
    end
    // synthesis translate_on

endmodule

`default_nettype wire


