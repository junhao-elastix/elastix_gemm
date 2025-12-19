// ------------------------------------------------------------------
// BRAM Fill Controller
//
// Purpose: Controls weight loading from row_bram to MLP BRAM columns
// Architecture:
//   - FSM-based controller for sequential weight loading
//   - Supports column groups for C > 16
//   - Handles address calculation with base address offset
//
// Operation:
//   - Reads weights from row_bram (right side)
//   - Writes weights to MLP BRAM columns via comp_mlp_bram_col_wrapper
//   - Processes one column at a time, one NV at a time
//   - Supports multiple column groups for large C values
//
// Author: Refactored from compute_engine_mlp.sv
// Date: Dec 16, 2025
// ------------------------------------------------------------------

`timescale 1ps / 1ps
`default_nettype none

module comp_bram_fill_ctrl #(
    parameter int NUM_COLUMNS = 16  // Number of MLP columns (fixed at 16)
) (
    input  logic                     i_clk,
    input  logic                     i_reset_n,

    // Control interface
    input  logic                     i_fill_start,           // Pulse to start fill operation
    output logic                     o_fill_done,            // Fill operation complete

    // Configuration parameters
    input  logic [7:0]               i_vec_len,              // V: Number of NVs per column
    input  logic [7:0]               i_right_ugd_len,        // C: Total number of columns
    input  logic [15:0]              i_right_base_addr,      // Base address for row_bram reads
    input  logic [3:0]               i_col_group_cnt,        // Current column group (0-7)

    // DISPATCH distribution parameters (used when i_fill_is_dispatch=1)
    input  logic                     i_fill_is_dispatch,    // 1: DISPATCH-distribute fill, 0: TILE column-major fill
    input  logic [7:0]               i_disp_man_nv_cnt,      // Total NVs to load (man_nv_cnt)
    input  logic [NUM_COLUMNS-1:0]   i_disp_col_en,          // Enabled column mask (LSBs used)
    input  logic [4:0]               i_disp_col_start,       // Start column index for round-robin distribution
    input  logic                     i_disp_broadcast,      // 1=broadcast, 0=distribute

    // Interface to comp_mlp_bram_col_wrapper
    output logic [6:0]               o_nv_right_rd_idx,      // row_bram read address
    output logic                     o_wt_valid,             // Weight data valid (latch trigger)
    input  logic                     i_wt_ready,             // Ready to accept weight data
    output logic [3:0]               o_col_sel,              // Target column (0-15)
    output logic                     o_wt_col_valid,         // 1 if this column is < C (valid), else 0 (zero-fill)
    output logic [6:0]               o_wt_nv_idx,            // NV index within column
    output logic [1:0]               o_wt_cycle_cnt,         // Current cycle within 4-cycle load
    output logic                     o_wt_loading            // Currently loading (FILL_LOAD state)
);

    // =========================================================================
    // State Machine Definition
    // =========================================================================
    typedef enum logic [2:0] {
        FILL_IDLE     = 3'b000,
        FILL_READ     = 3'b001,
        FILL_LOAD     = 3'b010,  // 4-cycle weight loading (merged from wrapper FSM)
        FILL_NEXT     = 3'b011,
        FILL_DONE     = 3'b100
    } fill_state_t;

    fill_state_t fill_state_reg, fill_state_next;

    // =========================================================================
    // Internal Signals
    // =========================================================================
    // Fill counters
    logic [7:0] fill_nv_cnt;      // NV counter within column (0 to vec_len-1)
    logic [3:0] fill_col_cnt;     // Column counter within group (0 to NUM_COLUMNS-1)
    logic [1:0] wt_cycle_cnt;     // Weight loading cycle counter (0-3)

    // DISPATCH-mode counters (sequential source NV index)
    logic [7:0] disp_src_nv_cnt;  // 0..(disp_man_nv_cnt-1)
    logic [3:0] disp_col_sel_reg; // Latched destination column for current NV
    logic [6:0] disp_wt_nv_idx_reg; // Latched destination NV index within column for current NV

    // DISPATCH-mode derived fields
    logic [7:0] disp_batch_idx;     // batch = src_nv / vec_len
    logic [7:0] disp_nv_in_batch;   // within-batch NV index = src_nv % vec_len
    logic [7:0] disp_total_batches; // man_nv_cnt / vec_len
    logic [4:0] disp_num_enabled;   // popcount(col_en)
    logic [4:0] disp_start_logical; // col_start % num_enabled
    logic [4:0] disp_logical_col;   // (start + batch) % num_enabled
    logic [7:0] disp_nv_row;        // (start + batch) / num_enabled

    // Next mapping outputs (computed combinationally)
    logic [4:0] disp_col_sel_next;
    logic [6:0] disp_wt_nv_idx_next;

    // Enabled column list
    // NOTE: In the current MLP-mode contract, `col_en` is treated as deprecated/ignored.
    // We always consider all NUM_COLUMNS physical columns enabled for distribution.
    logic [4:0] enabled_cols [NUM_COLUMNS-1:0];
    logic [4:0] enabled_count;
    integer k;

    // Address calculation
    logic [13:0] fill_nv_idx_full;  // Extended to support larger indices
    logic [6:0]  fill_nv_idx;       // NV index for address calculation
    logic [6:0]  right_base_nv_idx; // row_bram NV index base (line_addr >> 2)
    logic [7:0]  col_abs;           // Absolute column index across groups (0..127)
    logic        col_valid;         // col_abs < C

    // =========================================================================
    // State Transition Logic
    // =========================================================================
    always_comb begin
        fill_state_next = fill_state_reg;

        case (fill_state_reg)
            FILL_IDLE: begin
                if (i_fill_start) begin
                    fill_state_next = FILL_READ;
                end
            end

            FILL_READ: begin
                // Wait one cycle for row_bram read, then start loading if ready
                if (i_wt_ready) begin
                    fill_state_next = FILL_LOAD;
                end
            end

            FILL_LOAD: begin
                // Stay in FILL_LOAD for 4 cycles (merged from wrapper's WT_LOAD)
                if (wt_cycle_cnt == 2'd3) begin
                    fill_state_next = FILL_NEXT;
                end
            end

            FILL_NEXT: begin
                if (i_fill_is_dispatch) begin
                    if (disp_src_nv_cnt == (i_disp_man_nv_cnt - 1)) begin
                        fill_state_next = FILL_DONE;
                    end else begin
                        fill_state_next = FILL_READ;
                    end
                end else begin
                    if (fill_col_cnt == (NUM_COLUMNS - 1) &&
                        fill_nv_cnt == (i_vec_len - 1)) begin
                        fill_state_next = FILL_DONE;
                    end else begin
                        fill_state_next = FILL_READ;
                    end
                end
            end

            FILL_DONE: begin
                fill_state_next = FILL_IDLE;
            end

            default: begin
                fill_state_next = FILL_IDLE;
            end
        endcase
    end

    // =========================================================================
    // Sequential State Update
    // =========================================================================
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            fill_state_reg <= FILL_IDLE;
            fill_nv_cnt    <= 8'd0;
            fill_col_cnt   <= 4'd0;
            wt_cycle_cnt   <= 2'd0;
            disp_src_nv_cnt <= 8'd0;
            disp_col_sel_reg <= 4'd0;
            disp_wt_nv_idx_reg <= 7'd0;
        end else begin
            fill_state_reg <= fill_state_next;
            
            `ifdef SIMULATION
            if (fill_state_reg != fill_state_next) begin
                $display("[FILL_CTRL_STATE] @%0t %s -> %s (is_dispatch=%0b)",
                         $time, fill_state_reg.name(), fill_state_next.name(), i_fill_is_dispatch);
            end
            `endif

            case (fill_state_reg)
                FILL_IDLE: begin
                    fill_nv_cnt  <= 8'd0;
                    fill_col_cnt <= 4'd0;
                    wt_cycle_cnt <= 2'd0;
                    disp_src_nv_cnt <= 8'd0;
                end

                FILL_READ: begin
                    wt_cycle_cnt <= 2'd0;  // Reset cycle counter before loading
                    // Latch DISPATCH destination mapping at start of each NV
                    if (i_fill_is_dispatch) begin
                        disp_col_sel_reg   <= disp_col_sel_next;
                        disp_wt_nv_idx_reg <= disp_wt_nv_idx_next;
                    end
                end

                FILL_LOAD: begin
                    wt_cycle_cnt <= wt_cycle_cnt + 2'd1;  // Increment during 4-cycle load
                end

                FILL_NEXT: begin
                    wt_cycle_cnt <= 2'd0;
                    if (i_fill_is_dispatch) begin
                        if (disp_src_nv_cnt != (i_disp_man_nv_cnt - 1)) begin
                            disp_src_nv_cnt <= disp_src_nv_cnt + 8'd1;
                        end
                    end else begin
                        if (fill_nv_cnt == (i_vec_len - 1)) begin
                            fill_nv_cnt  <= 8'd0;
                            fill_col_cnt <= fill_col_cnt + 4'd1;
                        end else begin
                            fill_nv_cnt <= fill_nv_cnt + 8'd1;
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
    // For C > 16, we need to add the column group offset:
    //   fill_nv_idx = ((col_group_cnt * 16) + fill_col_cnt) * vec_len + fill_nv_cnt
    // This reads weights from the correct offset in row_bram for each group
    //
    // Memory layout (column-major, V NVs per column):
    //   Group 0: Col 0 [NV 0..V-1], Col 1 [NV V..2V-1], ..., Col 15 [NV 15V..16V-1]
    //   Group 1: Col 16 [NV 16V..17V-1], Col 17 [NV 17V..18V-1], ..., Col 31 [NV 31V..32V-1]
    //   etc.
    always_comb begin
        // TILE-mode: column-major address calculation
        // Calculate: ((col_group_cnt * 16) + fill_col_cnt) * vec_len + fill_nv_cnt
        // = (col_group_cnt * 16 * V) + (fill_col_cnt * V) + fill_nv_cnt
        fill_nv_idx_full = ({i_col_group_cnt, 4'd0} * i_vec_len) +  // group offset: col_group_cnt * 16 * V
                          (fill_col_cnt * i_vec_len) +               // column offset within group
                          fill_nv_cnt;                                // NV within column
        fill_nv_idx = fill_nv_idx_full[6:0];
    end

    // DISPATCH-mode mapping: sequential source NV stream distributed across enabled columns
    // Per MULTI_TILE_DISPATCH_REFERENCE.md:
    // - One "UGD vector" = i_vec_len NVs goes to one column.
    // - Columns are selected round-robin starting at i_disp_col_start within enabled set.
    // - When wrapping to the first enabled column, the destination "row" increments.
    //
    // This produces destination wt_nv_idx = (dest_row * i_vec_len) + nv_in_batch.
    always_comb begin
        // Build enabled column list (physical col indices 0..NUM_COLUMNS-1)
        // `i_disp_col_en` is ignored in MLP mode: treat all columns enabled.
        enabled_count = NUM_COLUMNS[4:0];
        for (k = 0; k < NUM_COLUMNS; k = k + 1) begin
            enabled_cols[k] = k[4:0];
        end

        disp_num_enabled   = enabled_count;
        disp_total_batches = (i_vec_len == 8'd0) ? 8'd0 : (i_disp_man_nv_cnt / i_vec_len);
        disp_batch_idx     = (i_vec_len == 8'd0) ? 8'd0 : (disp_src_nv_cnt / i_vec_len);
        disp_nv_in_batch   = (i_vec_len == 8'd0) ? 8'd0 : (disp_src_nv_cnt % i_vec_len);

        disp_start_logical = i_disp_col_start % disp_num_enabled;
        disp_logical_col   = (disp_start_logical + disp_batch_idx) % disp_num_enabled;
        disp_nv_row        = (disp_start_logical + disp_batch_idx) / disp_num_enabled;
        disp_col_sel_next  = enabled_cols[disp_logical_col];

        // Destination NV index within column
        // NOTE: broadcast mode is not parallelized here; the caller should use distribute semantics
        // (one column per batch). This mapping is the distribute mapping.
        disp_wt_nv_idx_next = (disp_nv_row * i_vec_len + disp_nv_in_batch);
    end

    // Determine whether the current column within this group is valid for the configured C.
    // For the final partial group when C is not divisible by 16, columns >= C are invalid.
    assign col_abs   = {i_col_group_cnt, 4'd0} + {4'd0, fill_col_cnt};
    assign col_valid = (col_abs < i_right_ugd_len);

    // row_bram stores 4 line writes per NV, and the NV read interface is indexed by NV number.
    // Convert the line-address base (0..511) into an NV index base (0..127) by shifting right by 2.
    assign right_base_nv_idx = i_right_base_addr[8:2];

    // =========================================================================
    // Control Signal Generation
    // =========================================================================
    // List ALL control signals explicitly in EACH state for clear debugging
    always_comb begin
        // Default assignments
        o_nv_right_rd_idx = 7'd0;
        o_wt_valid        = 1'b0;
        o_col_sel         = 4'd0;
        o_wt_col_valid    = 1'b0;
        o_wt_nv_idx       = 7'd0;

        case (fill_state_reg)
            FILL_IDLE: begin
                o_nv_right_rd_idx = 7'd0;
                o_wt_valid        = 1'b0;
                o_col_sel         = 4'd0;
                o_wt_col_valid    = 1'b0;
                o_wt_nv_idx       = 7'd0;
            end

            FILL_READ: begin
                // Add base address offset when reading from row_bram
                // Assert valid on transition to LOAD to trigger data latch
                if (i_fill_is_dispatch) begin
                    o_nv_right_rd_idx = right_base_nv_idx + disp_src_nv_cnt[6:0];
                    o_wt_valid        = i_wt_ready;
                    o_col_sel         = disp_col_sel_next[3:0];
                    o_wt_col_valid    = 1'b1;
                    o_wt_nv_idx       = disp_wt_nv_idx_next;
                end else begin
                    o_nv_right_rd_idx = right_base_nv_idx + fill_nv_idx;
                    o_wt_valid        = i_wt_ready;  // Valid when ready to start loading
                    o_col_sel         = fill_col_cnt;        // Column within MLP (0-15)
                    o_wt_col_valid    = col_valid;
                    o_wt_nv_idx       = fill_nv_cnt[6:0];    // NV index within column (for V>1)
                end
            end

            FILL_LOAD: begin
                // Maintain signals during 4-cycle load
                if (i_fill_is_dispatch) begin
                    o_nv_right_rd_idx = right_base_nv_idx + disp_src_nv_cnt[6:0];
                    o_wt_valid        = 1'b0;
                    o_col_sel         = disp_col_sel_reg;
                    o_wt_col_valid    = 1'b1;
                    o_wt_nv_idx       = disp_wt_nv_idx_reg;
                end else begin
                    o_nv_right_rd_idx = right_base_nv_idx + fill_nv_idx;
                    o_wt_valid        = 1'b0;  // Valid only for one cycle to trigger latch
                    o_col_sel         = fill_col_cnt;
                    o_wt_col_valid    = col_valid;
                    o_wt_nv_idx       = fill_nv_cnt[6:0];
                end
            end

            FILL_NEXT: begin
                // Prepare for next iteration
                if (i_fill_is_dispatch) begin
                    o_nv_right_rd_idx = right_base_nv_idx + disp_src_nv_cnt[6:0];
                    o_wt_valid        = 1'b0;
                    o_col_sel         = disp_col_sel_reg;
                    o_wt_col_valid    = 1'b1;
                    o_wt_nv_idx       = disp_wt_nv_idx_reg;
                end else begin
                    o_nv_right_rd_idx = right_base_nv_idx + fill_nv_idx;
                    o_wt_valid        = 1'b0;
                    o_col_sel         = fill_col_cnt;
                    o_wt_col_valid    = col_valid;
                    o_wt_nv_idx       = fill_nv_cnt[6:0];
                end
            end

            FILL_DONE: begin
                o_nv_right_rd_idx = 7'd0;
                o_wt_valid        = 1'b0;
                o_col_sel         = 4'd0;
                o_wt_col_valid    = 1'b0;
                o_wt_nv_idx       = 7'd0;
            end

            default: begin
                o_nv_right_rd_idx = 7'd0;
                o_wt_valid        = 1'b0;
                o_col_sel         = 4'd0;
                o_wt_col_valid    = 1'b0;
                o_wt_nv_idx       = 7'd0;
            end
        endcase
    end

    // =========================================================================
    // Output Assignments
    // =========================================================================
    assign o_fill_done   = (fill_state_reg == FILL_DONE);
    assign o_wt_cycle_cnt = wt_cycle_cnt;
    assign o_wt_loading  = (fill_state_reg == FILL_LOAD);

    // =========================================================================
    // Debug Output
    // =========================================================================
    // synthesis translate_off
    always @(posedge i_clk) begin
        if (fill_state_reg == FILL_LOAD && wt_cycle_cnt == 2'd0) begin
            $display("[COMP_BRAM_FILL_CTRL] @%0t LOAD_START: col=%0d, nv_idx=%0d, rd_idx=%0d (base=%0d+%0d), nv_right_rd_idx=%0d",
                     $time, o_col_sel, o_wt_nv_idx, fill_nv_idx, right_base_nv_idx, fill_nv_idx, o_nv_right_rd_idx);
        end
    end
    // synthesis translate_on

endmodule

`default_nettype wire

