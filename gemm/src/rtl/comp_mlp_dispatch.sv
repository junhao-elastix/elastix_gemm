// ------------------------------------------------------------------
// MLP Dispatch Controller
//
// Purpose: Handles DISPATCH RIGHT operations (row_bram → MLP BRAM weight_bram)
// Architecture:
//   - Manages weight loading from row_bram to MLP BRAM columns
//   - Supports round-robin distribution with col_start parameter
//   - Tracks accumulated write address pointers per column
//   - Resets write pointers on TILE command
//
// Weight Loading Mechanism:
//   - Each 256-bit line from row_bram → split into 4 pieces (64-bit each)
//   - Each 64-bit piece → one of 4 parallel MLP BRAM stacks
//   - 1 Native Vector (NV) = 4 lines in row_bram = 128 GFP8 numbers
//   - Maps 1 line to 1 line in weight_bram per logical column
//   - Takes 4 cycles to fill 1 NV in one column across all 4 stacks
//   - Fills V NVs (V*4 lines total) to a logical column before moving to next
//
// Address Management:
//   - tile_addr: Starting write address in MLP BRAM for this DISPATCH
//   - col_start: Starting logical column for round-robin distribution
//   - Per-column write pointers accumulate across multiple DISPATCH commands
//   - Write pointers reset to 0 when TILE command is issued
//   - When wrapping at column 16, write address continues accumulating
//
// Distribution Example:
//   - C=4, V=4: Columns 0-3 get V0-3 each (16 lines per column)
//   - Next dispatch C=18, V=4: Starts from logical column 4 (col_start=4)
//   - When wrapping at column 16, write address pointer continues at line 16
//
// Author: Refactored for proper address accumulation
// Date: Dec 18 2025
// ------------------------------------------------------------------

`timescale 1ps / 1ps
`default_nettype none

module comp_mlp_dispatch #(
    parameter int NUM_COLUMNS = 16  // Number of MLP columns (fixed at 16)
) (
    input  logic                     i_clk,
    input  logic                     i_reset_n,

    // =========================================================================
    // Command Interface
    // =========================================================================
    input  logic                     i_disp_start,           // Pulse to start DISPATCH
    output logic                     o_disp_done,            // DISPATCH operation complete
    
    input  logic                     i_tile_start,           // TILE command pulse (resets write pointers)

    // =========================================================================
    // DISPATCH Command Parameters
    // =========================================================================
    input  logic [7:0]               i_disp_man_nv_cnt,      // Total NVs to dispatch
    input  logic [7:0]               i_disp_ugd_vec_size,    // V: NVs per UGD vector (per column)
    input  logic [9:0]               i_disp_tile_addr,        // Starting write address in MLP BRAM
    input  logic [4:0]               i_disp_col_start,        // Starting logical column for distribution
    input  logic                     i_disp_broadcast,       // 1=broadcast, 0=distribute (distribute only for right)

    // =========================================================================
    // row_bram Read Interface
    // =========================================================================
    output logic [6:0]               o_nv_right_rd_idx,      // row_bram read address (NV index)
    input  logic [255:0]             i_nv_right_man [0:3],  // 128 mantissas as 4 groups of 256 bits
    input  logic [31:0]               i_nv_right_exp,         // 4 exponents (8-bit each)

    // =========================================================================
    // MLP BRAM Write Interface (to comp_mlp_bram_col_wrapper)
    // =========================================================================
    output logic                     o_wt_valid,             // Weight data valid (latch trigger)
    input  logic                     i_wt_ready,             // Ready to accept weight data
    output logic [255:0]             o_nv_right_man [0:3],  // Weight mantissas to wrapper
    output logic [31:0]              o_nv_right_exp,          // Weight exponents to wrapper
    output logic [3:0]               o_col_sel,               // Target column (0-15)
    output logic [6:0]               o_wt_nv_idx,            // NV index within column
    output logic [1:0]               o_wt_cycle_cnt,         // Current cycle within 4-cycle load (0-3)
    output logic                     o_wt_loading,           // Currently loading (active during 4-cycle write)
    output logic [9:0]               o_wt_base_addr           // Effective write base address for this column
);

    // =========================================================================
    // State Machine Definition
    // =========================================================================
    typedef enum logic [2:0] {
        DISP_IDLE     = 3'b000,
        DISP_READ     = 3'b001,  // Read from row_bram
        DISP_LOAD     = 3'b010,  // 4-cycle weight loading into MLP BRAM
        DISP_NEXT     = 3'b011,  // Prepare for next NV
        DISP_DONE     = 3'b100
    } disp_state_t;

    disp_state_t disp_state_reg, disp_state_next;

    // =========================================================================
    // Internal Signals
    // =========================================================================
    // Dispatch counters
    logic [7:0]  disp_src_nv_cnt;      // Sequential source NV index (0..man_nv_cnt-1)
    logic [1:0]  wt_cycle_cnt;         // Weight loading cycle counter (0-3)
    
    // Distribution calculation - combinational (for next cycle)
    logic [4:0]  disp_num_enabled;      // Number of enabled columns (always 16 for MLP mode)
    logic [7:0]  disp_batch_idx;         // Batch index = src_nv / vec_len
    logic [7:0]  disp_nv_in_batch;      // NV index within batch = src_nv % vec_len
    logic [4:0]  disp_start_logical;    // col_start % num_enabled
    logic [4:0]  disp_logical_col;      // (start + batch) % num_enabled
    logic [7:0]  disp_nv_row;           // (start + batch) / num_enabled
    logic [3:0]  disp_col_sel_next;     // Physical column index (0-15)
    logic [6:0]  disp_wt_nv_idx_next;   // Destination NV index within column

    // PIPELINE STAGE: Registered distribution results (timing fix)
    // These break the critical path from division/modulo to BRAM
    logic [7:0]  disp_batch_idx_p1;      // Pipelined batch index
    logic [7:0]  disp_nv_in_batch_p1;   // Pipelined NV in batch
    logic [4:0]  disp_logical_col_p1;   // Pipelined logical column
    logic [7:0]  disp_nv_row_p1;        // Pipelined nv_row
    logic [3:0]  disp_col_sel_p1;       // Pipelined column select
    logic [6:0]  disp_wt_nv_idx_p1;     // Pipelined NV index
    logic [15:0] nv_row_offset_p1;      // Pipelined: nv_row * V * 8 (pre-computed)
    
    // Latched values during 4-cycle load
    logic [3:0]  col_sel_reg;
    logic [6:0]  wt_nv_idx_reg;
    logic [7:0]  disp_ugd_vec_size_reg;  // Latched V
    logic [9:0]  disp_tile_addr_reg;     // Latched tile_addr

    // TIMING FIX: Pre-computed stride values (V * 8) - breaks multiplication from critical path
    logic [12:0] v_stride_reg;           // V * 8, registered for timing
    logic [12:0] tile_plus_stride_reg;   // tile_addr + (V * 8), pre-computed

    // Per-column write address pointers (accumulate across dispatches)
    // Each column tracks its current write address base
    logic [9:0]  col_wr_ptr [0:NUM_COLUMNS-1];

    // Effective write base address for current column
    logic [9:0]  wt_base_addr_eff;

    // =========================================================================
    // Per-Column Write Pointer Management
    // =========================================================================
    // Track the current write address base for each column
    // - Reset to 0 on TILE command
    // - Accumulate across multiple DISPATCH commands
    // - Update when finishing V NVs to a column (advance by V*8 addresses)
    //
    // TIMING FIX: Use pipelined disp_nv_in_batch_p1 and pre-computed v_stride_reg
    // to break critical path from modulo/multiplication to col_wr_ptr

    logic [3:0] prev_col_sel;  // Track previous column to detect column changes

    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            for (int i = 0; i < NUM_COLUMNS; i++) begin
                col_wr_ptr[i] <= 10'd0;
            end
            prev_col_sel <= 4'd0;
            v_stride_reg <= 13'd0;
            tile_plus_stride_reg <= 13'd0;
        end else if (i_tile_start) begin
            // Reset all write pointers on TILE command
            for (int i = 0; i < NUM_COLUMNS; i++) begin
                col_wr_ptr[i] <= 10'd0;
            end
            prev_col_sel <= 4'd0;
        end else if (i_disp_start) begin
            // Reset all write pointers on new DISPATCH command
            // Each DISPATCH specifies its own tile_addr - don't carry over stale pointers
            for (int i = 0; i < NUM_COLUMNS; i++) begin
                col_wr_ptr[i] <= 10'd0;
            end
            prev_col_sel <= 4'd0;
            // Pre-compute stride values for timing (V * 8)
            v_stride_reg <= {5'b0, i_disp_ugd_vec_size} << 3;  // V * 8
            tile_plus_stride_reg <= {3'b0, i_disp_tile_addr} + ({5'b0, i_disp_ugd_vec_size} << 3);
        end else begin
            // Update write pointer when we finish writing V NVs to a column
            // This happens when we move to a new column (detected by col_sel changing)
            // TIMING FIX: Use PIPELINED disp_nv_in_batch_p1 (registered last cycle)
            if (disp_state_reg == DISP_NEXT) begin
                // Check if we just finished V NVs to the previous column
                // Use PIPELINED value - this was computed for the CURRENT NV in previous cycle
                if (disp_nv_in_batch_p1 == 8'd0 && disp_src_nv_cnt > 0) begin
                    // Previous column finished V NVs, update its pointer
                    // Use PRE-COMPUTED stride instead of multiplication
                    if (col_wr_ptr[prev_col_sel] > 10'd0) begin
                        col_wr_ptr[prev_col_sel] <= col_wr_ptr[prev_col_sel] + v_stride_reg[9:0];
                    end else begin
                        col_wr_ptr[prev_col_sel] <= tile_plus_stride_reg[9:0];
                    end
                end
                // Update prev_col_sel for next iteration
                prev_col_sel <= col_sel_reg;
            end else if (disp_state_reg == DISP_DONE) begin
                // At end of dispatch, update pointer for the last column
                // Use PRE-COMPUTED stride instead of multiplication
                if (col_wr_ptr[col_sel_reg] > 10'd0) begin
                    col_wr_ptr[col_sel_reg] <= col_wr_ptr[col_sel_reg] + v_stride_reg[9:0];
                end else begin
                    col_wr_ptr[col_sel_reg] <= tile_plus_stride_reg[9:0];
                end
            end
        end
    end

    // Calculate effective write base address for current column
    // Strategy:
    // - tile_addr is the starting address for THIS dispatch
    // - If a column already has accumulated data (col_wr_ptr[col] > 0), use that
    // - Otherwise, use tile_addr + (nv_row * V * 8) to account for column groups
    // - After writing V NVs to a column, update col_wr_ptr[col] = base + (V*8)
    // NOTE: Use col_sel_reg (current column being written) not disp_col_sel_next (next column)
    // CRITICAL: When C > 16, logical columns wrap to physical columns 0-15, but nv_row > 0
    //   indicates we're in a different column group. We must write to a different address offset.
    //   This ensures group 0 writes to address 0, group 1 writes to address (V*8), etc.
    //
    // TIMING FIX: Use pipelined values (disp_nv_row_p1, disp_col_sel_p1) in DISP_READ state
    // to break the critical path from division/modulo to BRAM.
    // ADDITIONAL FIX: nv_row_offset_p1 is pre-computed and REGISTERED in previous cycle
    // to eliminate multiplication from critical path completely.
    logic [7:0]  disp_nv_row_reg;       // Latched nv_row for address calculation
    logic [15:0] nv_row_offset_reg;     // Latched offset for DISP_LOAD

    always_ff @(posedge i_clk) begin
        if (disp_state_reg == DISP_READ) begin
            disp_nv_row_reg <= disp_nv_row_p1;        // Use pipelined value
            nv_row_offset_reg <= nv_row_offset_p1;    // Use pipelined offset (already registered)
        end
    end

    always_comb begin
        // Use accumulated pointer if it exists, otherwise use tile_addr
        // This ensures continuity across multiple dispatches
        // In DISP_READ state, use PIPELINED values (computed and registered previous cycle)
        // In DISP_LOAD state, use col_sel_reg (the column currently being written)
        logic [3:0] col_for_addr;
        logic [7:0] nv_row_for_addr;
        logic [15:0] nv_row_offset_for_addr;
        if (disp_state_reg == DISP_READ) begin
            col_for_addr = disp_col_sel_p1;           // PIPELINED - timing fix
            nv_row_for_addr = disp_nv_row_p1;         // PIPELINED - timing fix
            nv_row_offset_for_addr = nv_row_offset_p1; // PIPELINED offset (registered)
        end else begin
            col_for_addr = col_sel_reg;
            nv_row_for_addr = disp_nv_row_reg;        // Use latched nv_row
            nv_row_offset_for_addr = nv_row_offset_reg; // Use latched offset
        end

        // CRITICAL: When nv_row > 0, we're in a new column group (logical columns >= 16).
        // In this case, we must write to a different address offset, regardless of col_wr_ptr.
        // col_wr_ptr is only valid within the same column group (nv_row = 0).
        if (nv_row_for_addr > 8'd0) begin
            // New column group: use tile_addr + column group offset
            // TIMING FIX: Use PIPELINED offset - no multiplication on critical path
            wt_base_addr_eff = disp_tile_addr_reg + nv_row_offset_for_addr[9:0];
        end else if (col_wr_ptr[col_for_addr] > 10'd0) begin
            // Same column group (nv_row = 0): use accumulated pointer for multi-dispatch continuity
            wt_base_addr_eff = col_wr_ptr[col_for_addr];
        end else begin
            // First dispatch to this column in group 0: use tile_addr
            wt_base_addr_eff = disp_tile_addr_reg;
        end
    end

    // =========================================================================
    // Distribution Calculation
    // =========================================================================
    // Need wider signals for nv_row calculation when col_start can be > 16
    logic [7:0] col_start_plus_batch;  // Full column index (col_start + batch)

    // For pipeline: calculate values for NEXT NV (src_nv_cnt + 1)
    logic [7:0]  disp_src_nv_next;      // Next NV counter value
    logic [7:0]  disp_batch_idx_next;   // Batch index for next NV
    logic [7:0]  disp_nv_in_batch_next; // NV in batch for next NV
    logic [4:0]  disp_logical_col_next; // Logical column for next NV
    logic [7:0]  disp_nv_row_next;      // Row for next NV
    logic [7:0]  col_start_plus_batch_next;

    // TIMING FIX: Incremental update signals (avoid division on critical path)
    // These are computed from PIPELINED values (_p1) using comparisons instead of division
    logic        batch_idx_will_incr;    // True when next NV starts new batch (nv_in_batch wraps)
    logic        logical_col_will_wrap;  // True when next NV wraps to column 0 (nv_row increments)
    logic [7:0]  v_minus_1;              // V - 1, pre-computed for comparison

    always_comb begin
        // All columns enabled in MLP mode
        disp_num_enabled = NUM_COLUMNS[4:0];

        // TIMING FIX: Pre-compute V-1 for comparison (avoids subtraction on critical path)
        v_minus_1 = disp_ugd_vec_size_reg - 8'd1;

        // TIMING FIX: Incremental update signals using PIPELINED values (_p1)
        // These use comparisons instead of division, breaking the critical path
        // batch_idx increments when we've processed V NVs to current column (nv_in_batch wraps)
        batch_idx_will_incr = (disp_ugd_vec_size_reg != 8'd0) && (disp_nv_in_batch_p1 == v_minus_1);
        // logical_col wraps when batch_idx increments AND we're at column 15
        logical_col_will_wrap = batch_idx_will_incr && (disp_logical_col_p1 == 5'd15);

        // Calculate batch and NV within batch for CURRENT NV
        disp_batch_idx   = (disp_ugd_vec_size_reg == 8'd0) ? 8'd0 : (disp_src_nv_cnt / disp_ugd_vec_size_reg);
        disp_nv_in_batch = (disp_ugd_vec_size_reg == 8'd0) ? 8'd0 : (disp_src_nv_cnt % disp_ugd_vec_size_reg);

        // Calculate logical column (physical column 0-15)
        // disp_start_logical: Starting physical column within group 0-15
        disp_start_logical = i_disp_col_start % disp_num_enabled;
        disp_logical_col   = (disp_start_logical + disp_batch_idx) % disp_num_enabled;

        // Calculate nv_row (column group) using FULL col_start value, not modulo
        // This preserves information about which column group we started in
        // e.g., col_start=30 + batch_idx=0 = 30, nv_row = 30/16 = 1 (correct!)
        //       col_start=30 + batch_idx=2 = 32, nv_row = 32/16 = 2 (correct!)
        col_start_plus_batch = {3'b0, i_disp_col_start} + disp_batch_idx;
        disp_nv_row          = col_start_plus_batch / disp_num_enabled;

        // Physical column index (0-15)
        disp_col_sel_next = disp_logical_col[3:0];

        // Destination NV index within column
        // CRITICAL: For column groups (nv_row > 0), reset nv_idx to 0 for the new group.
        // This ensures group 0 uses nv_idx 0-3, group 1 uses nv_idx 0-3 (not 4-7).
        // The base address offset (nv_row * V * 8) already accounts for the group separation.
        disp_wt_nv_idx_next = disp_nv_in_batch;  // Reset per column group, base address handles group offset

        // =========================================================================
        // PIPELINE LOOKAHEAD: Calculate values for NEXT NV (src_nv_cnt + 1)
        // These are registered and used in the next DISP_READ cycle
        // =========================================================================
        disp_src_nv_next = disp_src_nv_cnt + 8'd1;
        disp_batch_idx_next   = (disp_ugd_vec_size_reg == 8'd0) ? 8'd0 : (disp_src_nv_next / disp_ugd_vec_size_reg);
        disp_nv_in_batch_next = (disp_ugd_vec_size_reg == 8'd0) ? 8'd0 : (disp_src_nv_next % disp_ugd_vec_size_reg);
        disp_logical_col_next = (disp_start_logical + disp_batch_idx_next) % disp_num_enabled;
        col_start_plus_batch_next = {3'b0, i_disp_col_start} + disp_batch_idx_next;
        disp_nv_row_next = col_start_plus_batch_next / disp_num_enabled;
    end

    // =========================================================================
    // State Machine: State Transition Logic
    // =========================================================================
    always_comb begin
        disp_state_next = disp_state_reg;

        case (disp_state_reg)
            DISP_IDLE: begin
                if (i_disp_start) begin
                    disp_state_next = DISP_READ;
                end
            end

            DISP_READ: begin
                // Wait one cycle for row_bram read, then start loading if ready
                if (i_wt_ready) begin
                    disp_state_next = DISP_LOAD;
                end
            end

            DISP_LOAD: begin
                // Stay in DISP_LOAD for 4 cycles (one NV)
                if (wt_cycle_cnt == 2'd3) begin
                    disp_state_next = DISP_NEXT;
                end
            end

            DISP_NEXT: begin
                if (disp_src_nv_cnt == (i_disp_man_nv_cnt - 1)) begin
                    disp_state_next = DISP_DONE;
                end else begin
                    disp_state_next = DISP_READ;
                end
            end

            DISP_DONE: begin
                disp_state_next = DISP_IDLE;
            end

            default: begin
                disp_state_next = DISP_IDLE;
            end
        endcase
    end

    // =========================================================================
    // State Machine: Sequential State Update
    // =========================================================================
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            disp_state_reg <= DISP_IDLE;
            disp_src_nv_cnt <= 8'd0;
            wt_cycle_cnt <= 2'd0;
            col_sel_reg <= 4'd0;
            wt_nv_idx_reg <= 7'd0;
            disp_ugd_vec_size_reg <= 8'd0;
            disp_tile_addr_reg <= 10'd0;
            // Pipeline registers reset
            disp_batch_idx_p1 <= 8'd0;
            disp_nv_in_batch_p1 <= 8'd0;
            disp_logical_col_p1 <= 5'd0;
            disp_nv_row_p1 <= 8'd0;
            disp_col_sel_p1 <= 4'd0;
            disp_wt_nv_idx_p1 <= 7'd0;
            nv_row_offset_p1 <= 16'd0;
        end else begin
            disp_state_reg <= disp_state_next;

            case (disp_state_reg)
                DISP_IDLE: begin
                    disp_src_nv_cnt <= 8'd0;
                    wt_cycle_cnt <= 2'd0;
                    if (i_disp_start) begin
                        // Latch command parameters
                        disp_ugd_vec_size_reg <= i_disp_ugd_vec_size;
                        disp_tile_addr_reg <= i_disp_tile_addr;
                        // =================================================================
                        // TIMING FIX: Hard-code initial values for src_nv_cnt=0
                        // Since src_nv_cnt=0 in DISP_IDLE:
                        //   batch_idx = 0/V = 0
                        //   nv_in_batch = 0%V = 0
                        //   logical_col = col_start % 16 = col_start[3:0] (NUM_COLUMNS=16)
                        //   nv_row = col_start / 16 = col_start >> 4
                        // This COMPLETELY avoids division on initialization path!
                        // =================================================================
                        disp_batch_idx_p1 <= 8'd0;                      // 0/V = 0
                        disp_nv_in_batch_p1 <= 8'd0;                    // 0%V = 0
                        disp_logical_col_p1 <= {1'b0, i_disp_col_start[3:0]};  // col_start % 16
                        disp_nv_row_p1 <= {4'b0, i_disp_col_start[4:4]};       // col_start / 16 (for 5-bit col_start)
                        disp_col_sel_p1 <= i_disp_col_start[3:0];       // Same as logical_col
                        disp_wt_nv_idx_p1 <= 7'd0;                      // Same as nv_in_batch
                        // nv_row_offset = nv_row * V * 8
                        // Since nv_row = col_start >> 4, use bit manipulation:
                        // nv_row_offset = (col_start >> 4) * V * 8 = (col_start[4] ? 1 : 0) * V * 8
                        // For 5-bit col_start, col_start[4] indicates if we're in column group 1
                        nv_row_offset_p1 <= i_disp_col_start[4] ? ({5'b0, i_disp_ugd_vec_size} << 3) : 16'd0;
                    end
                end

                DISP_READ: begin
                    wt_cycle_cnt <= 2'd0;  // Reset cycle counter before loading
                    // Latch distribution mapping at start of each NV
                    // Use pipelined values instead of combinational
                    if (i_wt_ready) begin
                        col_sel_reg <= disp_col_sel_p1;
                        wt_nv_idx_reg <= disp_wt_nv_idx_p1;
                    end
                end

                DISP_LOAD: begin
                    wt_cycle_cnt <= wt_cycle_cnt + 2'd1;  // Increment during 4-cycle load
                end

                DISP_NEXT: begin
                    wt_cycle_cnt <= 2'd0;
                    if (disp_src_nv_cnt != (i_disp_man_nv_cnt - 1)) begin
                        disp_src_nv_cnt <= disp_src_nv_cnt + 8'd1;
                        // =================================================================
                        // TIMING FIX: Use INCREMENTAL logic instead of division-based lookahead
                        // The incremental signals (batch_idx_will_incr, logical_col_will_wrap)
                        // are computed from pipelined values using comparisons, not divisions.
                        // This breaks the critical path through the division operations.
                        // =================================================================

                        // nv_in_batch: wraps to 0 when batch completes, else increment
                        disp_nv_in_batch_p1 <= batch_idx_will_incr ? 8'd0 : (disp_nv_in_batch_p1 + 8'd1);

                        // batch_idx: increment when we've processed V NVs (batch completes)
                        disp_batch_idx_p1 <= batch_idx_will_incr ? (disp_batch_idx_p1 + 8'd1) : disp_batch_idx_p1;

                        // logical_col: wrap to 0 when at col 15 and batch completes, else incr on batch complete
                        if (logical_col_will_wrap) begin
                            disp_logical_col_p1 <= 5'd0;
                            disp_col_sel_p1 <= 4'd0;
                        end else if (batch_idx_will_incr) begin
                            disp_logical_col_p1 <= disp_logical_col_p1 + 5'd1;
                            disp_col_sel_p1 <= disp_col_sel_p1 + 4'd1;
                        end
                        // else: stay same

                        // nv_row: increment when logical_col wraps (new column group)
                        if (logical_col_will_wrap) begin
                            disp_nv_row_p1 <= disp_nv_row_p1 + 8'd1;
                            // Also update nv_row_offset incrementally
                            nv_row_offset_p1 <= nv_row_offset_p1 + v_stride_reg;
                        end
                        // else: stay same

                        // wt_nv_idx: same as nv_in_batch (the NV index within the column)
                        disp_wt_nv_idx_p1 <= batch_idx_will_incr ? 7'd0 : (disp_wt_nv_idx_p1 + 7'd1);
                    end
                end

                default: begin
                    // No updates in other states
                end
            endcase
        end
    end

    // =========================================================================
    // Control Signal Generation
    // =========================================================================
    always_comb begin
        // Default assignments
        o_nv_right_rd_idx = 7'd0;
        o_wt_valid        = 1'b0;
        o_col_sel         = 4'd0;
        o_wt_nv_idx       = 7'd0;
        o_wt_base_addr    = 10'd0;

        case (disp_state_reg)
            DISP_IDLE: begin
                o_nv_right_rd_idx = 7'd0;
                o_wt_valid        = 1'b0;
                o_col_sel         = 4'd0;
                o_wt_nv_idx       = 7'd0;
                o_wt_base_addr    = 10'd0;
            end

            DISP_READ: begin
                // Read from row_bram (always from offset 0 for DISPATCH)
                o_nv_right_rd_idx = disp_src_nv_cnt[6:0];
                o_wt_valid        = i_wt_ready;  // Valid when ready to start loading
                o_col_sel         = disp_col_sel_p1;     // PIPELINED - timing fix
                o_wt_nv_idx       = disp_wt_nv_idx_p1;   // PIPELINED - timing fix
                o_wt_base_addr    = wt_base_addr_eff;
            end

            DISP_LOAD: begin
                // Maintain signals during 4-cycle load
                o_nv_right_rd_idx = disp_src_nv_cnt[6:0];
                o_wt_valid        = 1'b0;  // Valid only for one cycle to trigger latch
                o_col_sel         = col_sel_reg;
                o_wt_nv_idx       = wt_nv_idx_reg;
                o_wt_base_addr    = wt_base_addr_eff;
            end

            DISP_NEXT: begin
                // Prepare for next iteration
                o_nv_right_rd_idx = disp_src_nv_cnt[6:0];
                o_wt_valid        = 1'b0;
                o_col_sel         = col_sel_reg;
                o_wt_nv_idx       = wt_nv_idx_reg;
                o_wt_base_addr    = wt_base_addr_eff;
            end

            DISP_DONE: begin
                o_nv_right_rd_idx = 7'd0;
                o_wt_valid        = 1'b0;
                o_col_sel         = 4'd0;
                o_wt_nv_idx       = 7'd0;
                o_wt_base_addr    = 10'd0;
            end

            default: begin
                o_nv_right_rd_idx = 7'd0;
                o_wt_valid        = 1'b0;
                o_col_sel         = 4'd0;
                o_wt_nv_idx       = 7'd0;
                o_wt_base_addr    = 10'd0;
            end
        endcase
    end

    // =========================================================================
    // Data Path: Pass through row_bram data to wrapper
    // =========================================================================
    assign o_nv_right_man[0] = i_nv_right_man[0];
    assign o_nv_right_man[1] = i_nv_right_man[1];
    assign o_nv_right_man[2] = i_nv_right_man[2];
    assign o_nv_right_man[3] = i_nv_right_man[3];
    assign o_nv_right_exp     = i_nv_right_exp;

    // =========================================================================
    // Output Assignments (non-pipelined)
    // =========================================================================
    assign o_disp_done   = (disp_state_reg == DISP_DONE);
    assign o_wt_cycle_cnt = wt_cycle_cnt;
    assign o_wt_loading  = (disp_state_reg == DISP_LOAD);

    // =========================================================================
    // Debug Output
    // =========================================================================
    `ifdef SIMULATION
    always @(posedge i_clk) begin
        if (disp_state_reg == DISP_LOAD && wt_cycle_cnt == 2'd0) begin
            $display("[COMP_MLP_DISPATCH] @%0t LOAD_START: col=%0d, nv_idx=%0d, src_nv=%0d, base_addr=%0d, tile_addr=%0d",
                     $time, o_col_sel, o_wt_nv_idx, disp_src_nv_cnt, o_wt_base_addr, disp_tile_addr_reg);
        end
        if (disp_state_reg != disp_state_next) begin
            $display("[COMP_MLP_DISPATCH] @%0t STATE: %s -> %s",
                     $time, disp_state_reg.name(), disp_state_next.name());
        end
    end
    `endif

endmodule

`default_nettype wire

