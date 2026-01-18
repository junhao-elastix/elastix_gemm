// ------------------------------------------------------------------
// Compute Engine MLP (GEMM-Compatible Interface)
//
// Top-level wrapper integrating:
//   - row_bram: L1 memory for activations (left) and weights (right)
//   - mlp_bram_col_wrapper: MLP compute array with 16 columns (4 stacks each)
//   - Direct FP16 output (via integer-domain adder pipeline)
//
// Command Path:
//   - FETCH: Handled by dispatcher_control (GDDR6 → row_bram)
//   - DISPATCH: Handled here (row_bram → MLP BRAM weight_bram)
//   - TILE: Handled here (MATMUL computation: row_bram → MLP → results)
//
// DISPATCH RIGHT (Right-Distribute Mode):
//   Purpose: Load weights from row_bram into MLP BRAM weight_bram
//   - Left-broadcast is deprecated (left activations stay in row_bram, stream to MLPs)
//   - Right-distribute loads weights into dedicated weight_bram per column
//
//   Weight Loading Mechanism:
//   - Each 256-bit line from row_bram → split into 4 pieces (64-bit each)
//   - Each 64-bit piece → one of 4 parallel MLP BRAM stacks
//   - 1 Native Vector (NV) = 4 lines in row_bram = 128 GFP8 numbers
//   - Maps 1 line to 1 line in weight_bram per logical column
//   - Takes 4 cycles to fill 1 NV in one column across all 4 stacks
//   - Fills V NVs (V*4 lines total) to a logical column before moving to next
//
//   Distribution Example:
//   - C=4, V=4: Columns 0-3 get V0-3 each (16 lines per column)
//   - Next dispatch C=18, V=4: Starts from logical column 4 (col_start=4)
//   - When wrapping at column 16, write address pointer continues at line 16
//
//   Address Management:
//   - tile_addr: Starting write address in MLP BRAM for this DISPATCH
//   - col_start: Starting logical column for round-robin distribution
//   - Internal wr_addr_ptr: Accumulates across multiple DISPATCH commands
//   - wr_addr_ptr is reset to 0 when TILE command is issued
//   - Otherwise, wr_addr_ptr keeps accumulating for multi-dispatch continuity
//
// TILE (MATMUL Computation) - NEW SCHEDULING:
//   Result order: B (batch) is outer loop, C (columns) is inner loop
//   This produces results consecutive in C first, then B:
//     [b0c0..c15, b0c16..c31, ..., b1c0..c15, b1c16..c31, ...]
//
//   For each batch b (0 to B-1):
//     For each column group g (0 to num_groups-1):
//       1. ACTIVATION: Read V NVs from row_bram for batch b
//          (same activation data replayed for all groups within batch)
//       2. WEIGHT READ: Read V NVs from MLP BRAM weight_bram
//          - Address offset = g * V * 8 (10-bit units)
//       3. COMPUTE: Dot product of activation[b] × weight[g]
//       4. OUTPUT: 16 FP16 results for (batch b, columns g*16..g*16+15)
//
// BCV Dimensions:
//   - B (i_tile_left_ugd_len): Number of activation batches
//   - C (i_tile_right_ugd_len): Number of columns (may exceed 16)
//   - V (i_tile_vec_len): Number of NVs to accumulate per output
//
// Author: Generated for MLP project
// Date: 2024
// Updated: Dec 2025 - Refactored scheduling: B outer, C inner for consecutive C results
// ------------------------------------------------------------------

`timescale 1ps / 1ps
`default_nettype none

module compute_engine_mlp #(
    parameter int TILE_ID = 0,                // Tile ID for debugging
    parameter int MAN_WIDTH = 256,            // Mantissa line width (256 bits = 32 × 8-bit)
    parameter int EXP_WIDTH = 8,              // Exponent width
    parameter int BRAM_DEPTH = 512,           // row_bram depth
    parameter int ADDR_WIDTH = $clog2(BRAM_DEPTH),
    parameter int NUM_MLPS = 8,                // Number of MLP primitives (2 columns each)
    parameter int NUM_COLUMNS = 2*NUM_MLPS           // Number of MLP columns (fixed)
) (
    input  logic                     i_clk,
    input  logic                     i_reset_n,

    // =========================================================================
    // Master Control Interface (DISPATCH command)
    // =========================================================================
    input  logic                     i_disp_start,           // Pulse from DISPATCH (trigger ST_FILL)
    input  logic [7:0]               i_disp_man_nv_cnt,      // Total Number of NVs to DISPATCH 
    input  logic [7:0]               i_disp_ugd_vec_size,    // Number of NVs per UGD vector
    input  logic [15:0]              i_disp_tile_addr,       // DISPATCH: Right matrix write base address
    input  logic                     i_disp_man_4b,          // 4-bit mantissa DISPATCH (unused)
    input  logic [23:0]              i_disp_col_en,          // Column enable mask (for distribute/broadcast semantics)
    input  logic [4:0]               i_disp_col_start,       // Distribution start column (for multi-dispatch continuity)
    input  logic                     i_disp_right,           // DISPATCH side: 0=LEFT (ignore), 1=RIGHT (process)
    input  logic                     i_disp_broadcast,      // 1=broadcast, 0=distribute
    output logic                     o_disp_done,            // DISPATCH operation complete

    // =========================================================================
    // Master Control Interface (TILE command)
    // =========================================================================
    input  logic                     i_tile_en,              // Static enable (configuration)
    input  logic                     i_tile_start,           // Dynamic pulse (start computing!)
    input  logic [15:0]              i_tile_left_addr,       // Left matrix start address (row_bram line address)
    input  logic [15:0]              i_tile_right_addr,      // TILE: Right matrix read base address
    input  logic [7:0]               i_tile_left_ugd_len,    // B: Number of activation batches
    input  logic [7:0]               i_tile_right_ugd_len,   // C: Number of columns
    input  logic [7:0]               i_tile_vec_len,         // V: Number of NVs to accumulate
    input  logic                     i_tile_left_man_4b,     // 4-bit mantissa left (unused)
    input  logic                     i_tile_right_man_4b,    // 4-bit mantissa right (unused)
    input  logic                     i_tile_main_loop_over_left, // Loop order (unused)
    input  logic [23:0]              i_mc_tile_en,           // Per-tile enable mask (unused)
    output logic                     o_tile_done,

    // =========================================================================
    // row_bram Write Interface (4 parallel ports)
    // External controller fills row_bram before starting operations
    // =========================================================================
    // Left mantissa write port (activations)
    input  logic [ADDR_WIDTH-1:0]    i_man_left_wr_addr,
    input  logic                     i_man_left_wr_en,
    input  logic [MAN_WIDTH-1:0]     i_man_left_wr_data,

    // Right mantissa write port (weights)
    input  logic [ADDR_WIDTH-1:0]    i_man_right_wr_addr,
    input  logic                     i_man_right_wr_en,
    input  logic [MAN_WIDTH-1:0]     i_man_right_wr_data,

    // Left exponent write port (activations)
    input  logic [ADDR_WIDTH-1:0]    i_exp_left_wr_addr,
    input  logic                     i_exp_left_wr_en,
    input  logic [EXP_WIDTH-1:0]     i_exp_left_wr_data,

    // Right exponent write port (weights)
    input  logic [ADDR_WIDTH-1:0]    i_exp_right_wr_addr,
    input  logic                     i_exp_right_wr_en,
    input  logic [EXP_WIDTH-1:0]     i_exp_right_wr_data,

    // =========================================================================
    // Result Interface (downstream) - 16 × FP16 per batch
    // =========================================================================
    output logic [255:0]             o_result_data,          // 16 × FP16 results
    output logic                     o_result_valid,
    input  logic                     i_result_full,          // Backpressure (unused for now)
    input  logic                     i_result_afull,         // Almost full (unused for now)

    // =========================================================================
    // Debug Interface
    // =========================================================================
    output logic [3:0]               o_ce_state,
    output logic [15:0]              o_result_count,
    
    // =========================================================================
    // Probe Interface (debug pipeline stages)
    // =========================================================================
    output logic [15:0]              o_probe_rowbram_data,   // First 16 bits written to row_bram
    output logic                     o_probe_rowbram_valid,  // Valid when row_bram write occurs
    output logic [23:0]              o_probe_fp24_data,      // First FP24 result from compute
    output logic                     o_probe_fp24_valid,     // Valid when FP24 result ready
    output logic [15:0]              o_probe_fp16_data,      // First FP16 result (converted)
    output logic                     o_probe_fp16_valid      // Valid when FP16 result ready
);

    // =========================================================================
    // Internal Signals
    // =========================================================================

    // row_bram NV read outputs
    logic [31:0]          nv_left_exp_raw;
    logic [MAN_WIDTH-1:0] nv_left_man [0:3];
    logic [31:0]          nv_right_exp_raw;
    logic [MAN_WIDTH-1:0] nv_right_man [0:3];

    // Exponents for MLP (converted from E5 to E8 format)
    logic [31:0]          nv_left_exp;
    logic [31:0]          nv_right_exp;

    // Column validity during weight fill (for supporting C not divisible by 16)
    logic                 wt_col_valid;

    // Effective weight payload presented to the wrapper (zero-filled when wt_col_valid=0)
    logic [MAN_WIDTH-1:0] nv_right_man_eff [0:3];
    logic [31:0]          nv_right_exp_eff;

    // Exponent conversion: GFP8E5 (bias=15) from external memory → GFP8E8 (bias=133) for MLP
    // Formula: exp_E8 = exp_E5 + (133 - 15) = exp_E5 + 118
    // This is always needed since external memory stores GFP8E5 format
    always_comb begin
        for (int i = 0; i < 4; i++) begin
            nv_left_exp[i*8 +: 8]  = nv_left_exp_raw[i*8 +: 8] + 8'd118;
            nv_right_exp[i*8 +: 8] = nv_right_exp_raw[i*8 +: 8] + 8'd118;
        end
    end

    // Note: nv_right_man_eff and nv_right_exp_eff are now assigned from comp_mlp_dispatch
    // The dispatch module handles the data path from row_bram to wrapper

    // row_bram NV read indices
    logic [6:0] nv_left_rd_idx;
    logic [6:0] nv_right_rd_idx;

    // mlp_bram_col_ctrl interface signals
    logic        wt_valid;
    logic        wt_ready;
    logic [3:0]  col_sel;
    logic [6:0]  wt_nv_idx;
    logic [1:0]  wt_cycle_cnt;
    logic        wt_loading;

    // BRAM fill controller interface
    logic        fill_done;

    logic        act_valid;
    logic        act_ready;
    logic        new_dot;
    logic        last_nv;

    // Activation payload to wrapper:
    // We need a true 2-slot (cur/next) buffer so the wrapper can latch the *next* NV payload
    // at NV boundaries while it continues streaming without per-NV drains.
    logic [255:0] act_cur_man [0:3];
    logic [31:0]  act_cur_exp;
    logic         act_cur_valid;
    logic         act_cur_new_dot;
    logic         act_cur_last_nv;

    logic [255:0] act_next_man [0:3];
    logic [31:0]  act_next_exp;
    logic         act_next_valid;
    logic         act_next_new_dot;
    logic         act_next_last_nv;

    // Scheduler drive mux: during NV-boundary ready pulses, present NEXT so wrapper can latch it.
    logic drive_next_payload;
    logic first_nv_sent;
    logic refill_next_pending;

    // Muxed activation payload actually presented to the wrapper
    logic [255:0] act_payload_man [0:3];
    logic [31:0]  act_payload_exp;

    // Compute scheduler interface (now handled locally in compute_engine_mlp)
    logic        compute_done;

    logic [71:0] mlp_dout [NUM_MLPS-1:0];
    logic        dout_valid;

    // FP16 results (directly from MLP outputs - no conversion needed!)
    // mlp_bram_col_ctrl now outputs FP16 directly via integer-domain adder
    logic [15:0] fp16_results [NUM_COLUMNS-1:0];
    logic        fp16_valid;

    // =========================================================================
    // Column Group Support (for C > 16)
    // =========================================================================
    // Number of column groups = ceil(C / 16)
    // For C=16: 1 group, C=32: 2 groups, C=64: 4 groups, C=128: 8 groups
    logic [3:0] num_col_groups;      // Max 8 groups (C=128)
    
    // Active parameters (from TILE or DISPATCH command)
    logic [7:0]  active_vec_len;        // V: from TILE or DISPATCH
    logic [7:0]  active_right_ugd_len;  // C: from TILE or DISPATCH
    logic [7:0]  active_left_ugd_len;   // B: from TILE
    logic [15:0] active_left_addr;      // Left base address for row_bram reads: from TILE
    logic [15:0] active_right_addr;     // Right base address for row_bram reads: from DISPATCH (fill) or TILE (compute)

    // DISPATCH distribution parameters (latched on i_disp_start)
    logic [23:0] active_disp_col_en;
    logic [4:0]  active_disp_col_start;
    logic        active_disp_broadcast;
    logic [7:0]  active_disp_man_nv_cnt;
    logic [9:0]  active_disp_wt_base_addr;  // Latched MLP BRAM write base for DISPATCH (avoid MC overwriting during WAIT_DISP)

    // Calculate number of column groups = ceil(C / 16)
    always_comb begin
        num_col_groups = (active_right_ugd_len + 8'd15) >> 4;
        if (num_col_groups == 0) begin
            num_col_groups = 4'd1;  // Minimum 1 group
        end
    end

    // =========================================================================
    // Scheduler-driven MLP BRAM read base address
    // =========================================================================
    // The scheduler now controls sched_group_cnt (inner loop within batch).
    // rd_base_addr_eff = base + group * V * 8
    logic [3:0]  sched_group_cnt;    // Current column group (inner loop)
    logic [9:0]  rd_base_addr_eff;
    
    always_comb begin
        rd_base_addr_eff = active_right_addr[9:0] + (sched_group_cnt * active_vec_len * 10'd8);
    end
    
    `ifdef SIMULATION
    logic [9:0] rd_base_addr_eff_prev;
    logic [7:0] sched_batch_cnt_prev;
    logic [3:0] sched_group_cnt_prev;
    always_ff @(posedge i_clk) begin
        if (rd_base_addr_eff != rd_base_addr_eff_prev || 
            sched_batch_cnt != sched_batch_cnt_prev ||
            sched_group_cnt != sched_group_cnt_prev) begin
            $display("[CE_MLP_SCHED] @%0t BATCH=%0d GROUP=%0d rd_base_addr_eff=%0d",
                     $time, sched_batch_cnt, sched_group_cnt, rd_base_addr_eff);
        end
        rd_base_addr_eff_prev <= rd_base_addr_eff;
        sched_batch_cnt_prev <= sched_batch_cnt;
        sched_group_cnt_prev <= sched_group_cnt;
    end
    `endif

    // =========================================================================
    // Top-Level State Machine
    // =========================================================================
    // NOTE (MLP mode contract):
    // - DISPATCH RIGHT loads weights into MLP BRAM (row_bram → MLP BRAM).
    // - TILE (MATMUL) should be compute-only: stream activations from row_bram and read weights from MLP BRAM.
    typedef enum logic [3:0] {
        ST_IDLE      = 4'd0,
        ST_DISP_FILL = 4'd1,   // DISPATCH RIGHT fill phase only
        ST_COMPUTE   = 4'd2,   // Compute phase (TILE)
        ST_DONE      = 4'd3
    } top_state_t;

    top_state_t top_state_reg;

    // Fill control (DISPATCH RIGHT only)
    logic fill_start;
    logic fill_dispatch_only;  // 1 when current operation is DISPATCH RIGHT fill-only

    // Compute control
    logic compute_start;

    // =========================================================================
    // Result Counter
    // =========================================================================
    logic [15:0] result_count;

    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            result_count <= 16'd0;
        end else if (i_tile_start && top_state_reg == ST_IDLE) begin
            result_count <= 16'd0;
        end else if (o_result_valid) begin
            result_count <= result_count + 1;
        end
    end

    assign o_result_count = result_count;
    assign o_ce_state = top_state_reg;

    // =========================================================================
    // Top-Level State Machine Logic
    // =========================================================================
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            top_state_reg <= ST_IDLE;
            fill_start <= 1'b0;
            compute_start <= 1'b0;
            fill_dispatch_only <= 1'b0;
            active_vec_len <= 8'd0;
            active_right_ugd_len <= 8'd0;
            active_left_ugd_len <= 8'd0;
            active_left_addr <= 16'd0;
            active_right_addr <= 16'd0;
            active_disp_col_en <= 24'd0;
            active_disp_col_start <= 5'd0;
            active_disp_broadcast <= 1'b0;
            active_disp_man_nv_cnt <= 8'd0;
            active_disp_wt_base_addr <= 10'd0;
        end else begin
            fill_start <= 1'b0;
            compute_start <= 1'b0;

            case (top_state_reg)
                ST_IDLE: begin
                    // Two paths out of IDLE:
                    // 1. TILE (MATMUL): compute-only (weights already in MLP BRAM from DISPATCH RIGHT)
                    // 2. DISPATCH RIGHT: load weights into MLP BRAM (row_bram → MLP BRAM)
                    if (i_tile_en && i_tile_start) begin
                        top_state_reg <= ST_COMPUTE;
                        fill_dispatch_only <= 1'b0;  // Full MATMUL flow
                        compute_start <= 1'b1;
                        // Latch TILE parameters
                        active_vec_len <= i_tile_vec_len;
                        active_right_ugd_len <= i_tile_right_ugd_len;
                        active_left_ugd_len <= i_tile_left_ugd_len;
                        active_left_addr <= i_tile_left_addr;
                        active_right_addr <= i_tile_right_addr;
                        `ifdef SIMULATION
                        $display("[CE_MLP%0d] @%0t TILE START: B=%0d, C=%0d, V=%0d, left_addr=%0d, right_addr=%0d",
                                 TILE_ID, $time, i_tile_left_ugd_len, i_tile_right_ugd_len, i_tile_vec_len,
                                 i_tile_left_addr, i_tile_right_addr);
                        `endif
                    end else if (i_disp_start) begin
                        // Only process DISPATCH RIGHT (weights). DISPATCH LEFT (activations) is ignored.
                        if (i_disp_right) begin
                            top_state_reg <= ST_DISP_FILL;
                            fill_start <= 1'b1;
                            fill_dispatch_only <= 1'b1;  // DISPATCH only (no compute)
                            // Latch DISPATCH parameters
                            active_vec_len <= i_disp_ugd_vec_size;
                            active_right_ugd_len <= i_disp_man_nv_cnt / i_disp_ugd_vec_size;
                            active_left_addr <= 16'd0;
                            active_right_addr <= 16'd0;
                            active_disp_col_en <= i_disp_col_en;
                            active_disp_col_start <= i_disp_col_start;
                            active_disp_broadcast <= i_disp_broadcast;
                            active_disp_man_nv_cnt <= i_disp_man_nv_cnt;
                            active_disp_wt_base_addr <= i_disp_tile_addr[9:0];
                        end
                        // DISPATCH LEFT: Ignore (activations stay in row_bram)
                    end
                end

                ST_DISP_FILL: begin
                    if (fill_done) begin
                        top_state_reg <= ST_DONE;
                    end
                end

                ST_COMPUTE: begin
                    if (compute_done) begin
                        top_state_reg <= ST_DONE;
                        `ifdef SIMULATION
                        $display("[CE_MLP%0d] @%0t TILE COMPLETE: B=%0d batches × %0d groups = %0d result pulses",
                                 TILE_ID, $time, active_left_ugd_len, num_col_groups, 
                                 active_left_ugd_len * num_col_groups);
                        `endif
                    end
                end

                ST_DONE: begin
                    top_state_reg <= ST_IDLE;
                end
            endcase
        end
    end

    // o_tile_done: Pulse when MATMUL completes (full flow)
    assign o_tile_done = (top_state_reg == ST_DONE) && !fill_dispatch_only;
    
    // o_disp_done: Registered signal that stays high until next DISPATCH starts
    logic disp_done_reg;
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            disp_done_reg <= 1'b0;
        end else begin
            if (i_disp_start) begin
                if (!i_disp_right) begin
                    disp_done_reg <= 1'b1;  // DISPATCH LEFT: done immediately
                end else begin
                    disp_done_reg <= 1'b0;  // DISPATCH RIGHT: clear on start
                end
            end else if ((top_state_reg == ST_DONE) && fill_dispatch_only) begin
                disp_done_reg <= 1'b1;
            end
        end
    end
    assign o_disp_done = disp_done_reg;

    // =========================================================================
    // row_bram Instance
    // =========================================================================
    comp_row_bram #(
        .MAN_WIDTH(MAN_WIDTH),
        .EXP_WIDTH(EXP_WIDTH),
        .BRAM_DEPTH(BRAM_DEPTH),
        .ADDR_WIDTH(ADDR_WIDTH)
    ) u_row_bram (
        .i_clk(i_clk),
        .i_reset_n(i_reset_n),

        // Write ports
        .i_man_left_wr_addr(i_man_left_wr_addr),
        .i_man_left_wr_en(i_man_left_wr_en),
        .i_man_left_wr_data(i_man_left_wr_data),

        .i_man_right_wr_addr(i_man_right_wr_addr),
        .i_man_right_wr_en(i_man_right_wr_en),
        .i_man_right_wr_data(i_man_right_wr_data),

        .i_exp_left_wr_addr(i_exp_left_wr_addr),
        .i_exp_left_wr_en(i_exp_left_wr_en),
        .i_exp_left_wr_data(i_exp_left_wr_data),

        .i_exp_right_wr_addr(i_exp_right_wr_addr),
        .i_exp_right_wr_en(i_exp_right_wr_en),
        .i_exp_right_wr_data(i_exp_right_wr_data),

        // NV read ports (raw GFP8 exponents, converted above)
        .i_nv_left_rd_idx(nv_left_rd_idx),
        .o_nv_left_exp(nv_left_exp_raw),
        .o_nv_left_man(nv_left_man),

        .i_nv_right_rd_idx(nv_right_rd_idx),
        .o_nv_right_exp(nv_right_exp_raw),
        .o_nv_right_man(nv_right_man)
    );

    // =========================================================================
    // MLP Dispatch Controller Instance (replaces comp_bram_fill_ctrl for DISPATCH)
    // =========================================================================
    logic [255:0] disp_nv_right_man [0:3];
    logic [31:0]  disp_nv_right_exp;
    logic [9:0]   disp_wt_base_addr;
    
    comp_mlp_dispatch #(
        .NUM_COLUMNS(NUM_COLUMNS)
    ) u_mlp_dispatch (
        .i_clk(i_clk),
        .i_reset_n(i_reset_n),

        // Command interface
        .i_disp_start(fill_start),
        .o_disp_done(fill_done),
        .i_tile_start(i_tile_start),

        // DISPATCH command parameters
        .i_disp_man_nv_cnt(active_disp_man_nv_cnt),
        .i_disp_ugd_vec_size(active_vec_len),
        .i_disp_tile_addr(active_disp_wt_base_addr),
        .i_disp_col_start(active_disp_col_start),
        .i_disp_broadcast(active_disp_broadcast),

        // row_bram read interface
        .o_nv_right_rd_idx(nv_right_rd_idx),
        .i_nv_right_man(nv_right_man),
        .i_nv_right_exp(nv_right_exp),

        // MLP BRAM write interface
        .o_wt_valid(wt_valid),
        .i_wt_ready(wt_ready),
        .o_nv_right_man(disp_nv_right_man),
        .o_nv_right_exp(disp_nv_right_exp),
        .o_col_sel(col_sel),
        .o_wt_nv_idx(wt_nv_idx),
        .o_wt_cycle_cnt(wt_cycle_cnt),
        .o_wt_loading(wt_loading),
        .o_wt_base_addr(disp_wt_base_addr)
    );
    
    // Pass through dispatch data
    assign nv_right_man_eff[0] = disp_nv_right_man[0];
    assign nv_right_man_eff[1] = disp_nv_right_man[1];
    assign nv_right_man_eff[2] = disp_nv_right_man[2];
    assign nv_right_man_eff[3] = disp_nv_right_man[3];
    assign nv_right_exp_eff = disp_nv_right_exp;
    assign wt_col_valid = 1'b1;

    // =========================================================================
    // MLP Activation/NV Scheduler - NEW: B outer, C inner
    // =========================================================================
    // For each batch (outer):
    //   For each column group (inner):
    //     Stream V NVs (activation replayed, weights cycle through groups)
    //     Output 16 results
    //
    // Key difference from old scheduler:
    //   - sched_batch_cnt is outer (advances after all groups done)
    //   - sched_group_cnt is inner (cycles 0..num_col_groups-1 per batch)
    //   - Activation read index = batch * V + nv_cnt (same for all groups in batch)
    //   - Weight read base = group * V * 8 (changes each group)
    
    typedef enum logic [2:0] {
        SCHED_IDLE        = 3'd0,
        SCHED_PRELOAD_CUR = 3'd1,
        SCHED_PRELOAD_NXT = 3'd2,
        SCHED_RUN         = 3'd3,
        SCHED_WAIT_RESULT = 3'd4
    } sched_state_t;

    sched_state_t sched_state_reg, sched_state_next;

    logic        sched_running;
    logic [7:0]  sched_batch_cnt;   // 0..B-1 (outer loop)
    // sched_group_cnt declared above near rd_base_addr_eff
    logic [7:0]  sched_nv_cnt;      // 0..V-1 within dot product
    logic [15:0] sched_result_cnt;  // Total results: B * num_col_groups

    // last_matmul: Indicates truly last dot product of entire TILE operation
    // This triggers FINAL_DRAIN in the wrapper instead of per-dot-product drains
    logic        last_matmul;
    assign last_matmul = (sched_batch_cnt == (active_left_ugd_len - 8'd1)) &&
                         (sched_group_cnt == (num_col_groups - 4'd1));

    // Row BRAM read index driving
    logic [6:0]  nv_left_rd_idx_reg;
    logic [13:0] left_base_nv_idx_full;
    logic [13:0] idx_full_cur;
    logic [13:0] idx_full_nxt;
    logic [6:0]  idx_cur;
    logic [6:0]  idx_nxt;
    logic        load_cur;
    logic        load_nxt;

    assign nv_left_rd_idx = nv_left_rd_idx_reg;

    // Compute current and next absolute NV indices
    // Activation index = base + batch * V + nv_cnt
    // This stays the SAME for all groups within a batch
    always_comb begin
        left_base_nv_idx_full = {7'd0, active_left_addr[8:2]};
        idx_full_cur = left_base_nv_idx_full + (sched_batch_cnt * active_vec_len) + sched_nv_cnt;
        idx_cur = idx_full_cur[6:0];

        if (sched_nv_cnt == (active_vec_len - 1)) begin
            idx_full_nxt = idx_full_cur; // unused on last NV
        end else begin
            idx_full_nxt = left_base_nv_idx_full + (sched_batch_cnt * active_vec_len) + (sched_nv_cnt + 8'd1);
        end
        idx_nxt = idx_full_nxt[6:0];
    end

    // Drive selection: present NEXT payload at NV boundaries
    always_comb begin
        drive_next_payload = 1'b0;
        if (sched_state_reg == SCHED_RUN) begin
            if (first_nv_sent && act_ready && act_cur_valid && act_next_valid && !act_cur_last_nv) begin
                drive_next_payload = 1'b1;
            end
        end
    end

    // Wrapper interface signals
    assign act_valid = (sched_state_reg == SCHED_RUN) && act_cur_valid && act_next_valid;
    assign new_dot   = drive_next_payload ? act_next_new_dot : act_cur_new_dot;
    assign last_nv   = drive_next_payload ? act_next_last_nv : act_cur_last_nv;

    always_comb begin
        if (drive_next_payload) begin
            act_payload_man[0] = act_next_man[0];
            act_payload_man[1] = act_next_man[1];
            act_payload_man[2] = act_next_man[2];
            act_payload_man[3] = act_next_man[3];
            act_payload_exp    = act_next_exp;
        end else begin
            act_payload_man[0] = act_cur_man[0];
            act_payload_man[1] = act_cur_man[1];
            act_payload_man[2] = act_cur_man[2];
            act_payload_man[3] = act_cur_man[3];
            act_payload_exp    = act_cur_exp;
        end
    end

    // Scheduler state transitions
    always_comb begin
        sched_state_next = sched_state_reg;
        load_cur = 1'b0;
        load_nxt = 1'b0;

        case (sched_state_reg)
            SCHED_IDLE: begin
                if (compute_start) begin
                    sched_state_next = SCHED_PRELOAD_CUR;
                end
            end

            SCHED_PRELOAD_CUR: begin
                load_cur = 1'b1;
                sched_state_next = SCHED_PRELOAD_NXT;
            end

            SCHED_PRELOAD_NXT: begin
                load_nxt = 1'b1;
                sched_state_next = SCHED_RUN;
            end

            SCHED_RUN: begin
                if (act_valid && act_ready && act_cur_last_nv) begin
                    // After last NV of a dot product, immediately load next dot product
                    // Don't wait for result - the wrapper handles result timing via capture_delay
                    // Check if this was the last dot product
                    if ((sched_batch_cnt == (active_left_ugd_len - 1)) &&
                        (sched_group_cnt == (num_col_groups - 1))) begin
                        // All dot products sent, wait for final result
                        sched_state_next = SCHED_WAIT_RESULT;
                    end else begin
                        // More dot products to send - immediately preload next
                        sched_state_next = SCHED_PRELOAD_CUR;
                    end
                end
            end

            SCHED_WAIT_RESULT: begin
                // Only entered after truly last dot product is sent
                // Wait for final result to complete
                if (dout_valid) begin
                    sched_state_next = SCHED_IDLE;
                end
            end

            default: begin
                sched_state_next = SCHED_IDLE;
            end
        endcase
    end

    // Drive row_bram read index
    always_comb begin
        if (sched_state_reg == SCHED_PRELOAD_CUR) begin
            nv_left_rd_idx_reg = idx_cur;
        end else if (sched_state_reg == SCHED_PRELOAD_NXT) begin
            nv_left_rd_idx_reg = (active_vec_len == 8'd1) ? idx_cur : idx_nxt;
        end else if ((sched_state_reg == SCHED_RUN) && !act_cur_last_nv) begin
            nv_left_rd_idx_reg = idx_nxt;
        end else begin
            nv_left_rd_idx_reg = idx_cur;
        end
    end

    // Scheduler sequential logic - NEW B outer, C inner structure
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            sched_state_reg   <= SCHED_IDLE;
            sched_running     <= 1'b0;
            sched_batch_cnt   <= 8'd0;
            sched_group_cnt   <= 4'd0;
            sched_nv_cnt      <= 8'd0;
            sched_result_cnt  <= 16'd0;
            compute_done      <= 1'b0;

            act_cur_valid     <= 1'b0;
            act_next_valid    <= 1'b0;
            act_cur_man[0]    <= 256'd0;
            act_cur_man[1]    <= 256'd0;
            act_cur_man[2]    <= 256'd0;
            act_cur_man[3]    <= 256'd0;
            act_cur_exp       <= 32'd0;
            act_cur_new_dot   <= 1'b0;
            act_cur_last_nv   <= 1'b0;
            act_next_man[0]   <= 256'd0;
            act_next_man[1]   <= 256'd0;
            act_next_man[2]   <= 256'd0;
            act_next_man[3]   <= 256'd0;
            act_next_exp      <= 32'd0;
            act_next_new_dot  <= 1'b0;
            act_next_last_nv  <= 1'b0;
            first_nv_sent     <= 1'b0;
            refill_next_pending <= 1'b0;
        end else begin
            sched_state_reg <= sched_state_next;
            compute_done    <= 1'b0;

            if (compute_start) begin
                sched_running    <= 1'b1;
                sched_batch_cnt  <= 8'd0;
                sched_group_cnt  <= 4'd0;
                sched_nv_cnt     <= 8'd0;
                sched_result_cnt <= 16'd0;
                act_cur_valid    <= 1'b0;
                act_next_valid   <= 1'b0;
                first_nv_sent    <= 1'b0;
                refill_next_pending <= 1'b0;
            end

            // Load current payload
            if (load_cur) begin
                act_cur_man[0]  <= nv_left_man[0];
                act_cur_man[1]  <= nv_left_man[1];
                act_cur_man[2]  <= nv_left_man[2];
                act_cur_man[3]  <= nv_left_man[3];
                act_cur_exp     <= nv_left_exp;
                act_cur_new_dot <= (sched_nv_cnt == 8'd0);
                act_cur_last_nv <= (sched_nv_cnt == (active_vec_len - 1));
                act_cur_valid   <= 1'b1;
                `ifdef SIMULATION
                $display("[CE_MLP_DBG] @%0t load_cur: active_vec_len=%0d sched_nv_cnt=%0d last_nv=%0b batch=%0d group=%0d",
                         $time, active_vec_len, sched_nv_cnt, (sched_nv_cnt == (active_vec_len - 1)),
                         sched_batch_cnt, sched_group_cnt);
                // Print first few bytes of activation data for debug
                if (sched_batch_cnt == 0 && sched_nv_cnt == 0) begin
                    $display("[CE_MLP_DATA] @%0t ACT man[0][31:0]=0x%08x exp[7:0]=0x%02x idx=%0d",
                             $time, nv_left_man[0][31:0], nv_left_exp[7:0], nv_left_rd_idx_reg);
                end
                `endif
            end

            // Load next payload
            if (load_nxt) begin
                act_next_man[0]  <= nv_left_man[0];
                act_next_man[1]  <= nv_left_man[1];
                act_next_man[2]  <= nv_left_man[2];
                act_next_man[3]  <= nv_left_man[3];
                act_next_exp     <= nv_left_exp;
                if (active_vec_len == 8'd1) begin
                    act_next_new_dot <= 1'b0;
                    act_next_last_nv <= 1'b1;
                end else begin
                    act_next_new_dot <= 1'b0;
                    act_next_last_nv <= (sched_nv_cnt + 8'd1) == (active_vec_len - 1);
                end
                act_next_valid   <= 1'b1;
            end

            // NV consumption handshake
            if ((sched_state_reg == SCHED_RUN) && act_valid && act_ready) begin
                if (!first_nv_sent) begin
                    first_nv_sent <= 1'b1;
                end else begin
                    if (!act_cur_last_nv) begin
                        // Shift NEXT -> CUR
                        act_cur_man[0]  <= act_next_man[0];
                        act_cur_man[1]  <= act_next_man[1];
                        act_cur_man[2]  <= act_next_man[2];
                        act_cur_man[3]  <= act_next_man[3];
                        act_cur_exp     <= act_next_exp;
                        act_cur_new_dot <= act_next_new_dot;
                        act_cur_last_nv <= act_next_last_nv;
                        act_cur_valid   <= 1'b1;
                        act_next_valid  <= 1'b0;
                        refill_next_pending <= 1'b1;

                        sched_nv_cnt <= sched_nv_cnt + 8'd1;
                    end
                end
            end

            // Refill NEXT
            if ((sched_state_reg == SCHED_RUN) && refill_next_pending) begin
                act_next_man[0]  <= nv_left_man[0];
                act_next_man[1]  <= nv_left_man[1];
                act_next_man[2]  <= nv_left_man[2];
                act_next_man[3]  <= nv_left_man[3];
                act_next_exp     <= nv_left_exp;
                act_next_new_dot <= 1'b0;
                act_next_last_nv <= (sched_nv_cnt + 8'd1) == (active_vec_len - 1);
                act_next_valid   <= 1'b1;
                refill_next_pending <= 1'b0;
            end

            // Dot product transition: update counters when last NV is consumed (for next dot product addressing)
            if ((sched_state_reg == SCHED_RUN) && act_valid && act_ready && act_cur_last_nv) begin
                // This dot product is done, prepare for next one
                `ifdef SIMULATION
                $display("[CE_MLP_TRANS] @%0t DOT_DONE: batch=%0d->%0d group=%0d->%0d",
                         $time, sched_batch_cnt,
                         (sched_group_cnt == (num_col_groups - 1)) ? sched_batch_cnt + 8'd1 : sched_batch_cnt,
                         sched_group_cnt,
                         (sched_group_cnt == (num_col_groups - 1)) ? 4'd0 : sched_group_cnt + 4'd1);
                `endif
                // Check if we finished all groups for this batch
                if (sched_group_cnt == (num_col_groups - 1)) begin
                    // Advance to next batch, reset group counter
                    sched_batch_cnt <= sched_batch_cnt + 8'd1;
                    sched_group_cnt <= 4'd0;
                end else begin
                    // More groups in this batch
                    sched_group_cnt <= sched_group_cnt + 4'd1;
                end

                // Reset per-dot-product state for next dot product
                sched_nv_cnt    <= 8'd0;
                act_cur_valid   <= 1'b0;
                act_next_valid  <= 1'b0;
                first_nv_sent   <= 1'b0;
            end

            // Result completion tracking (separate from dot product sending)
            if (dout_valid) begin
                sched_result_cnt <= sched_result_cnt + 16'd1;

                if (sched_result_cnt == (active_left_ugd_len * num_col_groups - 1)) begin
                    // All results received
                    compute_done  <= 1'b1;
                    sched_running <= 1'b0;
                end
            end
        end
    end

    // =========================================================================
    // comp_mlp_bram_col_wrapper Instance
    // =========================================================================
    comp_mlp_bram_col_wrapper #(
        .NUM_MLPS(NUM_MLPS)
    ) u_mlp_bram_col_wrapper  (
        .clk(i_clk),
        .rstn(i_reset_n),

        // Base address configuration
        .i_wt_base_addr(disp_wt_base_addr),
        .i_rd_base_addr(rd_base_addr_eff),

        // Weight interface
        .i_wt_valid(wt_valid),
        .o_wt_ready(wt_ready),
        .i_nv_right_man(nv_right_man_eff),
        .i_nv_right_exp(nv_right_exp_eff),
        .i_col_sel(col_sel),
        .i_wt_nv_idx(wt_nv_idx),
        .i_wt_cycle_cnt(wt_cycle_cnt),
        .i_wt_loading(wt_loading),

        // Activation interface
        .i_act_valid(act_valid),
        .o_act_ready(act_ready),
        .i_nv_left_man(act_payload_man),
        .i_nv_left_exp(act_payload_exp),
        .i_new_dot(new_dot),
        .i_last_nv(last_nv),
        .i_last_matmul(last_matmul && last_nv),  // Truly last dot product of entire TILE

        // Result interface
        .o_dout(mlp_dout),
        .o_dout_valid(dout_valid),
        .i_dout_ready(1'b1)
    );

    // =========================================================================
    // Result Extraction: FP16 directly from MLP outputs
    // =========================================================================
    genvar col;
    generate
        for (col = 0; col < NUM_COLUMNS; col = col + 1) begin : gen_fp16_extract
            localparam MLP_IDX = col / 2;
            localparam IS_ODD = col % 2;

            if (IS_ODD == 0) begin : even_col
                assign fp16_results[col] = mlp_dout[MLP_IDX][15:0];
            end else begin : odd_col
                assign fp16_results[col] = mlp_dout[MLP_IDX][31:16];
            end
        end
    endgenerate

    assign fp16_valid = dout_valid;

    // =========================================================================
    // Output Assembly: Pack 16 FP16 into 256-bit vector
    // =========================================================================
    localparam PIPELINE_LATENCY_CYCLES = 4;

    logic in_compute_now;
    logic [PIPELINE_LATENCY_CYCLES-1:0] compute_phase_history;
    logic in_compute_phase;

    assign in_compute_now = (top_state_reg == ST_COMPUTE);

    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            compute_phase_history <= '0;
        end else begin
            compute_phase_history <= {compute_phase_history[PIPELINE_LATENCY_CYCLES-2:0], in_compute_now};
        end
    end

    assign in_compute_phase = in_compute_now | (|compute_phase_history);

    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            o_result_data <= 256'd0;
            o_result_valid <= 1'b0;
        end else begin
            if (fp16_valid && in_compute_phase) begin
                o_result_data <= {
                    fp16_results[15], fp16_results[14], fp16_results[13], fp16_results[12],
                    fp16_results[11], fp16_results[10], fp16_results[9],  fp16_results[8],
                    fp16_results[7],  fp16_results[6],  fp16_results[5],  fp16_results[4],
                    fp16_results[3],  fp16_results[2],  fp16_results[1],  fp16_results[0]
                };
                o_result_valid <= 1'b1;
            end else begin
                o_result_valid <= 1'b0;
            end
        end
    end

    // =========================================================================
    // Probe Registers - Capture pipeline stages for debugging
    // =========================================================================
    
    logic [15:0] probe_rowbram_data_reg;
    logic        probe_rowbram_valid_reg;
    
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            probe_rowbram_data_reg <= 16'd0;
            probe_rowbram_valid_reg <= 1'b0;
        end else begin
            probe_rowbram_valid_reg <= i_man_left_wr_en | i_man_right_wr_en;
            if (i_man_left_wr_en) begin
                probe_rowbram_data_reg <= i_man_left_wr_data[15:0];
            end else if (i_man_right_wr_en) begin
                probe_rowbram_data_reg <= i_man_right_wr_data[15:0];
            end
        end
    end
    
    assign o_probe_rowbram_data = probe_rowbram_data_reg;
    assign o_probe_rowbram_valid = probe_rowbram_valid_reg;
    
    logic [23:0] probe_fp24_data_reg;
    logic        probe_fp24_valid_reg;
    
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            probe_fp24_data_reg <= 24'd0;
            probe_fp24_valid_reg <= 1'b0;
        end else begin
            probe_fp24_valid_reg <= dout_valid;
            if (dout_valid) begin
                probe_fp24_data_reg <= {8'h0, mlp_dout[0][15:0]};
            end
        end
    end
    
    assign o_probe_fp24_data = probe_fp24_data_reg;
    assign o_probe_fp24_valid = probe_fp24_valid_reg;
    
    logic [15:0] probe_fp16_data_reg;
    logic        probe_fp16_valid_reg;
    
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            probe_fp16_data_reg <= 16'd0;
            probe_fp16_valid_reg <= 1'b0;
        end else begin
            probe_fp16_valid_reg <= fp16_valid;
            if (fp16_valid) begin
                probe_fp16_data_reg <= fp16_results[0];
            end
        end
    end
    
    assign o_probe_fp16_data = probe_fp16_data_reg;
    assign o_probe_fp16_valid = probe_fp16_valid_reg;

endmodule

`default_nettype wire
