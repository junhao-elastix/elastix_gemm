// ------------------------------------------------------------------
// Compute Engine MLP (GEMM-Compatible Interface)
//
// Top-level wrapper integrating:
//   - row_bram: L1 memory for ACTIVATIONS ONLY (left matrix)
//   - mlp_bram_col_wrapper: MLP compute array with 16 columns (4 stacks each)
//   - Direct FP16 output (via integer-domain adder pipeline)
//
// Memory Architecture (REFACTORED Jan 2026):
//   - row_bram: Holds activations (left matrix) ONLY
//   - mlp_bram: Holds weights (right matrix) - written directly via line-by-line interface
//   - NO internal data copy between BRAMs (comp_mlp_dispatch removed)
//
// Command Path:
//   - FETCH: External (dispatcher_control) writes activations to row_bram
//   - WEIGHT LOAD: External writes weights directly to mlp_bram via vectorized interface
//   - TILE: MATMUL computation (row_bram activations × mlp_bram weights → results)
//
// Weight Loading (VECTORIZED Interface):
//   - External controller provides direct NV write signals
//   - i_wt_valid: Validates input data
//   - i_wt_mlp_sel[2:0]: Target MLP (0-7)
//   - i_wt_nv_idx[9:0]: Target NV index
//   - i_wt_wr_man[255:0]: Full 256-bit mantissa (distributed to stacks internally)
//   - i_wt_wr_exp[7:0]: 8-bit exponent
//
// TILE (MATMUL Computation):
//   Result order: B (batch) is outer loop, C (columns) is inner loop
//   This produces results consecutive in C first, then B:
//     [b0c0..c15, b0c16..c31, ..., b1c0..c15, b1c16..c31, ...]
//
// BCV Dimensions:
//   - B (i_tile_left_ugd_len): Number of activation batches
//   - C (i_tile_right_ugd_len): Number of columns (may exceed 16)
//   - V (i_tile_vec_len): Number of NVs to accumulate per output
//
// REFACTORED: Jan 2026 - Streamlined Scheduler & Vectorized Weight Interface
//
// Author: Generated for MLP project
// Date: 2024
// Updated: Jan 2026 - Streamlined Scheduler & Vectorized Weight Interface
// ------------------------------------------------------------------

`timescale 1ps / 1ps
`default_nettype none

module compute_engine_mlp #(
    parameter int TILE_ID = 0,                // Tile ID for debugging
    parameter int MAN_WIDTH = 256,            // Mantissa line width (256 bits = 32 × 8-bit)
    parameter int EXP_WIDTH = 8,              // Exponent width
    parameter int BRAM_DEPTH = 512,           // row_bram depth (activations only)
    parameter int ADDR_WIDTH = $clog2(BRAM_DEPTH),
    parameter int NUM_MLPS = 8,               // Number of MLP primitives (2 columns each)
    parameter int NUM_COLUMNS = 2*NUM_MLPS    // Number of MLP columns (fixed)
) (
    input  logic                     i_clk,
    input  logic                     i_reset_n,

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
    // row_bram Write Interface (Activations ONLY)
    // External controller fills row_bram with left matrix before TILE
    // =========================================================================
    // Left mantissa write port (activations)
    input  logic [ADDR_WIDTH-1:0]    i_man_left_wr_addr,
    input  logic                     i_man_left_wr_en,
    input  logic [MAN_WIDTH-1:0]     i_man_left_wr_data,

    // Left exponent write port (activations)
    input  logic [ADDR_WIDTH-1:0]    i_exp_left_wr_addr,
    input  logic                     i_exp_left_wr_en,
    input  logic [EXP_WIDTH-1:0]     i_exp_left_wr_data,

    // =========================================================================
    // MLP BRAM Weight Write Interface (VECTORIZED)
    // External controller writes weights directly to mlp_bram
    // =========================================================================
    input  logic                     i_wt_wr_en,             // Weight write enable (valid)
    output logic                     o_wt_wr_ready,          // Ready to accept write
    input  logic [255:0]             i_wt_wr_man,            // 256-bit mantissa
    input  logic [EXP_WIDTH-1:0]     i_wt_wr_exp,            // 8-bit exponent
    input  logic [2:0]               i_wt_mlp_sel,           // Target MLP (0-7)
    input  logic [9:0]               i_wt_nv_idx,            // Target NV index

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

    // row_bram NV read outputs (activations only)
    logic [31:0]          nv_left_exp_raw;
    logic [MAN_WIDTH-1:0] nv_left_man [0:3];

    // Exponents for MLP (converted from E5 to E8 format)
    logic [31:0]          nv_left_exp;

    // Exponent conversion: GFP8E5 (bias=15) from external memory → GFP8E8 (bias=133) for MLP
    // Formula: exp_E8 = exp_E5 + (133 - 15) = exp_E5 + 118
    // This is always needed since external memory stores GFP8E5 format
    always_comb begin
        for (int i = 0; i < 4; i++) begin
            nv_left_exp[i*8 +: 8] = nv_left_exp_raw[i*8 +: 8] + 8'd118;
        end
    end

    // row_bram NV read index (activations only)
    logic [6:0] nv_left_rd_idx;

    // Weight loading ready signal (from wrapper)
    logic        wt_wr_ready;

    // Activation Interface
    logic        act_valid;
    logic        act_ready;
    logic        new_dot;
    logic        last_nv;
    logic        last_matmul;
    logic [255:0] act_payload_man;
    logic [7:0]   act_payload_exp;

    // Compute scheduler interface
    logic        compute_done;

    logic [71:0] mlp_dout [NUM_MLPS-1:0];
    logic        dout_valid;

    // FP16 results (directly from MLP outputs - no conversion needed!)
    logic [15:0] fp16_results [NUM_COLUMNS-1:0];
    logic        fp16_valid;

    // =========================================================================
    // Column Group Support (for C > 16)
    // =========================================================================
    // Number of column groups = ceil(C / 16)
    logic [3:0] num_col_groups;      // Max 8 groups (C=128)
    
    // Active parameters (from TILE or DISPATCH command)
    logic [7:0]  active_vec_len;        // V: from TILE or DISPATCH
    logic [7:0]  active_right_ugd_len;  // C: from TILE or DISPATCH
    logic [7:0]  active_left_ugd_len;   // B: from TILE
    logic [15:0] active_left_addr;      // Left base address for row_bram reads: from TILE
    logic [15:0] active_right_addr;     // Right base address for row_bram reads: from DISPATCH (fill) or TILE (compute)

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
    
    // =========================================================================
    // Streaming Scheduler FSM
    // =========================================================================
    typedef enum logic [2:0] {
        SCHED_IDLE        = 3'd0,
        SCHED_RUNNING     = 3'd1,
        SCHED_WAIT_RESULT = 3'd2
    } sched_state_t;

    sched_state_t sched_state_reg, sched_state_next;

    logic        sched_running;
    logic [7:0]  sched_batch_cnt;   // 0..B-1 (outer loop)
    logic [7:0]  sched_nv_cnt;      // 0..V-1 within dot product
    logic [15:0] sched_result_cnt;  // Total results: B * num_col_groups

    // Compute control
    logic compute_start;

    // Result Counter
    logic [15:0] result_count;

    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            result_count <= 16'd0;
        end else if (i_tile_start && sched_state_reg == SCHED_IDLE) begin
            result_count <= 16'd0;
        end else if (o_result_valid) begin
            result_count <= result_count + 1;
        end
    end

    assign o_result_count = result_count;
    assign o_ce_state = {1'b0, sched_state_reg};

    // State Transition Logic
    always_comb begin
        sched_state_next = sched_state_reg;
        case (sched_state_reg)
            SCHED_IDLE: begin
                if (i_tile_en && i_tile_start) begin
                    sched_state_next = SCHED_RUNNING;
                end
            end
            SCHED_RUNNING: begin
                // Transition to WAIT_RESULT when last input sent
                // last_matmul condition: batch=B-1, group=G-1, nv=V-1
                if (act_valid && act_ready && last_matmul) begin
                    sched_state_next = SCHED_WAIT_RESULT;
                end
            end
            SCHED_WAIT_RESULT: begin
                if (compute_done) begin
                    sched_state_next = SCHED_IDLE;
                end
            end
            default: sched_state_next = SCHED_IDLE;
        endcase
    end

    // Sub-counter for NV parts (0..3)
    logic [1:0] nv_sub_cnt;
    logic sub_cnt_done;
    
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            nv_sub_cnt <= 2'd0;
        end else if (sched_state_reg == SCHED_RUNNING && act_ready) begin
            nv_sub_cnt <= nv_sub_cnt + 2'd1;
        end else if (sched_state_reg != SCHED_RUNNING) begin
            nv_sub_cnt <= 2'd0;
        end
    end
    
    assign sub_cnt_done = (nv_sub_cnt == 2'd3);

    // Sequential State Update & Counters
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            sched_state_reg <= SCHED_IDLE;
            sched_batch_cnt <= 8'd0;
            sched_group_cnt <= 4'd0;
            sched_nv_cnt    <= 8'd0;
            sched_result_cnt <= 16'd0;
            compute_done    <= 1'b0;
            
            active_vec_len <= 8'd0;
            active_right_ugd_len <= 8'd0;
            active_left_ugd_len <= 8'd0;
            active_left_addr <= 16'd0;
            active_right_addr <= 16'd0;
        end else begin
            sched_state_reg <= sched_state_next;
            compute_done    <= 1'b0;

            if (sched_state_reg == SCHED_IDLE && i_tile_en && i_tile_start) begin
                sched_batch_cnt <= 8'd0;
                sched_group_cnt <= 4'd0;
                sched_nv_cnt    <= 8'd0;
                sched_result_cnt <= 16'd0;
                
                active_vec_len <= i_tile_vec_len;
                active_right_ugd_len <= i_tile_right_ugd_len;
                active_left_ugd_len <= i_tile_left_ugd_len;
                active_left_addr <= i_tile_left_addr;
                active_right_addr <= i_tile_right_addr;
            end else if (sched_state_reg == SCHED_RUNNING) begin
                // Update counters when handshake occurs
                if (act_valid && act_ready && sub_cnt_done) begin
                    if (sched_nv_cnt == (active_vec_len - 1)) begin
                        sched_nv_cnt <= 8'd0;
                        if (sched_group_cnt == (num_col_groups - 1)) begin
                            sched_group_cnt <= 4'd0;
                            sched_batch_cnt <= sched_batch_cnt + 8'd1;
                        end else begin
                            sched_group_cnt <= sched_group_cnt + 4'd1;
                        end
                    end else begin
                        sched_nv_cnt <= sched_nv_cnt + 8'd1;
                    end
                end
            end
            
            // Result counting (Global)
            if (o_result_valid) begin
                 if (sched_result_cnt == (active_left_ugd_len * num_col_groups - 1)) begin
                     compute_done <= 1'b1;
                 end
                 sched_result_cnt <= sched_result_cnt + 16'd1;
            end
        end
    end

    assign o_tile_done = compute_done;

    // =========================================================================
    // Activation Data Path (Bubble-Free)
    // =========================================================================
    
    // Calculate Read Index
    logic [13:0] left_base_nv_idx_full;
    always_comb begin
        left_base_nv_idx_full = {7'd0, active_left_addr[8:2]};
        // Index = base + batch * V + nv_cnt
        // This is stable for the current cycle
        nv_left_rd_idx = left_base_nv_idx_full + (sched_batch_cnt * active_vec_len) + sched_nv_cnt;
    end

    // Drive Activation Interface with Mux
    always_comb begin
        case (nv_sub_cnt)
            2'd0: begin
                act_payload_man = nv_left_man[0];
                act_payload_exp = nv_left_exp[7:0];
            end
            2'd1: begin
                act_payload_man = nv_left_man[1];
                act_payload_exp = nv_left_exp[15:8];
            end
            2'd2: begin
                act_payload_man = nv_left_man[2];
                act_payload_exp = nv_left_exp[23:16];
            end
            2'd3: begin
                act_payload_man = nv_left_man[3];
                act_payload_exp = nv_left_exp[31:24];
            end
        endcase
    end
    
    assign act_valid = (sched_state_reg == SCHED_RUNNING);
    
    // New dot: start of a new dot product (first sub-part of first NV)
    assign new_dot = (sched_nv_cnt == 8'd0) && (nv_sub_cnt == 2'd0);
    
    // Last NV: end of current dot product (last sub-part of last NV)
    assign last_nv = (sched_nv_cnt == (active_vec_len - 1)) && (nv_sub_cnt == 2'd3);
    
    // Last Matmul: end of entire tile
    assign last_matmul = (sched_batch_cnt == (active_left_ugd_len - 1)) &&
                         (sched_group_cnt == (num_col_groups - 1)) &&
                         last_nv;

    // =========================================================================
    // Weight Exponent Conversion
    // =========================================================================
    logic [7:0] wt_line_exp_e8;
    assign wt_line_exp_e8 = i_wt_wr_exp + 8'd118;

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
        .i_man_left_wr_addr(i_man_left_wr_addr),
        .i_man_left_wr_en(i_man_left_wr_en),
        .i_man_left_wr_data(i_man_left_wr_data),
        .i_exp_left_wr_addr(i_exp_left_wr_addr),
        .i_exp_left_wr_en(i_exp_left_wr_en),
        .i_exp_left_wr_data(i_exp_left_wr_data),
        .i_nv_left_rd_idx(nv_left_rd_idx),
        .o_nv_left_exp(nv_left_exp_raw),
        .o_nv_left_man(nv_left_man)
    );

    // =========================================================================
    // comp_mlp_bram_col_wrapper Instance
    // =========================================================================
    comp_mlp_bram_col_wrapper #(
        .NUM_MLPS(NUM_MLPS)
    ) u_mlp_bram_col_wrapper  (
        .clk(i_clk),
        .rstn(i_reset_n),

        // Read base address configuration (for TILE compute)
        .i_rd_base_addr(rd_base_addr_eff),

        // Weight interface (VECTORIZED)
        .i_wt_valid(i_wt_wr_en),
        .o_wt_ready(wt_wr_ready),
        .i_nv_right_man(i_wt_wr_man),
        .i_nv_right_exp(wt_line_exp_e8),     // Converted E5→E8
        .i_wt_mlp_sel(i_wt_mlp_sel),
        .i_wt_nv_idx(i_wt_nv_idx),

        // Activation interface
        .i_act_valid(act_valid),
        .o_act_ready(act_ready),
        .i_nv_left_man(act_payload_man),
        .i_nv_left_exp(act_payload_exp),
        .i_new_dot(new_dot),
        .i_last_nv(last_nv),
        .i_last_matmul(last_matmul),  // Truly last dot product of entire TILE

        // Result interface
        .o_dout(mlp_dout),
        .o_dout_valid(dout_valid),
        .i_dout_ready(1'b1)
    );

    // =========================================================================
    // Output Logic (Pass-through)
    // =========================================================================
    assign o_wt_wr_ready = wt_wr_ready; 
    
    // Result extraction
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
    assign o_result_valid = fp16_valid;
    
    always_comb begin
        o_result_data = {
            fp16_results[15], fp16_results[14], fp16_results[13], fp16_results[12],
            fp16_results[11], fp16_results[10], fp16_results[9],  fp16_results[8],
            fp16_results[7],  fp16_results[6],  fp16_results[5],  fp16_results[4],
            fp16_results[3],  fp16_results[2],  fp16_results[1],  fp16_results[0]
        };
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
            probe_rowbram_valid_reg <= i_man_left_wr_en;
            if (i_man_left_wr_en) begin
                probe_rowbram_data_reg <= i_man_left_wr_data[15:0];
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
