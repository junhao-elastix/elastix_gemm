// ------------------------------------------------------------------
// Compute Engine MLP (GEMM-Compatible Interface)
//
// Top-level wrapper integrating:
//   - row_bram: L1 memory for activations (left) and weights (right)
//   - mlp_bram_col_ctrl: MLP compute array with 16 columns
//   - fp24_to_fp16: Output format conversion
//
// Interface designed to match compute_engine_modular.sv from gemm project
//
// Operation (triggered by i_tile_start):
//   1. WEIGHT FILL: Load weights from row_bram right → MLP BRAMs
//      - Column-major order: vec_len NVs per column
//      - 16 columns × vec_len NVs = 16*vec_len total NVs
//
//   2. COMPUTE: Stream activations from row_bram left → all columns
//      - BCV Loop: B batches × C columns (C=16 fixed) × V vectors
//      - For each batch: broadcast V activation NVs to all 16 columns
//      - Each batch produces 16 FP16 results (one per column)
//
//   3. OUTPUT: B × 256-bit vectors (16 FP16 results per batch)
//
// BCV Dimensions:
//   - B (i_tile_left_ugd_len): Number of activation batches
//   - C (i_tile_right_ugd_len): Number of columns (fixed to 16)
//   - V (i_tile_vec_len): Number of NVs to accumulate per output
//
// Author: Generated for MLP project
// Date: 2024
// ------------------------------------------------------------------

`timescale 1ns / 1ps
`default_nettype none

module compute_engine_mlp #(
    parameter int TILE_ID = 0,                // Tile ID for debugging
    parameter int MAN_WIDTH = 256,            // Mantissa line width (256 bits = 32 × 8-bit)
    parameter int EXP_WIDTH = 8,              // Exponent width
    parameter int BRAM_DEPTH = 512,           // row_bram depth
    parameter int ADDR_WIDTH = $clog2(BRAM_DEPTH),
    parameter int NUM_COLUMNS = 16,           // Number of MLP columns (fixed)
    parameter int NUM_MLPS = 8                // Number of MLP primitives (2 columns each)
) (
    input  logic                     i_clk,
    input  logic                     i_reset_n,

    // =========================================================================
    // Master Control Interface (TILE command) - gemm-compatible
    // =========================================================================
    input  logic                     i_tile_en,              // Static enable (configuration)
    input  logic                     i_tile_start,           // Dynamic pulse (start computing!)
    input  logic [15:0]              i_tile_left_addr,       // Left matrix start address (unused)
    input  logic [15:0]              i_tile_right_addr,      // Right matrix start address (unused)
    input  logic [7:0]               i_tile_left_ugd_len,    // B: Number of activation batches
    input  logic [7:0]               i_tile_right_ugd_len,   // C: Number of columns (ignored, fixed 16)
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
    output logic [15:0]              o_result_count
);

    // =========================================================================
    // Internal Signals
    // =========================================================================

    // row_bram NV read outputs
    logic [31:0]          nv_left_exp;
    logic [MAN_WIDTH-1:0] nv_left_man [0:3];
    logic [31:0]          nv_right_exp;
    logic [MAN_WIDTH-1:0] nv_right_man [0:3];

    // row_bram NV read indices
    logic [6:0] nv_left_rd_idx;
    logic [6:0] nv_right_rd_idx;

    // mlp_bram_col_ctrl interface signals
    logic        wt_valid;
    logic        wt_ready;
    logic [3:0]  col_sel;
    logic [6:0]  wt_nv_idx;

    logic        act_valid;
    logic        act_ready;
    logic        new_dot;
    logic        last_nv;

    logic [71:0] mlp_dout [NUM_MLPS-1:0];
    logic        dout_valid;

    // FP24 results (extracted from MLP outputs)
    logic [23:0] fp24_results [NUM_COLUMNS-1:0];

    // FP16 results (after conversion)
    logic [15:0] fp16_results [NUM_COLUMNS-1:0];
    logic        fp16_valid;

    // =========================================================================
    // Top-Level State Machine
    // =========================================================================
    typedef enum logic [3:0] {
        ST_IDLE      = 4'd0,
        ST_FILL      = 4'd1,   // Weight fill phase
        ST_COMPUTE   = 4'd2,   // Compute phase
        ST_DONE      = 4'd3
    } top_state_t;

    top_state_t top_state_reg;

    // =========================================================================
    // Weight Fill Controller FSM
    // =========================================================================
    typedef enum logic [2:0] {
        FILL_IDLE     = 3'b000,
        FILL_READ     = 3'b001,
        FILL_WAIT     = 3'b010,
        FILL_SEND     = 3'b011,
        FILL_NEXT     = 3'b100,
        FILL_DONE     = 3'b101
    } fill_state_t;

    fill_state_t fill_state_reg, fill_state_next;

    // Fill counters
    logic [7:0] fill_nv_cnt;
    logic [3:0] fill_col_cnt;

    // Fill control
    logic fill_start;
    logic fill_done;

    // =========================================================================
    // Compute Controller FSM
    // =========================================================================
    typedef enum logic [2:0] {
        COMP_IDLE        = 3'b000,
        COMP_READ        = 3'b001,
        COMP_WAIT        = 3'b010,
        COMP_SEND        = 3'b011,
        COMP_NEXT        = 3'b100,
        COMP_WAIT_FINISH = 3'b101,
        COMP_DONE        = 3'b110
    } comp_ctrl_state_t;

    comp_ctrl_state_t comp_ctrl_state_reg, comp_ctrl_state_next;

    // Compute counters
    logic [7:0] comp_nv_cnt;
    logic [7:0] comp_batch_cnt;

    // Compute control
    logic compute_start;
    logic compute_done;

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
        end else begin
            fill_start <= 1'b0;
            compute_start <= 1'b0;

            case (top_state_reg)
                ST_IDLE: begin
                    if (i_tile_en && i_tile_start) begin
                        top_state_reg <= ST_FILL;
                        fill_start <= 1'b1;
                        `ifdef SIMULATION
                        $display("[CE_MLP%0d] @%0t ST_IDLE: tile_start received, B=%0d, V=%0d",
                                 TILE_ID, $time, i_tile_left_ugd_len, i_tile_vec_len);
                        `endif
                    end
                end

                ST_FILL: begin
                    if (fill_done) begin
                        top_state_reg <= ST_COMPUTE;
                        compute_start <= 1'b1;
                        `ifdef SIMULATION
                        $display("[CE_MLP%0d] @%0t ST_FILL: fill_done, starting compute", TILE_ID, $time);
                        `endif
                    end
                end

                ST_COMPUTE: begin
                    if (compute_done) begin
                        top_state_reg <= ST_DONE;
                        `ifdef SIMULATION
                        $display("[CE_MLP%0d] @%0t ST_COMPUTE: compute_done", TILE_ID, $time);
                        `endif
                    end
                end

                ST_DONE: begin
                    top_state_reg <= ST_IDLE;
                end
            endcase
        end
    end

    assign o_tile_done = (top_state_reg == ST_DONE);

    // =========================================================================
    // row_bram Instance
    // =========================================================================
    row_bram #(
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

        // NV read ports
        .i_nv_left_rd_idx(nv_left_rd_idx),
        .o_nv_left_exp(nv_left_exp),
        .o_nv_left_man(nv_left_man),

        .i_nv_right_rd_idx(nv_right_rd_idx),
        .o_nv_right_exp(nv_right_exp),
        .o_nv_right_man(nv_right_man)
    );

    // =========================================================================
    // mlp_bram_col_ctrl Instance
    // =========================================================================
    mlp_bram_col_ctrl #(
        .NUM_MLPS(NUM_MLPS)
    ) u_mlp_bram_col_ctrl (
        .clk(i_clk),
        .rstn(i_reset_n),

        // Weight interface
        .i_wt_valid(wt_valid),
        .o_wt_ready(wt_ready),
        .i_nv_right_man(nv_right_man),
        .i_nv_right_exp(nv_right_exp),
        .i_col_sel(col_sel),
        .i_wt_nv_idx(wt_nv_idx),

        // Activation interface
        .i_act_valid(act_valid),
        .o_act_ready(act_ready),
        .i_nv_left_man(nv_left_man),
        .i_nv_left_exp(nv_left_exp),
        .i_new_dot(new_dot),
        .i_last_nv(last_nv),

        // Result interface
        .o_dout(mlp_dout),
        .o_dout_valid(dout_valid),
        .i_dout_ready(1'b1)
    );

    // =========================================================================
    // Weight Fill FSM: Next State Logic
    // =========================================================================
    always_comb begin
        fill_state_next = fill_state_reg;

        case (fill_state_reg)
            FILL_IDLE: begin
                if (fill_start) begin
                    fill_state_next = FILL_READ;
                end
            end

            FILL_READ: begin
                fill_state_next = FILL_WAIT;
            end

            FILL_WAIT: begin
                if (wt_ready) begin
                    fill_state_next = FILL_SEND;
                end
            end

            FILL_SEND: begin
                fill_state_next = FILL_NEXT;
            end

            FILL_NEXT: begin
                if (fill_col_cnt == (NUM_COLUMNS - 1) &&
                    fill_nv_cnt == (i_tile_vec_len - 1)) begin
                    fill_state_next = FILL_DONE;
                end else begin
                    fill_state_next = FILL_READ;
                end
            end

            FILL_DONE: begin
                fill_state_next = FILL_IDLE;
            end

            default: fill_state_next = FILL_IDLE;
        endcase
    end

    // =========================================================================
    // Weight Fill FSM: Registered Logic
    // =========================================================================
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            fill_state_reg <= FILL_IDLE;
            fill_nv_cnt    <= '0;
            fill_col_cnt   <= '0;
        end else begin
            fill_state_reg <= fill_state_next;

            case (fill_state_reg)
                FILL_IDLE: begin
                    fill_nv_cnt  <= '0;
                    fill_col_cnt <= '0;
                end

                FILL_NEXT: begin
                    if (fill_nv_cnt == (i_tile_vec_len - 1)) begin
                        fill_nv_cnt  <= '0;
                        fill_col_cnt <= fill_col_cnt + 4'd1;
                    end else begin
                        fill_nv_cnt <= fill_nv_cnt + 1;
                    end
                end

                default: ;
            endcase
        end
    end

    assign fill_done = (fill_state_reg == FILL_DONE);

    // =========================================================================
    // Weight Fill: Control Signal Generation
    // =========================================================================
    logic [6:0] fill_nv_idx;
    assign fill_nv_idx = (fill_col_cnt * i_tile_vec_len) + fill_nv_cnt[6:0];

    always_comb begin
        nv_right_rd_idx = 7'd0;
        wt_valid = 1'b0;
        col_sel = 4'd0;
        wt_nv_idx = 7'd0;

        case (fill_state_reg)
            FILL_READ, FILL_WAIT, FILL_SEND: begin
                nv_right_rd_idx = fill_nv_idx;
                col_sel = fill_col_cnt;
                wt_nv_idx = fill_nv_cnt[6:0];
            end
            default: ;
        endcase

        if (fill_state_reg == FILL_SEND) begin
            wt_valid = 1'b1;
        end
    end

    // =========================================================================
    // Compute Controller FSM: Next State Logic
    // =========================================================================
    always_comb begin
        comp_ctrl_state_next = comp_ctrl_state_reg;

        case (comp_ctrl_state_reg)
            COMP_IDLE: begin
                if (compute_start) begin
                    comp_ctrl_state_next = COMP_READ;
                end
            end

            COMP_READ: begin
                comp_ctrl_state_next = COMP_WAIT;
            end

            COMP_WAIT: begin
                if (act_ready) begin
                    comp_ctrl_state_next = COMP_SEND;
                end
            end

            COMP_SEND: begin
                comp_ctrl_state_next = COMP_NEXT;
            end

            COMP_NEXT: begin
                if (comp_nv_cnt == (i_tile_vec_len - 1)) begin
                    comp_ctrl_state_next = COMP_WAIT_FINISH;
                end else begin
                    comp_ctrl_state_next = COMP_READ;
                end
            end

            COMP_WAIT_FINISH: begin
                if (act_ready) begin
                    if (comp_batch_cnt == (i_tile_left_ugd_len - 1)) begin
                        comp_ctrl_state_next = COMP_DONE;
                    end else begin
                        comp_ctrl_state_next = COMP_READ;
                    end
                end
            end

            COMP_DONE: begin
                comp_ctrl_state_next = COMP_IDLE;
            end

            default: comp_ctrl_state_next = COMP_IDLE;
        endcase
    end

    // =========================================================================
    // Compute Controller FSM: Registered Logic
    // =========================================================================
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            comp_ctrl_state_reg <= COMP_IDLE;
            comp_nv_cnt         <= '0;
            comp_batch_cnt      <= '0;
        end else begin
            comp_ctrl_state_reg <= comp_ctrl_state_next;

            case (comp_ctrl_state_reg)
                COMP_IDLE: begin
                    comp_nv_cnt    <= '0;
                    comp_batch_cnt <= '0;
                end

                COMP_NEXT: begin
                    comp_nv_cnt <= comp_nv_cnt + 1;
                end

                COMP_WAIT_FINISH: begin
                    if (act_ready && (comp_batch_cnt != (i_tile_left_ugd_len - 1))) begin
                        comp_batch_cnt <= comp_batch_cnt + 1;
                        comp_nv_cnt    <= '0;
                    end
                end

                default: ;
            endcase
        end
    end

    assign compute_done = (comp_ctrl_state_reg == COMP_DONE);

    // =========================================================================
    // Compute Controller: Control Signal Generation
    // =========================================================================
    logic [13:0] comp_nv_idx_full;
    logic [6:0]  comp_nv_idx;
    assign comp_nv_idx_full = (comp_batch_cnt * i_tile_vec_len) + comp_nv_cnt;
    assign comp_nv_idx = comp_nv_idx_full[6:0];

    always_comb begin
        nv_left_rd_idx = 7'd0;
        act_valid = 1'b0;
        new_dot = 1'b0;
        last_nv = 1'b0;

        case (comp_ctrl_state_reg)
            COMP_READ, COMP_WAIT, COMP_SEND: begin
                nv_left_rd_idx = comp_nv_idx;
            end
            default: ;
        endcase

        if (comp_ctrl_state_reg == COMP_SEND) begin
            act_valid = 1'b1;
            new_dot = (comp_nv_cnt == '0);
            last_nv = (comp_nv_cnt == (i_tile_vec_len - 1));  // Last NV of this batch
        end
    end

    // =========================================================================
    // Result Extraction: FP24 from MLP outputs
    // Each MLP produces 72 bits = 2 columns × 24-bit FP24 + padding
    // mlp_dout[i][23:0] = even column (col 2*i)
    // mlp_dout[i][47:24] = odd column (col 2*i+1)
    // =========================================================================
    genvar col;
    generate
        for (col = 0; col < NUM_COLUMNS; col = col + 1) begin : gen_fp24_extract
            localparam MLP_IDX = col / 2;
            localparam IS_ODD = col % 2;

            if (IS_ODD == 0) begin : even_col
                assign fp24_results[col] = mlp_dout[MLP_IDX][23:0];
            end else begin : odd_col
                assign fp24_results[col] = mlp_dout[MLP_IDX][47:24];
            end
        end
    endgenerate

    // =========================================================================
    // FP24 to FP16 Conversion (16 parallel converters)
    // =========================================================================
    logic [15:0] fp16_conv_valid;

    generate
        for (col = 0; col < NUM_COLUMNS; col = col + 1) begin : gen_fp16_conv
            fp24_to_fp16 u_fp24_to_fp16 (
                .i_clk(i_clk),
                .i_reset_n(i_reset_n),
                .i_fp24(fp24_results[col]),
                .i_valid(dout_valid),
                .o_fp16(fp16_results[col]),
                .o_valid(fp16_conv_valid[col])
            );
        end
    endgenerate

    // All converters have same latency, use any valid signal
    assign fp16_valid = fp16_conv_valid[0];

    // =========================================================================
    // Output Assembly: Pack 16 FP16 into 256-bit vector
    // Gate result_valid to only be active during compute phase
    // =========================================================================
    logic in_compute_phase;
    assign in_compute_phase = (top_state_reg == ST_COMPUTE);

    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            o_result_data <= 256'd0;
            o_result_valid <= 1'b0;
        end else begin
            // Only output results during compute phase
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

endmodule

`default_nettype wire
