// ------------------------------------------------------------------
// Compute Engine MLP
//
// Top-level wrapper integrating:
//   - row_bram: L1 memory for activations (left) and weights (right)
//   - mlp_bram_col_ctrl: MLP compute array with 16 columns
//
// Three-Phase Operation:
//   1. WEIGHT FILL: Load weights from row_bram right → MLP BRAMs
//      - Column-major order: vec_len NVs per column
//      - 16 columns × vec_len NVs = 16*vec_len total NVs
//
//   2. COMPUTE: Stream activations from row_bram left → all columns
//      - Broadcast same activation NV to all 16 columns
//      - vec_len NVs accumulated per output
//      - B=1 for now (single batch)
//
//   3. OUTPUT: 16 × FP24 results available after compute
//
// Ready-Valid Interfaces:
//   - Upstream: row_bram write ports (4 parallel ports)
//   - Control: start_fill, start_compute pulses
//   - Downstream: 16 × 24-bit FP24 results with valid
//
// Author: Generated for MLP project
// Date: 2024
// ------------------------------------------------------------------

`timescale 1ns / 1ps
`default_nettype none

module compute_engine_mlp #(
    parameter MAN_WIDTH = 256,           // Mantissa line width (256 bits = 32 × 8-bit)
    parameter EXP_WIDTH = 8,             // Exponent width
    parameter BRAM_DEPTH = 512,          // row_bram depth
    parameter ADDR_WIDTH = $clog2(BRAM_DEPTH),
    parameter NUM_COLUMNS = 16,          // Number of MLP columns
    parameter NUM_MLPS = 8,              // Number of MLP primitives (2 columns each)
    parameter VEC_LEN_WIDTH = 8          // Width of vec_len parameter
) (
    input  wire                      i_clk,
    input  wire                      i_reset_n,

    // =========================================================================
    // Configuration
    // =========================================================================
    input  wire [VEC_LEN_WIDTH-1:0]  i_vec_len,        // Number of NVs per column (1-128)

    // =========================================================================
    // row_bram Write Interface (4 parallel ports)
    // External controller fills row_bram before starting operations
    // =========================================================================
    // Left mantissa write port (activations)
    input  wire [ADDR_WIDTH-1:0]     i_man_left_wr_addr,
    input  wire                      i_man_left_wr_en,
    input  wire [MAN_WIDTH-1:0]      i_man_left_wr_data,

    // Right mantissa write port (weights)
    input  wire [ADDR_WIDTH-1:0]     i_man_right_wr_addr,
    input  wire                      i_man_right_wr_en,
    input  wire [MAN_WIDTH-1:0]      i_man_right_wr_data,

    // Left exponent write port (activations)
    input  wire [ADDR_WIDTH-1:0]     i_exp_left_wr_addr,
    input  wire                      i_exp_left_wr_en,
    input  wire [EXP_WIDTH-1:0]      i_exp_left_wr_data,

    // Right exponent write port (weights)
    input  wire [ADDR_WIDTH-1:0]     i_exp_right_wr_addr,
    input  wire                      i_exp_right_wr_en,
    input  wire [EXP_WIDTH-1:0]      i_exp_right_wr_data,

    // =========================================================================
    // Control Interface
    // =========================================================================
    input  wire                      i_start_fill,     // Start weight fill phase
    input  wire                      i_start_compute,  // Start compute phase

    output wire                      o_fill_busy,      // Weight fill in progress
    output wire                      o_fill_done,      // Weight fill complete
    output wire                      o_compute_busy,   // Compute in progress
    output wire                      o_compute_done,   // Compute complete

    // =========================================================================
    // Result Interface (downstream)
    // =========================================================================
    output wire [23:0]               o_result [NUM_COLUMNS-1:0], // FP24 results
    output wire                      o_result_valid               // Results valid
);

    // =========================================================================
    // Internal Signals
    // =========================================================================

    // row_bram NV read outputs
    wire [31:0]          nv_left_exp;
    wire [MAN_WIDTH-1:0] nv_left_man [0:3];
    wire [31:0]          nv_right_exp;
    wire [MAN_WIDTH-1:0] nv_right_man [0:3];

    // row_bram NV read indices
    logic [6:0] nv_left_rd_idx;
    logic [6:0] nv_right_rd_idx;

    // Pack mantissas into 1024-bit vectors for mlp_bram_col_ctrl
    wire [1023:0] nv_left_man_packed = {nv_left_man[3], nv_left_man[2],
                                         nv_left_man[1], nv_left_man[0]};
    wire [1023:0] nv_right_man_packed = {nv_right_man[3], nv_right_man[2],
                                          nv_right_man[1], nv_right_man[0]};

    // mlp_bram_col_ctrl interface signals
    logic        wt_valid;
    wire         wt_ready;
    logic [3:0]  col_sel;

    logic        act_valid;
    wire         act_ready;
    logic        new_dot;

    wire [71:0]  mlp_dout [NUM_MLPS-1:0];
    wire         dout_valid;

    // =========================================================================
    // Weight Fill Controller FSM
    // =========================================================================
    typedef enum logic [2:0] {
        FILL_IDLE     = 3'b000,
        FILL_READ     = 3'b001,  // Read NV from row_bram
        FILL_WAIT     = 3'b010,  // Wait for mlp_bram_col_ctrl ready
        FILL_SEND     = 3'b011,  // Send NV to mlp_bram_col_ctrl
        FILL_NEXT     = 3'b100,  // Move to next NV/column
        FILL_DONE     = 3'b101
    } fill_state_t;

    fill_state_t fill_state_reg, fill_state_next;

    // Fill counters
    logic [VEC_LEN_WIDTH-1:0] fill_nv_cnt;    // NV counter within column (0 to vec_len-1)
    logic [3:0]               fill_col_cnt;   // Column counter (0 to 15)

    // =========================================================================
    // Compute Controller FSM
    // =========================================================================
    typedef enum logic [2:0] {
        COMP_IDLE        = 3'b000,
        COMP_READ        = 3'b001,  // Read activation NV from row_bram
        COMP_WAIT        = 3'b010,  // Wait for mlp_bram_col_ctrl ready
        COMP_SEND        = 3'b011,  // Send activation NV to mlp_bram_col_ctrl
        COMP_NEXT        = 3'b100,  // Move to next NV
        COMP_WAIT_FINISH = 3'b101,  // Wait for mlp_bram_col_ctrl to finish
        COMP_DONE        = 3'b110
    } comp_ctrl_state_t;

    comp_ctrl_state_t comp_ctrl_state_reg, comp_ctrl_state_next;

    // Compute counters
    logic [VEC_LEN_WIDTH-1:0] comp_nv_cnt;    // NV counter (0 to vec_len-1)

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

        // Write ports - directly connected to external interface
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
        .i_nv_right_man(nv_right_man_packed),
        .i_nv_right_exp(nv_right_exp),
        .i_col_sel(col_sel),

        // Activation interface
        .i_act_valid(act_valid),
        .o_act_ready(act_ready),
        .i_nv_left_man(nv_left_man_packed),
        .i_nv_left_exp(nv_left_exp),
        .i_new_dot(new_dot),

        // Result interface
        .o_dout(mlp_dout),
        .o_dout_valid(dout_valid),
        .i_dout_ready(1'b1)  // Always ready to accept results
    );

    // =========================================================================
    // Weight Fill FSM: Next State Logic
    // =========================================================================
    always_comb begin
        fill_state_next = fill_state_reg;

        case (fill_state_reg)
            FILL_IDLE: begin
                if (i_start_fill) begin
                    fill_state_next = FILL_READ;
                end
            end

            FILL_READ: begin
                // Combinational read from row_bram, proceed immediately
                fill_state_next = FILL_WAIT;
            end

            FILL_WAIT: begin
                if (wt_ready) begin
                    fill_state_next = FILL_SEND;
                end
            end

            FILL_SEND: begin
                // NV sent, move to next
                fill_state_next = FILL_NEXT;
            end

            FILL_NEXT: begin
                // Check if we've filled all NVs for all columns
                if (fill_col_cnt == (NUM_COLUMNS - 1) &&
                    fill_nv_cnt == (i_vec_len - 1)) begin
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
                    // Column-major: increment NV first, then column
                    if (fill_nv_cnt == (i_vec_len - 1)) begin
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

    // =========================================================================
    // Weight Fill: Control Signal Generation
    // =========================================================================
    // Calculate row_bram right NV index
    // Column-major layout: col_0_nv_0, col_0_nv_1, ..., col_0_nv_(vec_len-1), col_1_nv_0, ...
    // NV index = col_cnt * vec_len + nv_cnt
    wire [6:0] fill_nv_idx = (fill_col_cnt * i_vec_len) + fill_nv_cnt[6:0];

    always_comb begin
        // Default values
        nv_right_rd_idx = 7'd0;
        wt_valid = 1'b0;
        col_sel = 4'd0;

        case (fill_state_reg)
            FILL_READ, FILL_WAIT, FILL_SEND: begin
                nv_right_rd_idx = fill_nv_idx;
                col_sel = fill_col_cnt;
            end

            default: ;
        endcase

        // Assert wt_valid only in FILL_SEND state
        if (fill_state_reg == FILL_SEND) begin
            wt_valid = 1'b1;
        end
    end

    // =========================================================================
    // Compute Controller FSM: Next State Logic
    // =========================================================================
    // IMPORTANT: After sending the last NV, we must wait for mlp_bram_col_ctrl
    // to finish processing (16 cycles COMP_STREAM + drain cycles).
    // This is signaled by act_ready going high again.
    always_comb begin
        comp_ctrl_state_next = comp_ctrl_state_reg;

        case (comp_ctrl_state_reg)
            COMP_IDLE: begin
                if (i_start_compute) begin
                    comp_ctrl_state_next = COMP_READ;
                end
            end

            COMP_READ: begin
                // Combinational read from row_bram, proceed immediately
                comp_ctrl_state_next = COMP_WAIT;
            end

            COMP_WAIT: begin
                if (act_ready) begin
                    comp_ctrl_state_next = COMP_SEND;
                end
            end

            COMP_SEND: begin
                // Activation NV sent, move to next
                comp_ctrl_state_next = COMP_NEXT;
            end

            COMP_NEXT: begin
                // Check if we've processed all NVs
                if (comp_nv_cnt == (i_vec_len - 1)) begin
                    // Last NV sent - wait for mlp_bram_col_ctrl to finish
                    comp_ctrl_state_next = COMP_WAIT_FINISH;
                end else begin
                    comp_ctrl_state_next = COMP_READ;
                end
            end

            COMP_WAIT_FINISH: begin
                // Wait for mlp_bram_col_ctrl to finish processing
                // (act_ready goes high when comp_state == COMP_IDLE)
                if (act_ready) begin
                    comp_ctrl_state_next = COMP_DONE;
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
        end else begin
            comp_ctrl_state_reg <= comp_ctrl_state_next;

            case (comp_ctrl_state_reg)
                COMP_IDLE: begin
                    comp_nv_cnt <= '0;
                end

                COMP_NEXT: begin
                    comp_nv_cnt <= comp_nv_cnt + 1;
                end

                default: ;
            endcase
        end
    end

    // =========================================================================
    // Compute Controller: Control Signal Generation
    // =========================================================================
    // Activation NV index (sequential 0 to vec_len-1)
    wire [6:0] comp_nv_idx = comp_nv_cnt[6:0];

    always_comb begin
        // Default values
        nv_left_rd_idx = 7'd0;
        act_valid = 1'b0;
        new_dot = 1'b0;

        case (comp_ctrl_state_reg)
            COMP_READ, COMP_WAIT, COMP_SEND: begin
                nv_left_rd_idx = comp_nv_idx;
            end

            default: ;
        endcase

        // Assert act_valid only in COMP_SEND state
        if (comp_ctrl_state_reg == COMP_SEND) begin
            act_valid = 1'b1;
            // new_dot on first NV only (reset accumulator)
            new_dot = (comp_nv_cnt == '0);
        end
    end

    // =========================================================================
    // Output Status Signals
    // =========================================================================
    assign o_fill_busy    = (fill_state_reg != FILL_IDLE) && (fill_state_reg != FILL_DONE);
    assign o_fill_done    = (fill_state_reg == FILL_DONE);
    assign o_compute_busy = (comp_ctrl_state_reg != COMP_IDLE) && (comp_ctrl_state_reg != COMP_DONE);
    assign o_compute_done = (comp_ctrl_state_reg == COMP_DONE);

    // =========================================================================
    // Result Extraction
    // Extract FP24 from 72-bit MLP outputs
    // Each MLP produces 72 bits = 2 columns × 24-bit FP24 + some padding
    // From mlp_bram_col.sv: dout format is {fp24_odd, fp24_even} per MLP
    // mlp_dout[i][23:0] = even column (col 2*i)
    // mlp_dout[i][47:24] = odd column (col 2*i+1)
    // =========================================================================
    genvar col;
    generate
        for (col = 0; col < NUM_COLUMNS; col = col + 1) begin : gen_result
            localparam MLP_IDX = col / 2;
            localparam IS_ODD = col % 2;

            if (IS_ODD == 0) begin : even_col
                // Even column: bits [23:0]
                assign o_result[col] = mlp_dout[MLP_IDX][23:0];
            end else begin : odd_col
                // Odd column: bits [47:24]
                assign o_result[col] = mlp_dout[MLP_IDX][47:24];
            end
        end
    endgenerate

    assign o_result_valid = dout_valid && (comp_ctrl_state_reg == COMP_IDLE);

endmodule

`default_nettype wire
