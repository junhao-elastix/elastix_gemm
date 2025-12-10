`timescale 1ns / 1ps

// MLP BRAM Column Controller - 4-Stack Parallel Architecture
//
// Architecture: 4 × mlp_bram_col stacked in parallel
//   - Each stack handles 32 elements (one 256-bit mantissa group + 8-bit exponent)
//   - All 4 stacks process in parallel: 4× throughput
//   - Combinational FP24 adder tree sums partial results
//
// Weight Loading:
//   - 4 cycles to load one NV (vs 16 cycles with single stack)
//   - Each stack receives different 32-element group
//   - Same wren broadcast to all stacks
//
// Compute:
//   - 4 cycles of streaming (vs 16 with single stack)
//   - Each stack computes partial 32-element dot product
//   - FP24 adder tree combines 4 partial sums per column
//
// Output: 16 × FP24 results (same interface as before)

`default_nettype none

module mlp_bram_col_ctrl #(
    parameter integer NUM_MLPS = 8,
    parameter integer NUM_STACKS = 4,           // 4 parallel stacks
    parameter integer CYCLES_PER_NV = 4,        // 4 cycles per NV (32 elements / 8 per cycle)
    parameter integer PIPELINE_LATENCY = 2      // MLP pipeline latency for load timing
) (
    // Clock and Reset
    input  wire        clk,
    input  wire        rstn,

    // =========================================================================
    // Weight Loading Interface (upstream)
    // =========================================================================
    input  wire        i_wt_valid,           // Weight data valid
    output wire        o_wt_ready,           // Ready to accept weight data
    input  wire [255:0]  i_nv_right_man [0:3], // 128 mantissas as 4 groups of 256 bits
    input  wire [31:0]   i_nv_right_exp,       // 4 exponents (8-bit each)
    input  wire [3:0]    i_col_sel,            // Target column (0-15)
    input  wire [6:0]    i_wt_nv_idx,          // NV index within column (for V>1)

    // =========================================================================
    // Compute/Activation Interface (upstream)
    // =========================================================================
    input  wire        i_act_valid,          // Activation data valid
    output wire        o_act_ready,          // Ready to accept activation data
    input  wire [255:0]  i_nv_left_man [0:3], // 128 activation mantissas as 4 groups of 256 bits
    input  wire [31:0]   i_nv_left_exp,       // 4 exponents (8-bit each)
    input  wire        i_new_dot,            // Start new dot product (reset accumulator)
    input  wire        i_last_nv,            // This is the last NV of the batch (output after drain)

    // =========================================================================
    // Result Interface (downstream)
    // =========================================================================
    output wire [71:0] o_dout [NUM_MLPS-1:0], // MLP outputs (combined from 4 stacks)
    output wire        o_dout_valid,          // Results valid
    input  wire        i_dout_ready           // Downstream ready

);

    // =========================================================================
    // Weight Loading FSM
    // =========================================================================
    typedef enum logic [1:0] {
        WT_IDLE   = 2'b00,
        WT_LOAD   = 2'b01,
        WT_DONE   = 2'b10
    } wt_state_t;

    wt_state_t wt_state_reg, wt_state_next;

    // Weight cycle counter (0-3 for 4 cycles with 4 stacks)
    logic [1:0] wt_cycle_cnt;

    // Latched weight data
    logic [255:0]  wt_man_reg [0:3];  // 4 groups of 256 bits
    logic [31:0]   wt_exp_reg;
    logic [3:0]    col_sel_reg;
    logic [6:0]    wt_nv_idx_reg;     // NV index within column for V>1

    // =========================================================================
    // Compute FSM
    // =========================================================================
    typedef enum logic [2:0] {
        COMP_IDLE    = 3'b000,
        COMP_SETUP   = 3'b001,  // Setup cycle: ce=1, rdaddr=0, wait for BRAM
        COMP_STREAM  = 3'b010,
        COMP_DRAIN   = 3'b011
    } comp_state_t;

    comp_state_t comp_state_reg, comp_state_next;

    // Compute cycle counter (0-3 for 4 cycles of streaming)
    logic [1:0] comp_cycle_cnt;

    // Drain counter for pipeline flush
    logic [2:0] drain_cnt;

    // NV index counter (tracks which NV within a dot product we're processing)
    logic [6:0] nv_index;

    // Latched activation data
    logic [255:0]  act_man_reg [0:3];  // 4 groups of 256 bits
    logic [31:0]   act_exp_reg;
    logic          new_dot_reg;
    logic          last_nv_reg;        // Last NV of batch flag

    // =========================================================================
    // Per-Stack Data Extraction
    // Each stack handles one 256-bit group (32 elements)
    // wt_cycle_cnt[1:0] selects 64-bit chunk within group (0-3)
    // =========================================================================
    logic [63:0] wt_man_chunk [NUM_STACKS-1:0];
    logic [7:0]  wt_exp_chunk [NUM_STACKS-1:0];
    logic [71:0] bram_din_stack [NUM_STACKS-1:0];

    // Weight data extraction for each stack
    genvar s;
    generate
        for (s = 0; s < NUM_STACKS; s = s + 1) begin : gen_wt_extract
            always_comb begin
                // Select 64-bit mantissa chunk based on cycle count
                case (wt_cycle_cnt)
                    2'd0: wt_man_chunk[s] = wt_man_reg[s][63:0];
                    2'd1: wt_man_chunk[s] = wt_man_reg[s][127:64];
                    2'd2: wt_man_chunk[s] = wt_man_reg[s][191:128];
                    2'd3: wt_man_chunk[s] = wt_man_reg[s][255:192];
                endcase

                // Each stack uses its own exponent (same for all 4 cycles within stack)
                wt_exp_chunk[s] = wt_exp_reg[s*8 +: 8];
            end

            // Pack into 72-bit bram_din format: {exp[7:0], man[63:0]}
            assign bram_din_stack[s] = {wt_exp_chunk[s], wt_man_chunk[s]};
        end
    endgenerate

    // =========================================================================
    // Per-Stack Activation Data Extraction
    // =========================================================================
    logic [63:0] act_man_chunk [NUM_STACKS-1:0];
    logic [7:0]  act_exp_chunk [NUM_STACKS-1:0];
    logic [71:0] din_stack [NUM_STACKS-1:0];

    generate
        for (s = 0; s < NUM_STACKS; s = s + 1) begin : gen_act_extract
            always_comb begin
                // Select 64-bit mantissa chunk based on cycle count
                case (comp_cycle_cnt)
                    2'd0: act_man_chunk[s] = act_man_reg[s][63:0];
                    2'd1: act_man_chunk[s] = act_man_reg[s][127:64];
                    2'd2: act_man_chunk[s] = act_man_reg[s][191:128];
                    2'd3: act_man_chunk[s] = act_man_reg[s][255:192];
                endcase

                // Each stack uses its own exponent
                act_exp_chunk[s] = act_exp_reg[s*8 +: 8];
            end

            // Pack into 72-bit din format
            assign din_stack[s] = {act_exp_chunk[s], act_man_chunk[s]};
        end
    endgenerate

    // =========================================================================
    // Column to MLP/Bank Mapping (for weight loading)
    // =========================================================================
    wire [2:0] mlp_index = col_sel_reg[3:1];  // col_sel / 2
    wire       bank_sel  = col_sel_reg[0];     // col_sel % 2

    // Generate wren mask (only one MLP enabled during weight loading)
    // Same wren broadcast to all 4 stacks
    wire [NUM_MLPS-1:0] wren_wt = (wt_state_reg == WT_LOAD) ?
        ({{(NUM_MLPS-1){1'b0}}, 1'b1} << mlp_index) : {NUM_MLPS{1'b0}};

    // Generate wraddr:
    //   With 4 stacks, each stack stores 32 elements (4 cycles worth)
    //   Address layout: {wt_nv_idx[6:0], wt_cycle_cnt[1:0], ~bank_sel}
    //   - NV 0: addresses 0-7 (4 cycles × 2 banks)
    //   - NV 1: addresses 8-15
    //   - etc.
    wire [9:0] wraddr_wt = {wt_nv_idx_reg[6:0], wt_cycle_cnt, ~bank_sel};

    // =========================================================================
    // Compute Control Signal Generation
    // =========================================================================
    wire is_loading = (wt_state_reg == WT_LOAD);
    wire is_streaming = (comp_state_reg == COMP_STREAM);

    // ce: Active during streaming AND drain
    wire comp_ce = (comp_state_reg == COMP_STREAM) || (comp_state_reg == COMP_DRAIN);

    // accumulate: Enable after first cycle of COMP_STREAM, and during COMP_DRAIN
    wire comp_accumulate = ((comp_state_reg == COMP_STREAM) && (comp_cycle_cnt > 2'd0)) ||
                           (comp_state_reg == COMP_DRAIN);

    // load: Pulse at cycle 2 for new dot product (accounts for pipeline latency)
    // With 4 cycles, load at cycle 2 is still valid (cycles 0,1,2,3)
    wire comp_load = (comp_state_reg == COMP_STREAM) &&
                     (comp_cycle_cnt == PIPELINE_LATENCY[1:0]) && new_dot_reg;

    // =========================================================================
    // MLP BRAM Column Signal Muxing (shared across all stacks)
    // =========================================================================
    wire [9:0]          mlp_wraddr    = is_loading ? wraddr_wt : 10'b0;
    wire [NUM_MLPS-1:0] mlp_wren      = wren_wt;

    // rdaddr: For V>1, weights are stored at nv_index * 4 + cycle offset
    // (was nv_index * 16 with single stack)
    wire [8:0] nv_base_addr = {nv_index[6:0], 2'd0};  // nv_index * 4
    wire [8:0]          mlp_rdaddr    = is_loading ? 9'b0 :
                                        (comp_state_reg == COMP_SETUP) ? nv_base_addr :
                                        (comp_state_reg == COMP_STREAM) ? (nv_base_addr + {7'd0, comp_cycle_cnt} + 9'd1) :
                                        9'b0;
    wire                mlp_ce        = is_loading ? 1'b1 : comp_ce;
    wire                mlp_load      = is_loading ? 1'b0 : comp_load;
    wire                mlp_accumulate = is_loading ? 1'b0 : comp_accumulate;

    // =========================================================================
    // Weight Loading FSM: Next State Logic
    // =========================================================================
    always_comb begin
        wt_state_next = wt_state_reg;

        case (wt_state_reg)
            WT_IDLE: begin
                if (i_wt_valid) begin
                    wt_state_next = WT_LOAD;
                end
            end

            WT_LOAD: begin
                // 4 cycles instead of 16
                if (wt_cycle_cnt == 2'd3) begin
                    wt_state_next = WT_DONE;
                end
            end

            WT_DONE: begin
                wt_state_next = WT_IDLE;
            end

            default: wt_state_next = WT_IDLE;
        endcase
    end

    // =========================================================================
    // Weight Loading FSM: Registered Logic
    // =========================================================================
    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            wt_state_reg   <= WT_IDLE;
            wt_cycle_cnt   <= 2'd0;
            wt_man_reg[0]  <= 256'b0;
            wt_man_reg[1]  <= 256'b0;
            wt_man_reg[2]  <= 256'b0;
            wt_man_reg[3]  <= 256'b0;
            wt_exp_reg     <= 32'b0;
            col_sel_reg    <= 4'd0;
            wt_nv_idx_reg  <= 7'd0;
        end else begin
            wt_state_reg <= wt_state_next;

            case (wt_state_reg)
                WT_IDLE: begin
                    wt_cycle_cnt <= 2'd0;
                    if (i_wt_valid) begin
                        wt_man_reg[0] <= i_nv_right_man[0];
                        wt_man_reg[1] <= i_nv_right_man[1];
                        wt_man_reg[2] <= i_nv_right_man[2];
                        wt_man_reg[3] <= i_nv_right_man[3];
                        wt_exp_reg    <= i_nv_right_exp;
                        col_sel_reg   <= i_col_sel;
                        wt_nv_idx_reg <= i_wt_nv_idx;
                    end
                end

                WT_LOAD: begin
                    wt_cycle_cnt <= wt_cycle_cnt + 2'd1;
                end

                WT_DONE: begin
                    wt_cycle_cnt <= 2'd0;
                end

                default: ;
            endcase
        end
    end

    // =========================================================================
    // Compute FSM: Next State Logic
    // =========================================================================
    always_comb begin
        comp_state_next = comp_state_reg;

        case (comp_state_reg)
            COMP_IDLE: begin
                if (i_act_valid && !is_loading) begin
                    comp_state_next = COMP_SETUP;
                end
            end

            COMP_SETUP: begin
                comp_state_next = COMP_STREAM;
            end

            COMP_STREAM: begin
                // 4 cycles instead of 16
                if (comp_cycle_cnt == 2'd3) begin
                    comp_state_next = COMP_DRAIN;
                end
            end

            COMP_DRAIN: begin
                // Shorter drain since pipeline is same depth
                if (drain_cnt == 3'd2) begin
                    comp_state_next = COMP_IDLE;
                end
            end

            default: comp_state_next = COMP_IDLE;
        endcase
    end

    // =========================================================================
    // Compute FSM: Registered Logic
    // =========================================================================
    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            comp_state_reg  <= COMP_IDLE;
            comp_cycle_cnt  <= 2'd0;
            drain_cnt       <= 3'd0;
            act_man_reg[0]  <= 256'b0;
            act_man_reg[1]  <= 256'b0;
            act_man_reg[2]  <= 256'b0;
            act_man_reg[3]  <= 256'b0;
            act_exp_reg     <= 32'b0;
            new_dot_reg     <= 1'b0;
            last_nv_reg     <= 1'b0;
            nv_index        <= 7'd0;
        end else begin
            comp_state_reg <= comp_state_next;

            case (comp_state_reg)
                COMP_IDLE: begin
                    comp_cycle_cnt  <= 2'd0;
                    drain_cnt       <= 3'd0;
                    if (i_act_valid && !is_loading) begin
                        act_man_reg[0] <= i_nv_left_man[0];
                        act_man_reg[1] <= i_nv_left_man[1];
                        act_man_reg[2] <= i_nv_left_man[2];
                        act_man_reg[3] <= i_nv_left_man[3];
                        act_exp_reg <= i_nv_left_exp;
                        new_dot_reg <= i_new_dot;
                        last_nv_reg <= i_last_nv;  // Capture last NV flag
                        if (i_new_dot) begin
                            nv_index <= 7'd0;
                        end else begin
                            nv_index <= nv_index + 7'd1;
                        end
                    end
                end

                COMP_SETUP: begin
                    // Setup cycle: rdaddr set, BRAM reads weights
                end

                COMP_STREAM: begin
                    comp_cycle_cnt <= comp_cycle_cnt + 2'd1;
                end

                COMP_DRAIN: begin
                    drain_cnt <= drain_cnt + 3'd1;
                end

                default: ;
            endcase
        end
    end

    // =========================================================================
    // Ready-Valid Signals
    // =========================================================================
    assign o_wt_ready = (wt_state_reg == WT_IDLE);
    assign o_act_ready = (comp_state_reg == COMP_IDLE) && !is_loading;

    // Pulse o_dout_valid for exactly 1 cycle when result is ready
    // Result is ready when transitioning from DRAIN to IDLE AND this was the last NV of batch
    logic was_draining;
    logic was_last_nv;
    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            was_draining <= 1'b0;
            was_last_nv  <= 1'b0;
        end else begin
            was_draining <= (comp_state_reg == COMP_DRAIN);
            // Capture last_nv_reg at end of DRAIN so it's valid when we check in IDLE
            if (comp_state_reg == COMP_DRAIN) begin
                was_last_nv <= last_nv_reg;
            end
        end
    end
    // Pulse when entering IDLE from DRAIN AND this was the last NV of the batch
    assign o_dout_valid = (comp_state_reg == COMP_IDLE) && was_draining && was_last_nv && !is_loading;

    // =========================================================================
    // 4 × MLP BRAM Column Instances
    // =========================================================================
    wire [71:0] stack_dout [NUM_STACKS-1:0][NUM_MLPS-1:0];

    generate
        for (s = 0; s < NUM_STACKS; s = s + 1) begin : gen_mlp_stack
            // Per-stack din: zero during loading, activation during streaming
            wire [71:0] stack_din = (is_loading || !is_streaming) ? 72'b0 : din_stack[s];

            mlp_bram_col #(
                .NUM_MLPS(NUM_MLPS)
            ) u_mlp_bram_col (
                .clk(clk),
                .rstn(rstn),
                .ce(mlp_ce),
                .din(stack_din),
                .load(mlp_load),
                .accumulate(mlp_accumulate),
                .bram_din(bram_din_stack[s]),
                .wraddr(mlp_wraddr),
                .wren(mlp_wren),
                .rdaddr(mlp_rdaddr),
                .dout(stack_dout[s])
            );
        end
    endgenerate

    // =========================================================================
    // FP24 Adder Tree: Combine 4 partial results per column
    // Each MLP produces 2 FP24 results (Bank 0 and Bank 1)
    // dout[23:0]  = Bank CD result (even column)
    // dout[47:24] = Bank AB result (odd column)
    // =========================================================================

    // Extract FP24 values from each stack for each MLP
    wire [23:0] fp24_bank0 [NUM_STACKS-1:0][NUM_MLPS-1:0];  // Even columns
    wire [23:0] fp24_bank1 [NUM_STACKS-1:0][NUM_MLPS-1:0];  // Odd columns

    generate
        for (s = 0; s < NUM_STACKS; s = s + 1) begin : gen_fp24_extract
            for (genvar m = 0; m < NUM_MLPS; m = m + 1) begin : gen_mlp_fp24
                assign fp24_bank0[s][m] = stack_dout[s][m][23:0];   // Bank CD (even col)
                assign fp24_bank1[s][m] = stack_dout[s][m][47:24];  // Bank AB (odd col)
            end
        end
    endgenerate

    // 2-level adder tree for each bank of each MLP
    // Level 1: stack[0]+stack[1], stack[2]+stack[3]
    // Level 2: sum_01 + sum_23
    wire [23:0] sum_01_bank0 [NUM_MLPS-1:0];
    wire [23:0] sum_23_bank0 [NUM_MLPS-1:0];
    wire [23:0] final_bank0 [NUM_MLPS-1:0];

    wire [23:0] sum_01_bank1 [NUM_MLPS-1:0];
    wire [23:0] sum_23_bank1 [NUM_MLPS-1:0];
    wire [23:0] final_bank1 [NUM_MLPS-1:0];

    generate
        for (genvar m = 0; m < NUM_MLPS; m = m + 1) begin : gen_adder_tree
            // Bank 0 (even columns) adder tree
            fp24_add u_add_01_bank0 (
                .a(fp24_bank0[0][m]),
                .b(fp24_bank0[1][m]),
                .sum(sum_01_bank0[m])
            );

            fp24_add u_add_23_bank0 (
                .a(fp24_bank0[2][m]),
                .b(fp24_bank0[3][m]),
                .sum(sum_23_bank0[m])
            );

            fp24_add u_add_final_bank0 (
                .a(sum_01_bank0[m]),
                .b(sum_23_bank0[m]),
                .sum(final_bank0[m])
            );

            // Bank 1 (odd columns) adder tree
            fp24_add u_add_01_bank1 (
                .a(fp24_bank1[0][m]),
                .b(fp24_bank1[1][m]),
                .sum(sum_01_bank1[m])
            );

            fp24_add u_add_23_bank1 (
                .a(fp24_bank1[2][m]),
                .b(fp24_bank1[3][m]),
                .sum(sum_23_bank1[m])
            );

            fp24_add u_add_final_bank1 (
                .a(sum_01_bank1[m]),
                .b(sum_23_bank1[m]),
                .sum(final_bank1[m])
            );

            // Combine back into 72-bit output format
            // dout[23:0] = Bank CD (even column)
            // dout[47:24] = Bank AB (odd column)
            // dout[71:48] = status bits (keep from stack 0)
            assign o_dout[m] = {stack_dout[0][m][71:48], final_bank1[m], final_bank0[m]};
        end
    endgenerate

endmodule

`default_nettype wire
