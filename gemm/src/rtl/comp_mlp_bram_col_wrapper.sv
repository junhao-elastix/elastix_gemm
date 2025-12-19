// ------------------------------------------------------------------
// MLP BRAM Column Controller - 4-Stack Parallel Architecture
//
// Architecture: 4 × mlp_bram_col stacked in parallel
//   - Each stack handles 32 elements (one 256-bit mantissa group + 8-bit exponent)
//   - All 4 stacks process in parallel: 4× throughput
//   - Integer-domain FP adder pipeline sums partial results
//
// Weight Loading:
//   - 4 cycles to load one NV (vs 16 cycles with single stack)
//   - Each stack receives different 32-element group
//   - Same wren broadcast to all stacks
//
// Compute:
//   - 4 cycles of streaming (vs 16 with single stack)
//   - Each stack computes partial 32-element dot product
//   - Integer-domain adder pipeline combines 4 partial sums per column
//   - Single rounding point (FP24→Int→Sum→FP16) for improved accuracy
//
// Output: 16 × FP16 results (changed from FP24 for direct use)
//
// Author: Refactored for better organization
// Date: Dec 16, 2025
// ------------------------------------------------------------------

`timescale 1ps / 1ps
`default_nettype none

module comp_mlp_bram_col_wrapper #(
    parameter integer NUM_MLPS = 8,
    parameter integer NUM_STACKS = 4,           // 4 parallel stacks
    parameter integer CYCLES_PER_NV = 4,        // 4 cycles per NV (32 elements / 8 per cycle)
    parameter integer PIPELINE_LATENCY = 2      // MLP pipeline latency for load timing
) (
    // Clock and Reset
    input  logic        clk,
    input  logic        rstn,

    // =========================================================================
    // Base Address Configuration
    // =========================================================================
    input  logic [9:0]  i_wt_base_addr,       // Write base address (from DISPATCH command)
    input  logic [9:0]  i_rd_base_addr,       // Read base address (from TILE command)

    // =========================================================================
    // Weight Loading Interface (upstream from comp_bram_fill_ctrl)
    // =========================================================================
    input  logic        i_wt_valid,           // Weight data valid (latch trigger)
    output logic        o_wt_ready,           // Ready to accept weight data
    input  logic [255:0]  i_nv_right_man [0:3], // 128 mantissas as 4 groups of 256 bits
    input  logic [31:0]   i_nv_right_exp,       // 4 exponents (8-bit each)
    input  logic [3:0]    i_col_sel,            // Target column (0-15)
    input  logic [6:0]    i_wt_nv_idx,          // NV index within column (for V>1)
    input  logic [1:0]    i_wt_cycle_cnt,       // Weight cycle counter from fill_ctrl (0-3)
    input  logic          i_wt_loading,         // Loading in progress (from fill_ctrl FILL_LOAD state)

    // =========================================================================
    // Compute/Activation Interface (upstream)
    // =========================================================================
    input  logic        i_act_valid,          // Activation data valid
    output logic        o_act_ready,          // Ready to accept activation data
    input  logic [255:0]  i_nv_left_man [0:3], // 128 activation mantissas as 4 groups of 256 bits
    input  logic [31:0]   i_nv_left_exp,       // 4 exponents (8-bit each)
    input  logic        i_new_dot,            // Start new dot product (reset accumulator)
    input  logic        i_last_nv,            // This is the last NV of the batch (output after drain)

    // =========================================================================
    // Result Interface (downstream)
    // =========================================================================
    output logic [71:0] o_dout [NUM_MLPS-1:0], // MLP outputs (combined from 4 stacks)
    output logic        o_dout_valid,          // Results valid
    input  logic        i_dout_ready           // Downstream ready
);

    // =========================================================================
    // State Machine Definitions
    // =========================================================================
    // Weight Loading FSM removed - timing controlled by comp_bram_fill_ctrl

    // Compute FSM
    typedef enum logic [2:0] {
        COMP_IDLE    = 3'b000,
        COMP_SETUP   = 3'b001,  // Setup cycle: rdaddr set, wait for BRAM
        COMP_STREAM  = 3'b010,
        COMP_DRAIN   = 3'b011
    } comp_state_t;

    // =========================================================================
    // Internal Signal Declarations
    // =========================================================================
    
    // Weight Loading Signals
    logic [255:0]  wt_man_reg [0:3];         // Latched weight mantissas (4 groups of 256 bits)
    logic [31:0]   wt_exp_reg;               // Latched weight exponents
    logic [3:0]    col_sel_reg;               // Latched column select
    logic [6:0]    wt_nv_idx_reg;              // Latched NV index within column for V>1

    // Compute FSM Signals
    comp_state_t comp_state_reg, comp_state_next;
    logic [1:0] comp_cycle_cnt;                // Compute cycle counter (0-3 for 4 cycles of streaming)
    logic [2:0] drain_cnt;                    // Drain counter for pipeline flush
    logic [6:0] nv_index;                      // NV index counter (tracks which NV within a dot product)
    logic [255:0]  act_man_reg [0:3];          // Latched activation mantissas (4 groups of 256 bits)
    logic [31:0]   act_exp_reg;                // Latched activation exponents
    logic          new_dot_reg;                // Latched new_dot flag
    logic          last_nv_reg;                // Latched last NV of batch flag

    // NOTE: Activation data is latched in COMP_IDLE for the first NV of a batch,
    // and then latched at NV boundaries while staying in COMP_STREAM for subsequent NVs.

    // Per-Stack Data Extraction Signals
    logic [63:0] wt_man_chunk [NUM_STACKS-1:0];    // Weight mantissa chunks per stack
    logic [7:0]  wt_exp_chunk [NUM_STACKS-1:0];    // Weight exponent chunks per stack
    logic [71:0] bram_din_stack [NUM_STACKS-1:0];  // BRAM input data per stack
    logic [63:0] act_man_chunk [NUM_STACKS-1:0];   // Activation mantissa chunks per stack
    logic [7:0]  act_exp_chunk [NUM_STACKS-1:0];   // Activation exponent chunks per stack
    logic [71:0] din_stack [NUM_STACKS-1:0];       // MLP input data per stack

    // Column to MLP/Bank Mapping Signals
    logic [2:0] mlp_index;                    // MLP index (col_sel / 2)
    logic       bank_sel;                      // Bank select (col_sel % 2)
    logic [NUM_MLPS-1:0] wren_wt;              // Weight write enable mask
    logic [9:0] wraddr_wt;                     // Weight write address

    // Compute Control Signals
    logic is_loading;                          // Currently loading weights
    logic is_streaming;                        // Currently streaming activations
    logic comp_ce;                             // Compute clock enable
    logic comp_accumulate;                     // Compute accumulate enable
    logic comp_load;                           // Compute load signal

    // MLP BRAM Column Interface Signals
    logic [9:0]          mlp_wraddr;          // MLP write address
    logic [NUM_MLPS-1:0] mlp_wren;            // MLP write enable
    logic [8:0]          mlp_rdaddr;          // MLP read address
    logic                mlp_ce;              // MLP clock enable
    logic                mlp_load;            // MLP load signal
    logic                mlp_accumulate;       // MLP accumulate signal
    logic [8:0]          nv_base_addr;        // NV base address for read

    // Stack Output Signals
    logic [71:0] stack_dout [NUM_STACKS-1:0][NUM_MLPS-1:0];  // Stack outputs

    // FP24 Extraction and Adder Pipeline Signals
    logic [23:0] fp24_bank0 [NUM_STACKS-1:0][NUM_MLPS-1:0];  // FP24 values for even columns
    logic [23:0] fp24_bank1 [NUM_STACKS-1:0][NUM_MLPS-1:0];   // FP24 values for odd columns
    logic [NUM_STACKS-1:0][23:0] adder_input_bank0 [NUM_MLPS-1:0];  // Adder inputs for bank 0
    logic [NUM_STACKS-1:0][23:0] adder_input_bank1 [NUM_MLPS-1:0];  // Adder inputs for bank 1
    logic [15:0] final_bank0 [NUM_MLPS-1:0];                   // Final FP16 outputs for bank 0
    logic [15:0] final_bank1 [NUM_MLPS-1:0];                   // Final FP16 outputs for bank 1
    logic adder_valid_bank0 [NUM_MLPS-1:0];                    // Adder valid for bank 0
    logic adder_valid_bank1 [NUM_MLPS-1:0];                    // Adder valid for bank 1
    logic [23:0] stack0_status_d1 [NUM_MLPS-1:0];              // Status bits pipeline delay 1
    logic [23:0] stack0_status_d2 [NUM_MLPS-1:0];              // Status bits pipeline delay 2
    logic [23:0] stack0_status_d3 [NUM_MLPS-1:0];              // Status bits pipeline delay 3
    logic [23:0] stack0_status_d4 [NUM_MLPS-1:0];               // Status bits pipeline delay 4
    logic drain_valid;                                          // Drain valid signal

    // Output Valid Pipeline Signals
    logic was_draining;                        // Was in DRAIN state
    logic was_last_nv;                         // Was last NV flag
    logic dout_valid_pre;                      // Pre-pipeline valid signal
    logic dout_valid_d1;                       // Pipeline delay stage 1
    logic dout_valid_d2;                       // Pipeline delay stage 2
    logic dout_valid_d3;                       // Pipeline delay stage 3
    logic dout_valid_d4;                       // Pipeline delay stage 4

    // =========================================================================
    // Per-Stack Data Extraction: Weight Data
    // =========================================================================
    // Each stack handles one 256-bit group (32 elements)
    // wt_cycle_cnt[1:0] selects 64-bit chunk within group (0-3)
    genvar s;
    generate
        for (s = 0; s < NUM_STACKS; s = s + 1) begin : gen_wt_extract
            always_comb begin
                // Select 64-bit mantissa chunk based on cycle count
                case (i_wt_cycle_cnt)
                    2'd0: wt_man_chunk[s] = wt_man_reg[s][63:0];
                    2'd1: wt_man_chunk[s] = wt_man_reg[s][127:64];
                    2'd2: wt_man_chunk[s] = wt_man_reg[s][191:128];
                    2'd3: wt_man_chunk[s] = wt_man_reg[s][255:192];
                    default: wt_man_chunk[s] = 64'd0;
                endcase

                // Each stack uses its own exponent (same for all 4 cycles within stack)
                wt_exp_chunk[s] = wt_exp_reg[s*8 +: 8];
            end

            // Pack into 72-bit bram_din format: {exp[7:0], man[63:0]}
            assign bram_din_stack[s] = {wt_exp_chunk[s], wt_man_chunk[s]};
        end
    endgenerate

    // =========================================================================
    // Per-Stack Data Extraction: Activation Data
    // =========================================================================
    generate
        for (s = 0; s < NUM_STACKS; s = s + 1) begin : gen_act_extract
            always_comb begin
                // Select 64-bit mantissa chunk based on cycle count
                case (comp_cycle_cnt)
                    2'd0: act_man_chunk[s] = act_man_reg[s][63:0];
                    2'd1: act_man_chunk[s] = act_man_reg[s][127:64];
                    2'd2: act_man_chunk[s] = act_man_reg[s][191:128];
                    2'd3: act_man_chunk[s] = act_man_reg[s][255:192];
                    default: act_man_chunk[s] = 64'd0;
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
    assign mlp_index = col_sel_reg[3:1];  // col_sel / 2
    assign bank_sel  = col_sel_reg[0];     // col_sel % 2

    // Generate wren mask (only one MLP enabled during weight loading)
    // Same wren broadcast to all 4 stacks
    assign wren_wt = i_wt_loading ?
        ({{(NUM_MLPS-1){1'b0}}, 1'b1} << mlp_index) : {NUM_MLPS{1'b0}};

    // Generate wraddr:
    //   With 4 stacks, each stack stores 32 elements (4 cycles worth)
    //   Address layout: i_wt_base_addr + {wt_nv_idx[6:0], wt_cycle_cnt[1:0], ~bank_sel}
    //   Bank mapping (for asymmetric BRAM read/write):
    //     - Even column (bank_sel=0): wraddr[0]=1 → odd slot → BRAM upper [143:72] → Bank AB
    //     - Odd column (bank_sel=1): wraddr[0]=0 → even slot → BRAM lower [71:0] → Bank CD
    //   This inverted mapping means: even columns → Bank AB, odd columns → Bank CD
    //   The extraction in compute_engine_mlp.sv must match this mapping.
    //   - NV 0: addresses base+0 to base+7 (4 cycles × 2 banks)
    //   - NV 1: addresses base+8 to base+15
    //   - etc.
    assign wraddr_wt = i_wt_base_addr + {wt_nv_idx_reg[6:0], i_wt_cycle_cnt, ~bank_sel};

    // =========================================================================
    // Compute Control Signal Generation
    // =========================================================================
    assign is_loading = i_wt_loading;
    assign is_streaming = (comp_state_reg == COMP_STREAM);

    // ce: Active during streaming AND drain
    assign comp_ce = (comp_state_reg == COMP_STREAM) || (comp_state_reg == COMP_DRAIN);

    // accumulate:
    // - For the first NV of a dot (new_dot_reg=1), keep the original behavior (enable after cycle 0)
    // - For subsequent NVs (new_dot_reg=0), accumulate on *all* STREAM cycles, including cycle 0
    //   because the pipeline is already active across NV boundaries.
    assign comp_accumulate = ((comp_state_reg == COMP_STREAM) &&
                              (new_dot_reg ? (comp_cycle_cnt > 2'd0) : 1'b1)) ||
                             (comp_state_reg == COMP_DRAIN);

    // load: Pulse at cycle 2 for new dot product (accounts for pipeline latency)
    // With 4 cycles, load at cycle 2 is still valid (cycles 0,1,2,3)
    assign comp_load = (comp_state_reg == COMP_STREAM) &&
                       (comp_cycle_cnt == PIPELINE_LATENCY[1:0]) && new_dot_reg;

    // =========================================================================
    // MLP BRAM Column Signal Muxing (shared across all stacks)
    // =========================================================================
    assign mlp_wraddr = is_loading ? wraddr_wt : 10'b0;
    assign mlp_wren   = wren_wt;

    // rdaddr: For V>1, weights are stored at rd_base_addr + nv_index * 4 + word offset
    // NOTE: rd_base_addr is in 10-bit write address space, needs >>1 for 9-bit read space
    assign nv_base_addr = i_rd_base_addr[9:1] + {nv_index[6:0], 2'd0};  // (rd_base>>1) + nv_index * 4

    always_comb begin
        if (is_loading) begin
            mlp_rdaddr = 9'b0;
        end else if (comp_state_reg == COMP_SETUP) begin
            mlp_rdaddr = nv_base_addr;
        end else if (comp_state_reg == COMP_STREAM) begin
            // BRAM is 1-cycle latency; rdaddr is the "next" word.
            // On the last subcycle of a non-last NV, switch rdaddr to the next NV base
            // to eliminate a per-NV setup bubble.
            if ((comp_cycle_cnt == 2'd3) && !last_nv_reg) begin
                mlp_rdaddr = (i_rd_base_addr[9:1] + {(nv_index + 7'd1), 2'd0});
            end else begin
                mlp_rdaddr = nv_base_addr + {7'd0, comp_cycle_cnt} + 9'd1;
            end
        end else begin
            mlp_rdaddr = 9'b0;
        end
    end

    assign mlp_ce         = is_loading ? 1'b1 : comp_ce;
    assign mlp_load       = is_loading ? 1'b0 : comp_load;
    assign mlp_accumulate = is_loading ? 1'b0 : comp_accumulate;

    // =========================================================================
    // Weight Data Latching (FSM removed - timing controlled by comp_bram_fill_ctrl)
    // =========================================================================
    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            wt_man_reg[0]  <= 256'b0;
            wt_man_reg[1]  <= 256'b0;
            wt_man_reg[2]  <= 256'b0;
            wt_man_reg[3]  <= 256'b0;
            wt_exp_reg     <= 32'b0;
            col_sel_reg    <= 4'd0;
            wt_nv_idx_reg  <= 7'd0;
        end else begin
            // Latch data when i_wt_valid is asserted
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
    end
    
    // Debug: Weight writes (in separate always block to show current-cycle values)
    // `ifdef SIMULATION
    // always @(posedge clk) begin
    //     if (i_wt_valid) begin
    //         $display("[MLP_WR] @%0t COL=%0d NV_IDX=%0d CYCLE=%0d BASE_ADDR=%0d LOADING=%0b",
    //                  $time, i_col_sel, i_wt_nv_idx, i_wt_cycle_cnt, i_wt_base_addr, i_wt_loading);
    //     end
    // end
    // `endif

    // =========================================================================
    // Compute FSM: State Transition Logic
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
                // 4 cycles per NV. Drain only once at end of batch (last_nv).
                if (comp_cycle_cnt == 2'd3) begin
                    if (last_nv_reg) begin
                    comp_state_next = COMP_DRAIN;
                    end else begin
                        comp_state_next = COMP_STREAM;
                    end
                end
            end

            COMP_DRAIN: begin
                // Shorter drain since pipeline is same depth
                if (drain_cnt == 3'd2) begin
                    comp_state_next = COMP_IDLE;
                end
            end

            default: begin
                comp_state_next = COMP_IDLE;
            end
        endcase
    end

    // =========================================================================
    // Compute FSM: Sequential State Update
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
                        // Start of batch/dot product always begins at NV index 0 for weight reads
                            nv_index <= 7'd0;
                    end
                end

                COMP_SETUP: begin
                    // Setup cycle: rdaddr set, BRAM reads weights
                    // No counter updates
                end

                COMP_STREAM: begin
                    if (comp_cycle_cnt == 2'd3) begin
                        // NV boundary: wrap the subcycle counter.
                        comp_cycle_cnt <= 2'd0;

                        // If not last NV, latch next activation payload and advance weight index.
                        if (!last_nv_reg && i_act_valid && !is_loading) begin
                            act_man_reg[0] <= i_nv_left_man[0];
                            act_man_reg[1] <= i_nv_left_man[1];
                            act_man_reg[2] <= i_nv_left_man[2];
                            act_man_reg[3] <= i_nv_left_man[3];
                            act_exp_reg <= i_nv_left_exp;
                            new_dot_reg <= i_new_dot;
                            last_nv_reg <= i_last_nv;
                            nv_index    <= nv_index + 7'd1;
                        end
                    end else begin
                    comp_cycle_cnt <= comp_cycle_cnt + 2'd1;
                    end
                end

                COMP_DRAIN: begin
                    drain_cnt <= drain_cnt + 3'd1;
                end

                default: begin
                    // No updates in default state
                end
            endcase
        end
    end

    // =========================================================================
    // Ready-Valid Signals
    // =========================================================================
    assign o_wt_ready = !i_wt_loading;  // Ready when not currently loading
    // Ready exactly once per NV, preserving handshake semantics as "NV consumed".
    // - In IDLE: accept first NV of a batch.
    // - In STREAM: accept at NV boundary (end of subcycle 3), including last_nv (consumption).
    assign o_act_ready = !is_loading &&
                         ((comp_state_reg == COMP_IDLE) ||
                          ((comp_state_reg == COMP_STREAM) && (comp_cycle_cnt == 2'd3)));

    // =========================================================================
    // Output Valid Pipeline
    // =========================================================================
    // Pulse o_dout_valid for exactly 1 cycle when result is ready
    // Result is ready when transitioning from DRAIN to IDLE AND this was the last NV of batch
    // NOTE: Valid signal is delayed by 4 cycles to match pipelined FP24 adder tree
    //       (2 cycles per level × 2 levels = 4 cycles total)
    assign drain_valid = (comp_state_reg == COMP_DRAIN);

    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            was_draining   <= 1'b0;
            was_last_nv    <= 1'b0;
            dout_valid_d1  <= 1'b0;
            dout_valid_d2  <= 1'b0;
            dout_valid_d3  <= 1'b0;
            dout_valid_d4  <= 1'b0;
        end else begin
            was_draining <= (comp_state_reg == COMP_DRAIN);
            // Capture last_nv_reg at end of DRAIN so it's valid when we check in IDLE
            if (comp_state_reg == COMP_DRAIN) begin
                was_last_nv <= last_nv_reg;
            end
            // 4-stage pipeline delay to match adder tree latency
            dout_valid_d1 <= dout_valid_pre;
            dout_valid_d2 <= dout_valid_d1;
            dout_valid_d3 <= dout_valid_d2;
            dout_valid_d4 <= dout_valid_d3;
        end
    end

    // Pre-pipeline valid: pulse when entering IDLE from DRAIN AND this was the last NV
    assign dout_valid_pre = (comp_state_reg == COMP_IDLE) && was_draining && was_last_nv && !is_loading;
    // Output valid delayed by 4 cycles to align with pipelined adder tree output
    assign o_dout_valid = dout_valid_d4;

    // =========================================================================
    // MLP BRAM Column Instances (4 stacks)
    // =========================================================================
    generate
        for (s = 0; s < NUM_STACKS; s = s + 1) begin : gen_mlp_stack
            // Per-stack din: zero during loading, activation during streaming
            logic [71:0] stack_din;
            assign stack_din = (is_loading || !is_streaming) ? 72'b0 : din_stack[s];

            // Per-stack expb: zero during loading, activation exponent during streaming
            logic [7:0] stack_expb;
            assign stack_expb = (is_loading || !is_streaming) ? 8'b0 : act_exp_chunk[s];

            comp_mlp_bram_col #(
                .NUM_MLPS(NUM_MLPS)
            ) u_mlp_bram_col (
                .clk(clk),
                .rstn(rstn),
                .ce(mlp_ce),
                .din(stack_din),
                .load(mlp_load),
                .accumulate(mlp_accumulate),
                .expb(stack_expb),              // BFP activation exponent
                .bram_din(bram_din_stack[s]),
                .wraddr(mlp_wraddr),
                .wren(mlp_wren),
                .rdaddr(mlp_rdaddr),
                .dout(stack_dout[s])
            );
        end
    endgenerate

    // =========================================================================
    // FP24 Extraction from Stack Outputs
    // =========================================================================
    generate
        for (s = 0; s < NUM_STACKS; s = s + 1) begin : gen_fp24_extract
            for (genvar m = 0; m < NUM_MLPS; m = m + 1) begin : gen_mlp_fp24
                assign fp24_bank0[s][m] = stack_dout[s][m][23:0];   // Bank CD (even columns)
                assign fp24_bank1[s][m] = stack_dout[s][m][47:24];  // Bank AB (odd columns)
            end
        end
    endgenerate

    // =========================================================================
    // Repack FP24 Inputs for Adder Pipeline
    // =========================================================================
    generate
        for (genvar m = 0; m < NUM_MLPS; m = m + 1) begin : gen_repack
            for (genvar s = 0; s < NUM_STACKS; s = s + 1) begin : gen_stack_repack
                assign adder_input_bank0[m][s] = fp24_bank0[s][m];
                assign adder_input_bank1[m][s] = fp24_bank1[s][m];
            end
        end
    endgenerate

    // =========================================================================
    // Integer-Domain FP Adder Pipeline: Combine 4 partial results per column
    // =========================================================================
    // Each MLP produces 2 FP24 results (Bank 0 and Bank 1)
    // New approach: Convert FP24→Int→Sum→FP16 for single rounding point
    // 
    // Architecture:
    //   - 4 FP24 inputs from stacks → fp_to_int (1 cycle)
    //   - Integer adder tree (1 cycle for 2 levels)
    //   - int_to_fp with RNE rounding (2 cycles)
    //   - Total latency: 4 cycles (same as before)
    //   - Output: FP16 (eliminates downstream fp24_to_fp16 conversion)
    generate
        for (genvar m = 0; m < NUM_MLPS; m = m + 1) begin : gen_adder_tree
            // Integer-Domain FP Adder Pipeline for Bank 0 (even columns)
            comp_fp_adder_pipeline #(
                .NUM_INPUTS(4),
                .FP_IN_WIDTH(24),
                .FP_OUT_WIDTH(16),
                .INT_WIDTH(64),
                .FRAC_BITS(32),      // 32-bit fractional: 256x better precision
                .SEG_LEN(2)
            ) u_adder_bank0 (
                .clk(clk),
                .rst_n(rstn),
                .en(1'b1),
                .i_fp(adder_input_bank0[m]),
                .i_valid(drain_valid),
                .o_fp(final_bank0[m]),
                .o_valid(adder_valid_bank0[m])
            );

            // Integer-Domain FP Adder Pipeline for Bank 1 (odd columns)
            comp_fp_adder_pipeline #(
                .NUM_INPUTS(4),
                .FP_IN_WIDTH(24),
                .FP_OUT_WIDTH(16),
                .INT_WIDTH(64),
                .FRAC_BITS(32),      // 32-bit fractional: 256x better precision
                .SEG_LEN(2)
            ) u_adder_bank1 (
                .clk(clk),
                .rst_n(rstn),
                .en(1'b1),
                .i_fp(adder_input_bank1[m]),
                .i_valid(drain_valid),
                .o_fp(final_bank1[m]),
                .o_valid(adder_valid_bank1[m])
            );

            // Status bits pipeline (4 cycles to match adder tree latency)
            always_ff @(posedge clk or negedge rstn) begin
                if (!rstn) begin
                    stack0_status_d1[m] <= 24'd0;
                    stack0_status_d2[m] <= 24'd0;
                    stack0_status_d3[m] <= 24'd0;
                    stack0_status_d4[m] <= 24'd0;
                end else begin
                    stack0_status_d1[m] <= drain_valid ? stack_dout[0][m][71:48] : stack0_status_d1[m];
                    stack0_status_d2[m] <= stack0_status_d1[m];
                    stack0_status_d3[m] <= stack0_status_d2[m];
                    stack0_status_d4[m] <= stack0_status_d3[m];
                end
            end

            // Combine into output format
            // NOTE: Results are now FP16 instead of FP24!
            // dout[15:0] = Bank 0 result (FP16)
            // dout[31:16] = Bank 1 result (FP16)
            // dout[55:32] = status bits (24 bits, delayed to match 4-cycle pipeline)
            // dout[71:56] = padding (unused)
            assign o_dout[m] = {16'd0, stack0_status_d4[m], final_bank1[m], final_bank0[m]};
        end
    endgenerate

    // =========================================================================
    // Debug Output
    // =========================================================================
    // synthesis translate_off
    logic [2:0] comp_state_prev;
    logic       wt_loading_prev;
    always @(posedge clk) begin
        comp_state_prev <= comp_state_reg;
        wt_loading_prev <= i_wt_loading;

        // Report state changes
        // if (comp_state_reg != comp_state_prev) begin
        //     $display("[MLP_CTRL_COMP] @%0t state=%0d->%0d, act_valid=%b, is_loading=%b, last_nv=%b, rd_base=%0d, nv_idx=%0d",
        //              $time, comp_state_prev, comp_state_reg, i_act_valid, is_loading, i_last_nv, i_rd_base_addr, nv_index);
        // end
        // // Report STREAM read addresses
        // if (comp_state_reg == COMP_STREAM) begin
        //     $display("[MLP_CTRL_READ] @%0t STREAM cycle=%0d: rd_base=%0d, nv_idx=%0d, nv_base=%0d, mlp_rdaddr=%0d",
        //              $time, comp_cycle_cnt, i_rd_base_addr, nv_index, nv_base_addr, mlp_rdaddr);
        // end
        // // Report weight loading state changes
        // if (i_wt_loading && !wt_loading_prev) begin
        //     $display("[MLP_CTRL_WT] @%0t LOAD_START: cycle_cnt=%0d", $time, i_wt_cycle_cnt);
        // end else if (!i_wt_loading && wt_loading_prev) begin
        //     $display("[MLP_CTRL_WT] @%0t LOAD_END", $time);
        // end

        // // Report when result is valid
        // if (o_dout_valid) begin
        //     $display("[MLP_CTRL] @%0t DOUT_VALID: was_draining=%b, was_last_nv=%b, is_loading=%b",
        //              $time, was_draining, was_last_nv, is_loading);
        //     // Show Bank 0 (CD) and Bank 1 (AB) values for first 4 MLPs
        //     $display("[MLP_CTRL] @%0t MLP0: bank0(CD)=0x%06x bank1(AB)=0x%06x o_dout=0x%018x",
        //              $time, final_bank0[0], final_bank1[0], o_dout[0]);
        //     $display("[MLP_CTRL] @%0t MLP1: bank0(CD)=0x%06x bank1(AB)=0x%06x o_dout=0x%018x",
        //              $time, final_bank0[1], final_bank1[1], o_dout[1]);
        //     $display("[MLP_CTRL] @%0t MLP2: bank0(CD)=0x%06x bank1(AB)=0x%06x o_dout=0x%018x",
        //              $time, final_bank0[2], final_bank1[2], o_dout[2]);
        //     $display("[MLP_CTRL] @%0t MLP3: bank0(CD)=0x%06x bank1(AB)=0x%06x o_dout=0x%018x",
        //              $time, final_bank0[3], final_bank1[3], o_dout[3]);
        // end

        // // Report act_ready signal
        // if (o_act_ready && i_act_valid) begin
        //     $display("[MLP_CTRL] @%0t ACT_HANDSHAKE: act_valid=%b, act_ready=%b, new_dot=%b, last_nv=%b",
        //              $time, i_act_valid, o_act_ready, i_new_dot, i_last_nv);
        // end

        // // Report weight BRAM writes (enable for debugging tile_addr issues)
        // if (i_wt_loading && |wren_wt) begin
        //     $display("[MLP_BRAM_WT_WR] @%0t WRITE: mlp_idx=%0d, col_sel=%0d, bank_sel=%0d, wraddr=%0d, wt_base=%0d, wt_nv_idx=%0d, cycle=%0d",
        //              $time, mlp_index, col_sel_reg, bank_sel, wraddr_wt, i_wt_base_addr, wt_nv_idx_reg, i_wt_cycle_cnt);
        // end
        // // Report weight BRAM reads
        // if (comp_state_reg == COMP_STREAM || comp_state_reg == COMP_SETUP) begin
        //     $display("[MLP_BRAM_WT_RD] @%0t READ: state=%0d, rdaddr=%0d, rd_base=%0d, nv_idx=%0d, nv_base=%0d, cycle=%0d",
        //              $time, comp_state_reg, mlp_rdaddr, i_rd_base_addr, nv_index, nv_base_addr, comp_cycle_cnt);
        // end
    end
    // synthesis translate_on

endmodule

`default_nettype wire
