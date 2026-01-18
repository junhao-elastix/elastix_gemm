// ------------------------------------------------------------------
// MLP BRAM Column Controller - FIFO-Decoupled Architecture
//
// Architecture: 4 × mlp_bram_col stacked in parallel with FIFO decoupling
//   - Each stack handles 32 elements (one 256-bit mantissa group + 8-bit exponent)
//   - All 4 stacks process in parallel: 4× throughput
//   - FIFOs between MLP outputs and adder tree for timing decoupling
//   - Integer-domain FP adder pipeline sums partial results
//
// FIFO Architecture:
//   - 32 FIFOs total (4 stacks × 8 MLPs)
//   - Each FIFO is 48 bits wide (2 × FP24 for bank0 and bank1)
//   - Depth: 4 entries (sufficient for timing jitter absorption)
//   - FWFT (First Word Fall Through) for zero-latency read
//   - Backpressure: MLP stalls if FIFOs full
//
// Data Flow:
//   MLP Stack[s][m] → FIFO[s][m] → Adder Tree[m] → FP16 Output
//
// Weight Loading:
//   - 4 cycles to load one NV (vs 16 cycles with single stack)
//   - Each stack receives different 32-element group
//   - Same wren broadcast to all stacks
//
// Compute:
//   - 4 cycles of streaming (vs 16 with single stack)
//   - Each stack computes partial 32-element dot product
//   - Results pushed to FIFOs when drain completes
//   - Adder tree pops from FIFOs when all 4 stacks have data
//
// Output: 16 × FP16 results (packed as 8 × 32-bit words)
//
// Pipeline Latency:
//   - MLP internal pipeline: 2 cycles
//   - FIFO: 0 cycles (FWFT)
//   - Adder pipeline: 4 cycles (1 fp_to_int + 1 adder + 2 int_to_fp)
//
// FSM States (Continuous Operation Architecture):
//   - COMP_IDLE: Waiting for first activation data (i_act_valid)
//   - COMP_RUNNING: Continuous B×C×V operation, streaming activations through MLP
//   - COMP_FINAL_DRAIN: Only after truly last dot product (i_last_matmul=1)
//
// Key optimization: No per-dot-product DRAIN bubbles.
// Results are captured via pipeline delay and pushed to FIFO every V×4 cycles.
//
// Author: Refactored for FIFO-based decoupling
// Date: Jan 16, 2026
// ------------------------------------------------------------------

`timescale 1ps / 1ps
`default_nettype none

module comp_mlp_bram_col_wrapper #(
    parameter integer NUM_MLPS = 8,
    parameter integer NUM_STACKS = 4,           // 4 parallel stacks
    parameter integer CYCLES_PER_NV = 4,        // 4 cycles per NV (32 elements / 8 per cycle)
    parameter integer PIPELINE_LATENCY = 2,     // MLP pipeline latency for load timing
    parameter integer FIFO_DEPTH = 4            // FIFO depth for timing decoupling
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
    input  logic        i_last_nv,            // This is the last NV of the current dot product
    input  logic        i_last_matmul,        // Truly last dot product of entire TILE (triggers final drain)

    // =========================================================================
    // Result Interface (downstream)
    // =========================================================================
    output logic [71:0] o_dout [NUM_MLPS-1:0], // MLP outputs (combined from 4 stacks)
    output logic        o_dout_valid,          // Results valid
    input  logic        i_dout_ready           // Downstream ready
);

    // =========================================================================
    // Address Space Constants
    // =========================================================================
    localparam WRADDR_WIDTH = 10;
    localparam RDADDR_WIDTH = 9;
    localparam NV_SIZE_IN_WORDS = 4;
    localparam FIFO_WIDTH = 48;  // 2 × FP24 (bank0 + bank1)

    // =========================================================================
    // State Machine Definitions (3-state continuous operation)
    // =========================================================================
    typedef enum logic [1:0] {
        COMP_IDLE        = 2'b00,  // Waiting for first activation
        COMP_RUNNING     = 2'b01,  // Continuous B×C×V operation
        COMP_FINAL_DRAIN = 2'b10   // Only after truly last dot product
    } comp_state_t;

    // =========================================================================
    // Internal Signal Declarations
    // =========================================================================

    // Weight Loading Registers
    logic [255:0]  wt_man_reg [0:3];
    logic [31:0]   wt_exp_reg;
    logic [3:0]    col_sel_reg;
    logic [6:0]    wt_nv_idx_reg;

    // Compute FSM Signals
    comp_state_t comp_state_reg, comp_state_next;
    logic [1:0] comp_cycle_cnt;
    logic [2:0] drain_cnt;
    logic [6:0] nv_index;
    logic [255:0]  act_man_reg [0:3];
    logic [31:0]   act_exp_reg;
    logic          new_dot_reg;
    logic          last_nv_reg;

    // Per-Stack Data Extraction Signals
    logic [63:0] wt_man_chunk [NUM_STACKS-1:0];
    logic [7:0]  wt_exp_chunk [NUM_STACKS-1:0];
    logic [71:0] bram_din_stack [NUM_STACKS-1:0];
    logic [63:0] act_man_chunk [NUM_STACKS-1:0];
    logic [7:0]  act_exp_chunk [NUM_STACKS-1:0];
    logic [71:0] din_stack [NUM_STACKS-1:0];

    // Column to MLP/Bank Mapping Signals
    logic [2:0] mlp_index;
    logic       bank_sel;
    logic [NUM_MLPS-1:0] wt_write_enable;
    logic [9:0] wt_write_addr;

    // MLP BRAM Column Interface Signals
    logic [9:0]          mlp_wraddr;
    logic [NUM_MLPS-1:0] mlp_wren;
    logic [8:0]          mlp_rdaddr;
    logic                mlp_ce;
    logic                mlp_load;
    logic                mlp_accumulate;
    logic [8:0]          wt_rd_base_addr;

    // Stack Output Signals
    logic [71:0] stack_dout [NUM_STACKS-1:0][NUM_MLPS-1:0];

    // =========================================================================
    // FIFO Signals (NEW: FIFO-based decoupling)
    // =========================================================================
    // FIFO data: 48 bits = {fp24_bank1[23:0], fp24_bank0[23:0]}
    logic [FIFO_WIDTH-1:0] fifo_din  [NUM_STACKS-1:0][NUM_MLPS-1:0];
    logic [FIFO_WIDTH-1:0] fifo_dout [NUM_STACKS-1:0][NUM_MLPS-1:0];
    logic                  fifo_push [NUM_STACKS-1:0][NUM_MLPS-1:0];
    logic                  fifo_pop  [NUM_STACKS-1:0][NUM_MLPS-1:0];
    logic                  fifo_full [NUM_STACKS-1:0][NUM_MLPS-1:0];
    logic                  fifo_empty[NUM_STACKS-1:0][NUM_MLPS-1:0];

    // FIFO synchronization signals
    logic fifo_any_full;      // Any FIFO is full (backpressure)
    logic fifo_all_ready;     // All FIFOs have data (can pop)
    logic fifo_pop_enable;    // Pop from all FIFOs

    // Adder Pipeline Signals (from FIFOs instead of direct stack output)
    logic [23:0] fifo_fp24_bank0 [NUM_STACKS-1:0][NUM_MLPS-1:0];
    logic [23:0] fifo_fp24_bank1 [NUM_STACKS-1:0][NUM_MLPS-1:0];
    logic [NUM_STACKS-1:0][23:0] adder_input_bank0 [NUM_MLPS-1:0];
    logic [NUM_STACKS-1:0][23:0] adder_input_bank1 [NUM_MLPS-1:0];
    logic [15:0] final_bank0 [NUM_MLPS-1:0];
    logic [15:0] final_bank1 [NUM_MLPS-1:0];

    // Valid pipeline for adder output
    logic adder_input_valid;
    logic adder_output_valid;

    // Drain and output signals
    logic drain_valid;
    logic fifo_push_valid;

    // Registered last_matmul for final drain detection
    logic last_matmul_reg;

    // Capture delay pipeline: accounts for MLP 2-cycle pipeline latency
    // When a dot product completes (last_nv at cycle 3), we wait 2 cycles for result
    logic [1:0] capture_delay;
    logic dot_complete_pulse;

    // Named conditions for clearer logic
    logic in_running;
    logic in_final_drain;
    logic first_cycle_of_new_dot;

    // =========================================================================
    // Named Conditions
    // =========================================================================
    assign in_running     = (comp_state_reg == COMP_RUNNING);
    assign in_final_drain = (comp_state_reg == COMP_FINAL_DRAIN);
    assign first_cycle_of_new_dot = new_dot_reg && (comp_cycle_cnt == 2'd0);

    // Dot product completion detection: true when at last cycle of last NV
    logic dot_complete_condition;
    assign dot_complete_condition = in_running && (comp_cycle_cnt == 2'd3) && last_nv_reg &&
                                    !last_matmul_reg && !fifo_any_full;

    // Dot product completion pulse: edge detect to fire only once when condition becomes true
    // This triggers capture delay pipeline for INTERMEDIATE results only
    logic dot_complete_condition_d;
    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            dot_complete_condition_d <= 1'b0;
        end else begin
            dot_complete_condition_d <= dot_complete_condition;
        end
    end

    // Rising edge detection: pulse fires once when we first reach the end of a dot product
    assign dot_complete_pulse = dot_complete_condition && !dot_complete_condition_d;

    // =========================================================================
    // Per-Stack Data Extraction: Weight Data
    // =========================================================================
    genvar s;
    generate
        for (s = 0; s < NUM_STACKS; s = s + 1) begin : gen_wt_extract
            always_comb begin
                case (i_wt_cycle_cnt)
                    2'd0: wt_man_chunk[s] = wt_man_reg[s][63:0];
                    2'd1: wt_man_chunk[s] = wt_man_reg[s][127:64];
                    2'd2: wt_man_chunk[s] = wt_man_reg[s][191:128];
                    2'd3: wt_man_chunk[s] = wt_man_reg[s][255:192];
                    default: wt_man_chunk[s] = 64'd0;
                endcase
                wt_exp_chunk[s] = wt_exp_reg[s*8 +: 8];
            end
            assign bram_din_stack[s] = {wt_exp_chunk[s], wt_man_chunk[s]};
        end
    endgenerate

    // =========================================================================
    // Per-Stack Data Extraction: Activation Data
    // =========================================================================
    generate
        for (s = 0; s < NUM_STACKS; s = s + 1) begin : gen_act_extract
            always_comb begin
                case (comp_cycle_cnt)
                    2'd0: act_man_chunk[s] = act_man_reg[s][63:0];
                    2'd1: act_man_chunk[s] = act_man_reg[s][127:64];
                    2'd2: act_man_chunk[s] = act_man_reg[s][191:128];
                    2'd3: act_man_chunk[s] = act_man_reg[s][255:192];
                    default: act_man_chunk[s] = 64'd0;
                endcase
                act_exp_chunk[s] = act_exp_reg[s*8 +: 8];
            end
            assign din_stack[s] = {act_exp_chunk[s], act_man_chunk[s]};
        end
    endgenerate

    // =========================================================================
    // Column to MLP/Bank Mapping (for weight loading)
    // =========================================================================
    assign mlp_index = col_sel_reg[3:1];
    assign bank_sel  = col_sel_reg[0];
    assign wt_write_enable = i_wt_loading ?
        ({{(NUM_MLPS-1){1'b0}}, 1'b1} << mlp_index) : {NUM_MLPS{1'b0}};
    assign wt_write_addr = i_wt_base_addr + {wt_nv_idx_reg[6:0], i_wt_cycle_cnt, ~bank_sel};

    // =========================================================================
    // MLP BRAM Column Signal Muxing
    // =========================================================================
    assign mlp_wraddr = i_wt_loading ? wt_write_addr : 10'b0;
    assign mlp_wren   = wt_write_enable;
    assign wt_rd_base_addr = i_rd_base_addr[9:1] + {nv_index[6:0], 2'd0};

    always_comb begin
        if (i_wt_loading) begin
            mlp_rdaddr = 9'b0;
        end else if (in_running) begin
            // In RUNNING state: continuous streaming
            if ((comp_cycle_cnt == 2'd3) && !last_nv_reg) begin
                // Prepare for next NV read
                mlp_rdaddr = (i_rd_base_addr[9:1] + {(nv_index + 7'd1), 2'd0});
            end else if (comp_cycle_cnt == 2'd0) begin
                // First cycle: set base address
                mlp_rdaddr = wt_rd_base_addr;
            end else begin
                // Cycles 1-3: increment from base
                mlp_rdaddr = wt_rd_base_addr + {7'd0, comp_cycle_cnt};
            end
        end else begin
            mlp_rdaddr = 9'b0;
        end
    end

    // =========================================================================
    // Backpressure: Check if any FIFO is full
    // =========================================================================
    always_comb begin
        fifo_any_full = 1'b0;
        for (int ss = 0; ss < NUM_STACKS; ss++) begin
            for (int mm = 0; mm < NUM_MLPS; mm++) begin
                fifo_any_full = fifo_any_full | fifo_full[ss][mm];
            end
        end
    end

    // Stall condition: waiting for data at NV boundary (cycle 3)
    // Stall when we're at cycle 3 in RUNNING but no valid data is available
    logic stalling;
    assign stalling = in_running && (comp_cycle_cnt == 2'd3) &&
                      ((last_nv_reg && !last_matmul_reg && !(i_act_valid && i_new_dot)) ||  // Wait for next dot
                       (!last_nv_reg && !i_act_valid));                                      // Wait for next NV

    // MLP enable gated by backpressure only (NOT stalling - MLP needs to finish pipeline during stalls)
    assign mlp_ce = (i_wt_loading || in_running || in_final_drain) && !fifo_any_full;

    // Load signal: initialize accumulator at start of new dot product
    assign mlp_load = in_running && (comp_cycle_cnt == PIPELINE_LATENCY[1:0]) && new_dot_reg && !fifo_any_full;

    // Accumulate signal: active during streaming and final drain
    // Per MLP reference: accumulate=0 ONLY at cycle 0 of new_dot, accumulate=1 for all other cycles
    // CRITICAL: accumulate and load CAN both be 1 simultaneously at cycle 2 (per Python reference)
    assign mlp_accumulate = (in_final_drain ||
                             (in_running && !first_cycle_of_new_dot)) &&
                            !fifo_any_full && !stalling;

    // =========================================================================
    // Weight Data Latching
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

    // =========================================================================
    // Compute FSM: State Transition Logic (3-state continuous operation)
    // =========================================================================
    always_comb begin
        comp_state_next = comp_state_reg;

        case (comp_state_reg)
            COMP_IDLE: begin
                // Start running on first valid activation (when not loading weights)
                if (i_act_valid && !i_wt_loading && !fifo_any_full) begin
                    comp_state_next = COMP_RUNNING;
                end
            end

            COMP_RUNNING: begin
                // Stay in RUNNING between dot products
                // Only exit on truly last NV of last dot product (i_last_matmul=1)
                if (!fifo_any_full && comp_cycle_cnt == 2'd3 && last_nv_reg && last_matmul_reg) begin
                    comp_state_next = COMP_FINAL_DRAIN;
                end
                // Otherwise: stay in RUNNING (including between dot products)
            end

            COMP_FINAL_DRAIN: begin
                // Final drain only happens once at the very end
                if (!fifo_any_full && drain_cnt == 3'd2) begin
                    comp_state_next = COMP_IDLE;
                end
            end

            default: begin
                comp_state_next = COMP_IDLE;
            end
        endcase
    end

    // =========================================================================
    // Compute FSM: Sequential State Update (with backpressure)
    // =========================================================================
    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            comp_state_reg   <= COMP_IDLE;
            comp_cycle_cnt   <= 2'd0;
            drain_cnt        <= 3'd0;
            act_man_reg[0]   <= 256'b0;
            act_man_reg[1]   <= 256'b0;
            act_man_reg[2]   <= 256'b0;
            act_man_reg[3]   <= 256'b0;
            act_exp_reg      <= 32'b0;
            new_dot_reg      <= 1'b0;
            last_nv_reg      <= 1'b0;
            last_matmul_reg  <= 1'b0;
            nv_index         <= 7'd0;
            capture_delay    <= 2'b00;
        end else if (!fifo_any_full) begin
            // Only advance state when not stalled by backpressure
            comp_state_reg <= comp_state_next;

            // Capture delay pipeline: shift register for dot product completion
            capture_delay <= {capture_delay[0], dot_complete_pulse};

            case (comp_state_reg)
                COMP_IDLE: begin
                    comp_cycle_cnt   <= 2'd0;
                    drain_cnt        <= 3'd0;
                    capture_delay    <= 2'b00;
                    if (i_act_valid && !i_wt_loading) begin
                        // Latch first activation and transition to RUNNING
                        act_man_reg[0]  <= i_nv_left_man[0];
                        act_man_reg[1]  <= i_nv_left_man[1];
                        act_man_reg[2]  <= i_nv_left_man[2];
                        act_man_reg[3]  <= i_nv_left_man[3];
                        act_exp_reg     <= i_nv_left_exp;
                        new_dot_reg     <= i_new_dot;
                        last_nv_reg     <= i_last_nv;
                        last_matmul_reg <= i_last_matmul;
                        nv_index        <= 7'd0;
                        `ifdef SIMULATION
                        $display("[WRAPPER_DBG] @%0t IDLE->RUNNING first NV: i_last_nv=%0b i_new_dot=%0b",
                                 $time, i_last_nv, i_new_dot);
                        `endif
                    end
                end

                COMP_RUNNING: begin
                    // Continuous streaming: cycle through 0-3 for each NV
                    if (comp_cycle_cnt == 2'd3) begin
                        comp_cycle_cnt <= 2'd0;
                        // At NV boundary: check if more NVs or more dot products
                        if (last_nv_reg) begin
                            // End of current dot product
                            `ifdef SIMULATION
                            $display("[WRAPPER_DBG] @%0t END_DOT: last_matmul_reg=%0b i_act_valid=%0b i_wt_loading=%0b",
                                     $time, last_matmul_reg, i_act_valid, i_wt_loading);
                            `endif
                            if (!last_matmul_reg) begin
                                // More dot products coming: accept next NV at boundary
                                // CRITICAL: Only latch when i_new_dot=1 (scheduler has new dot product data)
                                if (i_act_valid && !i_wt_loading && i_new_dot) begin
                                    act_man_reg[0]  <= i_nv_left_man[0];
                                    act_man_reg[1]  <= i_nv_left_man[1];
                                    act_man_reg[2]  <= i_nv_left_man[2];
                                    act_man_reg[3]  <= i_nv_left_man[3];
                                    act_exp_reg     <= i_nv_left_exp;
                                    new_dot_reg     <= i_new_dot;
                                    last_nv_reg     <= i_last_nv;
                                    last_matmul_reg <= i_last_matmul;
                                    nv_index        <= 7'd0;  // Reset for new dot product
                                    `ifdef SIMULATION
                                    $display("[WRAPPER_DBG] @%0t NEXT_DOT latch: i_last_nv=%0b i_new_dot=%0b",
                                             $time, i_last_nv, i_new_dot);
                                    `endif
                                end else begin
                                    // Stall: keep cycle count at 3 until new data arrives
                                    comp_cycle_cnt <= 2'd3;
                                end
                            end
                            // If last_matmul_reg=1, state machine transitions to FINAL_DRAIN
                        end else begin
                            // More NVs in current dot product
                            if (i_act_valid && !i_wt_loading) begin
                                act_man_reg[0]  <= i_nv_left_man[0];
                                act_man_reg[1]  <= i_nv_left_man[1];
                                act_man_reg[2]  <= i_nv_left_man[2];
                                act_man_reg[3]  <= i_nv_left_man[3];
                                act_exp_reg     <= i_nv_left_exp;
                                new_dot_reg     <= i_new_dot;
                                last_nv_reg     <= i_last_nv;
                                last_matmul_reg <= i_last_matmul;
                                nv_index        <= nv_index + 7'd1;
                                `ifdef SIMULATION
                                $display("[WRAPPER_DBG] @%0t RUNNING latch NV: i_last_nv=%0b nv_index=%0d",
                                         $time, i_last_nv, nv_index + 7'd1);
                                `endif
                            end else begin
                                // Stall: keep cycle count at 3 until data arrives
                                comp_cycle_cnt <= 2'd3;
                            end
                        end
                    end else begin
                        comp_cycle_cnt <= comp_cycle_cnt + 2'd1;
                    end
                end

                COMP_FINAL_DRAIN: begin
                    // Final drain: only happens once at very end
                    drain_cnt <= drain_cnt + 3'd1;
                end

                default: begin
                    // No updates
                end
            endcase
        end
        // When fifo_any_full, counters freeze (backpressure)
    end

    // =========================================================================
    // Ready-Valid Signals (with backpressure)
    // =========================================================================
    assign o_wt_ready = !i_wt_loading && !fifo_any_full;

    // o_act_ready: Assert in IDLE for first NV, and in RUNNING at NV boundaries
    // This allows continuous acceptance of NVs without going through IDLE
    assign o_act_ready = !i_wt_loading && !fifo_any_full &&
                         ((comp_state_reg == COMP_IDLE) ||
                          (in_running && (comp_cycle_cnt == 2'd3)));

    // =========================================================================
    // FIFO Push Signal: Push when dot product result is ready
    // =========================================================================
    // Two cases for FIFO push:
    // 1. Intermediate dot products: use capture_delay pipeline (2 cycles after last_nv)
    //    - Suppress when in FINAL_DRAIN to avoid double-push for final result
    // 2. Final dot product: push during FINAL_DRAIN at drain_cnt==2
    assign drain_valid = in_final_drain && !fifo_any_full;
    assign fifo_push_valid = (!fifo_any_full) &&
                             ((capture_delay[1] && !in_final_drain) ||      // Intermediate results only
                              (in_final_drain && (drain_cnt == 3'd2)));     // Final result

    // =========================================================================
    // MLP BRAM Column Instances (4 stacks)
    // =========================================================================
    generate
        for (s = 0; s < NUM_STACKS; s = s + 1) begin : gen_mlp_stack
            logic [71:0] stack_din;
            assign stack_din = (i_wt_loading || !in_running) ? 72'b0 : din_stack[s];

            logic [7:0] stack_expb;
            assign stack_expb = (i_wt_loading || !in_running) ? 8'b0 : act_exp_chunk[s];

            comp_mlp_bram_col #(
                .NUM_MLPS(NUM_MLPS)
            ) u_mlp_bram_col (
                .clk(clk),
                .rstn(rstn),
                .ce(mlp_ce),
                .din(stack_din),
                .load(mlp_load),
                .accumulate(mlp_accumulate),
                .expb(stack_expb),
                .bram_din(bram_din_stack[s]),
                .wraddr(mlp_wraddr),
                .wren(mlp_wren),
                .rdaddr(mlp_rdaddr),
                .dout(stack_dout[s])
            );
        end
    endgenerate

    // =========================================================================
    // FIFO Instances: Decouple MLP outputs from Adder Tree
    // =========================================================================
    generate
        for (s = 0; s < NUM_STACKS; s = s + 1) begin : gen_fifo_stack
            for (genvar m = 0; m < NUM_MLPS; m = m + 1) begin : gen_fifo_mlp
                // FIFO data: pack both FP24 values
                // stack_dout[s][m][23:0]  = Bank CD (even columns)
                // stack_dout[s][m][47:24] = Bank AB (odd columns)
                assign fifo_din[s][m] = stack_dout[s][m][47:0];

                // Push to FIFO when drain completes
                assign fifo_push[s][m] = fifo_push_valid;

                // Pop from FIFO when all FIFOs have data and downstream ready
                assign fifo_pop[s][m] = fifo_pop_enable;

                comp_stack_fifo #(
                    .DATA_WIDTH(FIFO_WIDTH),
                    .DEPTH(FIFO_DEPTH)
                ) u_stack_fifo (
                    .clk(clk),
                    .rstn(rstn),
                    .i_data(fifo_din[s][m]),
                    .i_push(fifo_push[s][m]),
                    .o_full(fifo_full[s][m]),
                    .o_data(fifo_dout[s][m]),
                    .i_pop(fifo_pop[s][m]),
                    .o_empty(fifo_empty[s][m]),
                    .o_count()  // Not used
                );

                // Extract FP24 values from FIFO output
                assign fifo_fp24_bank0[s][m] = fifo_dout[s][m][23:0];
                assign fifo_fp24_bank1[s][m] = fifo_dout[s][m][47:24];
            end
        end
    endgenerate

    // =========================================================================
    // FIFO Consumption Logic: Pop when ALL FIFOs have data
    // =========================================================================
    always_comb begin
        fifo_all_ready = 1'b1;
        for (int ss = 0; ss < NUM_STACKS; ss++) begin
            for (int mm = 0; mm < NUM_MLPS; mm++) begin
                fifo_all_ready = fifo_all_ready & ~fifo_empty[ss][mm];
            end
        end
    end

    // Pop from all FIFOs when all have data and downstream is ready
    assign fifo_pop_enable = fifo_all_ready && i_dout_ready;

    // =========================================================================
    // Repack FIFO Outputs for Adder Pipeline
    // =========================================================================
    generate
        for (genvar m = 0; m < NUM_MLPS; m = m + 1) begin : gen_repack
            for (genvar ss = 0; ss < NUM_STACKS; ss = ss + 1) begin : gen_stack_repack
                assign adder_input_bank0[m][ss] = fifo_fp24_bank0[ss][m];
                assign adder_input_bank1[m][ss] = fifo_fp24_bank1[ss][m];
            end
        end
    endgenerate

    // =========================================================================
    // Adder Input Valid: When FIFOs are being consumed
    // =========================================================================
    assign adder_input_valid = fifo_pop_enable;

    // =========================================================================
    // Integer-Domain FP Adder Pipeline: Combine 4 partial results per column
    // =========================================================================
    generate
        for (genvar m = 0; m < NUM_MLPS; m = m + 1) begin : gen_adder_tree
            logic adder_valid_bank0, adder_valid_bank1;

            comp_fp_adder_pipeline #(
                .NUM_INPUTS(4),
                .FP_IN_WIDTH(24),
                .FP_OUT_WIDTH(16),
                .INT_WIDTH(64),
                .FRAC_BITS(32),
                .SEG_LEN(2)
            ) u_adder_bank0 (
                .clk(clk),
                .rst_n(rstn),
                .en(1'b1),
                .i_fp(adder_input_bank0[m]),
                .i_valid(adder_input_valid),
                .o_fp(final_bank0[m]),
                .o_valid(adder_valid_bank0)
            );

            comp_fp_adder_pipeline #(
                .NUM_INPUTS(4),
                .FP_IN_WIDTH(24),
                .FP_OUT_WIDTH(16),
                .INT_WIDTH(64),
                .FRAC_BITS(32),
                .SEG_LEN(2)
            ) u_adder_bank1 (
                .clk(clk),
                .rst_n(rstn),
                .en(1'b1),
                .i_fp(adder_input_bank1[m]),
                .i_valid(adder_input_valid),
                .o_fp(final_bank1[m]),
                .o_valid(adder_valid_bank1)
            );

            // Combine into output format
            assign o_dout[m] = {40'd0, final_bank1[m], final_bank0[m]};

            // Use adder valid from MLP 0 for overall output valid
            if (m == 0) begin : gen_valid
                assign adder_output_valid = adder_valid_bank0;
            end
        end
    endgenerate

    // =========================================================================
    // Output Valid: From adder pipeline valid signal
    // =========================================================================
    assign o_dout_valid = adder_output_valid;

    // =========================================================================
    // Debug Output
    // =========================================================================
    // synthesis translate_off
    logic [1:0] comp_state_prev;
    logic       wt_loading_prev;
    logic       fifo_push_prev;

    always @(posedge clk) begin
        comp_state_prev <= comp_state_reg;
        wt_loading_prev <= i_wt_loading;
        fifo_push_prev  <= fifo_push_valid;

        // Report FIFO push events
        if (fifo_push_valid && !fifo_push_prev) begin
            $display("[MLP_FIFO] @%0t PUSH: capture_delay=%b drain_cnt=%0d, any_full=%b last_nv=%b last_matmul=%b",
                     $time, capture_delay, drain_cnt, fifo_any_full, last_nv_reg, last_matmul_reg);
        end

        // Report dot_complete_pulse
        if (dot_complete_pulse) begin
            $display("[MLP_DOT] @%0t DOT_COMPLETE: last_nv=%b last_matmul=%b cycle=%d state=%d",
                     $time, last_nv_reg, last_matmul_reg, comp_cycle_cnt, comp_state_reg);
        end

        // Report FIFO pop events
        if (fifo_pop_enable) begin
            $display("[MLP_FIFO] @%0t POP: all_ready=%b, dout_ready=%b",
                     $time, fifo_all_ready, i_dout_ready);
        end

        // Report backpressure events
        if (fifo_any_full && (in_running || in_final_drain)) begin
            $display("[MLP_FIFO] @%0t BACKPRESSURE: state=%0d, any_full=%b",
                     $time, comp_state_reg, fifo_any_full);
        end

        // Report output valid
        if (o_dout_valid) begin
            $display("[MLP_FIFO] @%0t DOUT_VALID: MLP0 bank0=0x%04x bank1=0x%04x",
                     $time, final_bank0[0], final_bank1[0]);
        end
    end
    // synthesis translate_on

endmodule

`default_nettype wire
