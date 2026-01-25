// ------------------------------------------------------------------
// MLP BRAM Column Controller - Direct Streaming Architecture
//
// Architecture: 4 × mlp_bram_col stacked in parallel with direct streaming
//   - Each stack handles 32 elements (one 256-bit mantissa group + 8-bit exponent)
//   - All 4 stacks process in parallel: 4× throughput
//   - Direct connection from MLP outputs to adder tree (no FIFOs)
//   - Integer-domain FP adder pipeline sums partial results
//
// Data Flow (SIMPLE - No FIFOs):
//   MLP Stack[s][m] → (direct) → Adder Tree[m] → FP16 Output
//
// Weight Loading (SIMPLE COMBINATIONAL Interface - NO FSM):
//   - External controller provides direct BRAM write signals
//   - i_wt_wr_en: Immediate write enable (single cycle)
//   - i_wt_mlp_sel[2:0]: Target MLP (0-7)
//   - i_wt_stack_sel[1:0]: Target stack (0-3) for extraction and per-stack wren
//   - i_wt_wr_addr[9:0]: Direct BRAM address
//   - 64-bit mantissa extracted from 256-bit input based on stack_sel
//   - Per-stack write enables ensure only selected stack is written
//
// Compute:
//   - 4 cycles of streaming (vs 16 with single stack)
//   - Each stack computes partial 32-element dot product
//   - Results stream directly to adder tree when ready
//   - Adder tree always accepts data (no backpressure)
//
// Output: 16 x FP16 results (column-ordered: col0, col1, ..., col15)
//
// Pipeline Latency:
//   - MLP internal pipeline: 2 cycles
//   - Adder pipeline: 4 cycles (1 fp_to_int + 1 adder + 2 int_to_fp)
//
// FSM States (Continuous Operation Architecture):
//   - COMP_IDLE: Waiting for first activation data (i_act_valid)
//   - COMP_RUNNING: Continuous B×C×V operation, streaming activations through MLP
//   - COMP_FINAL_DRAIN: Only after truly last dot product (i_last_matmul=1)
//
// Key optimization: No per-dot-product DRAIN bubbles.
// Results are captured via pipeline delay every V×4 cycles.
//
// Critical Implementation Detail (comp_cycle_cnt):
//   - Cycle counter ONLY advances when act_handshake is true (valid data transfer)
//   - Counter freezes during gaps between batches (no valid activation data)
//   - This prevents spurious DOT_COMPLETE pulses
//   - Without this gating, counter would free-run and produce wrong result count
//
// REFACTORED: Jan 2026 - Simple combinational weight loading interface
//             (replaces complex FSM with per-stack write enables)
// REFACTORED: Jan 2026 - Removed internal FIFOs for direct streaming
//             (512 flex_fifo instances removed, simpler architecture)
//
// Author: Refactored for direct streaming + simple weight interface
// Date: Jan 24, 2026
// ------------------------------------------------------------------

`timescale 1ps / 1ps
`default_nettype none

module comp_MLPStack #(
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
    input  logic [9:0]  i_rd_base_addr,       // Read base address (from MATMUL command)

    // =========================================================================
    // Weight Loading Interface (DIRECT WRITE - NO HANDSHAKE)
    // =========================================================================
    // Direct BRAM Write Interface
    //   - External controller drives write signals directly
    //   - No handshake (no ready/valid protocol) - just write when data present
    //   - i_wt_wr_en: Write enable (simple pulse, not handshake)
    //   - i_nv_right_man: 256-bit mantissa (distributed to 4 stacks via depack)
    //   - i_nv_right_exp: 8-bit exponent (broadcast to 4 stacks)
    //   - i_wt_mlp_sel: Target MLP Column (0-7)
    //   - i_wt_wr_addr: Direct BRAM write address
    input  logic         i_wt_wr_en,          // Write enable (no handshake)
    input  logic [255:0] i_nv_right_man,      // 256-bit mantissa (distributed to 4 stacks)
    input  logic [7:0]   i_nv_right_exp,      // 8-bit exponent (broadcast to 4 stacks)
    input  logic [2:0]   i_wt_mlp_sel,        // Target MLP Column (0-7)
    input  logic [9:0]   i_wt_wr_addr,        // Direct BRAM write address

    // =========================================================================
    // Compute/Activation Interface (upstream)
    // =========================================================================
    input  logic        i_act_valid,          // Activation data valid
    output logic        o_act_ready,          // Ready to accept activation data
    input  logic [255:0] i_nv_left_man,       // 256-bit mantissa (distributed to 4 stacks)
    input  logic [7:0]   i_nv_left_exp,       // 8-bit exponent (broadcast to 4 stacks)
    input  logic        i_new_dot,            // Start new dot product (reset accumulator)
    input  logic        i_last_nv,            // This is the last NV of the current dot product
    input  logic        i_last_matmul,        // Truly last dot product of entire MATMUL (triggers final drain)

    // =========================================================================
    // Result Interface (downstream) - 16 parallel FP16 outputs to external FIFOs
    // =========================================================================
    output logic [15:0] o_result_fp16 [15:0],  // 16 x FP16 results (NUM_MLPS * 2 columns)
    output logic        o_result_push,         // Push enable for all 16 FIFOs
    input  logic        i_result_fifo_full     // OR of all external FIFO full flags
);

    // =========================================================================
    // Address Space Constants
    // =========================================================================
    localparam WRADDR_WIDTH = 10;
    localparam RDADDR_WIDTH = 9;
    localparam NV_SIZE_IN_WORDS = 4;

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

    // Weight Loading Signals (DIRECT WRITE - NO HANDSHAKE)
    logic          wt_loading;            // True during weight write (single cycle)
    logic [71:0]   wt_bram_din;           // BRAM write data {exp, man}

    // Compute FSM Signals
    comp_state_t comp_state_reg, comp_state_next;
    logic [1:0] comp_cycle_cnt;
    logic [2:0] drain_cnt;
    logic [6:0] nv_index;       // Which NV we're processing (0 to V-1)
    logic [6:0] next_nv_index;  // Combinational: nv_index value AFTER handshake
    logic [1:0] chunk_cnt;      // Which chunk within current NV (0-3)
    logic [1:0] next_chunk_cnt; // Combinational: chunk_cnt value AFTER handshake
    logic [255:0]  act_man_reg;
    logic [7:0]    act_exp_reg;
    logic          new_dot_reg;
    logic [1:0]    new_dot_delay;  // Shift register to delay new_dot by PIPELINE_LATENCY cycles
    logic          last_nv_reg;
    logic [1:0]    handshake_delay;  // Shift register to delay handshake for accumulate gating

    // Per-Stack Data Extraction Signals (for activations)
    logic [63:0] act_man_chunk [NUM_STACKS-1:0];
    logic [7:0]  act_exp_chunk [NUM_STACKS-1:0];
    logic [71:0] din_stack [NUM_STACKS-1:0];

    // Per-Stack Weight Write Enable (only selected stack gets written)
    logic [NUM_MLPS-1:0] wt_wren_stack [NUM_STACKS-1:0];

    // MLP BRAM Column Interface Signals
    logic [9:0]          mlp_wraddr;
    logic [8:0]          mlp_rdaddr;
    logic                mlp_ce;
    logic                mlp_load;
    logic                mlp_accumulate;
    logic [8:0]          wt_rd_base_addr;

    // Stack Output Signals
    logic [71:0] stack_dout [NUM_STACKS-1:0][NUM_MLPS-1:0];

    // =========================================================================
    // Adder Pipeline Signals (direct from MLP stack outputs)
    // =========================================================================
    logic [NUM_STACKS-1:0][23:0] adder_input_bank0 [NUM_MLPS-1:0];
    logic [NUM_STACKS-1:0][23:0] adder_input_bank1 [NUM_MLPS-1:0];
    logic [15:0] final_bank0 [NUM_MLPS-1:0];
    logic [15:0] final_bank1 [NUM_MLPS-1:0];

    // Valid pipeline for adder output
    logic adder_input_valid;
    logic adder_output_valid;

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
                                    !last_matmul_reg;

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
    // NOTE: Weight write address sequencing is handled by external controller
    // (no internal cycle counter needed - direct addressing via i_wt_wr_addr)

    // =========================================================================
    // Weight Loading: Data Slicing & Addressing
    // =========================================================================
    // 1. Data Slicing: Distribute 256-bit input to 4 stacks (64-bit each)
    logic [63:0] wt_man_slice [NUM_STACKS-1:0];
    
    // Per-stack slicing of the incoming 256-bit chunk
    assign wt_man_slice[0] = i_nv_right_man[63:0];
    assign wt_man_slice[1] = i_nv_right_man[127:64];
    assign wt_man_slice[2] = i_nv_right_man[191:128];
    assign wt_man_slice[3] = i_nv_right_man[255:192];

    // 2. Weight BRAM Data Construction
    // Each stack gets its slice + the BROADCAST exponent
    // NOTE: This logic is replicated per stack in the generation loop below
    
    // Weight loading is active when write enable is asserted (no handshake)
    assign wt_loading = i_wt_wr_en;

    // Per-stack write enables: ALL stacks are written simultaneously for the target MLP
    genvar s;
    generate
        for (s = 0; s < NUM_STACKS; s = s + 1) begin : gen_wt_wren
            always_comb begin
                if (wt_loading) begin
                    // Enable write for the selected MLP column across ALL stacks
                    wt_wren_stack[s] = ({{(NUM_MLPS-1){1'b0}}, 1'b1} << i_wt_mlp_sel);
                end else begin
                    wt_wren_stack[s] = {NUM_MLPS{1'b0}};
                end
            end
        end
    endgenerate

    // synthesis translate_off
    `ifdef DEBUG_MLPSTACK
    always @(posedge clk) begin
        // Debug: Show first few weight writes with full detail
        if (wt_loading && (i_wt_mlp_sel == 0) && (i_wt_wr_addr < 10)) begin
            $display("[MLPSTACK_WR] @%0t mlp_sel=%0d i_wt_wr_addr=%0d mlp_wraddr=%0d wt_loading=%b",
                     $time, i_wt_mlp_sel, i_wt_wr_addr, mlp_wraddr, wt_loading);
        end
    end
    `endif
    // synthesis translate_on

    // =========================================================================
    // Per-Stack Data Extraction: Activation Data
    // =========================================================================
    generate
        for (s = 0; s < NUM_STACKS; s = s + 1) begin : gen_act_extract
            always_comb begin
                // Activation Slicing:
                // Input i_nv_left_man is 256 bits (one chunk).
                // During compute (RUNNING), we consume one chunk per cycle.
                // The slicing logic must map the 256-bit input to the 4 stacks.
                
                // Correction: The input i_nv_left_man is ALREADY the 256-bit chunk for the current cycle.
                // We don't need to index into it with comp_cycle_cnt. 
                // We just distribute it to the stacks.
                
                act_man_chunk[s] = act_man_reg[s*64 +: 64];
                act_exp_chunk[s] = act_exp_reg; // Broadcast exponent
            end
            assign din_stack[s] = {act_exp_chunk[s], act_man_chunk[s]};
        end
    endgenerate

    // =========================================================================
    // MLP BRAM Column Signal Muxing (SIMPLIFIED)
    // =========================================================================
    // Weight write address construction:
    // Base NV Index (9 bits) + Cycle Offset (2 bits) -> 11 bits?
    // Wait, BRAM is addressed by LINES. 1 NV = 4 Lines.
    // So address = (nv_idx * 4) + cycle_cnt.
    // Direct BRAM write address from external controller
    // External controller manages address sequencing (no auto-increment here)
    assign mlp_wraddr = wt_loading ? i_wt_wr_addr : 10'b0;
    
    // mlp_wren is now per-stack (handled in stack instantiation)
    // CRITICAL: Use next_nv_index (combinational) to align base address with incoming NV
    // nv_index is registered and lags by one cycle at NV boundaries
    assign wt_rd_base_addr = i_rd_base_addr[9:1] + {next_nv_index[6:0], 2'd0};

    always_comb begin
        if (wt_loading) begin
            mlp_rdaddr = 9'b0;
        end else if (in_running || (comp_state_reg == COMP_IDLE && act_handshake)) begin
            // Compute rdaddr when:
            // 1. In RUNNING state (continuous streaming), OR
            // 2. Transitioning from IDLE to RUNNING (first handshake)
            // Read 4 consecutive addresses per NV: base+0, base+1, base+2, base+3
            // Base address = nv_index * 4 (shifted by 2 bits)
            // CRITICAL: Use next_chunk_cnt (combinational) to align rdaddr with activation data
            // chunk_cnt is registered and lags by one cycle, so we must use the pre-computed
            // next value to match the incoming activation chunk number
            mlp_rdaddr = wt_rd_base_addr + {7'd0, next_chunk_cnt};
        end else begin
            mlp_rdaddr = 9'b0;
        end
    end

    // Handshake signal for cleaner logic
    logic act_handshake;
    assign act_handshake = o_act_ready && i_act_valid;

    // CRITICAL: Compute next_chunk_cnt and next_nv_index combinationally for rdaddr alignment
    // These values must reflect the CURRENT handshake, not the PREVIOUS one.
    // The registered counters update AFTER posedge, so mlp_rdaddr would be off-by-one.
    // Solution: Compute what the counters WILL become and use those for rdaddr.

    // next_nv_index: Tracks which NV we're processing
    always_comb begin
        if (!act_handshake) begin
            // No handshake: keep current value
            next_nv_index = nv_index;
        end else if (i_new_dot) begin
            // New dot product: reset to 0
            next_nv_index = 7'd0;
        end else if (chunk_cnt == 2'd3) begin
            // Completed 4 chunks: move to next NV
            next_nv_index = nv_index + 7'd1;
        end else begin
            // Within same NV
            next_nv_index = nv_index;
        end
    end

    // next_chunk_cnt: Tracks which chunk within current NV (0-3)
    always_comb begin
        if (!act_handshake) begin
            // No handshake: keep current value
            next_chunk_cnt = chunk_cnt;
        end else if (i_new_dot) begin
            // New dot product: reset to 0
            next_chunk_cnt = 2'd0;
        end else if (chunk_cnt == 2'd3) begin
            // Wrapped around: reset to 0
            next_chunk_cnt = 2'd0;
        end else begin
            // Normal increment
            next_chunk_cnt = chunk_cnt + 2'd1;
        end
    end

    // Stall condition: waiting for data at NV boundary (cycle 3)
    // REMOVED for optimization: We assume data is always available once streaming starts
    // Stall when we're at cycle 3 in RUNNING but no valid data is available
    // Exception: If we are finishing the MATMUL (last_nv && last_matmul), we don't stall, we go to DRAIN
    logic stalling;
    assign stalling = 1'b0; // FORCE NO STALL

    // MLP enable: Keep active during computation to maintain pipeline timing
    assign mlp_ce = wt_loading || in_running || in_final_drain;

    // Load signal: initialize accumulator at start of new dot product
    // Fires PIPELINE_LATENCY cycles after new_dot arrives (when chunk 2 is being processed)
    // new_dot_delay[1] is the delayed new_dot signal, high at the correct load timing
    assign mlp_load = in_running && new_dot_delay[1];

    // Accumulate signal: active during streaming and final drain
    // During RUNNING, gate with DELAYED handshake to account for MLP pipeline latency
    // Data input at cycle N arrives at accumulator at cycle N+2, so use handshake_delay[1]
    // This is CRITICAL for registered BRAM reads which cause stall cycles at NV boundaries
    assign mlp_accumulate = in_final_drain || (in_running && handshake_delay[1]);

    // =========================================================================
    // Weight Loading: DIRECT WRITE (no handshake)
    // =========================================================================
    // Weight loading signals:
    // - wt_loading = i_wt_wr_en (external controller drives)
    // - mlp_wraddr = i_wt_wr_addr (external controller provides address)
    // - wt_bram_din = {exp, man_chunk} (combinational extraction/depack)
    // - wt_wren_stack[s] = per-stack write enable based on mlp_sel

    // =========================================================================
    // Compute FSM: State Transition Logic (3-state continuous operation)
    // =========================================================================
    always_comb begin
        comp_state_next = comp_state_reg;

        case (comp_state_reg)
            COMP_IDLE: begin
                // Start running on first valid activation (when not loading weights)
                if (i_act_valid && !wt_loading) begin
                    comp_state_next = COMP_RUNNING;
                end
            end

            COMP_RUNNING: begin
                // Stay in RUNNING between dot products
                // Only exit on truly last NV of last dot product (i_last_matmul=1)
                if (comp_cycle_cnt == 2'd3 && last_nv_reg && last_matmul_reg) begin
                    comp_state_next = COMP_FINAL_DRAIN;
                end
                // Otherwise: stay in RUNNING (including between dot products)
            end

            COMP_FINAL_DRAIN: begin
                // Final drain only happens once at the very end
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
    // Compute FSM: Sequential State Update (with backpressure)
    // =========================================================================
    // logic act_handshake; // Moved up to signal declarations
    // assign act_handshake = o_act_ready && i_act_valid; // Moved up

    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            comp_state_reg   <= COMP_IDLE;
            comp_cycle_cnt   <= 2'd0;
            drain_cnt        <= 3'd0;
            act_man_reg      <= 256'b0;
            act_exp_reg      <= 8'b0;
            new_dot_reg      <= 1'b0;
            new_dot_delay    <= 2'b00;
            last_nv_reg      <= 1'b0;
            last_matmul_reg  <= 1'b0;
            nv_index         <= 7'd0;
            chunk_cnt        <= 2'd0;
            capture_delay    <= 2'b00;
            handshake_delay  <= 2'b00;
        end else begin
            // State update (no backpressure - direct streaming)
            comp_state_reg <= comp_state_next;

            // Capture delay pipeline: shift register for dot product completion
            capture_delay <= {capture_delay[0], dot_complete_pulse};

            // Handshake delay pipeline: tracks valid data through MLP pipeline
            // Always shifts every cycle to properly delay by PIPELINE_LATENCY
            handshake_delay <= {handshake_delay[0], act_handshake};

            // Unified Activation Latching
            if (act_handshake) begin
                act_man_reg     <= i_nv_left_man;
                act_exp_reg     <= i_nv_left_exp;
                new_dot_reg     <= i_new_dot;
                // Shift register for new_dot: delays by PIPELINE_LATENCY cycles
                // Uses OLD new_dot_reg value (before this cycle's i_new_dot update)
                new_dot_delay   <= {new_dot_delay[0], new_dot_reg};
                last_nv_reg     <= i_last_nv;
                last_matmul_reg <= i_last_matmul;

                // Proper chunk tracking: 4 chunks per NV
                if (i_new_dot) begin
                    // Start of new dot product: reset both counters
                    nv_index  <= 7'd0;
                    chunk_cnt <= 2'd0;
                end else if (chunk_cnt == 2'd3) begin
                    // Completed 4 chunks, move to next NV
                    chunk_cnt <= 2'd0;
                    nv_index  <= nv_index + 7'd1;
                end else begin
                    // Still within same NV
                    chunk_cnt <= chunk_cnt + 2'd1;
                end

                // synthesis translate_off
                `ifdef DEBUG_MLPSTACK
                $display("[WRAPPER_DBG] @%0t ACT_LATCH: i_last_nv=%0b i_new_dot=%0b nv_idx=%0d chunk=%0d",
                         $time, i_last_nv, i_new_dot,
                         i_new_dot ? 7'd0 : (chunk_cnt == 2'd3 ? nv_index + 7'd1 : nv_index),
                         i_new_dot ? 2'd0 : (chunk_cnt == 2'd3 ? 2'd0 : chunk_cnt + 2'd1));
                `endif
                // synthesis translate_on
            end

            case (comp_state_reg)
                COMP_IDLE: begin
                    comp_cycle_cnt   <= 2'd0;
                    drain_cnt        <= 3'd0;
                    capture_delay    <= 2'b00;
                end

                COMP_RUNNING: begin
                    // Only advance cycle counter when valid data is being processed
                    // This prevents spurious DOT_COMPLETE pulses during gaps between batches
                    if (act_handshake) begin
                        if (comp_cycle_cnt == 2'd3) begin
                            comp_cycle_cnt <= 2'd0;
                        end else begin
                            comp_cycle_cnt <= comp_cycle_cnt + 2'd1;
                        end
                    end
                    // When no valid data, counter freezes (stall)
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
    end

    // =========================================================================
    // Ready-Valid Signals (with backpressure)
    // =========================================================================
    // o_wt_line_ready assigned earlier from wt_state_reg

    // o_act_ready: Assert continuously in RUNNING to receive 1 chunk/cycle
    // Architecture requires activation chunks to arrive synchronously with rdaddr cycling
    // - Cycle 0: chunk 0 activations × weights at rdaddr 0
    // - Cycle 1: chunk 1 activations × weights at rdaddr 1
    // - etc.
    assign o_act_ready = !wt_loading && ((comp_state_reg == COMP_IDLE) || in_running);

    // =========================================================================
    // MLP BRAM Column Instances (4 stacks)
    // =========================================================================
    generate
        for (s = 0; s < NUM_STACKS; s = s + 1) begin : gen_mlp_stack
            logic [71:0] stack_din;
            assign stack_din = (wt_loading || !in_running) ? 72'b0 : din_stack[s];

            logic [7:0] stack_expb;
            assign stack_expb = (wt_loading || !in_running) ? 8'b0 : act_exp_chunk[s];

            // Weight BRAM Data Muxing
            // When loading: {broadcast_exp, slice_man}
            logic [71:0] stack_bram_din;
            assign stack_bram_din = wt_loading ? {i_nv_right_exp, wt_man_slice[s]} : 72'b0;

            comp_MLPRow #(
                .NUM_MLPS(NUM_MLPS)
            ) u_mlp_row (
                .clk(clk),
                .rstn(rstn),
                .ce(mlp_ce),
                .din(stack_din),
                .load(mlp_load),
                .accumulate(mlp_accumulate),
                .expb(stack_expb),
                .bram_din(stack_bram_din),        // SIMPLIFIED: Per-stack data construction
                .wraddr(mlp_wraddr),
                .wren(wt_wren_stack[s]),          // SIMPLIFIED: Per-stack write enable
                .rdaddr(mlp_rdaddr),
                .dout(stack_dout[s])
            );
        end
    endgenerate

    // =========================================================================
    // Direct Connection: MLP outputs to Adder Tree (no FIFOs)
    // =========================================================================
    // Repack MLP stack outputs directly to adder inputs
    // MLP output mapping (verified by simulation):
    //   stack_dout[s][m][47:24] = DOT_PRODUCT_0 (bank0 = EVEN columns)
    //   stack_dout[s][m][23:0]  = DOT_PRODUCT_1 (bank1 = ODD columns)
    generate
        for (genvar m = 0; m < NUM_MLPS; m = m + 1) begin : gen_repack
            for (genvar ss = 0; ss < NUM_STACKS; ss = ss + 1) begin : gen_stack_repack
                assign adder_input_bank0[m][ss] = stack_dout[ss][m][47:24];  // EVEN col from upper bits
                assign adder_input_bank1[m][ss] = stack_dout[ss][m][23:0];   // ODD col from lower bits
            end
        end
    endgenerate

    // =========================================================================
    // Adder Input Valid: Direct from capture pipeline
    // =========================================================================
    // Valid signal follows capture_delay pipeline (2 cycles after last_nv)
    // Two cases for valid results:
    // 1. Intermediate dot products: capture_delay[1] fires 2 cycles after dot completion
    // 2. Final dot product: during FINAL_DRAIN at drain_cnt==2
    assign adder_input_valid = (capture_delay[1] && !in_final_drain) ||
                               (in_final_drain && (drain_cnt == 3'd2));

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

            // Map to column-ordered output:
            // Even columns: bank0 (MLP0 bank0 -> col0, MLP1 bank0 -> col2, ...)
            // Odd columns:  bank1 (MLP0 bank1 -> col1, MLP1 bank1 -> col3, ...)
            assign o_result_fp16[m*2]     = final_bank0[m];  // Even column
            assign o_result_fp16[m*2 + 1] = final_bank1[m];  // Odd column

            // Use adder valid from MLP 0 for overall output valid
            if (m == 0) begin : gen_valid
                assign adder_output_valid = adder_valid_bank0;
            end
        end
    endgenerate

    // =========================================================================
    // Output Push: From adder pipeline valid signal
    // =========================================================================
    assign o_result_push = adder_output_valid;

    // =========================================================================
    // Debug Output
    // =========================================================================
    // synthesis translate_off
    `ifdef DEBUG_MLPSTACK
    logic [1:0] comp_state_prev;
    logic       wt_loading_prev;
    logic       adder_valid_prev;

    always @(posedge clk) begin
        comp_state_prev <= comp_state_reg;
        wt_loading_prev <= wt_loading;
        adder_valid_prev <= adder_input_valid;

        // Report adder input valid events (result streaming)
        if (adder_input_valid && !adder_valid_prev) begin
            $display("[MLP_STREAM] @%0t ADDER_VALID: capture_delay=%b drain_cnt=%0d last_nv=%b last_matmul=%b",
                     $time, capture_delay, drain_cnt, last_nv_reg, last_matmul_reg);
        end

        // Report dot_complete_pulse
        if (dot_complete_pulse) begin
            $display("[MLP_DOT] @%0t DOT_COMPLETE: last_nv=%b last_matmul=%b cycle=%d state=%d",
                     $time, last_nv_reg, last_matmul_reg, comp_cycle_cnt, comp_state_reg);
        end

        // Report output push
        if (o_result_push) begin
            $display("[MLP_STREAM] @%0t RESULT_PUSH: col0=0x%04x col1=0x%04x col2=0x%04x col3=0x%04x",
                     $time, o_result_fp16[0], o_result_fp16[1], o_result_fp16[2], o_result_fp16[3]);
        end

        // Report raw FP24 when streaming to adder (before adder tree)
        if (adder_input_valid) begin
            $display("[MLP_RAW] @%0t FP24 inputs to adder MLP0 bank0: s0=0x%06x s1=0x%06x s2=0x%06x s3=0x%06x",
                     $time, adder_input_bank0[0][0], adder_input_bank0[0][1],
                     adder_input_bank0[0][2], adder_input_bank0[0][3]);
            $display("[MLP_RAW] @%0t FP24 inputs to adder MLP0 bank1: s0=0x%06x s1=0x%06x s2=0x%06x s3=0x%06x",
                     $time, adder_input_bank1[0][0], adder_input_bank1[0][1],
                     adder_input_bank1[0][2], adder_input_bank1[0][3]);
        end
    end
    `endif
    // synthesis translate_on

endmodule : comp_MLPStack

`default_nettype wire


