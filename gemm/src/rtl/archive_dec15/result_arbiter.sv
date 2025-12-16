// ------------------------------------------------------------------
// Result Arbiter - Command-Driven Round-Robin Result Collection
//
// Purpose: Collects FP16 results from multiple compute tiles via READOUT command
//
// Architecture:
//  - Command-driven collection using VECTOR_READOUT (0xF5)
//  - Round-robin scheduling across enabled tiles (uses col_en from MATMUL)
//  - Shadow FIFO counting for immediate state tracking (compensates for 2-cycle BRAM latency)
//  - Handles 2-cycle BRAM read latency with pipeline stages
//  - Supports 1-24 parallel compute tiles
//
// Operation:
//  1. ARB_IDLE: Wait for READOUT command
//  2. ARB_READOUT: Round-robin read from enabled tile FIFOs
//
// Key Features:
//  - Explicit control via READOUT command (no automatic collection)
//  - Results stay in tile FIFOs until host issues READOUT
//  - Shadow FIFO counts track logical FIFO state immediately (physical count has 2-cycle delay)
//  - Pending read tracking prevents FIFO over-read due to pipeline latency
//  - Backpressure handling (stops when result_bram full)
//
// Author: MS2.0 Multi-Tile Architecture
// Date: Wed Nov 12 2025
// ------------------------------------------------------------------

module result_arbiter
#(
    parameter int NUM_TILES = 2  // Number of parallel compute tiles (2-24)
)
(
    // Clock and Reset
    input  logic        i_clk,
    input  logic        i_reset_n,

    // MATMUL Command Interface (from Master Control) - for col_en only
    input  logic [23:0] i_mc_tile_en,            // Per-tile enable bitmask (which tiles have results)

    // READOUT Command Interface (from Master Control)
    input  logic        i_readout_en,            // READOUT command enable
    input  logic [7:0]  i_readout_start_col,     // Starting tile index (0-23)
    input  logic [31:0] i_readout_rd_len,        // Total FP16 results to read
    output logic        o_readout_done,          // READOUT completion signal

    // Tile FIFO Read Interface (to per-tile FIFOs)
    output logic        o_tile_fifo_rd_en [NUM_TILES],  // FIFO read enables
    input  logic [15:0] i_tile_fifo_rd_data [NUM_TILES], // FIFO read data (FP16)
    input  logic [8:0]  i_tile_fifo_count [NUM_TILES],   // FIFO status (0-256)

    // Tile Write Indicators (from Compute Engines)
    input  logic        i_ce_result_valid [NUM_TILES],   // CE write strobes

    // Result BRAM Interface (to result_fifo)
    output logic [15:0] o_result_data,           // Muxed result data to result_fifo
    output logic        o_result_valid,          // Result valid strobe
    input  logic        i_result_fifo_full       // Backpressure from result_fifo
);

    // ------------------------------------------------------------------
    // State Machine
    // ------------------------------------------------------------------
    typedef enum logic [1:0] {
        ARB_IDLE,       // Wait for READOUT command
        ARB_READOUT     // Command-driven result collection
    } arb_state_t;

    arb_state_t arb_state_reg;

    // ------------------------------------------------------------------
    // READOUT Control Registers
    // ------------------------------------------------------------------
    logic [31:0] readout_count_reg;         // Results collected so far
    logic [4:0]  readout_tile_reg;          // Current tile index (0-23)
    logic [31:0] readout_rd_len_reg;        // Total results to collect
    logic        readout_done_reg;          // Completion signal
    logic [7:0]  readout_tile_col_count;    // How many results to read from current tile before advancing
    logic [7:0]  readout_tile_results_read; // How many results read from current tile so far

    // Per-tile pending read counters (track reads in-flight due to 2-cycle BRAM latency)
    logic [1:0]  arb_tile_pending_reads [NUM_TILES];  // 0-2 pending reads per tile

    // Shadow FIFO counts (immediate tracking of logical FIFO state)
    // Physical FIFO count has 2-cycle latency, shadow count updates immediately
    logic [8:0]  arb_tile_shadow_count [NUM_TILES];

    // ------------------------------------------------------------------
    // Pipeline Registers for 2-Cycle BRAM Read Latency
    // ------------------------------------------------------------------
    logic [4:0]  arb_read_tile_pipe;      // Pipeline stage 1: which tile being read
    logic [4:0]  arb_read_tile_reg;       // Pipeline stage 2: which tile was read 2 cycles ago
    logic        arb_read_valid_pipe;     // Pipeline stage 1: read enable
    logic        arb_read_valid_reg;      // Pipeline stage 2: delayed read enable (data valid)
    logic        any_tile_rd_en;          // OR of all tile rd_en signals

    // ------------------------------------------------------------------
    // Main State Machine - Round-Robin Concurrent Collection
    // ------------------------------------------------------------------
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            arb_state_reg <= ARB_IDLE;
            readout_count_reg <= 32'd0;
            readout_tile_reg <= 5'd0;
            readout_rd_len_reg <= 32'd0;
            readout_done_reg <= 1'b0;
            for (int i = 0; i < NUM_TILES; i++) begin
                o_tile_fifo_rd_en[i] <= 1'b0;
                arb_tile_pending_reads[i] <= 2'd0;
                arb_tile_shadow_count[i] <= 9'd0;
            end
        end else begin
            case (arb_state_reg)
                ARB_IDLE: begin
                    // Clear done signal unconditionally when idle (critical for multi-command operation)
                    readout_done_reg <= 1'b0;

                    // Clear all FIFO read enables when idle
                    for (int i = 0; i < NUM_TILES; i++) begin
                        o_tile_fifo_rd_en[i] <= 1'b0;
                        arb_tile_pending_reads[i] <= 2'd0;
                    end

                    // Priority 1: READOUT command-driven result collection
                    `ifdef SIMULATION
                    if (i_readout_en) begin
                        $display("[ARB] @%0t ARB_IDLE sees i_readout_en=1, transitioning to ARB_READOUT", $time);
                    end
                    `endif

                    if (i_readout_en) begin
                        // Capture READOUT parameters
                        readout_tile_reg <= i_readout_start_col[4:0];  // Starting tile (0-23)
                        readout_rd_len_reg <= i_readout_rd_len;         // Total results to read
                        readout_count_reg <= 32'd0;                     // Reset counter
                        readout_done_reg <= 1'b0;                       // Clear done signal

                        // Initialize shadow counts for READOUT
                        for (int i = 0; i < NUM_TILES; i++) begin
                            arb_tile_shadow_count[i] <= i_tile_fifo_count[i];
                            arb_tile_pending_reads[i] <= 2'd0;
                        end

                        arb_state_reg <= ARB_READOUT;
                        `ifdef SIMULATION
                        $display("[ARB] @%0t IDLE->READOUT: start_col=%0d, rd_len=%0d, i_mc_tile_en=0x%06x",
                                $time, i_readout_start_col, i_readout_rd_len, i_mc_tile_en);
                        for (int i = 0; i < NUM_TILES; i++) begin
                            $display("[ARB] @%0t   Tile[%0d]: shadow_count=%0d, fifo_count=%0d, enabled=%0d",
                                    $time, i, i_tile_fifo_count[i], i_tile_fifo_count[i], i_mc_tile_en[i]);
                        end
                        `endif
                    end
                end

                ARB_READOUT: begin
                    // Command-driven result readout with round-robin multi-tile support
                    // Reads one result from each enabled tile in sequence

                    // Clear all FIFO read enables first
                    for (int i = 0; i < NUM_TILES; i++) begin
                        o_tile_fifo_rd_en[i] <= 1'b0;
                    end

                    // Track shadow count increments from compute engine writes (if any)
                    for (int i = 0; i < NUM_TILES; i++) begin
                        if (i_ce_result_valid[i]) begin
                            arb_tile_shadow_count[i] <= arb_tile_shadow_count[i] + 1;
                        end
                    end

                    // Decrement pending_reads when data comes out (pipeline stage 2 completes)
                    if (arb_read_valid_reg) begin
                        arb_tile_pending_reads[arb_read_tile_reg] <= arb_tile_pending_reads[arb_read_tile_reg] - 1;
                    end

                    // SAFETY CHECK: If no tiles are enabled, complete immediately
                    // This prevents infinite loop if ce_tile_en_reg was cleared prematurely
                    if (i_mc_tile_en == '0) begin
                        readout_done_reg <= 1'b1;
                        arb_state_reg <= ARB_IDLE;
                        `ifdef SIMULATION
                        $display("[ARB] @%0t READOUT->IDLE: No tiles enabled (i_mc_tile_en=0), completing with %0d/%0d results",
                                $time, readout_count_reg, readout_rd_len_reg);
                        `endif
                    // Check if we've collected all requested results
                    end else if (readout_count_reg >= readout_rd_len_reg) begin
                        // Done - signal completion
                        readout_done_reg <= 1'b1;
                        arb_state_reg <= ARB_IDLE;
                        `ifdef SIMULATION
                        $display("[ARB] @%0t READOUT->IDLE: Collected %0d results",
                                $time, readout_count_reg);
                        `endif
                    end else begin
                        // Still have results to collect - check current tile

                        // Check if current tile is enabled (uses col_en from MATMUL command)
                        if (!i_mc_tile_en[readout_tile_reg]) begin
                            // Tile is disabled - since all enabled tiles are sequential from bit 0,
                            // a disabled tile means we've wrapped past the last enabled tile
                            // Go directly back to tile 0 (first enabled tile)
                            readout_tile_reg <= 5'd0;
                            `ifdef SIMULATION
                            $display("[ARB] @%0t READOUT: Tile %0d disabled, wrapping to tile 0",
                                    $time, readout_tile_reg);
                            `endif
                        end else begin
                            // Tile is enabled - check for data availability
                            automatic logic [8:0] shadow_available = arb_tile_shadow_count[readout_tile_reg] -
                                                                      arb_tile_pending_reads[readout_tile_reg];

                            if (shadow_available > 0 && !i_result_fifo_full) begin
                                // Data available and space in result FIFO - read one result and advance
                                o_tile_fifo_rd_en[readout_tile_reg] <= 1'b1;
                                arb_tile_shadow_count[readout_tile_reg] <= arb_tile_shadow_count[readout_tile_reg] - 1;
                                arb_tile_pending_reads[readout_tile_reg] <= arb_tile_pending_reads[readout_tile_reg] + 1;
                                readout_count_reg <= readout_count_reg + 1;

                                // Advance to next tile (round-robin)
                                readout_tile_reg <= (readout_tile_reg + 1) % NUM_TILES;

                                `ifdef SIMULATION
                                $display("[ARB] @%0t READOUT: Reading from tile %0d (count=%0d/%0d, shadow=%0d), advancing to tile %0d",
                                        $time, readout_tile_reg, readout_count_reg + 1, readout_rd_len_reg,
                                        shadow_available, (readout_tile_reg + 1) % NUM_TILES);
                                `endif
                            end else if (!i_result_fifo_full) begin
                                // No data available but result_fifo not full
                                // For unbalanced distributions, some tiles finish early - SKIP them
                                // Advance to next tile without reading (don't wait forever)
                                readout_tile_reg <= (readout_tile_reg + 1) % NUM_TILES;

                                `ifdef SIMULATION
                                $display("[ARB] @%0t READOUT: Tile %0d has no data (shadow=%0d), skipping to tile %0d",
                                        $time, readout_tile_reg, shadow_available, (readout_tile_reg + 1) % NUM_TILES);
                                `endif
                            end
                            // else: result_fifo is full - wait (don't advance anything)
                        end
                    end
                end

                default: arb_state_reg <= ARB_IDLE;
            endcase
        end
    end

    // ------------------------------------------------------------------
    // Pipeline for 2-Cycle BRAM Read Latency
    // ------------------------------------------------------------------
    // Cycle N:   Assert o_tile_fifo_rd_en[i]
    // Cycle N+1: BRAM reads internally
    // Cycle N+2: i_tile_fifo_rd_data[i] has valid data → write to result_bram

    // Check if ANY tile has rd_en asserted (combinational)
    always_comb begin
        any_tile_rd_en = 1'b0;
        for (int i = 0; i < NUM_TILES; i++) begin
            if (o_tile_fifo_rd_en[i]) any_tile_rd_en = 1'b1;
        end
    end

    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            arb_read_tile_pipe <= 5'd0;
            arb_read_tile_reg <= 5'd0;
            arb_read_valid_pipe <= 1'b0;
            arb_read_valid_reg <= 1'b0;
        end else begin
            // 2-stage pipeline for BRAM read latency
            // Stage 1: Capture which tile had rd_en asserted
            for (int i = 0; i < NUM_TILES; i++) begin
                if (o_tile_fifo_rd_en[i]) begin
                    arb_read_tile_pipe <= i[4:0];
                    break;
                end
            end
            arb_read_valid_pipe <= any_tile_rd_en;

            // Stage 2: Delayed by 1 more cycle
            arb_read_tile_reg <= arb_read_tile_pipe;
            arb_read_valid_reg <= arb_read_valid_pipe;

            // Debug output
            `ifdef SIMULATION
            if (arb_read_valid_pipe) begin
                $display("[ARB_OUTPUT] @%0t result_data=0x%04x from tile[%0d] (arb_read_tile_pipe=%0d)",
                         $time, i_tile_fifo_rd_data[arb_read_tile_pipe], arb_read_tile_pipe, arb_read_tile_pipe);
            end
            `endif
        end
    end

    // ------------------------------------------------------------------
    // Output Multiplexer with Pipeline Stage
    // ------------------------------------------------------------------
    // CRITICAL FIX: o_result_data must be REGISTERED to match o_result_valid timing
    // Without this register, o_result_data arrives 1 cycle early and gets overwritten
    // Data flows: tile_fifo (1-cycle delay) → arbiter register → result_bram
    logic [15:0] o_result_data_reg;

    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            o_result_data_reg <= '0;
        end else begin
            // Use arb_read_tile_pipe (not _reg) to match the pipeline stage
            o_result_data_reg <= i_tile_fifo_rd_data[arb_read_tile_pipe];
        end
    end

    assign o_result_data = o_result_data_reg;
    assign o_result_valid = arb_read_valid_reg;
    assign o_readout_done = readout_done_reg;

endmodule : result_arbiter
