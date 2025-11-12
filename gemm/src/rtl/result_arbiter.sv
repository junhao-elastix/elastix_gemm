// ------------------------------------------------------------------
// Result Arbiter - Concurrent Round-Robin Result Collection
//
// Purpose: Collects FP16 results from multiple compute tiles in round-robin fashion
//
// Architecture:
//  - Monitors per-tile result FIFOs for available data
//  - Round-robin scheduling across enabled tiles for fair collection
//  - Shadow FIFO counting for immediate state tracking (compensates for 2-cycle BRAM latency)
//  - Handles 2-cycle BRAM read latency with pipeline stages
//  - Supports 2-24 parallel compute tiles
//
// Operation:
//  1. ARB_IDLE: Wait for MATMUL command, capture dimensions and col_en
//  2. ARB_COLLECT: Round-robin read from enabled tile FIFOs
//  3. ARB_DONE: All enabled tiles produced B×C results, wait for next MATMUL
//
// Key Features:
//  - Concurrent collection (doesn't wait for one tile to finish before reading next)
//  - Shadow FIFO counts track logical FIFO state immediately (physical count has 2-cycle delay)
//  - Pending read tracking prevents FIFO over-read due to pipeline latency
//  - Backpressure handling (stops when result_bram full)
//
// Author: MS2.0 Multi-Tile Architecture
// Date: Tue Oct 28 2025
// ------------------------------------------------------------------

module result_arbiter
#(
    parameter int NUM_TILES = 2  // Number of parallel compute tiles (2-24)
)
(
    // Clock and Reset
    input  logic        i_clk,
    input  logic        i_reset_n,

    // MATMUL Command Interface (from Master Control)
    input  logic [23:0] i_mc_tile_en,            // Per-tile enable bitmask
    input  logic [7:0]  i_mc_left_ugd_len,       // Batch dimension (B)
    input  logic [7:0]  i_mc_right_ugd_len,      // Column dimension (C)

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
    typedef enum logic [2:0] {
        ARB_IDLE,
        ARB_COLLECT,
        ARB_DONE
    } arb_state_t;

    arb_state_t arb_state_reg;

    // ------------------------------------------------------------------
    // Arbiter Control Registers
    // ------------------------------------------------------------------
    logic [15:0] arb_results_per_tile_reg;  // B×C results expected per tile
    logic [7:0]  arb_c_per_tile_reg;        // C_per_tile (columns per tile)
    logic [4:0]  arb_current_tile_reg;      // Round-robin pointer (0-23)
    logic [23:0] arb_col_en_reg;            // Captured tile enable mask

    // Per-tile chunk counters (track how many results collected from each tile in current chunk)
    logic [7:0]  arb_tile_chunk_cnt [NUM_TILES];  // 0 to C_per_tile-1, then wraps to 0

    // Per-tile result counters (how many results collected from each tile)
    logic [15:0] arb_tile_result_cnt [NUM_TILES];

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
            arb_results_per_tile_reg <= 16'd0;
            arb_c_per_tile_reg <= 8'd0;
            arb_col_en_reg <= 24'd0;
            arb_current_tile_reg <= 5'd0;
            for (int i = 0; i < NUM_TILES; i++) begin
                arb_tile_result_cnt[i] <= 16'd0;
                arb_tile_chunk_cnt[i] <= 8'd0;
                o_tile_fifo_rd_en[i] <= 1'b0;
                arb_tile_pending_reads[i] <= 2'd0;
                arb_tile_shadow_count[i] <= 9'd0;
            end
        end else begin
            case (arb_state_reg)
                ARB_IDLE: begin
                    // Clear all FIFO read enables when idle
                    for (int i = 0; i < NUM_TILES; i++) begin
                        o_tile_fifo_rd_en[i] <= 1'b0;
                        arb_tile_pending_reads[i] <= 2'd0;
                    end

                    // Wait for MATMUL command to start result collection
                    if (|i_mc_tile_en) begin  // Start when ANY tile enabled
                        // Capture matrix dimensions AND tile enable mask
                        // CRITICAL: Compute engines produce B×C results per tile in ONE execution
                        // Cast to 16-bit BEFORE multiplication to avoid overflow
                        arb_results_per_tile_reg <= 16'(i_mc_left_ugd_len) * 16'(i_mc_right_ugd_len);
                        arb_c_per_tile_reg <= i_mc_right_ugd_len;  // C_per_tile for chunked collection
                        arb_col_en_reg <= i_mc_tile_en;  // Capture which tiles are enabled
                        arb_current_tile_reg <= 5'd0;    // Start round-robin from tile 0

                        // Debug: Show which tiles will be collecting from
                        `ifdef SIMULATION
                        $display("[ARB] @%0t Starting result collection: col_en=0x%06x, B=%0d, C=%0d, results_per_tile=%0d",
                                 $time, i_mc_tile_en, i_mc_left_ugd_len, i_mc_right_ugd_len,
                                 16'(i_mc_left_ugd_len) * 16'(i_mc_right_ugd_len));
                        for (int i = 0; i < NUM_TILES; i++) begin
                            if (i_mc_tile_en[i]) begin
                                $display("[ARB] @%0t   --> Will collect from Tile[%0d]", $time, i);
                            end
                        end
                        `endif

                        // Reset per-tile counters and initialize shadow counts from FIFOs
                        for (int i = 0; i < NUM_TILES; i++) begin
                            arb_tile_result_cnt[i] <= 16'd0;
                            arb_tile_chunk_cnt[i] <= 8'd0;   // Reset per-tile chunk counters
                            arb_tile_pending_reads[i] <= 2'd0;
                            arb_tile_shadow_count[i] <= i_tile_fifo_count[i];  // Snapshot current FIFO state
                        end

                        arb_state_reg <= ARB_COLLECT;
                        `ifdef SIMULATION
                        $display("[ARB] @%0t IDLE->COLLECT: B=%0d, C=%0d, results_per_tile=%0d, col_en=0x%06x",
                                $time, i_mc_left_ugd_len, i_mc_right_ugd_len,
                                16'(i_mc_left_ugd_len) * 16'(i_mc_right_ugd_len), i_mc_tile_en);
                        `endif
                    end
                end

                ARB_COLLECT: begin
                    // Clear all FIFO read enables first (only ONE will be set per cycle)
                    for (int i = 0; i < NUM_TILES; i++) begin
                        o_tile_fifo_rd_en[i] <= 1'b0;
                    end

                    // Track shadow count increments from compute engine writes
                    for (int i = 0; i < NUM_TILES; i++) begin
                        if (i_ce_result_valid[i]) begin
                            arb_tile_shadow_count[i] <= arb_tile_shadow_count[i] + 1;
                        end
                    end

                    // Decrement pending_reads when data actually comes out (pipeline stage 2 completes)
                    if (arb_read_valid_reg) begin
                        arb_tile_pending_reads[arb_read_tile_reg] <= arb_tile_pending_reads[arb_read_tile_reg] - 1;
                    end

                    // Round-robin FIFO draining: Check current tile's FIFO for data
                    // Skip disabled tiles - find next enabled tile
                    if (!arb_col_en_reg[arb_current_tile_reg]) begin
                        // Tile not enabled, find next enabled tile
                        automatic logic [4:0] next_tile = arb_current_tile_reg;
                        for (int i = 1; i < NUM_TILES; i++) begin
                            next_tile = (arb_current_tile_reg + i) % NUM_TILES;
                            if (arb_col_en_reg[next_tile]) break;
                        end
                        arb_current_tile_reg <= next_tile;
                    end
                    // Check if current tile's FIFO has data AND space for more pending reads AND result_bram not full
                    // ALSO check if we haven't reached chunk limit yet (prevent reading extra result)
                    // Use shadow count (immediate) instead of physical empty (2-cycle delayed)
                    // Shadow count > 0 means FIFO has data (or will have after in-flight writes complete)
                    else if ((arb_tile_shadow_count[arb_current_tile_reg] > 9'd0) &&
                             arb_tile_pending_reads[arb_current_tile_reg] < 2'd2 &&
                             arb_tile_chunk_cnt[arb_current_tile_reg] < arb_c_per_tile_reg &&  // NEW: Check chunk limit BEFORE reading
                             !i_result_fifo_full) begin
                        // Read from current tile's FIFO
                        o_tile_fifo_rd_en[arb_current_tile_reg] <= 1'b1;
                        arb_tile_pending_reads[arb_current_tile_reg] <= arb_tile_pending_reads[arb_current_tile_reg] + 1;
                        arb_tile_result_cnt[arb_current_tile_reg] <= arb_tile_result_cnt[arb_current_tile_reg] + 1;
                        arb_tile_shadow_count[arb_current_tile_reg] <= arb_tile_shadow_count[arb_current_tile_reg] - 1;  // Immediate decrement

                        // Increment THIS TILE's chunk counter
                        arb_tile_chunk_cnt[arb_current_tile_reg] <= arb_tile_chunk_cnt[arb_current_tile_reg] + 1;

                        `ifdef SIMULATION
                        $display("[ARB] @%0t COLLECT: Tile %0d FIFO start read[%0d/%0d] chunk[%0d/%0d] (shadow=%0d->%0d, phys=%0d, pending=%0d->%0d)",
                                $time, arb_current_tile_reg,
                                arb_tile_result_cnt[arb_current_tile_reg], arb_results_per_tile_reg,
                                arb_tile_chunk_cnt[arb_current_tile_reg], arb_c_per_tile_reg,
                                arb_tile_shadow_count[arb_current_tile_reg],
                                arb_tile_shadow_count[arb_current_tile_reg] - 1,
                                i_tile_fifo_count[arb_current_tile_reg],
                                arb_tile_pending_reads[arb_current_tile_reg],
                                arb_tile_pending_reads[arb_current_tile_reg] + 1);
                        `endif

                        // CHUNKED COLLECTION: Check if we've collected C_per_tile results from current tile
                        // This produces row-major output order: tile0[C_per_tile], tile1[C_per_tile], tile0[C_per_tile], ...
                        // NOTE: arb_tile_chunk_cnt has ALREADY been incremented above
                        if (arb_tile_chunk_cnt[arb_current_tile_reg] >= arb_c_per_tile_reg) begin
                            // Collected C_per_tile results from this tile, reset this tile's chunk counter and move to next tile
                            arb_tile_chunk_cnt[arb_current_tile_reg] <= 8'd0;  // Reset THIS tile's chunk counter
                            begin
                                automatic logic [4:0] next_tile = arb_current_tile_reg;
                                for (int i = 1; i <= NUM_TILES; i++) begin
                                    next_tile = (arb_current_tile_reg + i) % NUM_TILES;
                                    if (arb_col_en_reg[next_tile]) break;
                                end
                                arb_current_tile_reg <= next_tile;
                                `ifdef SIMULATION
                                $display("[ARB] @%0t CHUNK COMPLETE tile %0d (%0d results): Moving to tile %0d for next chunk",
                                        $time, arb_current_tile_reg, arb_tile_chunk_cnt[arb_current_tile_reg], next_tile);
                                `endif
                            end
                        end
                        // else: stay on same tile to collect more results in this chunk
                    end
                    else if (arb_tile_chunk_cnt[arb_current_tile_reg] >= arb_c_per_tile_reg) begin
                        // Current tile's chunk is full, switch to next tile
                        arb_tile_chunk_cnt[arb_current_tile_reg] <= 8'd0;  // Reset chunk counter
                        begin
                            automatic logic [4:0] next_tile = arb_current_tile_reg;
                            for (int i = 1; i <= NUM_TILES; i++) begin
                                next_tile = (arb_current_tile_reg + i) % NUM_TILES;
                                if (arb_col_en_reg[next_tile] && arb_tile_result_cnt[next_tile] < arb_results_per_tile_reg) break;
                            end
                            if (next_tile != arb_current_tile_reg) begin
                                arb_current_tile_reg <= next_tile;
                                `ifdef SIMULATION
                                $display("[ARB] @%0t Tile %0d chunk full (%0d/%0d), switching to tile %0d",
                                        $time, arb_current_tile_reg, arb_tile_chunk_cnt[arb_current_tile_reg],
                                        arb_c_per_tile_reg, next_tile);
                                `endif
                            end
                        end
                    end
                    else if (arb_tile_result_cnt[arb_current_tile_reg] >= arb_results_per_tile_reg) begin
                        // Current tile has produced all its results, switch to next tile even if mid-chunk
                        automatic logic [4:0] next_tile = arb_current_tile_reg;
                        for (int i = 1; i <= NUM_TILES; i++) begin
                            next_tile = (arb_current_tile_reg + i) % NUM_TILES;
                            if (arb_col_en_reg[next_tile] && arb_tile_result_cnt[next_tile] < arb_results_per_tile_reg) break;
                        end
                        if (next_tile != arb_current_tile_reg) begin
                            arb_current_tile_reg <= next_tile;
                            arb_tile_chunk_cnt[next_tile] <= 8'd0;  // Reset chunk counter for new tile
                            `ifdef SIMULATION
                            $display("[ARB] @%0t Tile %0d finished (%0d/%0d results), switching to tile %0d mid-chunk",
                                    $time, arb_current_tile_reg, arb_tile_result_cnt[arb_current_tile_reg],
                                    arb_results_per_tile_reg, next_tile);
                            `endif
                        end
                    end
                    // else: Current tile FIFO empty/busy, wait (don't switch tiles mid-chunk unless tile is done)

                    // Check if ALL enabled tiles have produced their B×C results
                    // This check happens every cycle to detect completion
                    begin
                        automatic logic all_tiles_done = 1'b1;
                        for (int i = 0; i < NUM_TILES; i++) begin
                            if (arb_col_en_reg[i]) begin
                                if (arb_tile_result_cnt[i] < arb_results_per_tile_reg) begin
                                    all_tiles_done = 1'b0;
                                end
                            end
                        end

                        if (all_tiles_done) begin
                            `ifdef SIMULATION
                            $display("[ARB] @%0t COLLECT->DONE: All enabled tiles produced %0d results each",
                                    $time, arb_results_per_tile_reg);
                            `endif
                            arb_state_reg <= ARB_DONE;

                            // Clear all read enables
                            for (int i = 0; i < NUM_TILES; i++) begin
                                o_tile_fifo_rd_en[i] <= 1'b0;
                            end
                        end
                    end
                end

                ARB_DONE: begin
                    // Wait for next MATMUL command
                    if (|i_mc_tile_en) begin  // New MATMUL when ANY tile enabled
                        arb_state_reg <= ARB_IDLE;  // Will start new collection next cycle
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

endmodule : result_arbiter
