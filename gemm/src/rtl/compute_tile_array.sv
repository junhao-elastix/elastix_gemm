// ------------------------------------------------------------------
// Compute Tile Array - Multi-Tile Matrix Multiplication Engine
//
// Purpose: Parallel array of NUM_TILES compute engines with private L1 BRAMs
// Features:
//  - NUM_TILES configurable (default 16, max 16)
//  - Each tile has private tile_bram_left and tile_bram_right (512 lines each)
//  - Dispatcher writes to tile BRAMs (broadcast or distribute)
//  - Each compute_engine_modular reads from its private tile BRAM
//  - column_enable mask controls which tiles execute
//  - Results collected in tile-major order
//
// Architecture:
//  ┌─────────────────────────────────────────────────────┐
//  │  Tile 0         Tile 1    ...    Tile (N-1)         │
//  │  ┌─────────┐   ┌─────────┐      ┌─────────┐        │
//  │  │tile_bram│   │tile_bram│      │tile_bram│        │
//  │  │  _left  │   │  _left  │      │  _left  │        │
//  │  └────┬────┘   └────┬────┘      └────┬────┘        │
//  │       │             │                 │             │
//  │       ▼             ▼                 ▼             │
//  │  ┌─────────┐   ┌─────────┐      ┌─────────┐        │
//  │  │ compute │   │ compute │      │ compute │        │
//  │  │ _engine │   │ _engine │      │ _engine │        │
//  │  │_modular │   │_modular │      │_modular │        │
//  │  └────┬────┘   └────┬────┘      └────┬────┘        │
//  │       │             │                 │             │
//  │       ▼             ▼                 ▼             │
//  │  ┌─────────┐   ┌─────────┐      ┌─────────┐        │
//  │  │tile_bram│   │tile_bram│      │tile_bram│        │
//  │  │ _right  │   │ _right  │      │ _right  │        │
//  │  └─────────┘   └─────────┘      └─────────┘        │
//  └─────────────────────────────────────────────────────┘
//
// Author: Single_Row Multi-Tile Architecture Migration
// Date: Mon Oct 20 2025
// ------------------------------------------------------------------

module compute_tile_array
import gemm_pkg::*;
#(
    parameter NUM_TILES = 16,               // Number of parallel compute tiles
    parameter TILE_BRAM_DEPTH = 512,        // 512 lines = 128 NVs
    parameter TILE_BRAM_WIDTH = 256,        // 256 bits/line
    parameter TILE_BRAM_ADDR_WIDTH = 9      // 9 bits for 512 depth
) (
    input  logic        i_clk,
    input  logic        i_reset_n,

    // ====================================================================
    // Tile Command Interface (from master_control, shared across tiles)
    // ====================================================================
    input  logic                          i_tile_en,
    input  logic [NUM_TILES-1:0]          i_column_enable,      // Which tiles to execute
    input  logic [tile_mem_addr_width_gp-1:0] i_left_addr,
    input  logic [tile_mem_addr_width_gp-1:0] i_right_addr,
    input  logic [tile_mem_addr_width_gp-1:0] i_left_ugd_len,
    input  logic [tile_mem_addr_width_gp-1:0] i_right_ugd_len,
    input  logic [tile_mem_addr_width_gp-1:0] i_vec_len,
    input  logic [7:0]                    i_dim_b,
    input  logic [7:0]                    i_dim_c,
    input  logic [7:0]                    i_dim_v,
    input  logic                          i_left_man_4b,
    input  logic                          i_right_man_4b,
    input  logic                          i_main_loop_over_left,
    output logic                          o_tile_done,          // All enabled tiles done

    // ====================================================================
    // Dispatcher Write Interface (writes to tile BRAMs)
    // ====================================================================
    // Left mantissa BRAM writes (broadcast or distribute)
    input  logic [NUM_TILES-1:0]          i_dispatcher_man_wr_en_left,
    input  logic [TILE_BRAM_ADDR_WIDTH-1:0] i_dispatcher_man_wr_addr_left,
    input  logic [TILE_BRAM_WIDTH-1:0]    i_dispatcher_man_wr_data_left,

    // Right mantissa BRAM writes (broadcast or distribute)
    input  logic [NUM_TILES-1:0]          i_dispatcher_man_wr_en_right,
    input  logic [TILE_BRAM_ADDR_WIDTH-1:0] i_dispatcher_man_wr_addr_right,
    input  logic [TILE_BRAM_WIDTH-1:0]    i_dispatcher_man_wr_data_right,

    // Left exponent BRAM writes (broadcast or distribute)
    input  logic [NUM_TILES-1:0]          i_dispatcher_exp_wr_en_left,
    input  logic [TILE_BRAM_ADDR_WIDTH-1:0] i_dispatcher_exp_wr_addr_left,
    input  logic [7:0]                    i_dispatcher_exp_wr_data_left,

    // Right exponent BRAM writes (broadcast or distribute)
    input  logic [NUM_TILES-1:0]          i_dispatcher_exp_wr_en_right,
    input  logic [TILE_BRAM_ADDR_WIDTH-1:0] i_dispatcher_exp_wr_addr_right,
    input  logic [7:0]                    i_dispatcher_exp_wr_data_right,

    // ====================================================================
    // Result Interface (tile-major output)
    // ====================================================================
    output logic [15:0]                   o_result_data,        // FP16 result
    output logic                          o_result_valid,       // Result valid
    output logic [3:0]                    o_result_tile_id,     // Which tile this result is from
    input  logic                          i_result_full,
    input  logic                          i_result_afull,

    // ====================================================================
    // Debug
    // ====================================================================
    output logic [3:0]                    o_ce_state [0:NUM_TILES-1]
);

    // ===================================================================
    // Per-Tile Signals
    // ===================================================================

    // tile_bram_left mantissa instances
    logic [TILE_BRAM_ADDR_WIDTH-1:0] tile_left_rd_addr [0:NUM_TILES-1];
    logic [TILE_BRAM_WIDTH-1:0]      tile_left_rd_data [0:NUM_TILES-1];
    logic                            tile_left_rd_en   [0:NUM_TILES-1];

    // tile_bram_right mantissa instances
    logic [TILE_BRAM_ADDR_WIDTH-1:0] tile_right_rd_addr [0:NUM_TILES-1];
    logic [TILE_BRAM_WIDTH-1:0]      tile_right_rd_data [0:NUM_TILES-1];
    logic                            tile_right_rd_en   [0:NUM_TILES-1];

    // tile_bram_left exponent instances
    logic [TILE_BRAM_ADDR_WIDTH-1:0] tile_left_exp_rd_addr [0:NUM_TILES-1];
    logic [7:0]                      tile_left_exp_rd_data [0:NUM_TILES-1];

    // tile_bram_right exponent instances
    logic [TILE_BRAM_ADDR_WIDTH-1:0] tile_right_exp_rd_addr [0:NUM_TILES-1];
    logic [7:0]                      tile_right_exp_rd_data [0:NUM_TILES-1];

    // Compute engine outputs
    logic [15:0]                     tile_result_data  [0:NUM_TILES-1];
    logic                            tile_result_valid [0:NUM_TILES-1];
    logic                            tile_done         [0:NUM_TILES-1];

    // ===================================================================
    // Generate NUM_TILES Compute Tiles
    // ===================================================================
    genvar t;
    generate
        for (t = 0; t < NUM_TILES; t++) begin : gen_tiles

            // ---------------------------------------------------------------
            // tile_bram_left - Private L1 cache for activations
            // ---------------------------------------------------------------
            tile_bram_wrapper #(
                .DEPTH      (TILE_BRAM_DEPTH),
                .WIDTH      (TILE_BRAM_WIDTH),
                .ADDR_WIDTH (TILE_BRAM_ADDR_WIDTH)
            ) u_tile_bram_left (
                .i_clk      (i_clk),
                .i_reset_n  (i_reset_n),

                // Mantissa Port A: Write from dispatcher
                .i_man_wr_addr  (i_dispatcher_man_wr_addr_left),
                .i_man_wr_data  (i_dispatcher_man_wr_data_left),
                .i_man_wr_en    (i_dispatcher_man_wr_en_left[t]),

                // Mantissa Port B: Read from compute engine
                .i_man_rd_addr  (tile_left_rd_addr[t]),
                .o_man_rd_data  (tile_left_rd_data[t]),
                .i_man_rd_en    (tile_left_rd_en[t]),

                // Exponent Write Interface: Write from dispatcher
                .i_exp_wr_addr  (i_dispatcher_exp_wr_addr_left),
                .i_exp_wr_data  (i_dispatcher_exp_wr_data_left),
                .i_exp_wr_en    (i_dispatcher_exp_wr_en_left[t]),

                // Exponent Read Interface: Read from compute engine
                .i_exp_rd_addr  (tile_left_exp_rd_addr[t]),
                .o_exp_rd_data  (tile_left_exp_rd_data[t])
            );

            // ---------------------------------------------------------------
            // tile_bram_right - Private L1 cache for weights
            // ---------------------------------------------------------------
            tile_bram_wrapper #(
                .DEPTH      (TILE_BRAM_DEPTH),
                .WIDTH      (TILE_BRAM_WIDTH),
                .ADDR_WIDTH (TILE_BRAM_ADDR_WIDTH)
            ) u_tile_bram_right (
                .i_clk      (i_clk),
                .i_reset_n  (i_reset_n),

                // Mantissa Port A: Write from dispatcher
                .i_man_wr_addr  (i_dispatcher_man_wr_addr_right),
                .i_man_wr_data  (i_dispatcher_man_wr_data_right),
                .i_man_wr_en    (i_dispatcher_man_wr_en_right[t]),

                // Mantissa Port B: Read from compute engine
                .i_man_rd_addr  (tile_right_rd_addr[t]),
                .o_man_rd_data  (tile_right_rd_data[t]),
                .i_man_rd_en    (tile_right_rd_en[t]),

                // Exponent Write Interface: Write from dispatcher
                .i_exp_wr_addr  (i_dispatcher_exp_wr_addr_right),
                .i_exp_wr_data  (i_dispatcher_exp_wr_data_right),
                .i_exp_wr_en    (i_dispatcher_exp_wr_en_right[t]),

                // Exponent Read Interface: Read from compute engine
                .i_exp_rd_addr  (tile_right_exp_rd_addr[t]),
                .o_exp_rd_data  (tile_right_exp_rd_data[t])
            );

            // ---------------------------------------------------------------
            // compute_engine_modular - Matrix multiplication engine
            // ---------------------------------------------------------------
            logic tile_en_gated;
            assign tile_en_gated = i_tile_en && i_column_enable[t];

            compute_engine_modular u_compute_engine (
                .i_clk               (i_clk),
                .i_reset_n           (i_reset_n),

                // Tile command
                .i_tile_en           (tile_en_gated),
                .i_left_addr         (i_left_addr),
                .i_right_addr        (i_right_addr),
                .i_left_ugd_len      (i_left_ugd_len),
                .i_right_ugd_len     (i_right_ugd_len),
                .i_vec_len           (i_vec_len),
                .i_dim_b             (i_dim_b),
                .i_dim_c             (i_dim_c),
                .i_dim_v             (i_dim_v),
                .i_left_man_4b       (i_left_man_4b),
                .i_right_man_4b      (i_right_man_4b),
                .i_main_loop_over_left (i_main_loop_over_left),
                .o_tile_done         (tile_done[t]),

                // Left BRAM mantissa read interface (private tile_bram)
                .o_bram_left_rd_addr (tile_left_rd_addr[t]),
                .o_bram_left_rd_en   (tile_left_rd_en[t]),
                .i_bram_left_rd_data (tile_left_rd_data[t]),

                // Right BRAM mantissa read interface (private tile_bram)
                .o_bram_right_rd_addr (tile_right_rd_addr[t]),
                .o_bram_right_rd_en   (tile_right_rd_en[t]),
                .i_bram_right_rd_data (tile_right_rd_data[t]),

                // Left exponent BRAM read interface (per-tile, from tile_bram_left)
                .o_left_exp_rd_addr  (tile_left_exp_rd_addr[t]),
                .i_left_exp_rd_data  (tile_left_exp_rd_data[t]),

                // Right exponent BRAM read interface (per-tile, from tile_bram_right)
                .o_right_exp_rd_addr (tile_right_exp_rd_addr[t]),
                .i_right_exp_rd_data (tile_right_exp_rd_data[t]),

                // Result output
                .o_result_data       (tile_result_data[t]),
                .o_result_valid      (tile_result_valid[t]),
                .i_result_full       (i_result_full),
                .i_result_afull      (i_result_afull),

                // Debug
                .o_ce_state          (o_ce_state[t]),
                .o_result_count      ()  // Not used in array, discard
            );

        end
    endgenerate

    // ===================================================================
    // Result Collection Logic (Tile-Major Order)
    // ===================================================================
    // Simple priority encoder: Output results from lowest tile ID first
    // More sophisticated collection in result_collector.sv (Phase 4)

    logic [3:0] active_tile_idx;

    always_comb begin
        // Default: no active tile
        active_tile_idx = 4'd0;
        o_result_data = 16'h0000;
        o_result_valid = 1'b0;

        // Priority encoder: Find first tile with valid result
        for (int i = 0; i < NUM_TILES; i++) begin
            if (tile_result_valid[i]) begin
                active_tile_idx = i[3:0];
                o_result_data = tile_result_data[i];
                o_result_valid = 1'b1;
                break;  // Exit on first match
            end
        end
    end

    assign o_result_tile_id = active_tile_idx;

    // ===================================================================
    // Tile Done Aggregation
    // ===================================================================
    // All enabled tiles must be done for o_tile_done to assert
    always_comb begin
        o_tile_done = 1'b1;  // Assume done
        for (int i = 0; i < NUM_TILES; i++) begin
            if (i_column_enable[i]) begin
                o_tile_done = o_tile_done && tile_done[i];
            end
        end
    end

endmodule
