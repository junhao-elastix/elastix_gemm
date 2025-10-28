// ------------------------------------------------------------------
// MS2.0 GEMM Engine Top Module
//
// Purpose: Complete GEMM engine with direct FIFO interface for hardware
// Contains:
//  - Command FIFO (4096×32-bit): Buffers incoming microcode commands
//  - Master Control (MC): Unified command processor and router
//  - Dispatcher Control (DC): GDDR6 fetch and BRAM buffering
//  - Compute Engine (CE): Modular GFP8 matrix multiplication
//  - Result FIFO (16384×16-bit): Buffers FP16 computation results
//
// Data Flow:
//  Host → cmd_fifo → master_control →
//    → dispatcher_control → GDDR6 NAP → dispatcher_bram (dual-read) →
//    → compute_engine_modular → result_fifo → Host
//
// Key Features:
//  - Direct FIFO interface (no CSR bridge)
//  - Dual-port BRAM for parallel left/right matrix access
//  - FP16 result output (no FP24 conversion)
//  - Configurable GDDR6 page ID
//  - Comprehensive debug/status outputs
//
// Author: MS2.0 FIFO Architecture Integration
// Date: Sun Oct 12 2025
// ------------------------------------------------------------------

`include "nap_interfaces.svh"

module engine_top
import gemm_pkg::*;
#(
    parameter [8:0] GDDR6_PAGE_ID = 9'd2,   // GDDR6 Channel page ID
    parameter TGT_DATA_WIDTH = 256,         // Target data width (256-bit AXI)
    parameter AXI_ADDR_WIDTH = 42,          // AXI address width (42-bit for GDDR6)
    parameter NUM_TILES = 16                // Number of parallel compute tiles (max 16)
)
(
    // Clock and Reset
    input  logic                         i_clk,       // System clock (200MHz)
    input  logic                         i_reset_n,   // Active-low reset

    // ====================================================================
    // Host Command FIFO Interface (Direct Write)
    // ====================================================================
    input  logic [31:0]                  i_cmd_fifo_wdata,
    input  logic                         i_cmd_fifo_wen,
    output logic                         o_cmd_fifo_full,
    output logic                         o_cmd_fifo_afull,
    output logic [12:0]                  o_cmd_fifo_count,

    // ====================================================================
    // Host Result FIFO Interface (Direct Read)
    // ====================================================================
    output logic [15:0]                  o_result_fifo_rdata,    // FP16 result data
    input  logic                         i_result_fifo_ren,      // Read enable from host
    output logic                         o_result_fifo_empty,    // FIFO empty flag
    output logic [14:0]                  o_result_fifo_count,    // Number of results available

    // ====================================================================
    // NAP AXI Interface (to GDDR6)
    // ====================================================================
    t_AXI4.initiator                     nap_axi,

    // ====================================================================
    // Status Outputs
    // ====================================================================
    output logic                         o_engine_busy,
    output logic [3:0]                   o_mc_state,      // Master control state
    output logic [3:0]                   o_mc_state_next, // Master control next state
    output logic [3:0]                   o_dc_state,      // Dispatcher control state
    output logic [3:0]                   o_ce_state [0:NUM_TILES-1], // Per-tile compute engine states
    output logic [cmd_op_width_gp-1:0]   o_last_opcode,   // Last executed opcode

    // ====================================================================
    // Debug Outputs
    // ====================================================================
    output logic [9:0]                   o_bram_wr_count,         // BRAM write counter
    output logic [15:0]                  o_result_count,          // Result counter
    output logic [31:0]                  o_mc_tile_dimensions,    // MC TILE dims {dim_b, dim_c, dim_v, 8'h00}
    output logic [31:0]                  o_mc_payload_word1,      // MC payload word 1
    output logic [31:0]                  o_mc_payload_word2,      // MC payload word 2
    output logic [31:0]                  o_mc_payload_word3,      // MC payload word 3
    output logic [31:0]                  o_bcv_debug_state,       // BCV controller state
    output logic [31:0]                  o_bcv_debug_dimensions   // BCV captured dimensions
);

    // ===================================================================
    // Internal Connection Signals
    // ===================================================================

    // Command FIFO → Master Control
    logic [31:0]  cmd_fifo_rdata;
    logic         cmd_fifo_empty;
    logic [12:0]  cmd_fifo_count;
    logic         cmd_fifo_ren;

    // Master Control → Dispatcher Control
    logic                                mc_dc_fetch_en;
    logic [link_addr_width_gp-1:0]       mc_dc_fetch_addr;
    logic [link_len_width_gp-1:0]        mc_dc_fetch_len;
    logic                                mc_dc_fetch_target; // 0=left, 1=right
    logic                                dc_mc_fetch_done;

    logic                                mc_dc_disp_en;
    logic [tile_mem_addr_width_gp-1:0]   mc_dc_disp_addr;
    logic [tile_mem_addr_width_gp-1:0]   mc_dc_disp_len;
    logic                                mc_dc_man_4b_8b_n;
    logic                                dc_mc_disp_done;

    // Master Control → Compute Tile Array
    logic                                mc_ce_tile_en;
    logic [NUM_TILES-1:0]                mc_ce_column_enable;  // NEW: Which tiles to execute
    logic [tile_mem_addr_width_gp-1:0]   mc_ce_left_addr;
    logic [tile_mem_addr_width_gp-1:0]   mc_ce_right_addr;
    logic [tile_mem_addr_width_gp-1:0]   mc_ce_left_ugd_len;
    logic [tile_mem_addr_width_gp-1:0]   mc_ce_right_ugd_len;
    logic [tile_mem_addr_width_gp-1:0]   mc_ce_vec_len;
    logic [7:0]                          mc_ce_dim_b;
    logic [7:0]                          mc_ce_dim_c;
    logic [7:0]                          mc_ce_dim_v;
    logic                                mc_ce_left_man_4b;
    logic                                mc_ce_right_man_4b;
    logic                                mc_ce_main_loop_over_left;
    logic                                ce_mc_tile_done;

    // NEW: Dispatcher Control → Tile Array Write Interface
    // Left mantissa writes (broadcast to all tiles)
    logic [NUM_TILES-1:0]  dc_tile_man_wr_en_left;
    logic [8:0]            dc_tile_man_wr_addr_left;
    logic [255:0]          dc_tile_man_wr_data_left;

    // Right mantissa writes (distribute to tiles)
    logic [NUM_TILES-1:0]  dc_tile_man_wr_en_right;
    logic [8:0]            dc_tile_man_wr_addr_right;
    logic [255:0]          dc_tile_man_wr_data_right;

    // Left exponent writes (broadcast to all tiles)
    logic [NUM_TILES-1:0]  dc_tile_exp_wr_en_left;
    logic [8:0]            dc_tile_exp_wr_addr_left;
    logic [7:0]            dc_tile_exp_wr_data_left;

    // Right exponent writes (distribute to tiles)
    logic [NUM_TILES-1:0]  dc_tile_exp_wr_en_right;
    logic [8:0]            dc_tile_exp_wr_addr_right;
    logic [7:0]            dc_tile_exp_wr_data_right;

    // Compute Tile Array → Result FIFO
    logic [15:0]   ce_result_data;     // FP16 results
    logic          ce_result_valid;
    logic [3:0]    ce_result_tile_id;  // NEW: Which tile produced this result
    logic          result_fifo_full;
    logic          result_fifo_afull;

    // Hardcoded single-tile configuration for Phase 1
    // Phase 3 will update master_control to provide column_enable from MATMUL command
    assign mc_ce_column_enable = 16'h0001;  // Enable only tile 0 for Phase 1

    // Debug signals
    logic [3:0]  mc_state;
    logic [3:0]  mc_state_next;
    logic [3:0]  dc_state;
    logic [3:0]  ce_state [0:NUM_TILES-1];  // Per-tile states
    logic [cmd_op_width_gp-1:0] last_opcode;
    logic [9:0]  bram_wr_count;
    logic [15:0] result_count;

    // Phase 2: Dispatcher write ports now connected (minimal DISPATCH implementation)
    // These will be properly driven by dispatcher_control during ST_DISPATCH
    // (Removed temporary tie-offs)

    // ===================================================================
    // Module Instantiations
    // ===================================================================

    // ------------------------------------------------------------------
    // Command FIFO - Buffers incoming microcode commands
    // ------------------------------------------------------------------
    cmd_fifo u_cmd_fifo (
        .i_clk              (i_clk),
        .i_reset_n          (i_reset_n),

        // Write Interface (from Host/PCIe)
        .i_wr_data          (i_cmd_fifo_wdata),
        .i_wr_en            (i_cmd_fifo_wen),
        .o_full             (o_cmd_fifo_full),
        .o_afull            (o_cmd_fifo_afull),

        // Read Interface (to Master Control)
        .o_rd_data          (cmd_fifo_rdata),
        .i_rd_en            (cmd_fifo_ren),
        .o_empty            (cmd_fifo_empty),

        // Status
        .o_count            (cmd_fifo_count)
    );

    assign o_cmd_fifo_count = cmd_fifo_count;

    // ------------------------------------------------------------------
    // Master Control - Unified command processor and router
    // ------------------------------------------------------------------
    master_control u_master_control (
        .i_clk              (i_clk),
        .i_reset_n          (i_reset_n),

        // Bypass mode (0 = normal operation)
        .i_bypass_mode      (2'b00),

        // Command FIFO Interface
        .i_cmd_fifo_rdata   (cmd_fifo_rdata),
        .i_cmd_fifo_empty   (cmd_fifo_empty),
        .i_cmd_fifo_count   (cmd_fifo_count),
        .o_cmd_fifo_ren     (cmd_fifo_ren),
        
        // Peripheral State Inputs (for command synchronization)
        .i_dc_state         (dc_state),
        .i_ce_state         (ce_state[0]),      // Phase 1: Use tile[0] state for single-tile compatibility
        .i_result_fifo_afull(result_fifo_afull),

        // Dispatcher Control Interface (FETCH/DISP commands)
        .o_dc_fetch_en      (mc_dc_fetch_en),
        .o_dc_fetch_addr    (mc_dc_fetch_addr),
        .o_dc_fetch_len     (mc_dc_fetch_len),
        .o_dc_fetch_target  (mc_dc_fetch_target),
        .i_dc_fetch_done    (dc_mc_fetch_done),

        .o_dc_disp_en       (mc_dc_disp_en),
        .o_dc_disp_addr     (mc_dc_disp_addr),
        .o_dc_disp_len      (mc_dc_disp_len),
        .o_dc_man_4b_8b_n   (mc_dc_man_4b_8b_n),
        .i_dc_disp_done     (dc_mc_disp_done),

        // Compute Engine Interface (TILE command)
        .o_ce_tile_en       (mc_ce_tile_en),
        .o_ce_left_addr     (mc_ce_left_addr),
        .o_ce_right_addr    (mc_ce_right_addr),
        .o_ce_left_ugd_len  (mc_ce_left_ugd_len),
        .o_ce_right_ugd_len (mc_ce_right_ugd_len),
        .o_ce_vec_len       (mc_ce_vec_len),
        .o_ce_dim_b         (mc_ce_dim_b),
        .o_ce_dim_c         (mc_ce_dim_c),
        .o_ce_dim_v         (mc_ce_dim_v),
        .o_ce_left_man_4b   (mc_ce_left_man_4b),
        .o_ce_right_man_4b  (mc_ce_right_man_4b),
        .o_ce_main_loop_over_left (mc_ce_main_loop_over_left),
        .i_ce_tile_done     (ce_mc_tile_done),

        // Status/Debug
        .o_mc_state         (mc_state),
        .o_mc_state_next    (mc_state_next),
        .o_last_opcode      (last_opcode),
        .o_mc_sees_count    (),  // Unused
        .o_cmd_op_debug     (),  // Unused
        .o_mc_tile_dimensions (o_mc_tile_dimensions),
        .o_mc_payload_word1 (o_mc_payload_word1),
        .o_mc_payload_word2 (o_mc_payload_word2),
        .o_mc_payload_word3 (o_mc_payload_word3)
    );

    // ------------------------------------------------------------------
    // Dispatcher Control - GDDR6 fetch and BRAM buffering
    // ------------------------------------------------------------------
    dispatcher_control #(
        .TGT_DATA_WIDTH     (TGT_DATA_WIDTH),
        .AXI_ADDR_WIDTH     (AXI_ADDR_WIDTH),
        .BRAM_DEPTH         (2048),           // Dual 128×128 matrix buffer
        .GDDR6_PAGE_ID      (GDDR6_PAGE_ID),
        .NUM_TILES          (NUM_TILES)       // NEW: Number of tiles
    ) u_dispatcher_control (
        .i_clk              (i_clk),
        .i_reset_n          (i_reset_n),

        // Master Control Interface
        .i_fetch_en         (mc_dc_fetch_en),
        .i_fetch_addr       (mc_dc_fetch_addr),
        .i_fetch_len        (mc_dc_fetch_len),
        .i_fetch_target     (mc_dc_fetch_target),
        .o_fetch_done       (dc_mc_fetch_done),

        .i_disp_en          (mc_dc_disp_en),
        .i_disp_addr        (mc_dc_disp_addr),
        .i_disp_len         (mc_dc_disp_len),
        .i_man_4b_8b_n      (mc_dc_man_4b_8b_n),
        .o_disp_done        (dc_mc_disp_done),

        // NOTE: BRAM/Exponent ports kept for Phase 1 compatibility
        // These read ports are now unused (compute_tile_array has private tile_bram)
        .i_bram_rd_addr_left    (11'd0),            // Tied off
        .o_bram_rd_data_left    (),                 // Unconnected
        .i_bram_rd_en_left      (1'b0),             // Tied off

        .i_bram_rd_addr_right   (11'd0),            // Tied off
        .o_bram_rd_data_right   (),                 // Unconnected
        .i_bram_rd_en_right     (1'b0),             // Tied off

        .o_left_exp_wr_addr     (),                 // Unconnected
        .o_left_exp_wr_data     (),                 // Unconnected
        .o_left_exp_wr_en       (),                 // Unconnected

        .o_right_exp_wr_addr    (),                 // Unconnected
        .o_right_exp_wr_data    (),                 // Unconnected
        .o_right_exp_wr_en      (),                 // Unconnected

        .i_left_exp_rd_addr     (9'd0),             // Tied off
        .o_left_exp_rd_data     (),                 // Unconnected

        .i_right_exp_rd_addr    (9'd0),             // Tied off
        .o_right_exp_rd_data    (),                 // Unconnected

        // NEW Phase 2: Tile BRAM Write Interface (DISPATCH)
        .o_tile_man_wr_en_left      (dc_tile_man_wr_en_left),
        .o_tile_man_wr_addr_left    (dc_tile_man_wr_addr_left),
        .o_tile_man_wr_data_left    (dc_tile_man_wr_data_left),

        .o_tile_man_wr_en_right     (dc_tile_man_wr_en_right),
        .o_tile_man_wr_addr_right   (dc_tile_man_wr_addr_right),
        .o_tile_man_wr_data_right   (dc_tile_man_wr_data_right),

        .o_tile_exp_wr_en_left      (dc_tile_exp_wr_en_left),
        .o_tile_exp_wr_addr_left    (dc_tile_exp_wr_addr_left),
        .o_tile_exp_wr_data_left    (dc_tile_exp_wr_data_left),

        .o_tile_exp_wr_en_right     (dc_tile_exp_wr_en_right),
        .o_tile_exp_wr_addr_right   (dc_tile_exp_wr_addr_right),
        .o_tile_exp_wr_data_right   (dc_tile_exp_wr_data_right),

        // AXI GDDR6 Interface
        .axi_ddr_if         (nap_axi),

        // Debug
        .o_dc_state         (dc_state),
        .o_bram_wr_count    (bram_wr_count)
    );

    // ------------------------------------------------------------------
    // Compute Tile Array - NUM_TILES parallel compute engines with private L1 BRAMs
    // ------------------------------------------------------------------
    compute_tile_array #(
        .NUM_TILES          (NUM_TILES),
        .TILE_BRAM_DEPTH    (512),              // 512 lines = 128 NVs per tile
        .TILE_BRAM_WIDTH    (256),              // 256 bits/line
        .TILE_BRAM_ADDR_WIDTH (9)               // 9 bits for 512 depth
    ) u_compute_tile_array (
        .i_clk              (i_clk),
        .i_reset_n          (i_reset_n),

        // Tile Command Interface (from Master Control)
        .i_tile_en          (mc_ce_tile_en),
        .i_column_enable    (mc_ce_column_enable),  // NEW: Which tiles to execute
        .i_left_addr        (mc_ce_left_addr),
        .i_right_addr       (mc_ce_right_addr),
        .i_left_ugd_len     (mc_ce_left_ugd_len),
        .i_right_ugd_len    (mc_ce_right_ugd_len),
        .i_vec_len          (mc_ce_vec_len),
        .i_dim_b            (mc_ce_dim_b),
        .i_dim_c            (mc_ce_dim_c),
        .i_dim_v            (mc_ce_dim_v),
        .i_left_man_4b      (mc_ce_left_man_4b),
        .i_right_man_4b     (mc_ce_right_man_4b),
        .i_main_loop_over_left (mc_ce_main_loop_over_left),
        .o_tile_done        (ce_mc_tile_done),

        // Dispatcher Write Interface - Left Mantissa (broadcast)
        .i_dispatcher_man_wr_en_left    (dc_tile_man_wr_en_left),
        .i_dispatcher_man_wr_addr_left  (dc_tile_man_wr_addr_left),
        .i_dispatcher_man_wr_data_left  (dc_tile_man_wr_data_left),

        // Dispatcher Write Interface - Right Mantissa (distribute)
        .i_dispatcher_man_wr_en_right   (dc_tile_man_wr_en_right),
        .i_dispatcher_man_wr_addr_right (dc_tile_man_wr_addr_right),
        .i_dispatcher_man_wr_data_right (dc_tile_man_wr_data_right),

        // Dispatcher Write Interface - Left Exponent (broadcast)
        .i_dispatcher_exp_wr_en_left    (dc_tile_exp_wr_en_left),
        .i_dispatcher_exp_wr_addr_left  (dc_tile_exp_wr_addr_left),
        .i_dispatcher_exp_wr_data_left  (dc_tile_exp_wr_data_left),

        // Dispatcher Write Interface - Right Exponent (distribute)
        .i_dispatcher_exp_wr_en_right   (dc_tile_exp_wr_en_right),
        .i_dispatcher_exp_wr_addr_right (dc_tile_exp_wr_addr_right),
        .i_dispatcher_exp_wr_data_right (dc_tile_exp_wr_data_right),

        // Result Interface (tile-major output)
        .o_result_data      (ce_result_data),
        .o_result_valid     (ce_result_valid),
        .o_result_tile_id   (ce_result_tile_id),    // NEW: Tile ID for results
        .i_result_full      (result_fifo_full),
        .i_result_afull     (result_fifo_afull),

        // Debug
        .o_ce_state         (ce_state)              // Per-tile states array
    );

    // ------------------------------------------------------------------
    // Result FIFO - Buffers FP16 computation results
    // ------------------------------------------------------------------
    result_bram u_result_fifo (
        .i_clk              (i_clk),
        .i_reset_n          (i_reset_n),

        // Write Interface (from Compute Engine)
        .i_wr_data          (ce_result_data),
        .i_wr_en            (ce_result_valid),
        .o_full             (result_fifo_full),
        .o_afull            (result_fifo_afull),

        // Read Interface (to Host/PCIe)
        .o_rd_data          (o_result_fifo_rdata),
        .i_rd_en            (i_result_fifo_ren),
        .o_empty            (o_result_fifo_empty),

        // Status
        .o_count            (o_result_fifo_count)
    );

    // ===================================================================
    // Status Logic
    // ===================================================================

    // Engine is busy if any component is active
    logic any_tile_busy;
    always_comb begin
        any_tile_busy = 1'b0;
        for (int i = 0; i < NUM_TILES; i++) begin
            if (ce_state[i] != 4'd0) begin
                any_tile_busy = 1'b1;
                break;
            end
        end
    end

    assign o_engine_busy = (cmd_fifo_count != 13'd0) ||
                          (mc_state != 4'd0) ||
                          (dc_state != 4'd0) ||
                          any_tile_busy;

    // ===================================================================
    // Debug Output Assignments
    // ===================================================================
    assign o_mc_state = mc_state;
    assign o_mc_state_next = mc_state_next;
    assign o_dc_state = dc_state;
    assign o_ce_state = ce_state;
    assign o_last_opcode = last_opcode;
    assign o_bram_wr_count = bram_wr_count;
    assign o_result_count = result_count;
    
    // MC and BCV debug outputs (MC outputs connected to master_control, BCV tied off)
    // o_mc_tile_dimensions, o_mc_payload_word1/2/3 connected in master_control instantiation
    assign o_bcv_debug_state = 32'd0;       // BCV debug not exposed by compute_engine_modular
    assign o_bcv_debug_dimensions = 32'd0;  // BCV debug not exposed by compute_engine_modular

endmodule : engine_top

