// ------------------------------------------------------------------
// MS2.0 GEMM Engine Top Module (with Integrated Tile BRAM)
//
// Purpose: Complete GEMM engine with direct FIFO interface for hardware
// Contains:
//  - Command FIFO (4096x32-bit): Buffers incoming microcode commands
//  - Master Control (MC): Unified command processor and router
//  - Dispatcher Control (DC): GDDR6 fetch and L2 BRAM buffering
//  - Compute Engine (CE): Modular GFP8 matrix multiplication with private L1 tile_bram
//  - Result FIFO (16384x16-bit): Buffers FP16 computation results
//
// Data Flow (Three-Level Memory Hierarchy):
//  GDDR6 (L3) -> [FETCH] -> dispatcher_bram (L2) -> [DISPATCH] ->
//    -> tile_bram (L1, inside CE) -> [MATMUL] -> result_fifo -> Host
//
// Key Features:
//  - Integrated tile_bram inside compute_engine_modular (private L1 cache)
//  - DISPATCH copies dispatcher_bram → tile_bram (four parallel write paths)
//  - Direct FIFO interface (no CSR bridge)
//  - FP16 result output (no FP24 conversion)
//  - Configurable GDDR6 page ID
//  - Comprehensive debug/status outputs
//
// Author: MS2.0 FIFO Architecture Integration + Tile BRAM Integration
// Date: Mon Oct 27 2025
// ------------------------------------------------------------------

`include "nap_interfaces.svh"

module engine_top
import gemm_pkg::*;
#(
    parameter [8:0] GDDR6_PAGE_ID = 9'd2,   // GDDR6 Channel page ID
    parameter TGT_DATA_WIDTH = 256,         // Target data width (256-bit AXI)
    parameter AXI_ADDR_WIDTH = 42,          // AXI address width (42-bit for GDDR6)
    parameter int NUM_TILES = 2             // Number of parallel compute tiles (2-24)
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
    output logic [3:0]                   o_ce_state,      // Compute engine state
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

    // Command FIFO -> Master Control
    logic [31:0]  cmd_fifo_rdata;
    logic         cmd_fifo_empty;
    logic [12:0]  cmd_fifo_count;
    logic         cmd_fifo_ren;

    // Master Control -> Dispatcher Control
    logic                                mc_dc_fetch_en;
    logic [link_addr_width_gp-1:0]       mc_dc_fetch_addr;
    logic [link_len_width_gp-1:0]        mc_dc_fetch_len;
    logic                                mc_dc_fetch_target; // 0=left, 1=right
    logic                                dc_mc_fetch_done;

    logic                                mc_dc_disp_en;
    logic [15:0]                         mc_dc_disp_tile_addr;    // Expanded to 16-bit per spec
    logic [7:0]                          mc_dc_disp_man_nv_cnt;   // NEW: Total NVs to dispatch
    logic [7:0]                          mc_dc_disp_ugd_vec_size; // NEW: NVs per UGD vector
    logic                                mc_dc_disp_man_4b;       // Renamed from man_4b_8b_n
    logic [23:0]                         mc_dc_disp_col_en;       // UPDATED: 24-bit column enable mask (was 16-bit)
    logic [4:0]                          mc_dc_disp_col_start;    // UPDATED: 5-bit distribution start (was 6-bit)
    logic                                mc_dc_disp_right;        // NEW: Dispatch side (0=left, 1=right)
    logic                                mc_dc_disp_broadcast;    // NEW: Broadcast mode (0=distribute, 1=broadcast)
    logic                                dc_mc_disp_done;

    // Master Control -> Compute Engine
    // Master Control -> Compute Engine (spec-compliant)
    logic [23:0] mc_ce_tile_en;          // Per-tile enable (24 tiles max)
    logic [15:0] mc_ce_tile_left_addr;       // 16 bits: Left matrix start address
    logic [15:0] mc_ce_tile_right_addr;      // 16 bits: Right matrix start address
    logic [7:0]  mc_ce_tile_left_ugd_len;    // 8 bits: Left UGD vectors (Batch dimension)
    logic [7:0]  mc_ce_tile_right_ugd_len;   // 8 bits: Right UGD vectors (Column dimension)
    logic [7:0]  mc_ce_tile_vec_len;         // 8 bits: UGD vector size (Vector count)
    logic        mc_ce_tile_left_man_4b;
    logic        mc_ce_tile_right_man_4b;
    logic        mc_ce_tile_main_loop_over_left;
    logic        ce_mc_tile_done;

    // Dispatcher Control BRAM Read Ports (dispatcher_control ↔ dispatcher_bram)
    // Mantissa read data (dual ports) - used during DISPATCH operations
    logic [255:0]  dc_disp_man_left_rd_data;
    logic [255:0]  dc_disp_man_right_rd_data;

    // Dispatcher Control Exponent BRAM (dispatcher_control → dispatcher_bram)
    // Exponent write ports (from unpacking logic)
    logic [8:0]    dc_disp_exp_left_wr_addr;
    logic [7:0]    dc_disp_exp_left_wr_data;
    logic          dc_disp_exp_left_wr_en;

    logic [8:0]    dc_disp_exp_right_wr_addr;
    logic [7:0]    dc_disp_exp_right_wr_data;
    logic          dc_disp_exp_right_wr_en;

    // Exponent read data (dispatcher_bram → dispatcher_control during DISPATCH)
    logic [7:0]    dc_disp_exp_left_rd_data;
    logic [7:0]    dc_disp_exp_right_rd_data;

    // Dispatcher -> Tile BRAM (DISPATCH copy write ports)
    // FOUR PARALLEL WRITE PATHS - All driven by same counter [0-511]
    logic [8:0]    dc_tile_man_left_wr_addr;     // 9-bit: [0:511]
    logic [255:0]  dc_tile_man_left_wr_data;
    logic          dc_tile_man_left_wr_en;

    logic [8:0]    dc_tile_man_right_wr_addr;    // 9-bit: [0:511]
    logic [255:0]  dc_tile_man_right_wr_data;
    logic          dc_tile_man_right_wr_en;

    logic [8:0]    dc_tile_left_exp_wr_addr;
    logic [7:0]    dc_tile_left_exp_wr_data;
    logic          dc_tile_left_exp_wr_en;

    logic [8:0]    dc_tile_right_exp_wr_addr;
    logic [7:0]    dc_tile_right_exp_wr_data;
    logic          dc_tile_right_exp_wr_en;

    // DISPATCH operation read control
    logic [8:0]    dc_disp_rd_addr;      // 9-bit: dispatcher_bram is 512 deep
    logic          dc_disp_rd_en;

    // Multi-tile DISPATCH control (NEW: Per-tile write enables)
    logic [23:0]   dc_tile_wr_en;        // Per-tile write enable array [0:23]

    // Compute Engine -> Result FIFO
    logic [15:0]   ce_result_data;     // FP16 results
    logic          ce_result_valid;
    logic          result_fifo_full;
    logic          result_fifo_afull;

    // Debug signals
    logic [3:0]  mc_state;
    logic [3:0]  mc_state_next;
    logic [3:0]  dc_state;
    logic [3:0]  ce_state;
    logic [cmd_op_width_gp-1:0] last_opcode;
    logic [9:0]  bram_wr_count;
    logic [15:0] result_count;

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
        .i_ce_state         (ce_state),
        .i_result_fifo_afull(result_fifo_afull),

        // Dispatcher Control Interface (FETCH/DISP commands)
        .o_dc_fetch_en      (mc_dc_fetch_en),
        .o_dc_fetch_addr    (mc_dc_fetch_addr),
        .o_dc_fetch_len     (mc_dc_fetch_len),
        .o_dc_fetch_target  (mc_dc_fetch_target),
        .i_dc_fetch_done    (dc_mc_fetch_done),

        .o_dc_disp_en       (mc_dc_disp_en),
        .o_dc_disp_tile_addr    (mc_dc_disp_tile_addr),
        .o_dc_disp_man_nv_cnt   (mc_dc_disp_man_nv_cnt),
        .o_dc_disp_ugd_vec_size (mc_dc_disp_ugd_vec_size),
        .o_dc_disp_man_4b       (mc_dc_disp_man_4b),
        .o_dc_disp_col_en       (mc_dc_disp_col_en),
        .o_dc_disp_col_start    (mc_dc_disp_col_start),
        .o_dc_disp_right        (mc_dc_disp_right),      // NEW: Dispatch side
        .o_dc_disp_broadcast    (mc_dc_disp_broadcast),
        .i_dc_disp_done     (dc_mc_disp_done),

        // Compute Engine Interface (TILE command - spec-compliant)
        .o_ce_tile_en            (mc_ce_tile_en),
        .o_ce_tile_left_addr          (mc_ce_tile_left_addr),
        .o_ce_tile_right_addr         (mc_ce_tile_right_addr),
        .o_ce_tile_left_ugd_len       (mc_ce_tile_left_ugd_len),
        .o_ce_tile_right_ugd_len      (mc_ce_tile_right_ugd_len),
        .o_ce_tile_vec_len            (mc_ce_tile_vec_len),
        .o_ce_tile_left_man_4b        (mc_ce_tile_left_man_4b),
        .o_ce_tile_right_man_4b       (mc_ce_tile_right_man_4b),
        .o_ce_tile_main_loop_over_left (mc_ce_tile_main_loop_over_left),
        .i_ce_tile_done          (ce_mc_tile_done),

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
    // BRAM Read Connections (DISPATCH-only reads)
    // ------------------------------------------------------------------
    // Only dispatcher reads from dispatcher_bram during DISPATCH operations
    // Compute engine now has integrated tile_bram for MATMUL operations
    // No multiplexing needed - direct connections to dc_disp_rd_* signals

    // ------------------------------------------------------------------
    // Dispatcher Control - GDDR6 fetch and BRAM buffering
    // ------------------------------------------------------------------
    dispatcher_control #(
        .MAN_WIDTH          (TGT_DATA_WIDTH),
        .EXP_WIDTH          (8),
        .BRAM_DEPTH         (512),            // Dispatcher BRAM depth (matches dispatcher_bram hardcoded value)
        .TILE_DEPTH         (512),            // Tile BRAM depth per side
        .AXI_ADDR_WIDTH     (AXI_ADDR_WIDTH),
        .GDDR6_PAGE_ID      (GDDR6_PAGE_ID)
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
        .i_disp_tile_addr   (mc_dc_disp_tile_addr),
        .i_disp_man_nv_cnt  (mc_dc_disp_man_nv_cnt),
        .i_disp_ugd_vec_size(mc_dc_disp_ugd_vec_size),
        .i_disp_man_4b      (mc_dc_disp_man_4b),
        .i_disp_col_en      (mc_dc_disp_col_en),
        .i_disp_col_start   (mc_dc_disp_col_start),
        .i_disp_right       (mc_dc_disp_right),      // NEW: Dispatch side
        .i_disp_broadcast   (mc_dc_disp_broadcast),
        .o_disp_done        (dc_mc_disp_done),

        // Dispatcher BRAM Read Ports (dispatcher_bram → dispatcher_control during DISPATCH)
        .i_disp_man_left_rd_addr   (dc_disp_rd_addr),
        .i_disp_man_left_rd_en     (dc_disp_rd_en),
        .o_disp_man_left_rd_data   (dc_disp_man_left_rd_data),

        .i_disp_man_right_rd_addr  (dc_disp_rd_addr),
        .i_disp_man_right_rd_en    (dc_disp_rd_en),
        .o_disp_man_right_rd_data  (dc_disp_man_right_rd_data),

        // Dispatcher BRAM Exponent Write Ports (dispatcher_control → dispatcher_bram from unpacking)
        .o_disp_exp_left_wr_addr   (dc_disp_exp_left_wr_addr),
        .o_disp_exp_left_wr_en     (dc_disp_exp_left_wr_en),
        .o_disp_exp_left_wr_data   (dc_disp_exp_left_wr_data),

        .o_disp_exp_right_wr_addr  (dc_disp_exp_right_wr_addr),
        .o_disp_exp_right_wr_en    (dc_disp_exp_right_wr_en),
        .o_disp_exp_right_wr_data  (dc_disp_exp_right_wr_data),

        // Dispatcher BRAM Exponent Read Ports (dispatcher_bram → dispatcher_control during DISPATCH)
        .i_disp_exp_left_rd_addr   (dc_disp_rd_addr),
        .i_disp_exp_left_rd_en     (dc_disp_rd_en),
        .o_disp_exp_left_rd_data   (dc_disp_exp_left_rd_data),

        .i_disp_exp_right_rd_addr  (dc_disp_rd_addr),
        .i_disp_exp_right_rd_en    (dc_disp_rd_en),
        .o_disp_exp_right_rd_data  (dc_disp_exp_right_rd_data),

        // Tile BRAM Write Ports (for DISPATCH copy) - FOUR PARALLEL PATHS
        .o_tile_man_left_wr_addr   (dc_tile_man_left_wr_addr),
        .o_tile_man_left_wr_en     (dc_tile_man_left_wr_en),
        .o_tile_man_left_wr_data   (dc_tile_man_left_wr_data),

        .o_tile_man_right_wr_addr  (dc_tile_man_right_wr_addr),
        .o_tile_man_right_wr_en    (dc_tile_man_right_wr_en),
        .o_tile_man_right_wr_data  (dc_tile_man_right_wr_data),

        .o_tile_exp_left_wr_addr   (dc_tile_left_exp_wr_addr),
        .o_tile_exp_left_wr_en     (dc_tile_left_exp_wr_en),
        .o_tile_exp_left_wr_data   (dc_tile_left_exp_wr_data),

        .o_tile_exp_right_wr_addr  (dc_tile_right_exp_wr_addr),
        .o_tile_exp_right_wr_en    (dc_tile_right_exp_wr_en),
        .o_tile_exp_right_wr_data  (dc_tile_right_exp_wr_data),

        // AXI GDDR6 Interface
        .axi_ddr_if         (nap_axi),

        // Debug
        .o_dc_state         (dc_state),
        .o_disp_wr_count    (bram_wr_count),
        .o_disp_wr_addr     (),  // Unused
        .o_disp_wr_en       (),  // Unused

        // DISPATCH copy read control
        .o_disp_rd_addr     (dc_disp_rd_addr),
        .o_disp_rd_en       (dc_disp_rd_en),

        // Multi-tile write enable array (NEW: Per-tile dispatch control)
        .o_tile_wr_en       (dc_tile_wr_en)
    );

    // ------------------------------------------------------------------
    // Tile BRAM - Now integrated inside compute_engine_modular
    // Removed standalone instantiation (Oct 27, 2025)
    // ------------------------------------------------------------------

    // ------------------------------------------------------------------
    // Compute Engine Array - Multi-tile parallel execution
    // NOW WITH GENERATE LOOP for NUM_TILES instances (Oct 28, 2025)
    // ------------------------------------------------------------------
    // Per-tile signals (arrays)
    logic [15:0]   ce_result_data_arr [NUM_TILES];    // Per-tile result data
    logic          ce_result_valid_arr [NUM_TILES];   // Per-tile result valid
    logic          ce_tile_done_arr [NUM_TILES];      // Per-tile done signals
    logic [3:0]    ce_state_arr [NUM_TILES];          // Per-tile state
    logic [15:0]   result_count_arr [NUM_TILES];      // Per-tile result count

    generate
        for (genvar tile_id = 0; tile_id < NUM_TILES; tile_id++) begin : gen_compute_tiles
            compute_engine_modular u_compute_engine (
                .i_clk              (i_clk),
                .i_reset_n          (i_reset_n),

                // Master Control Interface (SELECTIVE per-tile enable)
                .i_tile_en                    (mc_ce_tile_en[tile_id]),
                .i_tile_left_addr             (mc_ce_tile_left_addr),
                .i_tile_right_addr            (mc_ce_tile_right_addr),
                .i_tile_left_ugd_len          (mc_ce_tile_left_ugd_len),
                .i_tile_right_ugd_len         (mc_ce_tile_right_ugd_len),
                .i_tile_vec_len               (mc_ce_tile_vec_len),
                .i_tile_left_man_4b           (mc_ce_tile_left_man_4b),
                .i_tile_right_man_4b          (mc_ce_tile_right_man_4b),
                .i_tile_main_loop_over_left   (mc_ce_tile_main_loop_over_left),
                .o_tile_done                  (ce_tile_done_arr[tile_id]),

                // Tile BRAM Write Interface (SELECTIVE per-tile write enables)
                // Combine global write enable with per-tile enable from dispatcher
                .i_man_left_wr_addr      (dc_tile_man_left_wr_addr),
                .i_man_left_wr_en        (dc_tile_man_left_wr_en && dc_tile_wr_en[tile_id]),
                .i_man_left_wr_data      (dc_tile_man_left_wr_data),

                .i_man_right_wr_addr     (dc_tile_man_right_wr_addr),
                .i_man_right_wr_en       (dc_tile_man_right_wr_en && dc_tile_wr_en[tile_id]),
                .i_man_right_wr_data     (dc_tile_man_right_wr_data),

                .i_left_exp_wr_addr      (dc_tile_left_exp_wr_addr),
                .i_left_exp_wr_en        (dc_tile_left_exp_wr_en && dc_tile_wr_en[tile_id]),
                .i_left_exp_wr_data      (dc_tile_left_exp_wr_data),

                .i_right_exp_wr_addr     (dc_tile_right_exp_wr_addr),
                .i_right_exp_wr_en       (dc_tile_right_exp_wr_en && dc_tile_wr_en[tile_id]),
                .i_right_exp_wr_data     (dc_tile_right_exp_wr_data),

                // Result FIFO Write Interface (per-tile outputs)
                .o_result_data      (ce_result_data_arr[tile_id]),
                .o_result_valid     (ce_result_valid_arr[tile_id]),
                .i_result_full      (result_fifo_full),
                .i_result_afull     (result_fifo_afull),

                // Debug
                .o_ce_state         (ce_state_arr[tile_id]),
                .o_result_count     (result_count_arr[tile_id])
            );
        end
    endgenerate

    // DEBUG: Monitor write enable gating for first few cycles
    logic [7:0] debug_cycle_cnt = 0;
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            debug_cycle_cnt <= 0;
        end else begin
            // Track first 10 cycles of any write enable activity
            if ((dc_tile_man_left_wr_en || dc_tile_man_right_wr_en ||
                 dc_tile_left_exp_wr_en || dc_tile_right_exp_wr_en) && debug_cycle_cnt < 10) begin
                debug_cycle_cnt <= debug_cycle_cnt + 1;

                $display("[ENG_WR_EN] @%0t cycle=%0d, dc_tile_wr_en=0x%06x",
                         $time, debug_cycle_cnt, dc_tile_wr_en);

                for (int i = 0; i < NUM_TILES; i++) begin
                    $display("[ENG_WR_EN] @%0t   tile[%0d]: wr_en_bit=%0b, man_left=%0b->%0b, man_right=%0b->%0b, exp_left=%0b->%0b, exp_right=%0b->%0b",
                             $time, i, dc_tile_wr_en[i],
                             dc_tile_man_left_wr_en, dc_tile_man_left_wr_en && dc_tile_wr_en[i],
                             dc_tile_man_right_wr_en, dc_tile_man_right_wr_en && dc_tile_wr_en[i],
                             dc_tile_left_exp_wr_en, dc_tile_left_exp_wr_en && dc_tile_wr_en[i],
                             dc_tile_right_exp_wr_en, dc_tile_right_exp_wr_en && dc_tile_wr_en[i]);
                end
            end

            // Reset counter if no activity for a while
            if (!dc_tile_man_left_wr_en && !dc_tile_man_right_wr_en &&
                !dc_tile_left_exp_wr_en && !dc_tile_right_exp_wr_en) begin
                if (debug_cycle_cnt >= 10) begin
                    debug_cycle_cnt <= 0;  // Reset for next DISPATCH
                end
            end
        end
    end

    // Aggregate tile_done signals (only check ENABLED tiles)
    always_comb begin
        ce_mc_tile_done = 1'b1;
        for (int i = 0; i < NUM_TILES; i++) begin
            if (mc_ce_tile_en[i]) begin  // Only check tiles that were enabled
                ce_mc_tile_done = ce_mc_tile_done && ce_tile_done_arr[i];
            end
        end
    end

    // ------------------------------------------------------------------
    // Result Arbiter - Row-Interleaved Result Collection
    // Collects results from tiles in row-major order for transparency
    // (per SINGLE_ROW_REFERENCE.md: results appear as single matrix)
    // ------------------------------------------------------------------
    typedef enum logic [2:0] {
        ARB_IDLE,
        ARB_COLLECT,
        ARB_NEXT_TILE,
        ARB_NEXT_ROW,
        ARB_DONE
    } arb_state_t;

    arb_state_t arb_state_reg;

    // Arbiter control registers
    logic [7:0]  arb_left_ugd_len_reg;      // Number of rows (B)
    logic [7:0]  arb_right_ugd_len_reg;     // Results per tile per row
    logic [4:0]  arb_current_tile_reg;      // Current tile being read (0 to NUM_TILES-1)
    logic [7:0]  arb_current_row_reg;       // Current row (0 to B-1)
    logic [23:0] arb_col_en_reg;            // Captured col_en from MATMUL start
    logic [7:0]  arb_result_cnt_reg;        // Results collected from current tile in current row

    // Result arbiter state machine
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            arb_state_reg <= ARB_IDLE;
            arb_left_ugd_len_reg <= 8'd0;
            arb_right_ugd_len_reg <= 8'd0;
            arb_col_en_reg <= 24'd0;
            arb_current_tile_reg <= 5'd0;
            arb_current_row_reg <= 8'd0;
            arb_result_cnt_reg <= 8'd0;
        end else begin
            case (arb_state_reg)
                ARB_IDLE: begin
                    // Wait for MATMUL command to start result collection
                    if (|mc_ce_tile_en) begin  // Start when ANY tile enabled
                        // Capture matrix dimensions AND tile enable mask
                        arb_left_ugd_len_reg <= mc_ce_tile_left_ugd_len;    // B (rows)
                        arb_right_ugd_len_reg <= mc_ce_tile_right_ugd_len;  // C per tile (cols per tile)
                        arb_col_en_reg <= mc_ce_tile_en;                    // Capture which tiles are enabled
                        arb_current_tile_reg <= 5'd0;
                        arb_current_row_reg <= 8'd0;
                        arb_result_cnt_reg <= 8'd0;
                        arb_state_reg <= ARB_COLLECT;
                    end
                end

                ARB_COLLECT: begin
                    // Collect results from current tile (for current row)
                    // Skip disabled tiles immediately (use CAPTURED col_en, not live signal)
                    if (!arb_col_en_reg[arb_current_tile_reg]) begin
                        // This tile was not enabled at MATMUL start, skip to next tile
                        arb_state_reg <= ARB_NEXT_TILE;
                    end else if (ce_result_valid_arr[arb_current_tile_reg] && !result_fifo_full) begin
                        // Result transferred to FIFO
                        arb_result_cnt_reg <= arb_result_cnt_reg + 1;

                        if (arb_result_cnt_reg == arb_right_ugd_len_reg - 1) begin
                            // Collected all results from current tile for this row
                            arb_state_reg <= ARB_NEXT_TILE;
                        end
                    end
                end

                ARB_NEXT_TILE: begin
                    arb_result_cnt_reg <= 8'd0;
                    arb_current_tile_reg <= arb_current_tile_reg + 1;

                    if (arb_current_tile_reg == NUM_TILES - 1) begin
                        // All physical tiles checked (enabled or not)
                        arb_state_reg <= ARB_NEXT_ROW;
                    end else begin
                        // More tiles to check for this row
                        arb_state_reg <= ARB_COLLECT;
                    end
                end

                ARB_NEXT_ROW: begin
                    arb_current_tile_reg <= 5'd0;
                    arb_current_row_reg <= arb_current_row_reg + 1;

                    if (arb_current_row_reg == arb_left_ugd_len_reg - 1) begin
                        // All rows complete
                        arb_state_reg <= ARB_DONE;
                    end else begin
                        // More rows to collect
                        arb_state_reg <= ARB_COLLECT;
                    end
                end

                ARB_DONE: begin
                    // Wait for next MATMUL command
                    // Stay in DONE until new tile_en (state will reset via IDLE)
                    if (|mc_ce_tile_en) begin  // New MATMUL when ANY tile enabled
                        arb_state_reg <= ARB_IDLE;  // Will start new collection next cycle
                    end
                end

                default: arb_state_reg <= ARB_IDLE;
            endcase
        end
    end

    // Mux result data/valid based on current tile being read
    assign ce_result_data = ce_result_data_arr[arb_current_tile_reg];
    assign ce_result_valid = (arb_state_reg == ARB_COLLECT) ?
                             ce_result_valid_arr[arb_current_tile_reg] : 1'b0;

    // Debug outputs: Use tile 0 for state monitoring
    assign ce_state = ce_state_arr[0];
    assign result_count = result_count_arr[0];

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
    assign o_engine_busy = (cmd_fifo_count != 13'd0) ||
                          (mc_state != 4'd0) ||
                          (dc_state != 4'd0) ||
                          (ce_state != 4'd0);

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

