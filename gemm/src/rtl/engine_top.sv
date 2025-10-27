// ------------------------------------------------------------------
// MS2.0 GEMM Engine Top Module
//
// Purpose: Complete GEMM engine with direct FIFO interface for hardware
// Contains:
//  - Command FIFO (4096x32-bit): Buffers incoming microcode commands
//  - Master Control (MC): Unified command processor and router
//  - Dispatcher Control (DC): GDDR6 fetch and BRAM buffering
//  - Compute Engine (CE): Modular GFP8 matrix multiplication
//  - Result FIFO (16384x16-bit): Buffers FP16 computation results
//
// Data Flow:
//  Host -> cmd_fifo -> master_control ->
//    -> dispatcher_control -> GDDR6 NAP -> dispatcher_bram (dual-read) ->
//    -> compute_engine_modular -> result_fifo -> Host
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
    parameter AXI_ADDR_WIDTH = 42           // AXI address width (42-bit for GDDR6)
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
    logic [15:0]                         mc_dc_disp_col_en;       // NEW: Column enable mask
    logic [5:0]                          mc_dc_disp_col_start;    // NEW: Distribution start column
    logic                                mc_dc_disp_broadcast;    // NEW: Broadcast mode (reserved)
    logic                                dc_mc_disp_done;

    // Master Control -> Compute Engine
    // Master Control -> Compute Engine (spec-compliant)
    logic        mc_ce_tile_en;
    logic [15:0] mc_ce_left_addr;       // 16 bits: Left matrix start address
    logic [15:0] mc_ce_right_addr;      // 16 bits: Right matrix start address
    logic [7:0]  mc_ce_left_ugd_len;    // 8 bits: Left UGD vectors (Batch dimension)
    logic [7:0]  mc_ce_right_ugd_len;   // 8 bits: Right UGD vectors (Column dimension)
    logic [7:0]  mc_ce_vec_len;         // 8 bits: UGD vector size (Vector count)
    logic        mc_ce_left_man_4b;
    logic        mc_ce_right_man_4b;
    logic        mc_ce_main_loop_over_left;
    logic        ce_mc_tile_done;

    // Dispatcher Control BRAM -> Compute Engine (Dual Read Ports)
    // Left matrix mantissa port
    logic [10:0]   ce_dc_bram_rd_addr_left;
    logic [255:0]  dc_ce_bram_rd_data_left;
    logic          ce_dc_bram_rd_en_left;
    
    // Right matrix mantissa port
    logic [10:0]   ce_dc_bram_rd_addr_right;
    logic [255:0]  dc_ce_bram_rd_data_right;
    logic          ce_dc_bram_rd_en_right;
    
    // NEW: Dispatcher Control Exponent BRAM -> Compute Engine
    // Exponent write ports (from dispatcher unpacking)
    logic [8:0]    dc_left_exp_wr_addr;
    logic [7:0]    dc_left_exp_wr_data;
    logic          dc_left_exp_wr_en;

    logic [8:0]    dc_right_exp_wr_addr;
    logic [7:0]    dc_right_exp_wr_data;
    logic          dc_right_exp_wr_en;

    // Exponent read ports (to compute engine)
    logic [8:0]    ce_dc_left_exp_rd_addr;
    logic [7:0]    dc_ce_left_exp_rd_data;

    logic [8:0]    ce_dc_right_exp_rd_addr;
    logic [7:0]    dc_ce_right_exp_rd_data;

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
    logic [10:0]   dc_disp_rd_addr;
    logic          dc_disp_rd_en;

    // Tile BRAM -> Compute Engine (final data path)
    logic [255:0]  tile_ce_bram_rd_data_left;
    logic [255:0]  tile_ce_bram_rd_data_right;
    logic [7:0]    tile_ce_left_exp_rd_data;
    logic [7:0]    tile_ce_right_exp_rd_data;

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
        .o_dc_disp_broadcast    (mc_dc_disp_broadcast),
        .i_dc_disp_done     (dc_mc_disp_done),

        // Compute Engine Interface (TILE command - spec-compliant)
        .o_ce_tile_en            (mc_ce_tile_en),
        .o_ce_left_addr          (mc_ce_left_addr),
        .o_ce_right_addr         (mc_ce_right_addr),
        .o_ce_left_ugd_len       (mc_ce_left_ugd_len),
        .o_ce_right_ugd_len      (mc_ce_right_ugd_len),
        .o_ce_vec_len            (mc_ce_vec_len),
        .o_ce_left_man_4b        (mc_ce_left_man_4b),
        .o_ce_right_man_4b       (mc_ce_right_man_4b),
        .o_ce_main_loop_over_left (mc_ce_main_loop_over_left),
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
    // BRAM Read Address Muxing (for DISPATCH copy vs. normal CE read)
    // ------------------------------------------------------------------
    // During DISPATCH operation (dc_disp_rd_en=1), dispatcher reads from its own internal BRAM
    // With interleaved addressing: same address drives both left and right ports
    // Otherwise, CE drives the read addresses for normal MATMUL operation.
    logic [10:0] disp_bram_rd_addr_left_muxed;
    logic        disp_bram_rd_en_left_muxed;
    logic [10:0] disp_bram_rd_addr_right_muxed;
    logic        disp_bram_rd_en_right_muxed;
    logic [8:0]  disp_left_exp_rd_addr_muxed;
    logic [8:0]  disp_right_exp_rd_addr_muxed;

    // Mantissa read port muxing
    assign disp_bram_rd_addr_left_muxed  = dc_disp_rd_en ? dc_disp_rd_addr : ce_dc_bram_rd_addr_left;
    assign disp_bram_rd_en_left_muxed    = dc_disp_rd_en ? 1'b1 : ce_dc_bram_rd_en_left;
    assign disp_bram_rd_addr_right_muxed = dc_disp_rd_en ? dc_disp_rd_addr : ce_dc_bram_rd_addr_right;
    assign disp_bram_rd_en_right_muxed   = dc_disp_rd_en ? 1'b1 : ce_dc_bram_rd_en_right;

    // Exponent read port muxing
    assign disp_left_exp_rd_addr_muxed   = dc_disp_rd_en ? dc_disp_rd_addr[8:0] : ce_dc_left_exp_rd_addr;
    assign disp_right_exp_rd_addr_muxed  = dc_disp_rd_en ? dc_disp_rd_addr[8:0] : ce_dc_right_exp_rd_addr;

    // ------------------------------------------------------------------
    // Dispatcher Control - GDDR6 fetch and BRAM buffering
    // ------------------------------------------------------------------
    dispatcher_control #(
        .TGT_DATA_WIDTH     (TGT_DATA_WIDTH),
        .AXI_ADDR_WIDTH     (AXI_ADDR_WIDTH),
        .BRAM_DEPTH         (2048),           // Dual 128x128 matrix buffer
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
        .i_disp_broadcast   (mc_dc_disp_broadcast),
        .o_disp_done        (dc_mc_disp_done),

        // Dual BRAM Read Ports (for Compute Engine / DISPATCH copy)
        .i_bram_rd_addr_left    (disp_bram_rd_addr_left_muxed),   // Muxed for DISPATCH copy
        .o_bram_rd_data_left    (dc_ce_bram_rd_data_left),
        .i_bram_rd_en_left      (disp_bram_rd_en_left_muxed),     // Muxed for DISPATCH copy

        .i_bram_rd_addr_right   (disp_bram_rd_addr_right_muxed),  // Muxed for DISPATCH copy
        .o_bram_rd_data_right   (dc_ce_bram_rd_data_right),
        .i_bram_rd_en_right     (disp_bram_rd_en_right_muxed),    // Muxed for DISPATCH copy
        
        // NEW: Exponent Write Ports (from unpacking logic)
        .o_left_exp_wr_addr     (dc_left_exp_wr_addr),
        .o_left_exp_wr_data     (dc_left_exp_wr_data),
        .o_left_exp_wr_en       (dc_left_exp_wr_en),
        
        .o_right_exp_wr_addr    (dc_right_exp_wr_addr),
        .o_right_exp_wr_data    (dc_right_exp_wr_data),
        .o_right_exp_wr_en      (dc_right_exp_wr_en),
        
        // NEW: Exponent Read Ports (MUXED: DISPATCH operation uses dc_disp_rd_addr, else CE addresses)
        .i_left_exp_rd_addr     (disp_left_exp_rd_addr_muxed),
        .o_left_exp_rd_data     (dc_ce_left_exp_rd_data),

        .i_right_exp_rd_addr    (disp_right_exp_rd_addr_muxed),
        .o_right_exp_rd_data    (dc_ce_right_exp_rd_data),

        // Tile BRAM Write Ports (for DISPATCH copy) - FOUR PARALLEL PATHS
        .o_tile_man_left_wr_addr   (dc_tile_man_left_wr_addr),
        .o_tile_man_left_wr_data   (dc_tile_man_left_wr_data),
        .o_tile_man_left_wr_en     (dc_tile_man_left_wr_en),

        .o_tile_man_right_wr_addr  (dc_tile_man_right_wr_addr),
        .o_tile_man_right_wr_data  (dc_tile_man_right_wr_data),
        .o_tile_man_right_wr_en    (dc_tile_man_right_wr_en),

        .o_tile_left_exp_wr_addr   (dc_tile_left_exp_wr_addr),
        .o_tile_left_exp_wr_data   (dc_tile_left_exp_wr_data),
        .o_tile_left_exp_wr_en     (dc_tile_left_exp_wr_en),

        .o_tile_right_exp_wr_addr  (dc_tile_right_exp_wr_addr),
        .o_tile_right_exp_wr_data  (dc_tile_right_exp_wr_data),
        .o_tile_right_exp_wr_en    (dc_tile_right_exp_wr_en),

        // AXI GDDR6 Interface
        .axi_ddr_if         (nap_axi),

        // Debug
        .o_dc_state         (dc_state),
        .o_bram_wr_count    (bram_wr_count),
        .o_bram_wr_addr     (),  // Unused
        .o_bram_wr_en       (),  // Unused

        // DISPATCH copy read control
        .o_disp_rd_addr     (dc_disp_rd_addr),
        .o_disp_rd_en       (dc_disp_rd_en)
    );

    // ------------------------------------------------------------------
    // Tile BRAM - L1 memory with separate left/right architecture
    // ------------------------------------------------------------------
    tile_bram #(
        .DATA_WIDTH      (256),
        .MANTISSA_DEPTH  (512),   // 512 lines per side (left/right)
        .EXP_DEPTH       (512)
    ) u_tile_bram (
        .i_clk       (i_clk),
        .i_reset_n   (i_reset_n),

        // Write ports - FOUR PARALLEL PATHS
        // All four can write in SAME cycle with counter [0-511]
        .i_man_left_wr_addr   (dc_tile_man_left_wr_addr),
        .i_man_left_wr_data   (dc_tile_man_left_wr_data),
        .i_man_left_wr_en     (dc_tile_man_left_wr_en),

        .i_man_right_wr_addr  (dc_tile_man_right_wr_addr),
        .i_man_right_wr_data  (dc_tile_man_right_wr_data),
        .i_man_right_wr_en    (dc_tile_man_right_wr_en),

        .i_left_exp_wr_addr   (dc_tile_left_exp_wr_addr),
        .i_left_exp_wr_data   (dc_tile_left_exp_wr_data),
        .i_left_exp_wr_en     (dc_tile_left_exp_wr_en),

        .i_right_exp_wr_addr  (dc_tile_right_exp_wr_addr),
        .i_right_exp_wr_data  (dc_tile_right_exp_wr_data),
        .i_right_exp_wr_en    (dc_tile_right_exp_wr_en),

        // Read ports (to compute engine) - CE provides 11-bit, tile_bram uses [8:0]
        .i_left_man_rd_addr  (ce_dc_bram_rd_addr_left),
        .o_left_man_rd_data  (tile_ce_bram_rd_data_left),
        .i_left_man_rd_en    (ce_dc_bram_rd_en_left),

        .i_right_man_rd_addr (ce_dc_bram_rd_addr_right),
        .o_right_man_rd_data (tile_ce_bram_rd_data_right),
        .i_right_man_rd_en   (ce_dc_bram_rd_en_right),

        .i_left_exp_rd_addr  (ce_dc_left_exp_rd_addr),
        .o_left_exp_rd_data  (tile_ce_left_exp_rd_data),

        .i_right_exp_rd_addr (ce_dc_right_exp_rd_addr),
        .o_right_exp_rd_data (tile_ce_right_exp_rd_data)
    );

    // ------------------------------------------------------------------
    // Compute Engine - Modular GFP8 matrix multiplication with FP16 output
    // ------------------------------------------------------------------
    compute_engine_modular u_compute_engine (
        .i_clk              (i_clk),
        .i_reset_n          (i_reset_n),

        // Master Control Interface (spec-compliant)
        .i_tile_en               (mc_ce_tile_en),
        .i_left_addr             (mc_ce_left_addr),
        .i_right_addr            (mc_ce_right_addr),
        .i_left_ugd_len          (mc_ce_left_ugd_len),
        .i_right_ugd_len         (mc_ce_right_ugd_len),
        .i_vec_len               (mc_ce_vec_len),
        .i_left_man_4b           (mc_ce_left_man_4b),
        .i_right_man_4b          (mc_ce_right_man_4b),
        .i_main_loop_over_left   (mc_ce_main_loop_over_left),
        .o_tile_done             (ce_mc_tile_done),

        // Dual BRAM Mantissa Read Interface (from Tile BRAM - post-DISPATCH copy)
        .o_bram_left_rd_addr    (ce_dc_bram_rd_addr_left),
        .i_bram_left_rd_data    (tile_ce_bram_rd_data_left),    // NOW FROM TILE_BRAM!
        .o_bram_left_rd_en      (ce_dc_bram_rd_en_left),

        .o_bram_right_rd_addr   (ce_dc_bram_rd_addr_right),
        .i_bram_right_rd_data   (tile_ce_bram_rd_data_right),   // NOW FROM TILE_BRAM!
        .o_bram_right_rd_en     (ce_dc_bram_rd_en_right),

        // Exponent Read Interface (from Tile BRAM - post-DISPATCH copy)
        .o_left_exp_rd_addr     (ce_dc_left_exp_rd_addr),
        .i_left_exp_rd_data     (tile_ce_left_exp_rd_data),     // NOW FROM TILE_BRAM!

        .o_right_exp_rd_addr    (ce_dc_right_exp_rd_addr),
        .i_right_exp_rd_data    (tile_ce_right_exp_rd_data),    // NOW FROM TILE_BRAM!

        // Result FIFO Write Interface
        .o_result_data      (ce_result_data),
        .o_result_valid     (ce_result_valid),
        .i_result_full      (result_fifo_full),
        .i_result_afull     (result_fifo_afull),

        // Debug
        .o_ce_state         (ce_state),
        .o_result_count     (result_count)
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

