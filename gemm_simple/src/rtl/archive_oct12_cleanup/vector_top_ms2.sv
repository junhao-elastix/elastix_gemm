// ------------------------------------------------------------------
// Vector Top Level Module (MS2.0)
//
// This module instantiates and connects the MS2.0 architecture components:
// - Command FIFO: Buffers incoming microcode commands
// - Master Control (MC): Unified command processor and router
// - Dispatcher Control (DC): DDR fetch and BRAM buffering
// - Compute Engine (CE): Matrix computation with FP24 output
// - Result FIFO: Buffers FP24 computation results
//
// Datapath: Host → cmd_fifo → MC → {DC, CE} → result_fifo → Host
//           DDR ← DC(AXI) → BRAM → CE
//
// Author: MS2.0 Migration
// Date: Thu Oct 2 00:14:43 AM PDT 2025
// ------------------------------------------------------------------

`include "nap_interfaces.svh"

module vector_top_ms2
import gemm_pkg::*;
#(
    parameter TGT_DATA_WIDTH = 256,    // Target data width (256-bit AXI)
    parameter AXI_ADDR_WIDTH = 42      // AXI address width (42-bit for GDDR6 NoC: {Page[9], Line[26], Pad[2], Byte[5]})
)
(
    input  logic                        i_clk,
    input  logic                        i_reset_n,

    // ====================================================================
    // Host Command FIFO Interface
    // ====================================================================
    input  logic [cmd_buf_width_gp-1:0] i_cmd_fifo_wdata,
    input  logic                        i_cmd_fifo_wen,
    output logic                        o_cmd_fifo_full,
    output logic                        o_cmd_fifo_afull,
    output logic [12:0]                 o_cmd_fifo_count,

    // ====================================================================
    // Host Result FIFO Interface (FP16)
    // ====================================================================
    output logic [15:0]                 o_result_fifo_rdata,
    input  logic                        i_result_fifo_ren,
    output logic                        o_result_fifo_empty,
    output logic [14:0]                 o_result_fifo_count,  // 15-bit for 16,384 capacity

    // ====================================================================
    // DDR AXI Interface (for DC)
    // ====================================================================
    t_AXI4.initiator                    axi_ddr_if,

    // ====================================================================
    // Debug Interface
    // ====================================================================
    output logic [3:0]                  o_mc_state,
    output logic [3:0]                  o_dc_state,
    output logic [3:0]                  o_ce_state,
    output logic [cmd_op_width_gp-1:0]  o_last_opcode,
    output logic [9:0]                  o_bram_wr_count,
    output logic [15:0]                 o_result_count
);

    // ===================================================================
    // Internal Connection Signals
    // ===================================================================

    // Command FIFO → Master Control
    logic [cmd_buf_width_gp-1:0] cmd_fifo_rdata;
    logic                        cmd_fifo_empty;
    logic [12:0]                 cmd_fifo_count;
    logic                        cmd_fifo_ren;

    // Master Control → Dispatcher Control
    logic                         mc_dc_fetch_en;
    logic [link_addr_width_gp-1:0] mc_dc_fetch_addr;
    logic [link_len_width_gp-1:0]  mc_dc_fetch_len;
    logic                         dc_mc_fetch_done;

    logic                          mc_dc_disp_en;
    logic [tile_mem_addr_width_gp-1:0] mc_dc_disp_addr;
    logic [tile_mem_addr_width_gp-1:0] mc_dc_disp_len;
    logic                          mc_dc_man_4b_8b_n;
    logic                          dc_mc_disp_done;

    // Master Control → Compute Engine
    logic                          mc_ce_tile_en;
    logic [tile_mem_addr_width_gp-1:0] mc_ce_left_addr;
    logic [tile_mem_addr_width_gp-1:0] mc_ce_right_addr;
    logic [tile_mem_addr_width_gp-1:0] mc_ce_left_ugd_len;
    logic [tile_mem_addr_width_gp-1:0] mc_ce_right_ugd_len;
    logic [tile_mem_addr_width_gp-1:0] mc_ce_vec_len;
    logic [7:0]                    mc_ce_dim_b;
    logic [7:0]                    mc_ce_dim_c;
    logic [7:0]                    mc_ce_dim_v;
    logic                          mc_ce_left_man_4b;
    logic                          mc_ce_right_man_4b;
    logic                          mc_ce_main_loop_over_left;
    logic                          ce_mc_tile_done;

    // Dispatcher Control BRAM → Compute Engine (Dual Read Ports)
    // Left matrix port
    logic [10:0]   ce_dc_bram_rd_addr_left;
    logic [255:0]  dc_ce_bram_rd_data_left;
    logic          ce_dc_bram_rd_en_left;
    
    // Right matrix port
    logic [10:0]   ce_dc_bram_rd_addr_right;
    logic [255:0]  dc_ce_bram_rd_data_right;
    logic          ce_dc_bram_rd_en_right;

    // Compute Engine → Result FIFO
    logic [15:0]   ce_result_data;     // FP16 results
    logic          ce_result_valid;
    logic          result_fifo_full;
    logic          result_fifo_afull;

    // Debug signals
    logic [3:0]  mc_state;
    logic [3:0]  dc_state;
    logic [3:0]  ce_state;
    logic [cmd_op_width_gp-1:0] last_opcode;
    logic [9:0]  bram_wr_count;
    logic [15:0] result_count;

    // ===================================================================
    // Module Instantiations
    // ===================================================================

    // Command FIFO - Buffers incoming commands
    cmd_fifo u_cmd_fifo (
        .i_clk              (i_clk),
        .i_reset_n          (i_reset_n),

        // Write Interface (from Host)
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

    // Master Control - Unified command processor
    master_control u_master_control (
        .i_clk              (i_clk),
        .i_reset_n          (i_reset_n),

        // Command FIFO Interface
        .i_cmd_fifo_rdata   (cmd_fifo_rdata),
        .i_cmd_fifo_empty   (cmd_fifo_empty),
        .i_cmd_fifo_count   (cmd_fifo_count),
        .o_cmd_fifo_ren     (cmd_fifo_ren),

        // Dispatcher Control Interface
        .o_dc_fetch_en      (mc_dc_fetch_en),
        .o_dc_fetch_addr    (mc_dc_fetch_addr),
        .o_dc_fetch_len     (mc_dc_fetch_len),
        .i_dc_fetch_done    (dc_mc_fetch_done),

        .o_dc_disp_en       (mc_dc_disp_en),
        .o_dc_disp_addr     (mc_dc_disp_addr),
        .o_dc_disp_len      (mc_dc_disp_len),
        .o_dc_man_4b_8b_n   (mc_dc_man_4b_8b_n),
        .i_dc_disp_done     (dc_mc_disp_done),

        // Compute Engine Interface
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

        // Debug
        .o_mc_state         (mc_state),
        .o_last_opcode      (last_opcode)
    );

    // Dispatcher Control - DDR fetch and BRAM buffering
    dispatcher_control #(
        .TGT_DATA_WIDTH     (TGT_DATA_WIDTH),
        .AXI_ADDR_WIDTH     (AXI_ADDR_WIDTH),
        .BRAM_DEPTH         (2048)  // Increased from 528 to support dual 128×128 matrices (2×528=1056, rounded to 2048)
    ) u_dispatcher_control (
        .i_clk              (i_clk),
        .i_reset_n          (i_reset_n),

        // Master Control Interface
        .i_fetch_en         (mc_dc_fetch_en),
        .i_fetch_addr       (mc_dc_fetch_addr),
        .i_fetch_len        (mc_dc_fetch_len),
        .o_fetch_done       (dc_mc_fetch_done),

        .i_disp_en          (mc_dc_disp_en),
        .i_disp_addr        (mc_dc_disp_addr),
        .i_disp_len         (mc_dc_disp_len),
        .i_man_4b_8b_n      (mc_dc_man_4b_8b_n),
        .o_disp_done        (dc_mc_disp_done),

        // Dual BRAM Read Ports (for Compute Engine)
        .i_bram_rd_addr_left    (ce_dc_bram_rd_addr_left),
        .o_bram_rd_data_left    (dc_ce_bram_rd_data_left),
        .i_bram_rd_en_left      (ce_dc_bram_rd_en_left),
        
        .i_bram_rd_addr_right   (ce_dc_bram_rd_addr_right),
        .o_bram_rd_data_right   (dc_ce_bram_rd_data_right),
        .i_bram_rd_en_right     (ce_dc_bram_rd_en_right),

        // AXI DDR Interface
        .axi_ddr_if         (axi_ddr_if),

        // Debug
        .o_dc_state         (dc_state),
        .o_bram_wr_count    (bram_wr_count)
    );

    // Compute Engine - Matrix computation with FP24 output (modular version with dual BRAM)
    compute_engine_modular u_compute_engine (
        .i_clk              (i_clk),
        .i_reset_n          (i_reset_n),

        // Master Control Interface
        .i_tile_en          (mc_ce_tile_en),
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

        // Dual BRAM Read Interface (from Dispatcher Control)
        .o_bram_left_rd_addr    (ce_dc_bram_rd_addr_left),
        .i_bram_left_rd_data    (dc_ce_bram_rd_data_left),
        .o_bram_left_rd_en      (ce_dc_bram_rd_en_left),
        
        .o_bram_right_rd_addr   (ce_dc_bram_rd_addr_right),
        .i_bram_right_rd_data   (dc_ce_bram_rd_data_right),
        .o_bram_right_rd_en     (ce_dc_bram_rd_en_right),

        // Result FIFO Write Interface
        .o_result_data      (ce_result_data),
        .o_result_valid     (ce_result_valid),
        .i_result_full      (result_fifo_full),
        .i_result_afull     (result_fifo_afull),

        // Debug
        .o_ce_state         (ce_state),
        .o_result_count     (result_count)
    );

    // Result BRAM - Buffers FP16 computation results (16,384 entries for 128×128)
    result_bram u_result_bram (
        .i_clk              (i_clk),
        .i_reset_n          (i_reset_n),

        // Write Interface (from Compute Engine)
        .i_wr_data          (ce_result_data),
        .i_wr_en            (ce_result_valid),
        .o_full             (result_fifo_full),
        .o_afull            (result_fifo_afull),

        // Read Interface (to Host)
        .o_rd_data          (o_result_fifo_rdata),
        .i_rd_en            (i_result_fifo_ren),
        .o_empty            (o_result_fifo_empty),

        // Status
        .o_count            (o_result_fifo_count)
    );

    // ===================================================================
    // Debug Output Assignments
    // ===================================================================
    assign o_mc_state = mc_state;
    assign o_dc_state = dc_state;
    assign o_ce_state = ce_state;
    assign o_last_opcode = last_opcode;
    assign o_bram_wr_count = bram_wr_count;
    assign o_result_count = result_count;

endmodule : vector_top_ms2
