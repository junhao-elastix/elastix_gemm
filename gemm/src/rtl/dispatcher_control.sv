// ------------------------------------------------------------------
// Dispatcher Control Module (Wrapper) - Refactored Architecture
//
// Purpose: Wrapper module that instantiates fetcher, dispatcher, and dispatcher_bram
// Architecture:
//  - fetcher: Handles FETCH operations (GDDR6 → dispatcher_bram)
//  - dispatcher: Handles DISPATCH operations (dispatcher_bram → tile_bram)
//  - dispatcher_bram: Memory buffer between FETCH and DISPATCH stages
//
// Features:
//  - FETCH command: Read GFP8 block from DDR to dispatcher_bram
//  - DISPATCH command: Copy data from dispatcher_bram to tile_bram
//  - Independent state machines for FETCH and DISPATCH operations
//  - No compute engine read ports (removed per refactoring requirements)
//
// Author: Refactored from monolithic dispatcher_control.sv
// Date: $(date +"%Y-%m-%d")
// ------------------------------------------------------------------

`include "nap_interfaces.svh"

module dispatcher_control
import gemm_pkg::*;
#(
    parameter MAN_WIDTH = 256,         // Mantissa data width
    parameter EXP_WIDTH = 8,           // Exponent data width
    parameter BRAM_DEPTH = 512,        // Dispatcher BRAM depth
    parameter TILE_DEPTH = 512,        // Tile BRAM depth per side
    parameter AXI_ADDR_WIDTH = 42,     // AXI address width
    parameter BRAM_ADDR_WIDTH = $clog2(BRAM_DEPTH),  // 9-bit for 512 depth
    parameter TILE_ADDR_WIDTH = $clog2(TILE_DEPTH),  // 9-bit for 512 depth
    parameter [8:0] GDDR6_PAGE_ID = 9'd2  // GDDR6 Page ID for NoC routing
)
(
    // Clock and Reset
    input  logic                         i_clk,
    input  logic                         i_reset_n,

    // ====================================================================
    // Master Control Interface (FETCH/DISPATCH commands)
    // ====================================================================
    input  logic                         i_fetch_en,
    input  logic [link_addr_width_gp-1:0] i_fetch_addr,
    input  logic [link_len_width_gp-1:0]  i_fetch_len,
    input  logic                         i_fetch_target, // 0=left, 1=right
    output logic                         o_fetch_done,

    input  logic                         i_disp_en,
    input  logic [15:0]                  i_disp_tile_addr,    // Tile destination address
    input  logic [7:0]                   i_disp_man_nv_cnt,   // Total NVs to dispatch
    input  logic [7:0]                   i_disp_ugd_vec_size, // NVs per UGD vector
    input  logic                         i_disp_man_4b,       // Mantissa width (0=8-bit, 1=4-bit)
    input  logic [23:0]                  i_disp_col_en,       // Column enable mask (24 tiles max)
    input  logic [4:0]                   i_disp_col_start,    // Distribution start column
    input  logic                         i_disp_right,        // Dispatch side (0=left, 1=right)
    input  logic                         i_disp_broadcast,    // Distribution mode (0=distribute, 1=broadcast)
    output logic                         o_disp_done,

    // ====================================================================
    // Tile BRAM Write Ports (for DISPATCH copy operation)
    // FOUR PARALLEL OUTPUTS - All driven by same counter [0-511]
    // ====================================================================
    // Left mantissa write
    output logic [TILE_ADDR_WIDTH-1:0]   o_tile_man_left_wr_addr,
    output logic                         o_tile_man_left_wr_en,
    output logic [MAN_WIDTH-1:0]         o_tile_man_left_wr_data,

    // Right mantissa write
    output logic [TILE_ADDR_WIDTH-1:0]   o_tile_man_right_wr_addr,
    output logic                         o_tile_man_right_wr_en,
    output logic [MAN_WIDTH-1:0]         o_tile_man_right_wr_data,

    // Left exponent write
    output logic [TILE_ADDR_WIDTH-1:0]   o_tile_exp_left_wr_addr,
    output logic                         o_tile_exp_left_wr_en,
    output logic [EXP_WIDTH-1:0]         o_tile_exp_left_wr_data,

    // Right exponent write
    output logic [TILE_ADDR_WIDTH-1:0]   o_tile_exp_right_wr_addr,
    output logic                         o_tile_exp_right_wr_en,
    output logic [EXP_WIDTH-1:0]         o_tile_exp_right_wr_data,

    // Multi-tile write enable array (per-tile dispatch control)
    output logic [23:0]                  o_tile_wr_en,

    // ====================================================================
    // AXI-4 Initiator Interface for DDR access
    // ====================================================================
    t_AXI4.initiator                     axi_ddr_if,

    // ====================================================================
    // Debug Interface
    // ====================================================================
    output logic [3:0]                   o_dc_state,
    output logic [9:0]                   o_disp_wr_count,
    output logic [10:0]                  o_disp_wr_addr,    // Debug: BRAM write address
    output logic                         o_disp_wr_en,      // Debug: BRAM write enable
    output logic [8:0]                   o_disp_rd_addr,    // DISPATCH read address (debug)
    output logic                         o_disp_rd_en       // DISPATCH read enable (debug)
);

    // ====================================================================
    // Internal Signals for Inter-module Connections
    // ====================================================================
    
    // Fetcher → Dispatcher BRAM Write Interface
    logic [MAN_WIDTH-1:0]         fetcher_bram_wr_data;
    logic [BRAM_ADDR_WIDTH+2:0]   fetcher_bram_wr_addr;  // 11-bit for 0-527
    logic                         fetcher_bram_wr_en;
    logic                         fetcher_bram_wr_target;

    // Fetcher → Dispatcher BRAM Exponent Write Interface
    logic [TILE_ADDR_WIDTH-1:0]   fetcher_exp_left_wr_addr;
    logic                         fetcher_exp_left_wr_en;
    logic [EXP_WIDTH-1:0]         fetcher_exp_left_wr_data;
    logic [TILE_ADDR_WIDTH-1:0]   fetcher_exp_right_wr_addr;
    logic                         fetcher_exp_right_wr_en;
    logic [EXP_WIDTH-1:0]         fetcher_exp_right_wr_data;

    // Fetcher → Dispatcher BRAM Exp Packed Read Interface
    logic [3:0]                   fetcher_exp_packed_rd_addr;
    logic                         fetcher_exp_packed_rd_target;
    logic [MAN_WIDTH-1:0]         dispatcher_bram_exp_packed_rd_data;

    // Dispatcher → Dispatcher BRAM Read Interface
    logic [BRAM_ADDR_WIDTH-1:0]   dispatcher_man_left_rd_addr;
    logic                         dispatcher_man_left_rd_en;
    logic [MAN_WIDTH-1:0]         dispatcher_bram_man_left_rd_data;
    logic [BRAM_ADDR_WIDTH-1:0]   dispatcher_man_right_rd_addr;
    logic                         dispatcher_man_right_rd_en;
    logic [MAN_WIDTH-1:0]         dispatcher_bram_man_right_rd_data;
    logic [TILE_ADDR_WIDTH-1:0]   dispatcher_exp_left_rd_addr;
    logic                         dispatcher_exp_left_rd_en;
    logic [EXP_WIDTH-1:0]         dispatcher_bram_exp_left_rd_data;
    logic [TILE_ADDR_WIDTH-1:0]   dispatcher_exp_right_rd_addr;
    logic                         dispatcher_exp_right_rd_en;
    logic [EXP_WIDTH-1:0]         dispatcher_bram_exp_right_rd_data;

    // ====================================================================
    // Fetcher Module Instantiation
    // ====================================================================
    fetcher #(
        .MAN_WIDTH      (MAN_WIDTH),
        .EXP_WIDTH      (EXP_WIDTH),
        .BRAM_DEPTH     (BRAM_DEPTH),
        .AXI_ADDR_WIDTH (AXI_ADDR_WIDTH),
        .BRAM_ADDR_WIDTH(BRAM_ADDR_WIDTH),
        .TILE_ADDR_WIDTH(TILE_ADDR_WIDTH),
        .GDDR6_PAGE_ID  (GDDR6_PAGE_ID)
    ) u_fetcher (
        .i_clk                      (i_clk),
        .i_reset_n                  (i_reset_n),
        .i_fetch_en                 (i_fetch_en),
        .i_fetch_addr               (i_fetch_addr),
        .i_fetch_len                (i_fetch_len),
        .i_fetch_target             (i_fetch_target),
        .o_fetch_done               (o_fetch_done),
        .o_bram_wr_data             (fetcher_bram_wr_data),
        .o_bram_wr_addr             (fetcher_bram_wr_addr),
        .o_bram_wr_en               (fetcher_bram_wr_en),
        .o_bram_wr_target           (fetcher_bram_wr_target),
        .o_exp_left_wr_addr         (fetcher_exp_left_wr_addr),
        .o_exp_left_wr_en           (fetcher_exp_left_wr_en),
        .o_exp_left_wr_data         (fetcher_exp_left_wr_data),
        .o_exp_right_wr_addr        (fetcher_exp_right_wr_addr),
        .o_exp_right_wr_en          (fetcher_exp_right_wr_en),
        .o_exp_right_wr_data        (fetcher_exp_right_wr_data),
        .o_exp_packed_rd_addr       (fetcher_exp_packed_rd_addr),
        .o_exp_packed_rd_target     (fetcher_exp_packed_rd_target),
        .i_exp_packed_rd_data       (dispatcher_bram_exp_packed_rd_data),
        .axi_ddr_if                 (axi_ddr_if),
        .o_fetcher_state            (o_dc_state),  // Debug output
        .o_wr_addr                  (o_disp_wr_addr),  // Debug output
        .o_wr_en                    (o_disp_wr_en)  // Debug output
    );

    // ====================================================================
    // Dispatcher Module Instantiation
    // ====================================================================
    dispatcher #(
        .MAN_WIDTH       (MAN_WIDTH),
        .EXP_WIDTH       (EXP_WIDTH),
        .BRAM_DEPTH      (BRAM_DEPTH),
        .TILE_DEPTH      (TILE_DEPTH),
        .BRAM_ADDR_WIDTH (BRAM_ADDR_WIDTH),
        .TILE_ADDR_WIDTH (TILE_ADDR_WIDTH)
    ) u_dispatcher (
        .i_clk                      (i_clk),
        .i_reset_n                  (i_reset_n),
        .i_disp_en                  (i_disp_en),
        .i_disp_tile_addr           (i_disp_tile_addr),
        .i_disp_man_nv_cnt          (i_disp_man_nv_cnt),
        .i_disp_ugd_vec_size        (i_disp_ugd_vec_size),
        .i_disp_man_4b              (i_disp_man_4b),
        .i_disp_col_en              (i_disp_col_en),
        .i_disp_col_start           (i_disp_col_start),
        .i_disp_right               (i_disp_right),
        .i_disp_broadcast           (i_disp_broadcast),
        .o_disp_done                (o_disp_done),
        .o_disp_man_left_rd_addr    (dispatcher_man_left_rd_addr),
        .o_disp_man_left_rd_en      (dispatcher_man_left_rd_en),
        .i_disp_man_left_rd_data    (dispatcher_bram_man_left_rd_data),
        .o_disp_man_right_rd_addr   (dispatcher_man_right_rd_addr),
        .o_disp_man_right_rd_en     (dispatcher_man_right_rd_en),
        .i_disp_man_right_rd_data   (dispatcher_bram_man_right_rd_data),
        .o_disp_exp_left_rd_addr    (dispatcher_exp_left_rd_addr),
        .o_disp_exp_left_rd_en      (dispatcher_exp_left_rd_en),
        .i_disp_exp_left_rd_data    (dispatcher_bram_exp_left_rd_data),
        .o_disp_exp_right_rd_addr   (dispatcher_exp_right_rd_addr),
        .o_disp_exp_right_rd_en     (dispatcher_exp_right_rd_en),
        .i_disp_exp_right_rd_data   (dispatcher_bram_exp_right_rd_data),
        .o_tile_man_left_wr_addr    (o_tile_man_left_wr_addr),
        .o_tile_man_left_wr_en      (o_tile_man_left_wr_en),
        .o_tile_man_left_wr_data    (o_tile_man_left_wr_data),
        .o_tile_man_right_wr_addr   (o_tile_man_right_wr_addr),
        .o_tile_man_right_wr_en     (o_tile_man_right_wr_en),
        .o_tile_man_right_wr_data   (o_tile_man_right_wr_data),
        .o_tile_exp_left_wr_addr    (o_tile_exp_left_wr_addr),
        .o_tile_exp_left_wr_en      (o_tile_exp_left_wr_en),
        .o_tile_exp_left_wr_data    (o_tile_exp_left_wr_data),
        .o_tile_exp_right_wr_addr   (o_tile_exp_right_wr_addr),
        .o_tile_exp_right_wr_en     (o_tile_exp_right_wr_en),
        .o_tile_exp_right_wr_data    (o_tile_exp_right_wr_data),
        .o_tile_wr_en               (o_tile_wr_en),
        .o_dispatcher_state         ()  // Debug output (unused for now)
    );

    // ====================================================================
    // Dispatcher BRAM Module Instantiation
    // ====================================================================
    dispatcher_bram #(
        .MAN_WIDTH           (MAN_WIDTH),
        .EXP_WIDTH           (EXP_WIDTH),
        .EXP_PACKED_DEPTH    (16),
        .BRAM_DEPTH          (BRAM_DEPTH),
        .WR_ADDR_WIDTH       (BRAM_ADDR_WIDTH + 2),  // 11-bit for 0-527
        .RD_ADDR_WIDTH       (BRAM_ADDR_WIDTH)
    ) u_dispatcher_bram (
        .i_clk                  (i_clk),
        .i_reset_n              (i_reset_n),
        .i_wr_data              (fetcher_bram_wr_data),
        .i_wr_addr              (fetcher_bram_wr_addr),
        .i_wr_en                (fetcher_bram_wr_en),
        .i_wr_target            (fetcher_bram_wr_target),
        .i_exp_left_wr_addr     (fetcher_exp_left_wr_addr),
        .i_exp_left_wr_en       (fetcher_exp_left_wr_en),
        .i_exp_left_wr_data     (fetcher_exp_left_wr_data),
        .i_exp_right_wr_addr    (fetcher_exp_right_wr_addr),
        .i_exp_right_wr_en      (fetcher_exp_right_wr_en),
        .i_exp_right_wr_data    (fetcher_exp_right_wr_data),
        .i_man_left_rd_addr     (dispatcher_man_left_rd_addr),
        .i_man_left_rd_en       (dispatcher_man_left_rd_en),
        .o_man_left_rd_data     (dispatcher_bram_man_left_rd_data),
        .i_man_right_rd_addr    (dispatcher_man_right_rd_addr),
        .i_man_right_rd_en      (dispatcher_man_right_rd_en),
        .o_man_right_rd_data    (dispatcher_bram_man_right_rd_data),
        .i_exp_left_rd_addr     (dispatcher_exp_left_rd_addr),
        .i_exp_left_rd_en       (dispatcher_exp_left_rd_en),
        .o_exp_left_rd_data     (dispatcher_bram_exp_left_rd_data),
        .i_exp_right_rd_addr    (dispatcher_exp_right_rd_addr),
        .i_exp_right_rd_en      (dispatcher_exp_right_rd_en),
        .o_exp_right_rd_data    (dispatcher_bram_exp_right_rd_data),
        .i_exp_packed_rd_addr   (fetcher_exp_packed_rd_addr),
        .i_exp_packed_rd_target (fetcher_exp_packed_rd_target),
        .o_exp_packed_rd_data   (dispatcher_bram_exp_packed_rd_data)
    );

    // ====================================================================
    // Debug Outputs (pass through from dispatcher)
    // ====================================================================
    // For backward compatibility, wire dispatcher read address to debug outputs
    assign o_disp_rd_addr = dispatcher_man_left_rd_addr[8:0];  // Use left (or right, doesn't matter)
    assign o_disp_rd_en = dispatcher_man_left_rd_en | dispatcher_man_right_rd_en;
    assign o_disp_wr_count = 10'd0;  // Not used in refactored architecture

endmodule : dispatcher_control

