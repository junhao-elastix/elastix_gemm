// ------------------------------------------------------------------
// MS2.0 GEMM Engine Top Module (MLP-Based)
//
// Purpose: Complete GEMM engine with MLP-based compute engine
// Contains:
//  - Command FIFO (4096x32-bit): Buffers incoming microcode commands
//  - Master Control (MC): Unified command processor and router
//  - Dispatcher Control (DC): GDDR6 fetch and L2 BRAM buffering
//  - Compute Engine MLP (CE): MLP-based matrix multiplication
//
// Data Flow:
//  GDDR6 (L3) -> [FETCH] -> dispatcher_bram (L2) -> [DISPATCH] ->
//    -> tile_bram (L1, inside CE) -> [MATMUL] -> 256-bit direct output
//
// Key Features:
//  - MLP-based compute engine with native FP24 computation
//  - Direct 256-bit (16 × FP16) result output path
//  - Configurable GDDR6 page ID
//  - C > 16 support via column group iteration
//
// Author: Junhao Pan
// Date: 10/27/2025 (MLP refactor: 12/10/2025)
// ------------------------------------------------------------------

`include "nap_interfaces.svh"

module engine_top
import gemm_pkg::*;
#(
    parameter [8:0] GDDR6_PAGE_ID = 9'd0,   // GDDR6 Channel page ID
    parameter TGT_DATA_WIDTH = 256,         // Target data width (256-bit AXI)
    parameter AXI_ADDR_WIDTH = 42,          // AXI address width (42-bit for GDDR6)
    parameter int NUM_TILES = 8             // Number of parallel compute tiles (2-24)
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
    // 256-bit Result Output (16 × FP16 per cycle)
    // ====================================================================
    output logic [255:0]                 o_result_256_data,       // 16 × FP16 results
    output logic                         o_result_256_valid,      // Result valid pulse
    output logic [8:0]                   o_result_256_wr_addr,    // Auto-incrementing write address

    // ====================================================================
    // NAP AXI Interface (to GDDR6)
    // ====================================================================
    t_AXI4.initiator                     nap_axi,

    // ====================================================================
    // Flow Control
    // ====================================================================
    input  logic                         i_result_almost_full,   // Backpressure from result BRAM

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
    output logic [31:0]                  o_bcv_debug_dimensions,  // BCV captured dimensions
    
    // ====================================================================
    // Probe Outputs (pipeline stage debugging)
    // ====================================================================
    output logic [15:0]                  o_probe_disp_data,       // dispatcher_bram write data
    output logic                         o_probe_disp_valid,      // dispatcher_bram write valid
    output logic [15:0]                  o_probe_rowbram_data,    // row_bram write data
    output logic                         o_probe_rowbram_valid,   // row_bram write valid
    output logic [23:0]                  o_probe_fp24_data,       // FP24 compute result
    output logic                         o_probe_fp24_valid,      // FP24 result valid
    output logic [15:0]                  o_probe_fp16_data,       // FP16 converted result
    output logic                         o_probe_fp16_valid       // FP16 result valid
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
    logic [23:0] mc_ce_tile_en;          // Per-tile enable (24 tiles max) - STATIC configuration
    logic [23:0] mc_ce_tile_start;       // Per-tile start pulse - DYNAMIC control
    logic [15:0] mc_ce_tile_left_addr;       // 16 bits: Left matrix start address
    logic [15:0] mc_ce_tile_right_addr;      // 16 bits: Right matrix start address
    logic [7:0]  mc_ce_tile_left_ugd_len;    // 8 bits: Left UGD vectors (Batch dimension)
    logic [7:0]  mc_ce_tile_right_ugd_len;   // 8 bits: Right UGD vectors (Column dimension)
    logic [7:0]  mc_ce_tile_vec_len;         // 8 bits: UGD vector size (Vector count)
    logic        mc_ce_tile_left_man_4b;
    logic        mc_ce_tile_right_man_4b;
    logic        mc_ce_tile_main_loop_over_left;
    logic        ce_mc_tile_done;

    // Master Control -> Result Arbiter (READOUT command - currently stubbed)
    logic        mc_arb_readout_en;
    logic [7:0]  mc_arb_readout_start_col;
    logic [31:0] mc_arb_readout_rd_len;
    logic        arb_mc_readout_done;

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

    // DISPATCH control signals (declared early for use in port connections)
    logic          dc_disp_start;       // From dispatcher_control to compute_engine

    // Multi-tile DISPATCH control (per-tile write enables)
    // dc_tile_wr_en removed (no longer needed with direct FETCH to row_bram)

    // MLP internal signals (declared early for use in always_ff blocks)
    logic [255:0] mlp_result_data;     // 16 × FP16 results
    logic         mlp_result_valid;    // Result valid pulse
    logic         mlp_tile_done;       // Tile done signal
    logic         mlp_disp_done;       // DISPATCH done signal
    logic [3:0]   mlp_ce_state;        // CE state for debug
    logic [15:0]  mlp_result_count;    // Result count for debug
    logic [8:0]   mlp_wr_addr_cnt;     // 256-bit result write address counter
    logic [7:0]   debug_cycle_cnt;     // Debug cycle counter

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
        .i_result_fifo_afull(i_result_almost_full),  // Use external backpressure signal

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
        .o_ce_tile_en                 (mc_ce_tile_en),          // Static enable mask
        .o_ce_tile_start              (mc_ce_tile_start),       // Dynamic start pulse
        .o_ce_tile_left_addr          (mc_ce_tile_left_addr),
        .o_ce_tile_right_addr         (mc_ce_tile_right_addr),
        .o_ce_tile_left_ugd_len       (mc_ce_tile_left_ugd_len),
        .o_ce_tile_right_ugd_len      (mc_ce_tile_right_ugd_len),
        .o_ce_tile_vec_len            (mc_ce_tile_vec_len),
        .o_ce_tile_left_man_4b        (mc_ce_tile_left_man_4b),
        .o_ce_tile_right_man_4b       (mc_ce_tile_right_man_4b),
        .o_ce_tile_main_loop_over_left (mc_ce_tile_main_loop_over_left),
        .i_ce_tile_done          (ce_mc_tile_done),

        // Result Arbiter Interface (READOUT command)
        .o_readout_en            (mc_arb_readout_en),
        .o_readout_start_col     (mc_arb_readout_start_col),
        .o_readout_rd_len        (mc_arb_readout_rd_len),
        .i_readout_done          (arb_mc_readout_done),

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
        .MAN_WIDTH          (TGT_DATA_WIDTH),
        .EXP_WIDTH          (8),
        .BRAM_DEPTH         (512),
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
        .i_disp_right       (mc_dc_disp_right),
        .i_disp_broadcast   (mc_dc_disp_broadcast),
        .o_disp_done        (dc_mc_disp_done),

        // row_bram Write Ports (renamed from tile_*)
        .o_man_left_wr_addr   (dc_tile_man_left_wr_addr),
        .o_man_left_wr_en     (dc_tile_man_left_wr_en),
        .o_man_left_wr_data   (dc_tile_man_left_wr_data),

        .o_man_right_wr_addr  (dc_tile_man_right_wr_addr),
        .o_man_right_wr_en    (dc_tile_man_right_wr_en),
        .o_man_right_wr_data  (dc_tile_man_right_wr_data),

        .o_exp_left_wr_addr   (dc_tile_left_exp_wr_addr),
        .o_exp_left_wr_en     (dc_tile_left_exp_wr_en),
        .o_exp_left_wr_data   (dc_tile_left_exp_wr_data),

        .o_exp_right_wr_addr  (dc_tile_right_exp_wr_addr),
        .o_exp_right_wr_en    (dc_tile_right_exp_wr_en),
        .o_exp_right_wr_data  (dc_tile_right_exp_wr_data),
        
        // DISPATCH start signal (to compute_engine)
        .o_disp_start         (dc_disp_start),
        .i_disp_done_ce       (mlp_disp_done),

        // AXI GDDR6 Interface
        .axi_ddr_if         (nap_axi),

        // Debug
        .o_dc_state         (dc_state),
        .o_disp_wr_count    (bram_wr_count),
        .o_disp_wr_addr     (),  // Unused
        .o_disp_wr_en       (),  // Unused

        // DISPATCH copy read control (debug only)
        .o_disp_rd_addr     (dc_disp_rd_addr),
        .o_disp_rd_en       (dc_disp_rd_en),
        
        // Probe outputs
        .o_probe_disp_data  (o_probe_disp_data),
        .o_probe_disp_valid (o_probe_disp_valid)
    );

    // ------------------------------------------------------------------
    // Tile BRAM - Integrated inside compute_engine_mlp as row_bram
    // ------------------------------------------------------------------

    // ------------------------------------------------------------------
    // MLP Compute Engine - Single tile with direct 256-bit output
    // ------------------------------------------------------------------
    `ifdef SIMULATION
    initial begin
        $display("[ENGINE_TOP] @%0t MLP MODE: Instantiating compute_engine_mlp", $time);
    end
    `endif

    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            mlp_wr_addr_cnt <= 9'd0;
        end else if (mlp_result_valid) begin
            mlp_wr_addr_cnt <= mlp_wr_addr_cnt + 9'd1;
        end
    end

    // Connect to output ports
    assign o_result_256_data = mlp_result_data;
    assign o_result_256_valid = mlp_result_valid;
    assign o_result_256_wr_addr = mlp_wr_addr_cnt;

    // MLP Compute Engine Instance (single tile at id=0)
    compute_engine_mlp #(
        .TILE_ID            (0), 
        .NUM_MLPS           (NUM_TILES)
    ) u_compute_engine_mlp (
        .i_clk              (i_clk),
        .i_reset_n          (i_reset_n),

        // Master Control Interface (TILE command)
        .i_tile_en                    (mc_ce_tile_en[0]),
        .i_tile_start                 (mc_ce_tile_start[0]),
        .i_disp_start                 (dc_disp_start),       // NEW: DISPATCH triggers ST_FILL
        .i_disp_ugd_vec_size          (mc_dc_disp_ugd_vec_size),  // V for DISPATCH
        .i_disp_right_ugd_len         (mc_dc_disp_man_nv_cnt / mc_dc_disp_ugd_vec_size),  // C for DISPATCH
        .i_tile_left_addr             (mc_ce_tile_left_addr),
        .i_tile_right_addr            (mc_ce_tile_right_addr),
        .i_tile_left_ugd_len          (mc_ce_tile_left_ugd_len),
        .i_tile_right_ugd_len         (mc_ce_tile_right_ugd_len),
        .i_tile_vec_len               (mc_ce_tile_vec_len),
        .i_tile_left_man_4b           (mc_ce_tile_left_man_4b),
        .i_tile_right_man_4b          (mc_ce_tile_right_man_4b),
        .i_tile_main_loop_over_left   (mc_ce_tile_main_loop_over_left),
        .i_mc_tile_en                 (mc_ce_tile_en),
        .o_tile_done                  (mlp_tile_done),
        .o_disp_done                  (mlp_disp_done),       // NEW: DISPATCH done signal

        // row_bram Write Interface (4 parallel ports)
        // Direct from fetcher (no tile_wr_en gating needed)
        // Left mantissa (activations)
        .i_man_left_wr_addr      (dc_tile_man_left_wr_addr),
        .i_man_left_wr_en        (dc_tile_man_left_wr_en),
        .i_man_left_wr_data      (dc_tile_man_left_wr_data),

        // Right mantissa (weights)
        .i_man_right_wr_addr     (dc_tile_man_right_wr_addr),
        .i_man_right_wr_en       (dc_tile_man_right_wr_en),
        .i_man_right_wr_data     (dc_tile_man_right_wr_data),

        // Left exponent (activations)
        .i_exp_left_wr_addr      (dc_tile_left_exp_wr_addr),
        .i_exp_left_wr_en        (dc_tile_left_exp_wr_en),
        .i_exp_left_wr_data      (dc_tile_left_exp_wr_data),

        // Right exponent (weights)
        .i_exp_right_wr_addr     (dc_tile_right_exp_wr_addr),
        .i_exp_right_wr_en       (dc_tile_right_exp_wr_en),
        .i_exp_right_wr_data     (dc_tile_right_exp_wr_data),

        // Result → Direct 256-bit output (bypasses FIFO)
        .o_result_data      (mlp_result_data),
        .o_result_valid     (mlp_result_valid),
        .i_result_full      (1'b0),      // No backpressure for now
        .i_result_afull     (1'b0),

        // Debug
        .o_ce_state         (mlp_ce_state),
        .o_result_count     (mlp_result_count),
        
        // Probe outputs
        .o_probe_rowbram_data  (o_probe_rowbram_data),
        .o_probe_rowbram_valid (o_probe_rowbram_valid),
        .o_probe_fp24_data     (o_probe_fp24_data),
        .o_probe_fp24_valid    (o_probe_fp24_valid),
        .o_probe_fp16_data     (o_probe_fp16_data),
        .o_probe_fp16_valid    (o_probe_fp16_valid)
    );

    // MLP mode: ce_mc_tile_done is directly from MLP compute engine
    // (Simplified from multi-tile array to single signal)

    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            debug_cycle_cnt <= 8'd0;
        end else begin
            `ifdef SIMULATION
            if ((dc_tile_man_left_wr_en || dc_tile_man_right_wr_en ||
                 dc_tile_left_exp_wr_en || dc_tile_right_exp_wr_en) && debug_cycle_cnt < 10) begin
                debug_cycle_cnt <= debug_cycle_cnt + 1;

                $display("[ENG_WR_EN] @%0t cycle=%0d, man_left=%0b, man_right=%0b, exp_left=%0b, exp_right=%0b",
                         $time, debug_cycle_cnt,
                         dc_tile_man_left_wr_en, dc_tile_man_right_wr_en,
                         dc_tile_left_exp_wr_en, dc_tile_right_exp_wr_en);
            end
            `endif

            // Reset counter if no activity for a while
            if (!dc_tile_man_left_wr_en && !dc_tile_man_right_wr_en &&
                !dc_tile_left_exp_wr_en && !dc_tile_right_exp_wr_en) begin
                if (debug_cycle_cnt >= 10) begin
                    debug_cycle_cnt <= 0;  // Reset for next DISPATCH
                end
            end
        end
    end

    // MLP mode: tile_done directly from MLP compute engine
    assign ce_mc_tile_done = mlp_tile_done;

    // Stub readout done (READOUT command not used in MLP mode)
    assign arb_mc_readout_done = 1'b1;

    // Debug outputs: Use MLP signals for state monitoring
    assign ce_state = mlp_ce_state;
    assign result_count = mlp_result_count;

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
    assign o_bcv_debug_state = 32'd0;       // BCV debug not exposed at top level
    assign o_bcv_debug_dimensions = 32'd0;  // BCV debug not exposed at top level

endmodule : engine_top

