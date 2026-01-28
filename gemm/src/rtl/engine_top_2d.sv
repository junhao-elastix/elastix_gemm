// ------------------------------------------------------------------
// 2-D Multi-Row GEMM Engine Top Module
//
// Purpose: Top-level wrapper for 2-D GEMM architecture with NUM_ROWS rows
// Contains:
//  - Command FIFO (512x128-bit): Buffers incoming microcode commands
//  - Master Control (MC): Unified command processor with per-row V partitioning
//  - Dispatcher Control (DC) x16: Per-row GDDR6 fetch and dispatch
//  - Compute Engine (CE) x16: Per-row MLP compute array
//  - Result Collector (RC): Global reduction across rows using FP16 FIFO interface
//
// GDDR6 Channel Mapping (from GDDR6_ADDR_MAPPING.md):
//   Row 0-1:   Controller 0 Ch0/Ch1 (PAGE_ID 0xC, 0xD)
//   Row 2-3:   Controller 1 Ch0/Ch1 (PAGE_ID 0x4, 0x5)
//   Row 4-5:   Controller 2 Ch0/Ch1 (PAGE_ID 0x0, 0x1)
//   Row 6-7:   Controller 3 Ch0/Ch1 (PAGE_ID 0x8, 0x9)
//   Row 8-9:   Controller 4 Ch0/Ch1 (PAGE_ID 0xF, 0xE) - East side reversed
//   Row 10-11: Controller 5 Ch0/Ch1 (PAGE_ID 0x7, 0x6)
//   Row 12-13: Controller 6 Ch0/Ch1 (PAGE_ID 0x3, 0x2)
//   Row 14-15: Controller 7 Ch0/Ch1 (PAGE_ID 0xB, 0xA)
//
// Author: Junhao Pan
// Date: 01/22/2026
// ------------------------------------------------------------------

`include "nap_interfaces.svh"

module engine_top_2d
import gemm_pkg::*;
#(
    parameter int NUM_MLPS = 8,             // Number of MLPs in a MLPRow
    parameter int STACK_DEPTH = 4,          // Number of MLPRows in a MLPStack
    parameter int NUM_ROWS = 16,            // Number of rows (fixed to 16 GDDR6 channels)
    parameter int NUM_COLS = NUM_MLPS * 2,  // Number of logical columns (MLPs * 2 banks)
    parameter int MAN_WIDTH = 256,          // Mantissa line width
    parameter int EXP_WIDTH = 8,            // Exponent width
    parameter int BRAM_DEPTH = 512,         // BRAM depth
    parameter int ADDR_WIDTH = $clog2(BRAM_DEPTH)
)
(
    // Clock and Reset
    input  logic                         i_clk,
    input  logic                         i_reset_n,

    // ====================================================================
    // Command BRAM Read Interface (from external cmd BRAM)
    // ====================================================================
    input  logic [255:0]                 i_cmd_bram_rd_data,
    output logic                         o_cmd_bram_rd_en,
    output logic [8:0]                   o_cmd_bram_rd_addr,

    // ====================================================================
    // Command Control Interface (from host registers)
    // ====================================================================
    input  logic [31:0]                  i_cmd_cnt,        // Number of commands in BRAM
    input  logic                         i_cmd_valid,      // Host writes 1 to start transfer
    output logic                         o_cmd_valid_clr,  // Pulse when transfer complete
    output logic                         o_cmd_bridge_busy,// Bridge is actively transferring
    output logic [12:0]                  o_cmd_fifo_count, // Internal FIFO count (debug)

    // ====================================================================
    // 16 AXI Interfaces for GDDR6 Access (one per row)
    // ====================================================================
    t_AXI4.initiator                     axi_ddr_if [NUM_ROWS-1:0],

    // ====================================================================
    // Result Output Interface (BRAM Write to DMA Bridge)
    // Output is packed 256-bit lines (16 x FP16)
    // ====================================================================
    output logic                         o_bram_wr_en,
    output logic [8:0]                   o_bram_wr_addr,
    output logic [255:0]                 o_bram_wr_data,
    output logic [31:0]                  o_bram_wr_strobe,

    // ====================================================================
    // Status Outputs
    // ====================================================================
    output logic                         o_engine_busy,
    output logic [3:0]                   o_mc_state,      // Master control state
    output logic [3:0]                   o_rc_state,      // Result collector state

    // ====================================================================
    // Debug Outputs (for hardware debugging)
    // ====================================================================
    output logic [NUM_ROWS-1:0]          o_dbg_ce_ack_matmul,     // Per-row CE ACK (captured in MC)
    output logic [NUM_ROWS-1:0]          o_dbg_dc_ack_fetch,      // Per-row DC ACK (captured in MC)
    output logic                         o_dbg_cmd_valid,         // MC has valid command
    output logic                         o_dbg_matmul_en_pulse,   // MATMUL enable pulse
    output logic [3:0]                   o_dbg_ce_state_row0,     // CE state for row 0
    output logic [3:0]                   o_dbg_dc_state_row0      // DC state for row 0
);

    // ===================================================================
    // GDDR6 Page ID Mapping (16 channels)
    // ===================================================================
    // From GDDR6_ADDR_MAPPING.md and gddr_ref_design
    // West controllers (0-3): Ch0=lower Ctrl ID, Ch1=higher Ctrl ID
    // East controllers (4-7): Ch0=higher Ctrl ID, Ch1=lower Ctrl ID (reversed)
    localparam [8:0] GDDR6_CTRL_ID [0:NUM_ROWS-1] = '{
        9'hC, 9'hD,   // Controller 0: Ch0=0xC, Ch1=0xD (West)
        9'h4, 9'h5,   // Controller 1: Ch0=0x4, Ch1=0x5 (West)
        9'h0, 9'h1,   // Controller 2: Ch0=0x0, Ch1=0x1 (West)
        9'h8, 9'h9,   // Controller 3: Ch0=0x8, Ch1=0x9 (West)
        9'hF, 9'hE,   // Controller 4: Ch0=0xF, Ch1=0xE (East, reversed)
        9'h7, 9'h6,   // Controller 5: Ch0=0x7, Ch1=0x6 (East, reversed)
        9'h3, 9'h2,   // Controller 6: Ch0=0x3, Ch1=0x2 (East, reversed)
        9'hB, 9'hA    // Controller 7: Ch0=0xB, Ch1=0xA (East, reversed)
    };

    // ===================================================================
    // Opcode Constants (from gemm_pkg)
    // ===================================================================
    localparam logic [7:0] OPC_FETCH     = 8'hF0;
    localparam logic [7:0] OPC_DISP      = 8'hF1;
    localparam logic [7:0] OPC_MATMUL    = 8'hF2;
    localparam logic [7:0] OPC_WAIT_DISP = 8'hF3;
    localparam logic [7:0] OPC_WAIT_TILE = 8'hF4;
    localparam logic [7:0] OPC_READOUT   = 8'hF5;

    // ===================================================================
    // Internal Connection Signals
    // ===================================================================

    // Command BRAM Bridge -> Command FIFO (128-bit wide)
    logic [127:0] cmd_fifo_wdata_int;
    logic         cmd_fifo_wen_int;
    logic         cmd_fifo_full;
    logic         cmd_fifo_afull;

    // Command FIFO -> Master Control (128-bit wide)
    logic [127:0] cmd_fifo_rdata;
    logic         cmd_fifo_empty;
    logic [12:0]  cmd_fifo_count;
    logic         cmd_fifo_ren;

    // Master Control -> Per-Row Command Outputs
    logic [7:0]   mc_cmd_op;
    logic [7:0]   mc_cmd_id;
    logic [31:0]  mc_cmd_payload_word1 [NUM_ROWS-1:0];
    logic [31:0]  mc_cmd_payload_word2 [NUM_ROWS-1:0];
    logic [31:0]  mc_cmd_payload_word3 [NUM_ROWS-1:0];

    // Per-Row Dispatcher Control Interface
    logic [3:0]   dc_state       [NUM_ROWS-1:0];
    logic         dc_ack_fetch   [NUM_ROWS-1:0];
    logic         dc_ack_disp    [NUM_ROWS-1:0];
    logic [7:0]   dc_id          [NUM_ROWS-1:0];

    // Per-Row Compute Engine Interface
    logic [3:0]   ce_state       [NUM_ROWS-1:0];
    logic         ce_ack_matmul  [NUM_ROWS-1:0];
    logic [7:0]   ce_id          [NUM_ROWS-1:0];
    logic         ce_result_fifo_afull [NUM_ROWS-1:0];
    logic         ce_matmul_done [NUM_ROWS-1:0];

    // Result Collector Interface
    logic [3:0]   rc_state;
    logic         rc_busy;
    logic [7:0]   rc_id;
    logic         rc_ack_readout;

    // Result Collector -> result_to_dma (internal ready-valid)
    logic         rc_output_valid;
    logic         rc_output_last;
    logic [15:0]  rc_output_keep;
    logic [255:0] rc_output_data;
    logic         rc_output_ready;

    // ===================================================================
    // DC -> CE Data Paths (per row)
    // ===================================================================
    // Left path (activations)
    logic [ADDR_WIDTH-1:0] dc_left_man_wr_addr  [NUM_ROWS-1:0];
    logic                  dc_left_man_wr_en    [NUM_ROWS-1:0];
    logic [MAN_WIDTH-1:0]  dc_left_man_wr_data  [NUM_ROWS-1:0];
    logic [ADDR_WIDTH-1:0] dc_left_exp_wr_addr  [NUM_ROWS-1:0];
    logic                  dc_left_exp_wr_en    [NUM_ROWS-1:0];
    logic [EXP_WIDTH-1:0]  dc_left_exp_wr_data  [NUM_ROWS-1:0];

    // Right path (weights) - raw dispatcher output
    logic [ADDR_WIDTH-1:0] dc_right_wr_addr     [NUM_ROWS-1:0];
    logic [NUM_COLS-1:0]   dc_right_wr_en       [NUM_ROWS-1:0];
    logic [MAN_WIDTH-1:0]  dc_right_man_wr_data [NUM_ROWS-1:0];
    logic [EXP_WIDTH-1:0]  dc_right_exp_wr_data [NUM_ROWS-1:0];

    // ===================================================================
    // CE -> RC FIFO Interface (FP16-based)
    // Unpacked arrays to match compute_engine_2d ports
    // ===================================================================
    logic [15:0] ce_to_rc_result_data [NUM_ROWS-1:0][NUM_COLS-1:0];
    logic        ce_to_rc_result_empty [NUM_ROWS-1:0][NUM_COLS-1:0];
    logic        rc_to_ce_result_rd_en [NUM_ROWS-1:0][NUM_COLS-1:0];

    // MC state
    logic [3:0]   mc_state;

    // Debug signals from MC
    logic [NUM_ROWS-1:0] dbg_ce_ack_matmul_reg;
    logic [NUM_ROWS-1:0] dbg_dc_ack_fetch_reg;
    logic                dbg_cmd_valid;

    // ===================================================================
    // MATMUL Enable Generation
    // ===================================================================
    // Generate matmul_en pulse when MC issues MATMUL opcode
    logic [7:0] mc_cmd_op_prev;
    logic       matmul_en_pulse;

    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            mc_cmd_op_prev <= 8'h00;
        end else begin
            mc_cmd_op_prev <= mc_cmd_op;
        end
    end

    // Detect rising edge of MATMUL opcode
    assign matmul_en_pulse = (mc_cmd_op == OPC_MATMUL) && (mc_cmd_op_prev != OPC_MATMUL);

    // ===================================================================
    // Module Instantiations
    // ===================================================================

    // ------------------------------------------------------------------
    // Command BRAM-to-FIFO Bridge
    // Reads batched commands from external BRAM and pushes to internal FIFO
    // ------------------------------------------------------------------
    cmd_bram_fifo_bridge u_cmd_bridge (
        .i_clk              (i_clk),
        .i_reset_n          (i_reset_n),
        // Register interface (from external control)
        .i_cmd_cnt          (i_cmd_cnt),
        .i_cmd_valid        (i_cmd_valid),
        .o_cmd_valid_clr    (o_cmd_valid_clr),
        .o_rd_addr          (),  // Debug only, not connected
        .o_bridge_busy      (o_cmd_bridge_busy),
        // BRAM read interface (to external BRAM)
        .o_bram_rd_en       (o_cmd_bram_rd_en),
        .o_bram_rd_addr     (o_cmd_bram_rd_addr),
        .i_bram_rd_data     (i_cmd_bram_rd_data),
        // FIFO write interface (to internal cmd_fifo)
        .o_fifo_wdata       (cmd_fifo_wdata_int),
        .o_fifo_wen         (cmd_fifo_wen_int),
        .i_fifo_full        (cmd_fifo_full),
        .i_fifo_afull       (cmd_fifo_afull)
    );

    // ------------------------------------------------------------------
    // Command FIFO - Buffers incoming microcode commands
    // ------------------------------------------------------------------
    cmd_fifo u_cmd_fifo (
        .i_clk              (i_clk),
        .i_reset_n          (i_reset_n),

        // Write Interface (from BRAM bridge)
        .i_wr_data          (cmd_fifo_wdata_int),
        .i_wr_en            (cmd_fifo_wen_int),
        .o_full             (cmd_fifo_full),
        .o_afull            (cmd_fifo_afull),

        // Read Interface (to Master Control)
        .o_rd_data          (cmd_fifo_rdata),
        .i_rd_en            (cmd_fifo_ren),
        .o_empty            (cmd_fifo_empty),

        // Status
        .o_count            (cmd_fifo_count)
    );

    assign o_cmd_fifo_count = cmd_fifo_count;

    // ------------------------------------------------------------------
    // Master Control - 2-D Command Processor with Per-Row V Partitioning
    // ------------------------------------------------------------------
    master_control_2d #(
        .NUM_MLPS           (NUM_MLPS),
        .STACK_DEPTH        (STACK_DEPTH),
        .NUM_ROWS           (NUM_ROWS)
    ) u_master_control (
        .i_clk              (i_clk),
        .i_reset_n          (i_reset_n),

        // Command FIFO Interface
        .i_cmd_fifo_rdata   (cmd_fifo_rdata),
        .i_cmd_fifo_empty   (cmd_fifo_empty),
        .i_cmd_fifo_count   (cmd_fifo_count),
        .o_cmd_fifo_ren     (cmd_fifo_ren),

        // CMD out to Exec Units (per-row)
        .o_mc_cmd_op        (mc_cmd_op),
        .o_mc_cmd_id        (mc_cmd_id),
        .o_mc_cmd_payload_word1 (mc_cmd_payload_word1),
        .o_mc_cmd_payload_word2 (mc_cmd_payload_word2),
        .o_mc_cmd_payload_word3 (mc_cmd_payload_word3),

        // Dispatcher Control Interface - PER ROW
        .i_dc_state         (dc_state),
        .i_dc_ack_fetch     (dc_ack_fetch),
        .i_dc_ack_disp      (dc_ack_disp),
        .i_dc_id            (dc_id),

        // Compute Engine Interface - PER ROW
        .i_ce_state         (ce_state),
        .i_ce_ack_matmul    (ce_ack_matmul),
        .i_ce_id            (ce_id),
        .i_ce_result_fifo_afull (ce_result_fifo_afull),

        // Result Collector Interface - GLOBAL
        .i_rc_state         (rc_state),
        .i_rc_ack_readout   (rc_ack_readout),
        .i_rc_id            (rc_id),

        // Debug
        .o_mc_state         (mc_state),

        // Extended Debug
        .o_dbg_ce_ack_matmul_reg (dbg_ce_ack_matmul_reg),
        .o_dbg_dc_ack_fetch_reg  (dbg_dc_ack_fetch_reg),
        .o_dbg_cmd_valid         (dbg_cmd_valid)
    );

    // ------------------------------------------------------------------
    // Generate 16 Dispatcher Controls and 16 Compute Engines
    // ------------------------------------------------------------------
    generate
        for (genvar r = 0; r < NUM_ROWS; r++) begin : gen_row

            // =============================================================
            // Dispatcher Control Instance
            // =============================================================
            dispatcher_control_2d #(
                .MAN_WIDTH      (MAN_WIDTH),
                .EXP_WIDTH      (EXP_WIDTH),
                .BRAM_DEPTH     (BRAM_DEPTH),
                .FIFO_DEPTH     (1024),
                .NUM_COLS       (NUM_COLS),
                .AXI_ADDR_WIDTH (42),
                .ADDR_WIDTH     (ADDR_WIDTH),
                .GDDR6_CTRL_ID  (GDDR6_CTRL_ID[r])
            ) u_dispatcher_control (
                .i_clk              (i_clk),
                .i_reset_n          (i_reset_n),

                // Master Control Command Interface
                .i_mc_cmd_op        (mc_cmd_op),
                .i_mc_cmd_id        (mc_cmd_id),
                .i_cmd_payload_word1(mc_cmd_payload_word1[r]),
                .i_cmd_payload_word2(mc_cmd_payload_word2[r]),
                .i_cmd_payload_word3(mc_cmd_payload_word3[r]),
                .o_dc_ack_fetch     (dc_ack_fetch[r]),
                .o_dc_ack_disp      (dc_ack_disp[r]),
                .o_dc_id            (dc_id[r]),

                // Left Path: row_bram Write Interface (activations)
                .o_left_man_wr_addr (dc_left_man_wr_addr[r]),
                .o_left_man_wr_en   (dc_left_man_wr_en[r]),
                .o_left_man_wr_data (dc_left_man_wr_data[r]),
                .o_left_exp_wr_addr (dc_left_exp_wr_addr[r]),
                .o_left_exp_wr_en   (dc_left_exp_wr_en[r]),
                .o_left_exp_wr_data (dc_left_exp_wr_data[r]),

                // Right Path: Column BRAMs (weights)
                .o_right_wr_addr    (dc_right_wr_addr[r]),
                .o_right_wr_en      (dc_right_wr_en[r]),
                .o_right_man_wr_data(dc_right_man_wr_data[r]),
                .o_right_exp_wr_data(dc_right_exp_wr_data[r]),

                // AXI Interface
                .axi_ddr_if         (axi_ddr_if[r]),

                // Debug
                .o_dc_state         (dc_state[r]),
                .o_fetcher_state    (),
                .o_dispatcher_state (),
                .o_fetcher_lines_received (),
                .o_dispatcher_lines_processed (),
                .o_fifo_count       ()
            );

            // =============================================================
            // Weight Interface Adapter: DC RIGHT -> CE Weight
            // =============================================================
            // Dispatcher outputs per-column with one-hot enables
            // CE expects per-MLP addressing
            //
            // Conversion:
            //   - col_idx = one-hot decode of dc_right_wr_en
            //   - wt_mlp_sel = col_idx / 2
            //   - wt_nv_idx = (dc_right_wr_addr * 2) + (col_idx % 2)
            //
            // When any column is being written, we derive the MLP and bank

            localparam int COL_IDX_WIDTH = $clog2(NUM_COLS);
            localparam int MLP_SEL_WIDTH = $clog2(NUM_MLPS);

            logic        wt_wr_en_r;
            logic [MLP_SEL_WIDTH-1:0]  wt_mlp_sel_r;
            logic [9:0]  wt_nv_idx_r;
            logic [COL_IDX_WIDTH-1:0]  col_idx_r;

            // One-hot to binary decoder for column index
            always_comb begin
                col_idx_r = '0;
                for (int c = 0; c < NUM_COLS; c++) begin
                    if (dc_right_wr_en[r][c])
                        col_idx_r = COL_IDX_WIDTH'(c);
                end
            end

            // Weight write enable is OR of all column enables
            assign wt_wr_en_r = |dc_right_wr_en[r];

            // MLP selection: column / 2
            assign wt_mlp_sel_r = col_idx_r[COL_IDX_WIDTH-1:1];

            // NV index: addr * 2 + bank (where bank = col % 2)
            assign wt_nv_idx_r = {dc_right_wr_addr[r], 1'b0} + {9'b0, col_idx_r[0]};

            `ifdef DEBUG_ENGINE_TOP
            always @(posedge i_clk) begin
                if (wt_wr_en_r && r == 0) begin
                    $display("[WT_ADDR_CALC] @%0t row=%0d dc_addr=%0d col_idx=%0d mlp_sel=%0d nv_idx=%0d",
                             $time, r, dc_right_wr_addr[r], col_idx_r, wt_mlp_sel_r, wt_nv_idx_r);
                end
            end
            `endif

            // =============================================================
            // Compute Engine Instance
            // =============================================================
            compute_engine_2d #(
                .MATMUL_ID          (r),
                .MAN_WIDTH          (MAN_WIDTH),
                .EXP_WIDTH          (EXP_WIDTH),
                .BRAM_DEPTH         (BRAM_DEPTH),
                .ADDR_WIDTH         (ADDR_WIDTH),
                .NUM_MLPS           (NUM_MLPS),
                .NUM_COLS           (NUM_COLS),
                .RESULT_FIFO_DEPTH  (512)  // Increased for large batch support
            ) u_compute_engine (
                .i_clk              (i_clk),
                .i_reset_n          (i_reset_n),

                // MATMUL Command Interface
                .i_matmul_en        (matmul_en_pulse),
                .i_cmd_id           (mc_cmd_id),
                .i_cmd_payload_word1(mc_cmd_payload_word1[r]),
                .i_cmd_payload_word2(mc_cmd_payload_word2[r]),
                .i_cmd_payload_word3(mc_cmd_payload_word3[r]),
                .o_matmul_ack       (ce_ack_matmul[r]),
                .o_ce_id            (ce_id[r]),
                .o_matmul_done      (ce_matmul_done[r]),

                // row_bram Write Interface (from DC left path)
                .i_man_left_wr_addr (dc_left_man_wr_addr[r]),
                .i_man_left_wr_en   (dc_left_man_wr_en[r]),
                .i_man_left_wr_data (dc_left_man_wr_data[r]),
                .i_exp_left_wr_addr (dc_left_exp_wr_addr[r]),
                .i_exp_left_wr_en   (dc_left_exp_wr_en[r]),
                .i_exp_left_wr_data (dc_left_exp_wr_data[r]),

                // MLP Weight Write Interface (adapted from DC right path)
                .i_wt_wr_en         (wt_wr_en_r),
                .o_wt_wr_ready      (),
                .i_wt_wr_man        (dc_right_man_wr_data[r]),
                .i_wt_wr_exp        (dc_right_exp_wr_data[r]),
                .i_wt_mlp_sel       (wt_mlp_sel_r),
                .i_wt_nv_idx        (wt_nv_idx_r),

                // Result FIFO Interface (to RC)
                .o_result_data      (ce_to_rc_result_data[r]),
                .i_result_rd_en     (rc_to_ce_result_rd_en[r]),
                .o_result_empty     (ce_to_rc_result_empty[r]),
                .o_result_afull     (ce_result_fifo_afull[r]),

                // Debug
                .o_ce_state         (ce_state[r]),
                .o_result_count     ()
            );

        end
    endgenerate

    // ------------------------------------------------------------------
    // Result Collector - Global reduction across all rows (READOUT command)
    // ------------------------------------------------------------------
    result_collector_2d #(
        .NUM_ROWS           (NUM_ROWS),
        .NUM_COLS           (NUM_COLS),
        .ADDER_SEG_LEN      (2),
        .OUTPUT_FIFO_DEPTH  (512)  // Standardized FIFO depth
    ) u_result_collector (
        .i_clk              (i_clk),
        .i_reset_n          (i_reset_n),

        // Command Interface (snoops MC command bus)
        .i_mc_cmd_op        (mc_cmd_op),
        .i_mc_cmd_id        (mc_cmd_id),
        .i_cmd_payload_word1(mc_cmd_payload_word1[0]),
        .i_cmd_payload_word2(mc_cmd_payload_word2[0]),
        .i_cmd_payload_word3(mc_cmd_payload_word3[0]),
        .o_rc_ack_readout   (rc_ack_readout),

        // CE FIFO Interface (FP16 results from all CEs)
        .i_ce_result_data   (ce_to_rc_result_data),
        .i_ce_result_empty  (ce_to_rc_result_empty),
        .o_ce_result_rd_en  (rc_to_ce_result_rd_en),

        // Output Interface (to result_to_dma - internal ready-valid)
        .i_output_ready     (rc_output_ready),
        .o_output_valid     (rc_output_valid),
        .o_output_last      (rc_output_last),
        .o_output_keep      (rc_output_keep),
        .o_output_data      (rc_output_data),

        // Status
        .o_rc_state         (rc_state),
        .o_rc_busy          (rc_busy),
        .o_rc_cmd_id        (rc_id)
    );

    // ===================================================================
    // Result BRAM Adapter - Converts ready-valid to BRAM write interface
    // ===================================================================
    result_to_dma #(
        .DATA_WIDTH (256),
        .ADDR_WIDTH (9)
    ) u_result_to_dma (
        .i_clk          (i_clk),
        .i_reset_n      (i_reset_n),

        // Ready-Valid Input (from result_collector_2d)
        .i_data         (rc_output_data),
        .i_keep         (rc_output_keep),
        .i_last         (rc_output_last),
        .i_valid        (rc_output_valid),
        .o_ready        (rc_output_ready),

        // BRAM Write Output (to external DMA bridge)
        .o_bram_wr_en   (o_bram_wr_en),
        .o_bram_wr_addr (o_bram_wr_addr),
        .o_bram_wr_data (o_bram_wr_data),
        .o_bram_wr_strobe(o_bram_wr_strobe)
    );

    // ===================================================================
    // Status Logic
    // ===================================================================

    // Engine is busy if command FIFO has data, MC is not idle, or RC is busy
    assign o_engine_busy = (cmd_fifo_count != 13'd0) || (mc_state != 4'd0) || rc_busy;

    // ===================================================================
    // Output Assignments
    // ===================================================================
    assign o_mc_state = mc_state;
    assign o_rc_state = rc_state;

    // ===================================================================
    // Debug Output Assignments
    // ===================================================================
    assign o_dbg_ce_ack_matmul   = dbg_ce_ack_matmul_reg;
    assign o_dbg_dc_ack_fetch    = dbg_dc_ack_fetch_reg;
    assign o_dbg_cmd_valid       = dbg_cmd_valid;
    assign o_dbg_matmul_en_pulse = matmul_en_pulse;
    assign o_dbg_ce_state_row0   = ce_state[0];
    assign o_dbg_dc_state_row0   = dc_state[0];

endmodule : engine_top_2d
