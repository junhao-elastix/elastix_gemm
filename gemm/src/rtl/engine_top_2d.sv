// ------------------------------------------------------------------
// 2-D Multi-Row GEMM Engine Top Module
//
// Purpose: Top-level wrapper for 2-D GEMM architecture with NUM_ROWS rows
// Contains:
//  - Command FIFO (4096x32-bit): Buffers incoming microcode commands
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
    // Host Command FIFO Interface (Direct Write)
    // ====================================================================
    input  logic [31:0]                  i_cmd_fifo_wdata,
    input  logic                         i_cmd_fifo_wen,
    output logic                         o_cmd_fifo_full,
    output logic                         o_cmd_fifo_afull,
    output logic [12:0]                  o_cmd_fifo_count,

    // ====================================================================
    // 16 AXI Interfaces for GDDR6 Access (one per row)
    // ====================================================================
    t_AXI4.initiator                     axi_ddr_if [NUM_ROWS-1:0],

    // ====================================================================
    // Result Output Interface (to Host DMA)
    // Output is packed 256-bit lines (16 x FP16)
    // ====================================================================
    input  logic                         i_result_ready,
    output logic                         o_result_valid,
    output logic                         o_result_last,
    output logic [15:0]                  o_result_keep,   // 16-bit keep mask
    output logic [255:0]                 o_result_data,   // 256-bit packed (16 x FP16)

    // ====================================================================
    // Status Outputs
    // ====================================================================
    output logic                         o_engine_busy,
    output logic [3:0]                   o_mc_state,      // Master control state
    output logic [3:0]                   o_rc_state       // Result collector state
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

    // Command FIFO -> Master Control
    logic [31:0]  cmd_fifo_rdata;
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
        .o_mc_state         (mc_state)
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

            logic        wt_wr_en_r;
            logic [2:0]  wt_mlp_sel_r;
            logic [9:0]  wt_nv_idx_r;
            logic [3:0]  col_idx_r;

            // One-hot to binary decoder for column index
            always_comb begin
                col_idx_r = 4'd0;
                for (int c = 0; c < NUM_COLS; c++) begin
                    if (dc_right_wr_en[r][c])
                        col_idx_r = c[3:0];
                end
            end

            // Weight write enable is OR of all column enables
            assign wt_wr_en_r = |dc_right_wr_en[r];

            // MLP selection: column / 2
            assign wt_mlp_sel_r = col_idx_r[3:1];

            // NV index: addr * 2 + bank (where bank = col % 2)
            assign wt_nv_idx_r = {dc_right_wr_addr[r], 1'b0} + {9'b0, col_idx_r[0]};

            `ifdef SIMULATION
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
                .NUM_COLUMNS        (NUM_COLS),
                .RESULT_FIFO_DEPTH  (64)
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
        .OUTPUT_FIFO_DEPTH  (256)
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

        // Output Interface (to Host DMA - 256-bit packed FP16)
        .i_output_ready     (i_result_ready),
        .o_output_valid     (o_result_valid),
        .o_output_last      (o_result_last),
        .o_output_keep      (o_result_keep),
        .o_output_data      (o_result_data),

        // Status
        .o_rc_state         (rc_state),
        .o_rc_busy          (rc_busy),
        .o_rc_cmd_id        (rc_id)
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

endmodule : engine_top_2d
