// ------------------------------------------------------------------
// Dispatcher Control 2D Module
//
// Purpose: Integrate fetcher_2d, flex_fifo, and dispatcher_2d
// Features:
//  - fetcher_2d: Reads from GDDR6 via AXI, writes to flex_fifo
//  - flex_fifo: 256-bit x 1024 depth buffer between fetcher and dispatcher
//  - dispatcher_2d: Routes data to LEFT/RIGHT BRAMs
//
// Command Interface:
//  - Snoops MC command bus for FETCH (0xF0) and DISP (0xF1) opcodes
//  - Depacks and registers parameters internally based on opcode
//  - Returns immediate ACK on command receipt
//  - Updates o_dc_id when the actual operation completes
//
// Payload Formats (per-row, V already partitioned by MC):
//
// FETCH (0xF0):
//   word1 = start_addr[31:0]
//   word2 = {v_count[15:0], len[15:0]}
//   word3 = {31'b0, fetch_right}
//
// DISP (0xF1):
//   word1 = {nv_cnt[15:0], v_count[15:0]}  (nv_cnt = B or C count)
//   word2 = {16'b0, tile_addr[15:0]}
//   word3 = {16'b0, col_start[7:0], 5'b0, disp_right, broadcast, man_4b}
//
// Author: Junhao Pan
// Date: 1/22/2026 - Refactored to use packed MC command interface
// ------------------------------------------------------------------

`include "nap_interfaces.svh"

module dispatcher_control_2d
import gemm_pkg::*;
#(
    parameter int MAN_WIDTH = 256,         // Mantissa data width
    parameter int EXP_WIDTH = 8,           // Exponent data width
    parameter int BRAM_DEPTH = 512,        // BRAM depth for dispatcher
    parameter int FIFO_DEPTH = 1024,       // flex_fifo depth
    parameter int NUM_COLS = 16,           // Number of columns for RIGHT path round-robin wrap
    parameter AXI_ADDR_WIDTH = 42,     // AXI address width
    parameter ADDR_WIDTH = $clog2(BRAM_DEPTH),
    parameter [8:0] GDDR6_CTRL_ID = 9'd0  // GDDR6 Page ID for NoC routing
)
(
    // Clock and Reset
    input  logic                         i_clk,
    input  logic                         i_reset_n,

    // ====================================================================
    // Master Control Command Interface (Packed Payload)
    // ====================================================================
    input  logic [7:0]                   i_mc_cmd_op,           // Opcode from MC
    input  logic [7:0]                   i_mc_cmd_id,           // Command ID from MC
    input  logic [31:0]                  i_cmd_payload_word1,   // Per-row payload word 1
    input  logic [31:0]                  i_cmd_payload_word2,   // Per-row payload word 2
    input  logic [31:0]                  i_cmd_payload_word3,   // Per-row payload word 3
    output logic                         o_dc_ack_fetch,        // ACK: immediate on FETCH decode
    output logic                         o_dc_ack_disp,         // ACK: immediate on DISP decode

    // ====================================================================
    // cmd_id Tracking (for WAIT_DISP synchronization)
    // ====================================================================
    output logic [7:0]                   o_dc_id,               // Last completed cmd_id

    // ====================================================================
    // Left Path: row_bram Write Interface (activations - direct write)
    // ====================================================================
    output logic [ADDR_WIDTH-1:0]        o_left_man_wr_addr,
    output logic                         o_left_man_wr_en,
    output logic [MAN_WIDTH-1:0]         o_left_man_wr_data,
    output logic [ADDR_WIDTH-1:0]        o_left_exp_wr_addr,
    output logic                         o_left_exp_wr_en,
    output logic [EXP_WIDTH-1:0]         o_left_exp_wr_data,

    // ====================================================================
    // Right Path: NUM_COLS Column BRAMs Write Interface (weights - direct write)
    // ====================================================================
    output logic [ADDR_WIDTH-1:0]        o_right_wr_addr,       // Shared address bus
    output logic [NUM_COLS-1:0]          o_right_wr_en,         // 16 separate write enables (one-hot)
    output logic [MAN_WIDTH-1:0]         o_right_man_wr_data,   // Shared data bus
    output logic [EXP_WIDTH-1:0]         o_right_exp_wr_data,   // Shared exponent

    // ====================================================================
    // AXI-4 Initiator Interface for DDR access
    // ====================================================================
    t_AXI4.initiator                     axi_ddr_if,

    // ====================================================================
    // Debug Interface
    // ====================================================================
    output logic [3:0]                   o_dc_state,
    output logic [3:0]                   o_fetcher_state,
    output logic [3:0]                   o_dispatcher_state,
    output logic [15:0]                  o_fetcher_lines_received,
    output logic [15:0]                  o_dispatcher_lines_processed,
    output logic [$clog2(FIFO_DEPTH):0]  o_fifo_count
);

    // ====================================================================
    // Opcode Constants
    // ====================================================================
    localparam logic [7:0] CMD_FETCH = 8'hF0;
    localparam logic [7:0] CMD_DISP  = 8'hF1;

    // ====================================================================
    // Internal Signals - FIFO Interface
    // ====================================================================
    logic [MAN_WIDTH-1:0]   fifo_wr_data;
    logic                   fifo_wr_en;
    logic                   fifo_full;
    logic                   fifo_afull;
    logic [MAN_WIDTH-1:0]   fifo_rd_data;
    logic                   fifo_rd_en;
    logic                   fifo_empty;
    logic [$clog2(FIFO_DEPTH):0] fifo_count;

    // ====================================================================
    // Internal Signals - Fetcher Control
    // ====================================================================
    logic                   fetch_en_internal;       // Trigger fetcher
    logic [link_addr_width_gp-1:0] fetch_addr_internal;  // GDDR6 line address (26 bits)
    logic [15:0]            fetch_len_internal;      // Number of lines to fetch
    logic                   fetcher_done_internal;   // Internal completion signal
    logic [3:0]             fetcher_state;
    logic [15:0]            fetcher_lines_received;

    // ====================================================================
    // Internal Signals - Dispatcher Control
    // ====================================================================
    logic                   disp_start_pulse;        // Trigger dispatcher
    logic                   dispatcher_done_internal; // Internal completion signal
    logic [3:0]             dispatcher_state;
    logic [15:0]            dispatcher_lines_processed;

    // Dispatcher parameters (registered from command)
    localparam int COL_START_WIDTH = $clog2(NUM_COLS);
    logic [15:0]            disp_nv_cnt_reg;         // B (left) or C (right) count
    logic [15:0]            disp_ugd_len_reg;        // V count (NVs per UGD)
    logic [COL_START_WIDTH-1:0] disp_col_start_reg;      // Starting column (0..NUM_COLS-1)
    logic                   disp_right_reg;          // 0=Left, 1=Right
    logic [ADDR_WIDTH-1:0]  disp_tile_addr_reg;      // Base write address

    // ====================================================================
    // Command Registers for cmd_id Tracking
    // ====================================================================
    logic [7:0] fetch_cmd_id_reg;
    logic [7:0] disp_cmd_id_reg;
    logic [7:0] dc_id_reg;

    // ====================================================================
    // Opcode Detection (Edge Detection)
    // ====================================================================
    logic [7:0] cmd_op_prev;
    logic       fetch_detected;
    logic       disp_detected;

    // Detect rising edge of opcode change to target opcode
    assign fetch_detected = (i_mc_cmd_op == CMD_FETCH) && (cmd_op_prev != CMD_FETCH);
    assign disp_detected  = (i_mc_cmd_op == CMD_DISP)  && (cmd_op_prev != CMD_DISP);

    // ====================================================================
    // Fetcher 2D Instantiation
    // ====================================================================
    fetcher_2d #(
        .DATA_WIDTH     (MAN_WIDTH),
        .AXI_ADDR_WIDTH (AXI_ADDR_WIDTH),
        .GDDR6_CTRL_ID  (GDDR6_CTRL_ID)
    ) u_fetcher (
        .i_clk              (i_clk),
        .i_reset_n          (i_reset_n),
        
        // Fetch command interface
        .i_fetch_en         (fetch_en_internal),
        .i_fetch_addr       (fetch_addr_internal),
        .i_fetch_len        (fetch_len_internal),
        .o_fetch_done       (fetcher_done_internal),
        
        // External FIFO write interface
        .o_fifo_wr_data     (fifo_wr_data),
        .o_fifo_wr_en       (fifo_wr_en),
        .i_fifo_afull       (fifo_afull),
        
        // AXI interface
        .axi_ddr_if         (axi_ddr_if),
        
        // Debug
        .o_fetcher_state    (fetcher_state),
        .o_lines_received   (fetcher_lines_received)
    );

    // ====================================================================
    // Flex FIFO Instantiation (256-bit x 1024 depth)
    // ====================================================================
    flex_fifo #(
        .DATA_WIDTH (MAN_WIDTH),
        .DEPTH      (FIFO_DEPTH)
    ) u_fifo (
        .i_clk      (i_clk),
        .i_reset_n  (i_reset_n),
        
        // Write interface (from fetcher)
        .i_wr_data  (fifo_wr_data),
        .i_wr_en    (fifo_wr_en),
        .o_full     (fifo_full),
        .o_afull    (fifo_afull),
        
        // Read interface (to dispatcher)
        .o_rd_data  (fifo_rd_data),
        .i_rd_en    (fifo_rd_en),
        .o_empty    (fifo_empty),
        
        // Status
        .o_count    (fifo_count)
    );

    // ====================================================================
    // Dispatcher 2D Instantiation
    // ====================================================================
    dispatcher_2d #(
        .MAN_WIDTH  (MAN_WIDTH),
        .EXP_WIDTH  (EXP_WIDTH),
        .BRAM_DEPTH (BRAM_DEPTH),
        .NUM_COLS   (NUM_COLS),
        .ADDR_WIDTH (ADDR_WIDTH)
    ) u_dispatcher (
        .i_clk              (i_clk),
        .i_reset_n          (i_reset_n),
        
        // Command parameters (from registered values)
        .i_disp_start       (disp_start_pulse),
        .i_nv_cnt           (disp_nv_cnt_reg),
        .i_ugd_len          (disp_ugd_len_reg),
        .i_col_start        (disp_col_start_reg),
        .i_disp_right       (disp_right_reg),
        .i_tile_addr        (disp_tile_addr_reg),
        .o_disp_done        (dispatcher_done_internal),
        
        // FIFO read interface
        .i_fifo_rd_data     (fifo_rd_data),
        .i_fifo_empty       (fifo_empty),
        .o_fifo_rd_en       (fifo_rd_en),
        
        // Left path outputs (activations)
        .o_left_man_wr_addr (o_left_man_wr_addr),
        .o_left_man_wr_en   (o_left_man_wr_en),
        .o_left_man_wr_data (o_left_man_wr_data),
        .o_left_exp_wr_addr (o_left_exp_wr_addr),
        .o_left_exp_wr_en   (o_left_exp_wr_en),
        .o_left_exp_wr_data (o_left_exp_wr_data),
        
        // Right path outputs (weights)
        .o_right_wr_addr    (o_right_wr_addr),
        .o_right_wr_en      (o_right_wr_en),
        .o_right_man_wr_data(o_right_man_wr_data),
        .o_right_exp_wr_data(o_right_exp_wr_data),
        
        // Debug
        .o_disp_state       (dispatcher_state),
        .o_lines_processed  (dispatcher_lines_processed)
    );

    // ====================================================================
    // FETCH Command Handling
    // Payload Depack:
    //   word1 = start_addr[31:0]
    //   word2 = {v_count[15:0], len[15:0]}
    //   word3 = {31'b0, fetch_right}  (unused by dispatcher_control)
    // ====================================================================
    logic fetch_ack_reg;
    
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            cmd_op_prev         <= 8'h00;
            fetch_ack_reg       <= 1'b0;
            fetch_en_internal   <= 1'b0;
            fetch_addr_internal <= '0;
            fetch_len_internal  <= 16'd0;
            fetch_cmd_id_reg    <= 8'd0;
        end else begin
            cmd_op_prev <= i_mc_cmd_op;
            
            // Default: clear single-cycle signals
            fetch_ack_reg     <= 1'b0;
            fetch_en_internal <= 1'b0;

            // synthesis translate_off
            `ifdef DEBUG_DISPATCHER_CTRL
            // Debug: trace opcode values
            if (i_mc_cmd_op != 8'h00) begin
                $display("[DC2D_%0d] @%0t cmd_op=0x%02x, cmd_op_prev=0x%02x, fetch_det=%b, disp_det=%b",
                         GDDR6_CTRL_ID[3:0], $time, i_mc_cmd_op, cmd_op_prev, fetch_detected, disp_detected);
            end
            `endif
            // synthesis translate_on

            // Detect and process FETCH command
            if (fetch_detected) begin
                // ACK immediately on decode
                fetch_ack_reg <= 1'b1;

                // Depack and register parameters
                fetch_addr_internal <= i_cmd_payload_word1[link_addr_width_gp-1:0];  // Line address (26 bits)
                fetch_len_internal  <= i_cmd_payload_word2[15:0];     // len[15:0]
                fetch_cmd_id_reg    <= i_mc_cmd_id;

                // Trigger fetcher
                fetch_en_internal <= 1'b1;

                // synthesis translate_off
                `ifdef DEBUG_DISPATCHER_CTRL
                $display("[DC2D] @%0t FETCH CMD: addr=0x%08x, len=%0d, v=%0d, cmd_id=%0d",
                         $time, i_cmd_payload_word1, i_cmd_payload_word2[15:0],
                         i_cmd_payload_word2[31:16], i_mc_cmd_id);
                `endif
                // synthesis translate_on
            end
        end
    end
    
    assign o_dc_ack_fetch = fetch_ack_reg;

    // ====================================================================
    // DISPATCH Command Handling
    // Payload Depack:
    //   word1 = {nv_cnt[15:0], v_count[15:0]}
    //   word2 = {16'b0, tile_addr[15:0]}
    //   word3 = {16'b0, col_start[7:0], 5'b0, disp_right, broadcast, man_4b}
    // ====================================================================
    logic disp_ack_reg;
    
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            disp_ack_reg        <= 1'b0;
            disp_start_pulse    <= 1'b0;
            disp_nv_cnt_reg     <= 16'd0;
            disp_ugd_len_reg    <= 16'd0;
            disp_col_start_reg  <= 4'd0;
            disp_right_reg      <= 1'b0;
            disp_tile_addr_reg  <= '0;
            disp_cmd_id_reg     <= 8'd0;
        end else begin
            // Default: clear single-cycle signals
            disp_ack_reg     <= 1'b0;
            disp_start_pulse <= 1'b0;

            // Detect and process DISPATCH command
            if (disp_detected) begin
                // ACK immediately on decode
                disp_ack_reg <= 1'b1;

                // Depack and register parameters
                // word1 = {nv_cnt[31:16], v_count[15:0]}
                // word2 = {reserved[31:16], tile_addr[15:0]}
                // word3 = {reserved[31:16], col_start[7:0], 5'b0, disp_right[2], broadcast[1], man_4b[0]}
                // Note: Command format allocates 8 bits for col_start (bits [15:8])
                // Extract COL_START_WIDTH bits from bits [7+COL_START_WIDTH:8]
                // This supports NUM_COLS up to 256 (8 bits), but RTL must match command format
                disp_nv_cnt_reg    <= i_cmd_payload_word1[31:16];         // nv_cnt (B or C)
                disp_ugd_len_reg   <= i_cmd_payload_word1[15:0];          // v_count (V)
                disp_tile_addr_reg <= i_cmd_payload_word2[ADDR_WIDTH-1:0]; // tile_addr
                // Extract col_start: command format has 8 bits (bits [15:8])
                // Extract COL_START_WIDTH bits starting from bit 8
                // For COL_START_WIDTH <= 8: extract from [7+COL_START_WIDTH:8]
                // For COL_START_WIDTH > 8: would need command format change
                if (COL_START_WIDTH <= 8) begin
                    disp_col_start_reg <= COL_START_WIDTH'(i_cmd_payload_word3[7+COL_START_WIDTH:8]);
                end else begin
                    // COL_START_WIDTH > 8 not supported by command format (only 8 bits allocated)
                    // Zero-extend the 8-bit field
                    disp_col_start_reg <= {COL_START_WIDTH-8'(0), COL_START_WIDTH'(i_cmd_payload_word3[15:8])};
                end
                disp_right_reg     <= i_cmd_payload_word3[2];             // disp_right
                disp_cmd_id_reg    <= i_mc_cmd_id;
                
                // Trigger dispatcher
                disp_start_pulse <= 1'b1;

                // synthesis translate_off
                `ifdef DEBUG_DISPATCHER_CTRL
                $display("[DC2D] @%0t DISP CMD: right=%0d, nv_cnt=%0d, v=%0d, col_start=%0d, tile_addr=0x%04x, cmd_id=%0d",
                         $time, i_cmd_payload_word3[2], i_cmd_payload_word1[31:16],
                         i_cmd_payload_word1[15:0], i_cmd_payload_word3[15:8],
                         i_cmd_payload_word2[15:0], i_mc_cmd_id);
                `endif
                // synthesis translate_on
            end
        end
    end
    
    assign o_dc_ack_disp = disp_ack_reg;

    // ====================================================================
    // cmd_id Tracking - Update on Actual Completion
    // ====================================================================
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            dc_id_reg <= 8'd0;
        end else begin
            // Update dc_id when fetcher completes
            if (fetcher_done_internal) begin
                dc_id_reg <= fetch_cmd_id_reg;

                // synthesis translate_off
                `ifdef DEBUG_DISPATCHER_CTRL
                $display("[DC2D] @%0t FETCH completed: dc_id=%0d", $time, fetch_cmd_id_reg);
                `endif
                // synthesis translate_on
            end

            // Update dc_id when dispatcher completes
            if (dispatcher_done_internal) begin
                dc_id_reg <= disp_cmd_id_reg;

                // synthesis translate_off
                `ifdef DEBUG_DISPATCHER_CTRL
                $display("[DC2D] @%0t DISPATCH completed: dc_id=%0d", $time, disp_cmd_id_reg);
                `endif
                // synthesis translate_on
            end
        end
    end
    
    assign o_dc_id = dc_id_reg;

    // ====================================================================
    // Debug Outputs
    // ====================================================================
    // State encoding for debug
    typedef enum logic [3:0] {
        DC_IDLE          = 4'd0,
        DC_FETCH_ACTIVE  = 4'd1,
        DC_DISP_ACTIVE   = 4'd2
    } dc_state_t;
    
    dc_state_t dc_state;
    
    always_comb begin
        if (fetcher_state != 4'd0) begin
            dc_state = DC_FETCH_ACTIVE;
        end else if (dispatcher_state != 4'd0) begin
            dc_state = DC_DISP_ACTIVE;
        end else begin
            dc_state = DC_IDLE;
        end
    end
    
    assign o_dc_state = dc_state;
    assign o_fetcher_state = fetcher_state;
    assign o_dispatcher_state = dispatcher_state;
    assign o_fetcher_lines_received = fetcher_lines_received;
    assign o_dispatcher_lines_processed = dispatcher_lines_processed;
    assign o_fifo_count = fifo_count;

endmodule : dispatcher_control_2d
