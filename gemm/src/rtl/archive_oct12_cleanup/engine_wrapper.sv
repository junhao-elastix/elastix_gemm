// ------------------------------------------------------------------
// MS2.0 GEMM Engine Wrapper Module
//
// Purpose: Top-level wrapper for integrated MS2.0 GEMM engine
// Contains:
//  - CSR command bridge for register interface
//  - Command FIFO (4096×32-bit)
//  - Master control FSM for command parsing
//  - Dispatcher control for GDDR6 fetch operations
//  - Dispatcher BRAM with dual-read interface (2048×256-bit internal buffer)
//  - Modular compute engine for GFP8 matrix multiplication  
//  - Result BRAM for FP16 result storage (FIFO interface)
//
// Data Flow:
//  CSR → cmd_bridge → cmd_fifo → master_control →
//    → dispatcher_control → GDDR6 NAP → dispatcher_bram (dual-read) →
//    → compute_engine_modular → result_bram (FP16) → Host
//
// Author: Integration for MS2.0 GEMM Engine
// Date: Fri Oct 10 17:55:12 PDT 2025 (Modular Architecture)
// ------------------------------------------------------------------

`include "nap_interfaces.svh"

module engine_wrapper
import gemm_pkg::*;
#(
    parameter [8:0] GDDR6_PAGE_ID = 9'd13,  // GDDR6 Channel 1 page ID
    parameter BRAM_ADDR_WIDTH = 9,          // Result BRAM address width (512 lines)
    parameter BRAM_DATA_WIDTH = 256         // Result BRAM data width
)
(
    // Clock and Reset
    input  logic                         i_clk,       // reg_clk domain (200MHz)
    input  logic                         i_reset_n,

    // ====================================================================
    // CSR Interface (from elastix_gemm_top)
    // ====================================================================
    input  logic [31:0]                  i_cmd_word0,
    input  logic [31:0]                  i_cmd_word1,
    input  logic [31:0]                  i_cmd_word2,
    input  logic [31:0]                  i_cmd_word3,
    input  logic                         i_cmd_submit, // Rising edge trigger
    input  logic [1:0]                   i_bypass_mode, // Bypass mode: 0=normal, 1=CE bypass, 2=data forwarding

    // ====================================================================
    // NAP AXI Interface (to nap_responder_wrapper)
    // ====================================================================
    t_AXI4.initiator                     nap_axi,     // 42-bit addresses for GDDR6

    // ====================================================================
    // Result FIFO Interface (streaming output)
    // ====================================================================
    output logic [15:0]                  o_result_fifo_rdata,    // FP16 result data
    input  logic                         i_result_fifo_ren,      // Read enable from host
    output logic                         o_result_fifo_empty,    // FIFO empty flag
    output logic [6:0]                   o_result_fifo_count,    // Number of results available (0-64)

    // ====================================================================
    // Status Outputs (for CSR readback)
    // ====================================================================
    output logic                         o_engine_busy,
    output logic [31:0]                  o_result_count,
    output logic [3:0]                   o_mc_state,      // Master control state (registered)
    output logic [3:0]                   o_mc_state_next, // Master control next state (combinational)
    output logic [3:0]                   o_dc_state,      // Dispatcher control state
    output logic [3:0]                   o_ce_state,      // Compute engine state

    // ====================================================================
    // Debug Outputs (for troubleshooting)
    // ====================================================================
    output logic [31:0]                  o_debug_signals,
    output logic [31:0]                  o_bcv_debug_state,      // BCV controller internal state (Oct 10, 2025)
    output logic [31:0]                  o_bcv_debug_dimensions, // BCV captured dimensions (Oct 10, 2025)
    output logic [31:0]                  o_mc_tile_dimensions,   // Master control TILE dimensions (Oct 10, 2025)
    output logic [31:0]                  o_mc_payload_word1,     // Master control raw payload word 1 (Oct 10, 2025)
    output logic [31:0]                  o_mc_payload_word2,     // Master control raw payload word 2 (Oct 10, 2025)
    output logic [31:0]                  o_mc_payload_word3,     // Master control raw payload word 3 (Oct 10, 2025)

    // ====================================================================
    // BRAM Data Path Debug Outputs (Oct 9, 2025 - CE Stuck Debug)
    // ====================================================================
    output logic [10:0]                  o_ce_bram_rd_addr,    // CE BRAM read address
    output logic                         o_ce_bram_rd_en,      // CE BRAM read enable
    // output logic [2:0]                   o_ce_load_count,      // CE load counter - REMOVED: not in working CE
    output logic [255:0]                 o_dbram_rd_data,      // BRAM read data (full 256-bit line)
    output logic [10:0]                  o_dc_bram_wr_addr,    // DC BRAM write address
    output logic                         o_dc_bram_wr_en,      // DC BRAM write enable
    output logic                         o_dc_fetch_done,      // DC fetch complete flag
    output logic                         o_dc_disp_done        // DC dispatch complete flag
);

    // ===================================================================
    // Internal Signals
    // ===================================================================

    // Command buffer to Master Control (FIFO bypassed)
    logic [31:0] cmd_fifo_rdata;     // Data to master_control
    logic        cmd_fifo_ren;       // Read enable from master_control
    logic        cmd_fifo_empty;     // Empty flag
    logic [12:0] cmd_fifo_count;     // Count for status
    logic        cmd_fifo_full;      // Full flag (unused in bypass)
    logic [15:0] cmd_fifo_total_writes;  // Total writes (unused in bypass)

    // Master Control to Dispatcher Control
    logic                                mc_fetch_en;
    logic [link_addr_width_gp-1:0]      mc_fetch_addr;
    logic [link_len_width_gp-1:0]       mc_fetch_len;
    logic                                mc_fetch_done;

    logic                                mc_disp_en;
    logic [tile_mem_addr_width_gp-1:0]  mc_disp_addr;
    logic [tile_mem_addr_width_gp-1:0]  mc_disp_len;
    logic                                mc_man_4b_8b_n;
    logic                                mc_disp_done;

    // Add missing handshake completion signals from modules back to master_control
    logic                                dc_mc_fetch_done;
    logic                                dc_mc_disp_done;
    logic                                ce_mc_tile_done;

    // Master Control to Compute Engine - Fixed signal names for proper connections
    logic                                mc_tile_en;
    logic [tile_mem_addr_width_gp-1:0]  mc_ce_left_addr;
    logic [tile_mem_addr_width_gp-1:0]  mc_ce_right_addr;
    logic [tile_mem_addr_width_gp-1:0]  mc_ce_left_ugd_len;
    logic [tile_mem_addr_width_gp-1:0]  mc_ce_right_ugd_len;
    logic [tile_mem_addr_width_gp-1:0]  mc_ce_vec_len;
    logic [7:0]                          mc_ce_dim_b;
    logic [7:0]                          mc_ce_dim_c; 
    logic [7:0]                          mc_ce_dim_v;
    logic                                mc_ce_left_man_4b;
    logic                                mc_ce_right_man_4b;
    logic                                mc_ce_main_loop_over_left;
    logic                                mc_tile_done;

    // Debug signals
    logic [12:0]                         mc_sees_count_debug;  // What MC sees for cmd_fifo_count
    logic [7:0]                          mc_cmd_op_debug;     // What opcode MC captured
    logic [31:0]                         mc_tile_dimensions;  // Master control TILE dimensions
    logic [31:0]                         mc_payload_word1, mc_payload_word2, mc_payload_word3;  // MC raw payload words

    // Dispatcher BRAM interfaces (Dual Read Ports for MS2.0)
    logic                                dbram_wr_en;
    logic [$clog2(2048)-1:0]            dbram_wr_addr;
    logic [255:0]                       dbram_wr_data;

    // Dual BRAM read ports (left and right matrices)
    logic                                dbram_rd_en_left;
    logic [$clog2(2048)-1:0]            dbram_rd_addr_left;
    logic [255:0]                       dbram_rd_data_left;
    
    logic                                dbram_rd_en_right;
    logic [$clog2(2048)-1:0]            dbram_rd_addr_right;
    logic [255:0]                       dbram_rd_data_right;

    // Debug signals from submodules (Oct 9, 2025 - CE Stuck Debug)
    logic [10:0]                         dc_bram_wr_addr;
    logic                                dc_bram_wr_en;

    // Compute Engine to Result BRAM
    logic [15:0]                         ce_result_data;      // FP16 results
    logic                                ce_result_valid;
    logic                                result_ready;

    // ===================================================================
    // Module Instantiations
    // ===================================================================

    // ------------------------------------------------------------------
    // DIRECT CSR to CMD_FIFO Connection (NO CSR BRIDGE - Oct 7 2025)
    // Pattern: Counter-based sequencer matching engine_sim testbench behavior
    // Submit trigger → Push 4 words to FIFO over 4 cycles (no full checking)
    // ------------------------------------------------------------------

    // FIX Oct 8 2025: reg_control_block write_strobes are multi-cycle (typically 2 cycles)
    // Need edge detection to generate true 1-cycle pulse for push sequencer
    // Without this, 2-cycle strobe causes push_counter to reset every cycle (stuck at 1)
    logic cmd_submit_prev;
    logic cmd_submit_pulse;

    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            cmd_submit_prev <= 1'b0;
        end else begin
            cmd_submit_prev <= i_cmd_submit;
        end
    end

    // Rising edge detection: generates 1-cycle pulse on 0→1 transition
    assign cmd_submit_pulse = i_cmd_submit & ~cmd_submit_prev;

    // FIFO BYPASS: Push sequencer no longer needed - load all 4 words at once
    // (Previous push sequencer logic removed - see cmd_buffer below)

    // ------------------------------------------------------------------
    // DIRECT CSR APPROACH (Oct 8 2025) - NO BUFFER
    // Pass CSR registers directly to master_control
    // Master control samples on cmd_submit_pulse and reads 4 words sequentially
    // ------------------------------------------------------------------

    // COMMAND QUEUE IMPLEMENTATION
    localparam int unsigned CMD_QUEUE_DEPTH = 32;
    localparam int unsigned CMD_QUEUE_AW    = $clog2(CMD_QUEUE_DEPTH);

    logic [7:0]  cmd_submit_total;   // Total commands submitted
    logic [7:0]  cmd_read_total;     // Total commands fully read
    logic [7:0]  cmd_complete_total; // Total commands completed (MC returned to IDLE)
    logic [1:0]  cmd_word_count;     // Index within current command (for debug)
    logic        mc_was_busy;        // Track MC state changes to detect completion
    logic        cmd_fifo_ren_reg;   // Delayed read enable for proper index increment timing

    // Small queue to retain command payloads until master_control consumes them
    logic [31:0] cmd_queue_word0 [CMD_QUEUE_DEPTH-1:0];
    logic [31:0] cmd_queue_word1 [CMD_QUEUE_DEPTH-1:0];
    logic [31:0] cmd_queue_word2 [CMD_QUEUE_DEPTH-1:0];
    logic [31:0] cmd_queue_word3 [CMD_QUEUE_DEPTH-1:0];
    logic [2:0]  cmd_queue_len   [CMD_QUEUE_DEPTH-1:0];
    logic [CMD_QUEUE_AW-1:0] cmd_queue_head;
    logic [CMD_QUEUE_AW-1:0] cmd_queue_tail;
    logic [CMD_QUEUE_AW:0]   cmd_queue_count;

    logic        cmd_active_valid;
    logic [2:0]  cmd_active_len;
    logic [2:0]  cmd_active_index;
    logic [31:0] cmd_active_word0;
    logic [31:0] cmd_active_word1;
    logic [31:0] cmd_active_word2;
    logic [31:0] cmd_active_word3;

    // Determine number of 32-bit words for a given opcode
    function automatic [2:0] get_cmd_word_count(input logic [7:0] opcode);
        case (opcode)
            e_cmd_op_fetch:     get_cmd_word_count = 3'd3;
            e_cmd_op_disp:      get_cmd_word_count = 3'd2;
            e_cmd_op_tile:      get_cmd_word_count = 3'd4;
            e_cmd_op_wait_disp,
            e_cmd_op_wait_tile: get_cmd_word_count = 3'd1;
            default:            get_cmd_word_count = 3'd4;
        endcase
    endfunction

    // FIXED: Pending count is the DIFFERENCE between submitted and COMPLETED commands
    // (not just read - command stays pending until MC finishes execution)
    logic [7:0] cmd_pending_count;
    assign cmd_pending_count = cmd_submit_total - cmd_complete_total;

    logic queue_has_data;
    assign queue_has_data = (cmd_queue_count != 0);

    // Main queue/control logic
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            cmd_submit_total   <= 8'd0;
            cmd_read_total     <= 8'd0;
            cmd_complete_total <= 8'd0;
            mc_was_busy        <= 1'b0;
            cmd_fifo_ren_reg   <= 1'b0;
            cmd_word_count     <= 2'd0;
            cmd_queue_head     <= '0;
            cmd_queue_tail     <= '0;
            cmd_queue_count    <= '0;
            cmd_active_valid   <= 1'b0;
            cmd_active_len     <= 3'd0;
            cmd_active_index   <= 3'd0;
            cmd_active_word0   <= 32'd0;
            cmd_active_word1   <= 32'd0;
            cmd_active_word2   <= 32'd0;
            cmd_active_word3   <= 32'd0;
        end else begin
            // Track MC state transitions to detect command completion
            // When MC goes from busy (state != 0) to IDLE (state == 0), command completed
            mc_was_busy <= (o_mc_state != 4'd0);
            if (mc_was_busy && o_mc_state == 4'd0 && cmd_complete_total < cmd_read_total) begin
                cmd_complete_total <= cmd_complete_total + 1'd1;
                cmd_active_valid <= 1'b0;  // Clear active command on completion
                $display("[ENGINE_WRAPPER] @%0t Command completed: complete_total=%0d, pending=%0d",
                         $time, cmd_complete_total + 1'd1, cmd_pending_count - 1'd1);
            end

            // CRITICAL FIX (Oct 10, 2025): Increment index IMMEDIATELY when cmd_fifo_ren asserted
            // Master control expects index to change BEFORE next cycle's read
            // Delay register was causing all reads to use index=0
            if (cmd_fifo_ren && cmd_active_valid) begin
                if (cmd_active_index == cmd_active_len - 1) begin
                    // All words read, but KEEP valid until command completes
                    // Don't clear cmd_active_valid here - completion tracking handles it
                    cmd_active_index <= 3'd0;
                    cmd_word_count   <= 2'd0;
                    cmd_read_total   <= cmd_read_total + 1'd1;
                end else begin
                    cmd_active_index <= cmd_active_index + 3'd1;
                    cmd_word_count   <= cmd_active_index[1:0] + 2'd1;
                end
            end
            
            // Keep delay register for any other logic that might need it (unused now)
            cmd_fifo_ren_reg <= cmd_fifo_ren;

            // Load next command from queue when idle
            if (!cmd_active_valid && queue_has_data) begin
                cmd_active_word0 <= cmd_queue_word0[cmd_queue_head];
                cmd_active_word1 <= cmd_queue_word1[cmd_queue_head];
                cmd_active_word2 <= cmd_queue_word2[cmd_queue_head];
                cmd_active_word3 <= cmd_queue_word3[cmd_queue_head];
                cmd_active_len   <= cmd_queue_len[cmd_queue_head];
                cmd_active_index <= 3'd0;
                cmd_active_valid <= 1'b1;
                cmd_queue_head   <= cmd_queue_head + 1'b1;
                cmd_queue_count  <= cmd_queue_count - 1'b1;
                cmd_word_count   <= 2'd0;
            end

            // Capture new submissions
            if (cmd_submit_pulse) begin
                logic [2:0] words_this_cmd;
                words_this_cmd = get_cmd_word_count(i_cmd_word0[7:0]);
                cmd_submit_total <= cmd_submit_total + 1'd1;

                if (!cmd_active_valid && !queue_has_data) begin
                    // Command can become active immediately
                    cmd_active_word0 <= i_cmd_word0;
                    cmd_active_word1 <= i_cmd_word1;
                    cmd_active_word2 <= i_cmd_word2;
                    cmd_active_word3 <= i_cmd_word3;
                    cmd_active_len   <= words_this_cmd;
                    cmd_active_index <= 3'd0;
                    cmd_active_valid <= 1'b1;
                    cmd_word_count   <= 2'd0;
                end else begin
                    cmd_queue_word0[cmd_queue_tail] <= i_cmd_word0;
                    cmd_queue_word1[cmd_queue_tail] <= i_cmd_word1;
                    cmd_queue_word2[cmd_queue_tail] <= i_cmd_word2;
                    cmd_queue_word3[cmd_queue_tail] <= i_cmd_word3;
                    cmd_queue_len[cmd_queue_tail]   <= words_this_cmd;
                    cmd_queue_tail                  <= cmd_queue_tail + 1'b1;
                    cmd_queue_count                 <= cmd_queue_count + 1'b1;
                end
            end
        end
    end

    // Provide current command word to master_control
    logic [31:0] cmd_csr_mux;
    always_comb begin
        if (cmd_active_valid) begin
            case (cmd_active_index[1:0])
                2'd0: cmd_csr_mux = cmd_active_word0;
                2'd1: cmd_csr_mux = cmd_active_word1;
                2'd2: cmd_csr_mux = cmd_active_word2;
                default: cmd_csr_mux = cmd_active_word3;
            endcase
        end else begin
            cmd_csr_mux = 32'd0;
        end
    end

    assign cmd_fifo_rdata = cmd_csr_mux;
    assign cmd_fifo_empty = (cmd_pending_count == 0);
    assign cmd_fifo_count = {5'd0, cmd_pending_count};  // 8-bit count converted to 13-bit
    assign cmd_fifo_full = (cmd_queue_count == CMD_QUEUE_DEPTH);
    assign cmd_fifo_total_writes = 16'd0;

    /* FIFO DISABLED - Will re-enable after debugging
    cmd_fifo i_cmd_fifo (
        .i_clk          (i_clk),
        .i_reset_n      (i_reset_n),
        .i_wr_data      (cmd_fifo_wdata),
        .i_wr_en        (cmd_fifo_wen),
        .o_full         (cmd_fifo_full),
        .o_afull        (),
        .o_rd_data      (cmd_fifo_rdata),
        .i_rd_en        (cmd_fifo_ren),
        .o_empty        (cmd_fifo_empty),
        .o_count        (cmd_fifo_count),
        .o_total_writes (cmd_fifo_total_writes)
    );
    */

    // ------------------------------------------------------------------
    // Master Control - Reconnected for Full Engine Integration
    // ------------------------------------------------------------------
    master_control i_master_control (
        .i_clk          (i_clk),
        .i_reset_n      (i_reset_n),

        // Bypass mode
        .i_bypass_mode  (i_bypass_mode),

        // Command FIFO Interface
        .i_cmd_fifo_rdata (cmd_fifo_rdata),
        .i_cmd_fifo_empty (cmd_fifo_empty),
        .i_cmd_fifo_count (cmd_fifo_count),
        .o_cmd_fifo_ren   (cmd_fifo_ren),

        // Dispatcher Control Interface (FETCH/DISP commands)
        .o_dc_fetch_en   (mc_fetch_en),
        .o_dc_fetch_addr (mc_fetch_addr),
        .o_dc_fetch_len  (mc_fetch_len),
        .i_dc_fetch_done (dc_mc_fetch_done),

        .o_dc_disp_en    (mc_disp_en),
        .o_dc_disp_addr  (mc_disp_addr),
        .o_dc_disp_len   (mc_disp_len),
        .o_dc_man_4b_8b_n(mc_man_4b_8b_n),
        .i_dc_disp_done  (dc_mc_disp_done),

        // Compute Engine Interface (TILE command)
        .o_ce_tile_en            (mc_tile_en),
        .o_ce_left_addr          (mc_ce_left_addr),
        .o_ce_right_addr         (mc_ce_right_addr),
        .o_ce_left_ugd_len       (mc_ce_left_ugd_len),
        .o_ce_right_ugd_len      (mc_ce_right_ugd_len),
        .o_ce_vec_len            (mc_ce_vec_len),
        .o_ce_dim_b              (mc_ce_dim_b),
        .o_ce_dim_c              (mc_ce_dim_c),
        .o_ce_dim_v              (mc_ce_dim_v),
        .o_ce_left_man_4b        (mc_ce_left_man_4b),
        .o_ce_right_man_4b       (mc_ce_right_man_4b),
        .o_ce_main_loop_over_left(mc_ce_main_loop_over_left),
        .i_ce_tile_done          (ce_mc_tile_done),

        // Status/Debug
        .o_mc_state       (o_mc_state),
        .o_mc_state_next  (o_mc_state_next),  // Combinational next state
        .o_last_opcode    (),  // TODO: Connect if debug needed
        .o_mc_sees_count  (mc_sees_count_debug),  // What count MC actually sees
        .o_cmd_op_debug   (mc_cmd_op_debug),      // What opcode MC captured
        .o_mc_tile_dimensions(mc_tile_dimensions), // Master control TILE dimensions (Oct 10, 2025)
        .o_mc_payload_word1(mc_payload_word1),     // MC raw payload word 1 (Oct 10, 2025)
        .o_mc_payload_word2(mc_payload_word2),     // MC raw payload word 2 (Oct 10, 2025)
        .o_mc_payload_word3(mc_payload_word3)      // MC raw payload word 3 (Oct 10, 2025)
    );

    // ------------------------------------------------------------------
    // Dispatcher Control - UNCOMMENTED FOR BUILD TIME TESTING (Test 1/4)
    // ------------------------------------------------------------------
    dispatcher_control #(
        .TGT_DATA_WIDTH (256),
        .AXI_ADDR_WIDTH (42),
        .BRAM_DEPTH     (2048),
        .GDDR6_PAGE_ID  (GDDR6_PAGE_ID)
    ) i_dispatcher_control (
        .i_clk          (i_clk),
        .i_reset_n      (i_reset_n),

        // Master Control Interface (FIXED - connect to actual master_control outputs)
        .i_fetch_en     (mc_fetch_en),
        .i_fetch_addr   (mc_fetch_addr),
        .i_fetch_len    (mc_fetch_len),
        .o_fetch_done   (dc_mc_fetch_done),

        .i_disp_en      (mc_disp_en),
        .i_disp_addr    (mc_disp_addr),
        .i_disp_len     (mc_disp_len),
        .i_man_4b_8b_n  (mc_man_4b_8b_n),
        .o_disp_done    (dc_mc_disp_done),

        // Dual BRAM Read Ports (for Compute Engine)
        .i_bram_rd_addr_left    (dbram_rd_addr_left),
        .o_bram_rd_data_left    (dbram_rd_data_left),
        .i_bram_rd_en_left      (dbram_rd_en_left),
        
        .i_bram_rd_addr_right   (dbram_rd_addr_right),
        .o_bram_rd_data_right   (dbram_rd_data_right),
        .i_bram_rd_en_right     (dbram_rd_en_right),

        // AXI Interface for GDDR6
        .axi_ddr_if     (nap_axi),

        // Debug
        .o_dc_state     (o_dc_state),
        .o_bram_wr_count(),  // Not used
        .o_bram_wr_addr (dc_bram_wr_addr),
        .o_bram_wr_en   (dc_bram_wr_en)
    );

    // ------------------------------------------------------------------
    // Dispatcher BRAM (Internal to dispatcher_control in actual design)
    // Note: In the actual engine_sim, this is instantiated inside
    // dispatcher_control. We keep the interface consistent here.
    // ------------------------------------------------------------------
    // The dispatcher_bram is internal to dispatcher_control module
    // No separate instantiation needed

    // ------------------------------------------------------------------
    // Compute Engine - MS2.0 MODULAR VERSION WITH DUAL BRAM
    // ------------------------------------------------------------------
    // Modular design with dual BRAM read ports for ~42% performance improvement

    compute_engine_modular i_compute_engine (
        .i_clk          (i_clk),
        .i_reset_n      (i_reset_n),

        // Master Control Interface (TILE command)
        .i_tile_en      (mc_tile_en),
        .i_left_addr    (mc_ce_left_addr),
        .i_right_addr   (mc_ce_right_addr),
        .i_left_ugd_len (mc_ce_left_ugd_len),
        .i_right_ugd_len(mc_ce_right_ugd_len),
        .i_vec_len      (mc_ce_vec_len),
        .i_dim_b        (mc_ce_dim_b),
        .i_dim_c        (mc_ce_dim_c),
        .i_dim_v        (mc_ce_dim_v),
        .i_left_man_4b  (mc_ce_left_man_4b),
        .i_right_man_4b (mc_ce_right_man_4b),
        .i_main_loop_over_left(mc_ce_main_loop_over_left),
        .o_tile_done    (ce_mc_tile_done),

        // Dual BRAM Read Interface (from Dispatcher Control)
        .o_bram_left_rd_addr    (dbram_rd_addr_left),
        .i_bram_left_rd_data    (dbram_rd_data_left),
        .o_bram_left_rd_en      (dbram_rd_en_left),
        
        .o_bram_right_rd_addr   (dbram_rd_addr_right),
        .i_bram_right_rd_data   (dbram_rd_data_right),
        .o_bram_right_rd_en     (dbram_rd_en_right),

        // Result FIFO Write Interface
        .o_result_data  (ce_result_data),
        .o_result_valid (ce_result_valid),
        .i_result_full  (1'b0),  // Note: Result BRAM writer always ready (no backpressure)
        .i_result_afull (1'b0),  // Note: Result BRAM writer always ready (no backpressure)

        // Status
        .o_ce_state            (o_ce_state),
        .o_result_count        ()  // Connected through result_bram_writer
        // Debug ports: compute_engine_modular doesn't have these ports
        // .o_bcv_debug_state     (o_bcv_debug_state),
        // .o_bcv_debug_dimensions(o_bcv_debug_dimensions)
    );

    // ------------------------------------------------------------------
    // Result FIFO - Streaming output buffer (FIFO architecture)
    // Replaces result_bram_writer for better handling of variable-length results
    // ------------------------------------------------------------------
    logic result_fifo_full;
    logic result_fifo_afull;
    
    result_bram u_result_fifo (
        .i_clk          (i_clk),
        .i_reset_n      (i_reset_n),

        // Write Interface (from Compute Engine)
        .i_wr_data      (ce_result_data),      // FP16 results
        .i_wr_en        (ce_result_valid),
        .o_full         (result_fifo_full),
        .o_afull        (result_fifo_afull),

        // Read Interface (to Testbench/Host)
        .o_rd_data      (o_result_fifo_rdata),
        .i_rd_en        (i_result_fifo_ren),
        .o_empty        (o_result_fifo_empty),

        // Status
        .o_count        (o_result_fifo_count)
    );
    
    // Backpressure signal (currently unused, could connect to CE)
    assign result_ready = !result_fifo_full;
    
    // Result count from FIFO (extended to 32-bit for CSR interface)
    assign o_result_count = {25'b0, o_result_fifo_count};

    // ===================================================================
    // Status Logic
    // ===================================================================

    // Engine is busy if any component is active - TESTING WITH FORCED CSR BRIDGE IDLE
    // NOTE: CSR bridge forced to IDLE (busy=0), other components active
    assign o_engine_busy = 1'b0 ||                    // FORCED: cmd_bridge_busy = 0 (CSR bridge in IDLE)
                          (cmd_fifo_count != 13'd0) ||
                          (o_mc_state != 4'd0) ||
                          (o_dc_state != 4'd0) ||
                          (o_ce_state != 4'd0);

    // Debug signals for troubleshooting (COMMAND QUEUE DEBUG - Oct 9 20:30)
    assign o_debug_signals = {
        mc_cmd_op_debug,                // [31:24] Captured opcode (from cmd_op_reg)
        cmd_submit_total,               // [23:16] Total submitted
        cmd_read_total,                 // [15:8]  Total read (all words consumed)
        cmd_complete_total              // [7:0]   Total completed (MC returned to IDLE)
    };

    // ===================================================================
    // BRAM Data Path Debug Outputs (MS2.0 Dual BRAM)
    // ===================================================================
    assign o_ce_bram_rd_addr = dbram_rd_addr_left;  // Debug: show left matrix reads
    assign o_ce_bram_rd_en = dbram_rd_en_left;       // Debug: show left matrix enable
    assign o_dbram_rd_data = dbram_rd_data_left;     // Debug: show left matrix data
    assign o_dc_bram_wr_addr = dc_bram_wr_addr;
    assign o_dc_bram_wr_en = dc_bram_wr_en;
    assign o_dc_fetch_done = dc_mc_fetch_done;
    assign o_dc_disp_done = dc_mc_disp_done;

    // ===================================================================
    // Assertions (for simulation)
    // ===================================================================
    `ifdef SIM
        // Check for command submission while busy
        property no_submit_while_busy;
            @(posedge i_clk) disable iff (~i_reset_n)
            (i_cmd_submit && cmd_bridge_busy) |=>
            $display("[ENGINE_WRAPPER] WARNING: Command submitted while bridge busy");
        endproperty
        assert property (no_submit_while_busy);

        // Monitor state transitions
        always @(posedge i_clk) begin
            if (o_mc_state != 4'd0 || o_dc_state != 4'd0 || o_ce_state != 4'd0) begin
                $display("[ENGINE_WRAPPER] @%0t States: MC=%0d, DC=%0d, CE=%0d",
                         $time, o_mc_state, o_dc_state, o_ce_state);
            end
        end
    `endif

    // ===================================================================
    // Debug Signal Assignments
    // ===================================================================
    assign o_mc_tile_dimensions = mc_tile_dimensions;  // Master control TILE dimensions
    assign o_mc_payload_word1 = mc_payload_word1;      // MC raw payload word 1
    assign o_mc_payload_word2 = mc_payload_word2;      // MC raw payload word 2
    assign o_mc_payload_word3 = mc_payload_word3;      // MC raw payload word 3

endmodule : engine_wrapper