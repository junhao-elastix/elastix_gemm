// ------------------------------------------------------------------
// Dispatcher Control Module (MS2.0)
//
// Purpose: DDR fetch and BRAM buffering for MS2.0 architecture
// Features:
//  - FETCH command: Read GFP8 block (528 lines x 256-bit) from DDR to BRAM
//  - DISP command: Acknowledge vector dispatch configuration
//  - Dual-port BRAM: Port A (write from DDR), Port B (read by CE)
//  - AXI4 burst read interface for DDR access
//  - Sequential buffer access: Fetch complete -> done -> CE reads
//
// Memory Layout (GFP8 Block):
//  Lines 0-15:   Exponents (512 total, 32 per line)
//  Lines 16-527: Mantissas (128 rows x 4 groups/row = 512 lines)
//
// Author: MS2.0 Migration
// Date: Thu Oct 2 00:14:43 AM PDT 2025
// ------------------------------------------------------------------

`include "nap_interfaces.svh"

module dispatcher_control
import gemm_pkg::*;
#(
    parameter MAN_WIDTH = 256,         // Mantissa data width
    parameter EXP_WIDTH = 8,           // Exponent data width
    parameter BRAM_DEPTH = 512,        // Dispatcher BRAM depth (matches dispatcher_bram hardcoded value)
    parameter TILE_DEPTH = 512,        // Tile BRAM depth per side
    parameter AXI_ADDR_WIDTH = 42,     // AXI address width (GDDR6 NoC: {Page[9], Line[26], Pad[2], Byte[5]})
    parameter BRAM_ADDR_WIDTH = $clog2(BRAM_DEPTH),  // 9-bit for 512 depth
    parameter TILE_ADDR_WIDTH = $clog2(TILE_DEPTH),  // 9-bit for 512 depth
    parameter [8:0] GDDR6_PAGE_ID = 9'd2  // GDDR6 Page ID for NoC routing (Channel 1 default)
)
(
    // Clock and Reset
    input  logic                         i_clk,
    input  logic                         i_reset_n,

    // ====================================================================
    // Master Control Interface (FETCH/DISP commands)
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
    // Dispatcher BRAM Read Ports (to Compute Engine - parallel access)
    // ====================================================================
    // Left matrix mantissa read
    input  logic [BRAM_ADDR_WIDTH-1:0]   i_disp_man_left_rd_addr,
    input  logic                         i_disp_man_left_rd_en,
    output logic [MAN_WIDTH-1:0]         o_disp_man_left_rd_data,

    // Right matrix mantissa read
    input  logic [BRAM_ADDR_WIDTH-1:0]   i_disp_man_right_rd_addr,
    input  logic                         i_disp_man_right_rd_en,
    output logic [MAN_WIDTH-1:0]         o_disp_man_right_rd_data,

    // ====================================================================
    // Dispatcher BRAM Exponent Write Ports (for post-fetch unpacking)
    // ====================================================================
    output logic [TILE_ADDR_WIDTH-1:0]   o_disp_exp_left_wr_addr,
    output logic                         o_disp_exp_left_wr_en,
    output logic [EXP_WIDTH-1:0]         o_disp_exp_left_wr_data,

    output logic [TILE_ADDR_WIDTH-1:0]   o_disp_exp_right_wr_addr,
    output logic                         o_disp_exp_right_wr_en,
    output logic [EXP_WIDTH-1:0]         o_disp_exp_right_wr_data,

    // ====================================================================
    // Dispatcher BRAM Exponent Read Ports (to Compute Engine)
    // ====================================================================
    input  logic [TILE_ADDR_WIDTH-1:0]   i_disp_exp_left_rd_addr,
    input  logic                         i_disp_exp_left_rd_en,
    output logic [EXP_WIDTH-1:0]         o_disp_exp_left_rd_data,

    input  logic [TILE_ADDR_WIDTH-1:0]   i_disp_exp_right_rd_addr,
    input  logic                         i_disp_exp_right_rd_en,
    output logic [EXP_WIDTH-1:0]         o_disp_exp_right_rd_data,

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
    output logic [10:0]                  o_disp_wr_addr,    // Debug: BRAM write address (for gemm)
    output logic                         o_disp_wr_en,      // Debug: BRAM write enable (for gemm)

    // DISPATCH operation read address (for engine_top to mux to BRAM read port)
    output logic [8:0]                   o_disp_rd_addr,
    output logic                         o_disp_rd_en       // Active during ST_DISP_BUSY
);

    // ===================================================================
    // State Machine Definition
    // ===================================================================
    typedef enum logic [3:0] {
        ST_IDLE            = 4'd0,
        ST_FETCH_INIT      = 4'd1,
        ST_FETCH_READ      = 4'd2,
        ST_FETCH_READ_EXP  = 4'd3,  // Read exponent lines (0-15) into exp_packed
        ST_FETCH_READ_MAN  = 4'd4,  // Read mantissa lines (16-527) + parallel unpack
        ST_FETCH_DONE      = 4'd5,
        ST_DISP_BUSY       = 4'd6,  // Copy from dispatcher_bram to tile_bram (working state)
        ST_DISP_DONE       = 4'd7   // DISPATCH operation complete
    } state_t;

    state_t state_reg, state_next;

    // ===================================================================
    // Local Parameters
    // ===================================================================
    localparam FIXED_BURST_LEN = 15;   // AXI burst length = 16 beats
    localparam BYTES_PER_BEAT = 32;    // 32 bytes per AXI beat (256-bit)
    localparam ADDR_BYTE_SHIFT = 5;    // Byte address to beat address shift

    // ===================================================================
    // Internal Signals
    // ===================================================================

    // BRAM control signals
    logic [10:0] bram_wr_addr_reg;  // Increased from 10 to 11 bits for 2048-entry BRAM
    logic [MAN_WIDTH-1:0] bram_wr_data_reg;
    logic        bram_wr_en_reg;
    logic        bram_wr_target_reg;  // 0=left, 1=right

    // FETCH command tracking
    logic [link_addr_width_gp-1:0] fetch_addr_reg;
    logic        fetch_target_reg;  // 0=left, 1=right (captured from i_fetch_target)
    logic [10:0] current_line_reg;  // Increased from 10 to 11 bits for 2048-entry BRAM

    // Counters for tracking exp and mantissa lines during fetch
    logic [4:0]  exp_lines_fetched_reg;   // 0-15: exponent lines fetched
    logic [9:0]  man_lines_fetched_reg;   // 0-511: mantissa lines fetched

    // AXI transaction control
    logic axi_ar_req_reg;
    logic axi_r_ready_reg;
    logic [7:0] beat_count_reg;

    // Status flags
    logic fetch_done_reg;
    logic disp_done_reg;

    // Edge detection for command enables (prevent double-triggering)
    logic fetch_en_prev;
    logic disp_en_prev;

    // DISPATCH operation control
    logic [7:0] disp_man_nv_cnt_reg;     // Stored man_nv_cnt parameter
    logic [9:0] disp_lines_to_copy_reg;  // man_nv_cnt × 4 (total lines to copy)
    logic [8:0] disp_man_cnt_reg;        // Mantissa lines dispatched counter (0-511) - parallel 4-path
    logic [9:0] disp_exp_cnt_reg;        // Exponent entries dispatched counter (0-511)
    logic       disp_man_done_reg;       // Mantissa dispatch complete flag
    logic       disp_exp_done_reg;       // Exponent dispatch complete flag

    // DISPATCH command parameters (captured at trigger)
    logic         disp_right_reg;            // Dispatch side (0=left, 1=right)
    logic         disp_broadcast_reg;        // Distribution mode (0=distribute, 1=broadcast)
    logic [23:0]  disp_col_en_reg;           // Column enable mask
    logic [4:0]   disp_col_start_reg;        // Distribution start column
    logic [7:0]   disp_ugd_vec_size_reg;     // UGD vector size (NVs per batch)

    // Multi-tile dispatch control (per SINGLE_ROW_REFERENCE.md lines 144-154)
    logic [4:0]   disp_current_tile_idx_reg;     // Current tile being written (0-23)
    logic [7:0]   disp_num_enabled_tiles_reg;    // Count of enabled tiles (popcount of col_en)
    logic [8:0]   disp_tile_start_reg;           // Source pointer in dispatcher_bram
    logic [15:0]  disp_receive_tile_start_reg;   // Destination pointer in tile_bram
    logic [9:0]   disp_ugd_batch_lines_reg;      // Lines per batch (ugd_vec_size × 4, max=512)
    logic [7:0]   disp_batch_cnt_reg;            // Current batch being dispatched
    logic [7:0]   disp_total_batches_reg;        // Total batches to dispatch (man_nv_cnt / ugd_vec_size)
    logic [9:0]   disp_within_batch_cnt_reg;     // Lines within current batch (0 to ugd_batch_lines-1, max=511)

    // Address calculation signals
    logic [10:0]  dispatcher_read_addr;          // Final read address in dispatcher_bram
    logic [10:0]  tile_write_addr;               // Final write address in tile_bram

    // Parallel unpacking signals (for 3-buffer architecture)
    logic [3:0]  unpack_exp_packed_rd_addr_reg; // 0-15: which exp_packed line to read
    logic [MAN_WIDTH-1:0] exp_packed_rd_data_wire; // Data from exp_packed BRAM

    // ===================================================================
    // Helper Functions
    // ===================================================================
    // Population count (count number of 1's in a bitvector)
    function automatic logic [7:0] popcount_24bit(input logic [23:0] bits);
        int count;
        count = 0;
        for (int i = 0; i < 24; i++) begin
            count = count + bits[i];
        end
        return count[7:0];
    endfunction

    // Simplified tile selection: Sequential tiles starting from 0
    // Assumptions: col_en is sequential (e.g., 0x3=tiles[0:1], 0xF=tiles[0:3])
    //              col_start always 0, C divisible by num_tiles

    // ===================================================================
    // State Transition Logic
    // ===================================================================
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            state_reg <= ST_IDLE;
            fetch_en_prev <= 1'b0;
            disp_en_prev <= 1'b0;
        end else begin
            state_reg <= state_next;
            fetch_en_prev <= i_fetch_en;
            disp_en_prev <= i_disp_en;
        end
    end

    // Next state combinational logic
    always_comb begin
        state_next = state_reg;

        case (state_reg)
            ST_IDLE: begin
                // Only trigger on RISING edge of enables to prevent double-triggering
                if (i_fetch_en && !fetch_en_prev) begin
                    $display("[DC_DEBUG] @%0t ST_IDLE: i_fetch_en RISING EDGE, transitioning to FETCH_INIT", $time);
                    state_next = ST_FETCH_INIT;
                end else if (i_disp_en && !disp_en_prev) begin
                    state_next = ST_DISP_BUSY;
                end
            end

            ST_FETCH_INIT: begin
                // Initialize FETCH operation
                state_next = ST_FETCH_READ;
            end

            ST_FETCH_READ: begin
                // Issue AXI read request
                if (axi_ddr_if.arvalid && axi_ddr_if.arready) begin
                    if (exp_lines_fetched_reg < 16) begin
                        $display("[DC_DEBUG] @%0t ST_FETCH_READ: AR handshake, moving to FETCH_READ_EXP", $time);
                        state_next = ST_FETCH_READ_EXP;
                    end else begin
                        $display("[DC_DEBUG] @%0t ST_FETCH_READ: AR handshake, moving to FETCH_READ_MAN", $time);
                        state_next = ST_FETCH_READ_MAN;
                    end
                end
            end

            ST_FETCH_READ_EXP: begin
                // Read exponent burst (16 beats)
                if (axi_ddr_if.rvalid && axi_ddr_if.rready && axi_ddr_if.rlast) begin
                    if (exp_lines_fetched_reg >= 15) begin
                        $display("[DC_DEBUG] @%0t FETCH_READ_EXP complete (%0d lines), moving to FETCH_READ for mantissas", $time, exp_lines_fetched_reg + 1);
                        state_next = ST_FETCH_READ;  // Issue next AR for first mantissa burst
                    end else begin
                        state_next = ST_FETCH_READ;  // Issue next AR for more exponents
                    end
                end
            end

            ST_FETCH_READ_MAN: begin
                // Read mantissa bursts (32 bursts x 16 beats = 512 lines) + parallel unpack
                if (axi_ddr_if.rvalid && axi_ddr_if.rready && axi_ddr_if.rlast) begin
                    if (man_lines_fetched_reg >= 511) begin
                        $display("[DC_DEBUG] @%0t FETCH_READ_MAN complete (%0d lines), moving to FETCH_DONE", $time, man_lines_fetched_reg + 1);
                        state_next = ST_FETCH_DONE;
                    end else begin
                        state_next = ST_FETCH_READ;  // Issue next AR for more mantissas
                    end
                end
            end

            ST_FETCH_DONE: begin
                // Fetch complete - exponents already unpacked in parallel!
                $display("[DC_DEBUG] @%0t FETCH_DONE, returning to IDLE (unpacking done in parallel)", $time);
                state_next = ST_IDLE;
            end

            ST_DISP_BUSY: begin
                // Copy dispatcher_bram → tile_bram (both mantissas and exponents)
                // Copy man_nv_cnt × 4 lines (variable based on command parameter)
                if (disp_man_done_reg && disp_exp_done_reg) begin
                    state_next = ST_DISP_DONE;
                end else begin
                    state_next = ST_DISP_BUSY;
                end
            end

            ST_DISP_DONE: begin
                // DISPATCH operation complete, return to IDLE
                state_next = ST_IDLE;
            end

            default: begin
                state_next = ST_IDLE;
            end
        endcase
    end

    // ===================================================================
    // FETCH/DISP Command Processing
    // ===================================================================

    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            fetch_addr_reg <= '0;
            fetch_target_reg <= 1'b0;
            current_line_reg <= '0;
            exp_lines_fetched_reg <= '0;
            man_lines_fetched_reg <= '0;
            fetch_done_reg <= 1'b0;
            disp_done_reg <= 1'b0;

            // NEW: Initialize multi-tile dispatch variables
            disp_man_cnt_reg <= '0;
            disp_exp_cnt_reg <= '0;
            disp_man_done_reg <= 1'b0;
            disp_exp_done_reg <= 1'b0;
            disp_ugd_batch_lines_reg <= 10'd512;  // Initialize to safe maximum value
            disp_num_enabled_tiles_reg <= 8'd1;  // Initialize to 1 to avoid divide-by-zero
            disp_current_tile_idx_reg <= '0;
            disp_tile_start_reg <= '0;
            disp_receive_tile_start_reg <= '0;
            disp_batch_cnt_reg <= '0;
            disp_total_batches_reg <= '0;
            disp_within_batch_cnt_reg <= '0;
            batch_complete_pending <= 1'b0;
        end else begin
            fetch_done_reg <= 1'b0;  // Default
            disp_done_reg <= 1'b0;  // Default

            case (state_reg)
                ST_IDLE: begin
                    // Only capture parameters on RISING edge (same as state transition logic)
                    if (i_fetch_en && !fetch_en_prev) begin
                        fetch_addr_reg <= i_fetch_addr;
                        fetch_target_reg <= i_fetch_target;  // Capture left/right target
                        `ifdef SIMULATION
                        $display("[DC_CAPTURE] @%0t FETCH params: addr=0x%08x, len=%0d, target=%0d (%s)",
                                 $time, i_fetch_addr, i_fetch_len, i_fetch_target, i_fetch_target ? "RIGHT" : "LEFT");
                        `endif
                        current_line_reg <= '0;

                        // Reset phase counters for new fetch
                        exp_lines_fetched_reg <= '0;
                        man_lines_fetched_reg <= '0;

                        $display("[DC_DEBUG] @%0t FETCH_START: DDR_addr=%0d, len=%0d, current_line=%0d, target=%s",
                                 $time, i_fetch_addr, i_fetch_len, current_line_reg,
                                 i_fetch_target ? "RIGHT" : "LEFT");
                    end else if (i_disp_en && !disp_en_prev) begin
                        // Initialize DISPATCH operation and capture parameters
                        disp_man_nv_cnt_reg <= i_disp_man_nv_cnt;
                        disp_lines_to_copy_reg <= {2'b00, i_disp_man_nv_cnt} << 2;  // man_nv_cnt × 4
                        disp_man_cnt_reg <= '0;
                        disp_exp_cnt_reg <= '0;
                        disp_man_done_reg <= 1'b0;
                        disp_exp_done_reg <= 1'b0;
                        disp_done_reg <= 1'b0;

                        // NEW: Capture multi-tile dispatch parameters (per SINGLE_ROW_REFERENCE.md)
                        disp_right_reg <= i_disp_right;
                        disp_broadcast_reg <= i_disp_broadcast;
                        disp_col_en_reg <= i_disp_col_en;
                        disp_col_start_reg <= i_disp_col_start;
                        disp_ugd_vec_size_reg <= i_disp_ugd_vec_size;

                        // NEW: Calculate multi-tile dispatch parameters (per lines 144-154 of reference)
                        disp_num_enabled_tiles_reg <= popcount_24bit(i_disp_col_en);
                        disp_ugd_batch_lines_reg <= {1'b0, i_disp_ugd_vec_size} << 2;  // ugd_vec_size × 4
                        disp_total_batches_reg <= i_disp_man_nv_cnt / i_disp_ugd_vec_size;
                        disp_current_tile_idx_reg <= 5'd0;  // Always start at tile 0 (simplified assumption)

                        // NEW: Initialize pointers (use addresses from DISP command)
                        disp_tile_start_reg <= '0;  // Always read from 0 in dispatcher_bram (FETCH always starts at 0)
                        disp_receive_tile_start_reg <= i_disp_tile_addr;  // Write to tile BRAM at specified address
                        disp_batch_cnt_reg <= '0;  // Start at batch 0
                        disp_within_batch_cnt_reg <= '0;  // Start at line 0 within batch
                        disp_write_cnt <= -11'sd1;  // Start at -1 so first write is to address 0

                        $display("[DC] @%0t DISP triggered: man_nv_cnt=%0d, ugd_vec_size=%0d, total_batches=%0d, batch_lines=%0d, disp_right=%0b, broadcast=%0b, col_en=0x%06x, num_tiles=%0d",
                                 $time, i_disp_man_nv_cnt, i_disp_ugd_vec_size, i_disp_man_nv_cnt / i_disp_ugd_vec_size,
                                 {2'b00, i_disp_ugd_vec_size} << 2,
                                 i_disp_right, i_disp_broadcast, i_disp_col_en, popcount_24bit(i_disp_col_en));
                    end
                end

                ST_FETCH_READ_EXP: begin
                    // Increment exp line counter for each beat received
                    if (axi_ddr_if.rvalid && axi_ddr_if.rready) begin
                        exp_lines_fetched_reg <= exp_lines_fetched_reg + 1;
                        current_line_reg <= current_line_reg + 1;
                        $display("[DC_DEBUG] @%0t EXP_LINE: %0d/16", $time, exp_lines_fetched_reg + 1);
                    end
                end

                ST_FETCH_READ_MAN: begin
                    // Increment man line counter for each beat received
                    if (axi_ddr_if.rvalid && axi_ddr_if.rready) begin
                        man_lines_fetched_reg <= man_lines_fetched_reg + 1;
                        current_line_reg <= current_line_reg + 1;
                        if (man_lines_fetched_reg[3:0] == 4'd0 || axi_ddr_if.rlast) begin
                            $display("[DC_DEBUG] @%0t MAN_LINE: %0d/512", $time, man_lines_fetched_reg + 1);
                        end
                    end
                end

                ST_FETCH_DONE: begin
                    // Signal fetch_done immediately - unpacking done in parallel!
                    fetch_done_reg <= 1'b1;
                end

                ST_DISP_BUSY: begin
                    // Multi-tile dispatch with broadcast/distribute modes
                    // Per SINGLE_ROW_REFERENCE.md lines 186-188

                    // Initialize combinational flag
                    set_batch_complete = 1'b0;

                    // Copy one line per cycle (mantissa and exponent in parallel)
                    if (!disp_man_done_reg) begin
                        // Increment read counter
                        disp_within_batch_cnt_reg <= disp_within_batch_cnt_reg + 1;
                        // Increment write counter (lags read by 1 cycle initially due to -1 start)
                        disp_write_cnt <= disp_write_cnt + 11'sd1;

                        // Check if current batch complete (ugd_vec_size × 4 lines)
                        if (disp_within_batch_cnt_reg == (disp_ugd_batch_lines_reg - 1)) begin
                            // Batch complete, reset counters
                            disp_within_batch_cnt_reg <= '0;
                            disp_write_cnt <= -11'sd1;  // Reset write counter for next batch

                            if (disp_broadcast_reg) begin
                                // === BROADCAST MODE (SIMPLIFIED) ===
                                // Same data to all tiles, then advance batch
                                // Assumption: Tiles are sequential 0 to (num_tiles-1)
                                $display("[DC] @%0t BROADCAST: Batch %0d to tile %0d complete",
                                        $time, disp_batch_cnt_reg, disp_current_tile_idx_reg);

                                if (disp_current_tile_idx_reg == (disp_num_enabled_tiles_reg - 1)) begin
                                    // Last tile received this batch, advance to next batch
                                    disp_tile_start_reg <= disp_tile_start_reg + disp_ugd_batch_lines_reg;
                                    disp_receive_tile_start_reg <= disp_receive_tile_start_reg + disp_ugd_batch_lines_reg;
                                    disp_batch_cnt_reg <= disp_batch_cnt_reg + 1;
                                    disp_current_tile_idx_reg <= 5'd0;  // Wrap to tile 0

                                    $display("[DC] @%0t BROADCAST: All tiles done, advancing to batch %0d",
                                            $time, disp_batch_cnt_reg + 1);

                                    // Check if all batches dispatched
                                    if (disp_batch_cnt_reg == (disp_total_batches_reg - 1)) begin
                                        set_batch_complete = 1'b1;  // Mark for delayed done
                                        $display("[DC] @%0t BROADCAST: All %0d batches complete (pending final write)",
                                                $time, disp_total_batches_reg);
                                    end
                                end else begin
                                    // Move to next tile with SAME data (source pointer unchanged)
                                    disp_current_tile_idx_reg <= disp_current_tile_idx_reg + 1;
                                    $display("[DC] @%0t BROADCAST: Moving to tile %0d (same data)",
                                            $time, disp_current_tile_idx_reg + 1);
                                end
                            end else begin
                                // === DISTRIBUTE MODE (SIMPLIFIED) ===
                                // Each tile gets different data, round-robin
                                // Assumption: C divisible by num_tiles
                                $display("[DC] @%0t DISTRIBUTE: Batch %0d to tile %0d complete",
                                        $time, disp_batch_cnt_reg, disp_current_tile_idx_reg);

                                // Each tile gets different data, advance source pointer
                                disp_tile_start_reg <= disp_tile_start_reg + disp_ugd_batch_lines_reg;
                                disp_receive_tile_start_reg <= disp_receive_tile_start_reg + disp_ugd_batch_lines_reg;
                                disp_batch_cnt_reg <= disp_batch_cnt_reg + 1;

                                // Move to next tile (simple modulo wrap-around)
                                disp_current_tile_idx_reg <= (disp_current_tile_idx_reg + 1) % disp_num_enabled_tiles_reg;

                                // Check if all batches dispatched
                                if (disp_batch_cnt_reg == (disp_total_batches_reg - 1)) begin
                                    set_batch_complete = 1'b1;  // Mark for delayed done
                                    $display("[DC] @%0t DISTRIBUTE: All %0d batches complete (pending final write)",
                                            $time, disp_total_batches_reg);
                                end
                            end
                        end
                    end

                    // Unified batch completion management
                    if (batch_complete_pending) begin
                        disp_man_done_reg <= 1'b1;
                        disp_exp_done_reg <= 1'b1;
                        batch_complete_pending <= 1'b0;
                        $display("[DC] @%0t Final delayed write complete, setting done", $time);
                    end else if (set_batch_complete) begin
                        batch_complete_pending <= 1'b1;
                    end
                end

                ST_DISP_DONE: begin
                    // Signal DISPATCH operation complete
                    disp_done_reg <= 1'b1;
                    $display("[DC] @%0t DISP_DONE: All copies complete, signaling done", $time);
                end
            endcase
        end
    end

    assign o_fetch_done = fetch_done_reg;

    assign o_disp_done = disp_done_reg;

    // ===================================================================
    // DISPATCH Copy - Tile BRAM Write Logic
    // ===================================================================
    // During ST_DISP_BUSY, read from dispatcher_bram/exp_bram and write to tile_bram
    // The BRAM read has 1-cycle latency, so we pipeline: read cycle N, write cycle N+1

    logic [9:0] man_rd_addr_pipe;    // Pipeline for source address [0-511]
    logic [9:0] man_wr_addr_pipe;    // Pipeline for destination address [0-511]
    logic [9:0] exp_rd_addr_pipe;    // Pipeline for source address [0-511]
    logic [9:0] exp_wr_addr_pipe;    // Pipeline for destination address [0-511]

    // Write counter lags read counter by 1 due to BRAM latency
    logic signed [10:0] disp_write_cnt;  // Signed to allow -1 initial value
    logic       copy_active_pipe;
    logic       man_wr_valid_pipe;   // Valid signal for mantissa write
    logic       exp_wr_valid_pipe;   // Valid signal for exponent write

    // Multi-tile write enable pipeline (1-stage to avoid blocking first write)
    logic [4:0] physical_tile_id_pipe;   // Physical tile ID (0-23) for future round-robin
    // tile_wr_en now uses combinational logic (tile_wr_en_comb) - no pipeline register needed

    // BRAM read latency compensation - delay write valid by 1 cycle
    logic       man_wr_valid_delayed;
    logic       exp_wr_valid_delayed;

    // Delay done signals to allow final delayed write to complete
    logic       batch_complete_pending;    // Flag to delay setting done by 1 cycle
    logic       set_batch_complete;        // Combinational flag indicating batch just completed

    // Internal read addresses for DISPATCH operation
    // During DISPATCH, we internally control reads from dispatcher_bram
    // During MATMUL, external CE controls reads
    logic [TILE_ADDR_WIDTH-1:0] internal_man_left_rd_addr;
    logic [TILE_ADDR_WIDTH-1:0] internal_man_right_rd_addr;
    logic [TILE_ADDR_WIDTH-1:0] internal_exp_left_rd_addr;
    logic [TILE_ADDR_WIDTH-1:0] internal_exp_right_rd_addr;
    logic                       internal_rd_en;

    // Muxed read addresses (select internal during DISPATCH, external otherwise)
    logic [TILE_ADDR_WIDTH-1:0] muxed_man_left_rd_addr;
    logic [TILE_ADDR_WIDTH-1:0] muxed_man_right_rd_addr;
    logic [TILE_ADDR_WIDTH-1:0] muxed_exp_left_rd_addr;
    logic [TILE_ADDR_WIDTH-1:0] muxed_exp_right_rd_addr;
    logic                       muxed_man_left_rd_en;
    logic                       muxed_man_right_rd_en;
    logic                       muxed_exp_left_rd_en;
    logic                       muxed_exp_right_rd_en;

    // Address source multiplexing (internal during DISPATCH, external during MATMUL)
    // CRITICAL: internal addresses must be combinational to match pipeline timing
    always_comb begin
        if (state_reg == ST_DISP_BUSY) begin
            if (disp_right_reg) begin
                // RIGHT DISPATCH: Read from right side only
                internal_man_left_rd_addr  = '0;
                internal_man_right_rd_addr = man_rd_addr_pipe[TILE_ADDR_WIDTH-1:0];
                internal_exp_left_rd_addr  = '0;
                internal_exp_right_rd_addr = exp_rd_addr_pipe[TILE_ADDR_WIDTH-1:0];
            end else begin
                // LEFT DISPATCH: Read from left side only
                internal_man_left_rd_addr  = man_rd_addr_pipe[TILE_ADDR_WIDTH-1:0];
                internal_man_right_rd_addr = '0;
                internal_exp_left_rd_addr  = exp_rd_addr_pipe[TILE_ADDR_WIDTH-1:0];
                internal_exp_right_rd_addr = '0;
            end
            internal_rd_en = 1'b1;
        end else begin
            internal_man_left_rd_addr  = '0;
            internal_man_right_rd_addr = '0;
            internal_exp_left_rd_addr  = '0;
            internal_exp_right_rd_addr = '0;
            internal_rd_en = 1'b0;
        end
    end

    assign muxed_man_left_rd_addr  = (state_reg == ST_DISP_BUSY) ? internal_man_left_rd_addr  : i_disp_man_left_rd_addr;
    assign muxed_man_right_rd_addr = (state_reg == ST_DISP_BUSY) ? internal_man_right_rd_addr : i_disp_man_right_rd_addr;
    assign muxed_exp_left_rd_addr  = (state_reg == ST_DISP_BUSY) ? internal_exp_left_rd_addr  : i_disp_exp_left_rd_addr;
    assign muxed_exp_right_rd_addr = (state_reg == ST_DISP_BUSY) ? internal_exp_right_rd_addr : i_disp_exp_right_rd_addr;
    assign muxed_man_left_rd_en    = (state_reg == ST_DISP_BUSY) ? internal_rd_en : i_disp_man_left_rd_en;
    assign muxed_man_right_rd_en   = (state_reg == ST_DISP_BUSY) ? internal_rd_en : i_disp_man_right_rd_en;
    assign muxed_exp_left_rd_en    = (state_reg == ST_DISP_BUSY) ? internal_rd_en : i_disp_exp_left_rd_en;
    assign muxed_exp_right_rd_en   = (state_reg == ST_DISP_BUSY) ? internal_rd_en : i_disp_exp_right_rd_en;

    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            man_rd_addr_pipe <= '0;
            man_wr_addr_pipe <= '0;
            exp_rd_addr_pipe <= '0;
            exp_wr_addr_pipe <= '0;
            copy_active_pipe <= 1'b0;
            man_wr_valid_pipe <= 1'b0;
            exp_wr_valid_pipe <= 1'b0;
            man_wr_valid_delayed <= 1'b0;
            exp_wr_valid_delayed <= 1'b0;
            physical_tile_id_pipe <= '0;
        end else begin
            // Pipeline the addresses for 1-cycle BRAM read latency
            // Multi-tile dispatch with broadcast/distribute addressing

            // Calculate addresses (SAME for both broadcast and distribute modes)
            // The difference is handled by when disp_tile_start_reg advances:
            //   BROADCAST: Advances after all tiles receive same batch
            //   DISTRIBUTE: Advances after each tile receives (every batch)
            // READ address uses current counter
            dispatcher_read_addr = disp_tile_start_reg + disp_within_batch_cnt_reg;
            // WRITE address uses lagging counter (compensates for BRAM latency)
            tile_write_addr = disp_receive_tile_start_reg[10:0] + disp_write_cnt[9:0];

            // Assign to pipeline registers (truncate to 10-bit for pipe)
            man_rd_addr_pipe <= dispatcher_read_addr[9:0];
            man_wr_addr_pipe <= tile_write_addr[9:0];
            exp_rd_addr_pipe <= dispatcher_read_addr[9:0];
            exp_wr_addr_pipe <= tile_write_addr[9:0];

            copy_active_pipe <= (state_reg == ST_DISP_BUSY);

            // Valid signals: HIGH when actively copying (not done)
            man_wr_valid_pipe <= (state_reg == ST_DISP_BUSY) && !disp_man_done_reg;
            exp_wr_valid_pipe <= (state_reg == ST_DISP_BUSY) && !disp_exp_done_reg;

            // CRITICAL: Delay write valid by 1 cycle to account for BRAM read latency
            // Cycle N: Read address presented to BRAM
            // Cycle N+1: BRAM data available, delayed write valid goes high
            man_wr_valid_delayed <= man_wr_valid_pipe;
            exp_wr_valid_delayed <= exp_wr_valid_pipe;

            // Multi-tile write enable pipeline
            // Broadcast vs Distribute mode (per SINGLE_ROW_REFERENCE.md)
            physical_tile_id_pipe <= disp_current_tile_idx_reg;
        end
    end

    // Multi-tile write enable - COMBINATIONAL (no pipeline delay)
    // CRITICAL: Must update in SAME cycle as disp_current_tile_idx_reg changes
    // to avoid first write of new batch going to wrong tile
    logic [23:0] tile_wr_en_comb;
    always_comb begin
        if (state_reg == ST_DISP_BUSY) begin
            if (disp_broadcast_reg) begin
                // BROADCAST MODE: Enable all tiles in col_en
                // Same data written to all enabled tiles simultaneously
                tile_wr_en_comb = disp_col_en_reg;
            end else begin
                // DISTRIBUTE MODE: Enable only current tile (one-hot)
                // Different data written to each tile sequentially
                tile_wr_en_comb = 24'h000001 << disp_current_tile_idx_reg;
            end
        end else begin
            tile_wr_en_comb = '0;
        end
    end

    // Tile BRAM selective write (per SINGLE_ROW_REFERENCE.md)
    // SELECTIVE 2-PATH WRITE: Only write to selected side (left OR right)
    // disp_right_reg=0: Write to left side only
    // disp_right_reg=1: Write to right side only
    // This allows separate DISPATCH commands for left and right matrices

    // Pipeline disp_right_reg for synchronization with write valid signals
    logic disp_right_pipe;
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            disp_right_pipe <= 1'b0;
        end else begin
            disp_right_pipe <= disp_right_reg;
        end
    end

    // Tile BRAM write outputs (2-stage pipeline with BRAM read latency compensation)
    // Left mantissa write (ONLY when disp_right_reg=0)
    assign o_tile_man_left_wr_addr = man_wr_addr_pipe[8:0];
    assign o_tile_man_left_wr_data = o_disp_man_left_rd_data;        // From left BRAM read port
    assign o_tile_man_left_wr_en   = man_wr_valid_delayed && !disp_right_pipe;  // DELAYED write

    // Right mantissa write (ONLY when disp_right_reg=1)
    assign o_tile_man_right_wr_addr = man_wr_addr_pipe[8:0];
    assign o_tile_man_right_wr_data = o_disp_man_right_rd_data;      // From right BRAM read port
    assign o_tile_man_right_wr_en   = man_wr_valid_delayed && disp_right_pipe;   // DELAYED write

    // Tile BRAM exponent writes (selective based on disp_right_reg)
    assign o_tile_exp_left_wr_addr  = exp_wr_addr_pipe[8:0];
    assign o_tile_exp_left_wr_data  = o_disp_exp_left_rd_data;       // From left_exp_bram
    assign o_tile_exp_left_wr_en    = exp_wr_valid_delayed && !disp_right_pipe;  // DELAYED write

    assign o_tile_exp_right_wr_addr = exp_wr_addr_pipe[8:0];
    assign o_tile_exp_right_wr_data = o_disp_exp_right_rd_data;      // From right_exp_bram
    assign o_tile_exp_right_wr_en   = exp_wr_valid_delayed && disp_right_pipe;   // DELAYED write

    // Multi-tile write enable output (one-hot encoding of current tile)
    // COMBINATIONAL: Updates immediately when disp_current_tile_idx_reg changes
    assign o_tile_wr_en = tile_wr_en_comb;

    // DISPATCH read address outputs (for engine_top muxing to internal dispatcher_bram)
    // Selective read addressing based on disp_right_reg
    // - disp_right_reg=0: Read from left dispatcher_bram only
    // - disp_right_reg=1: Read from right dispatcher_bram only
    // Higher level (engine_top) uses disp_right signal to MUX between left/right BRAMs
    // Simplified: Direct counter for single-tile dispatch
    assign o_disp_rd_addr = disp_man_cnt_reg;  // Direct counter addressing
    assign o_disp_rd_en   = (state_reg == ST_DISP_BUSY) && !disp_man_done_reg;

    // ===================================================================
    // Parallel Exponent Unpacking - CONTINUOUS (independent of AXI)
    // ===================================================================
    // Unpack exponents in parallel with mantissa fetch
    // Uses a continuous counter to avoid skipping addresses during AXI burst gaps
    
    // Continuous unpacking counter (runs every cycle during ST_FETCH_READ_MAN)
    // CRITICAL: Only reset at start of FETCH, not when transitioning to ST_FETCH_READ!
    logic [9:0] unpack_idx_reg;
    
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            unpack_idx_reg <= 10'd0;
        end else if (state_reg == ST_IDLE && i_fetch_en && !fetch_en_prev) begin
            // Reset at start of new FETCH command
            unpack_idx_reg <= 10'd0;
        end else if (state_reg == ST_FETCH_READ_MAN && unpack_idx_reg < 10'd513) begin
            unpack_idx_reg <= unpack_idx_reg + 10'd1;
        end
    end
    
    // Calculate unpacking write index (1 cycle for BRAM internal read latency)
    // With combinational output, no stale data problem!
    // Cycle N: address set
    // Cycle N+1: data available (BRAM internal read completes, combinational output)
    logic [9:0] unpack_wr_idx;
    assign unpack_wr_idx = unpack_idx_reg - 10'd1;
    
    // Read address for exp_packed (which of 16 lines)
    // Since each exp_packed line has 32 exponents, we keep reading
    // the same line for 32 consecutive writes
    assign unpack_exp_packed_rd_addr_reg = unpack_wr_idx[9:5];  // /32
    
    // Extract byte offset within the 256-bit exp_packed line
    logic [4:0] exp_byte_offset;
    assign exp_byte_offset = unpack_wr_idx[4:0];  // %32
    
    // Extract the current exponent byte from exp_packed read data
    logic [7:0] current_exp_byte;
    assign current_exp_byte = exp_packed_rd_data_wire[exp_byte_offset*8 +: 8];
    
    // Exponent write enables (active during unpacking, skip first 1 cycle for BRAM latency)
    // Write continuously from unpack_idx 1-512 (unpack_wr_idx 0-511)
    assign o_disp_exp_left_wr_en = (state_reg == ST_FETCH_READ_MAN) && 
                              (fetch_target_reg == 1'b0) &&
                              (unpack_idx_reg >= 10'd1) &&
                              (unpack_idx_reg <= 10'd512);
    
    assign o_disp_exp_right_wr_en = (state_reg == ST_FETCH_READ_MAN) && 
                               (fetch_target_reg == 1'b1) &&
                               (unpack_idx_reg >= 10'd1) &&
                               (unpack_idx_reg <= 10'd512);
    
    // Exponent write addresses
    assign o_disp_exp_left_wr_addr = unpack_wr_idx[8:0];
    assign o_disp_exp_right_wr_addr = unpack_wr_idx[8:0];
    
    // Exponent write data
    assign o_disp_exp_left_wr_data = current_exp_byte;
    assign o_disp_exp_right_wr_data = current_exp_byte;

    `ifdef SIMULATION
    always @(posedge i_clk) begin
        if (o_disp_exp_left_wr_en) begin
            $display("[DISP_UNPACK] @%0t LEFT exp write: addr=%0d, data=0x%02x, packed_rd_addr=%0d, byte_offset=%0d, unpack_wr_idx=%0d",
                     $time, o_disp_exp_left_wr_addr, o_disp_exp_left_wr_data, unpack_exp_packed_rd_addr_reg, exp_byte_offset, unpack_wr_idx);
        end
        if (o_disp_exp_right_wr_en) begin
            $display("[DISP_UNPACK] @%0t RIGHT exp write: addr=%0d, data=0x%02x, packed_rd_addr=%0d, byte_offset=%0d, unpack_wr_idx=%0d, fetch_target_reg=%0d, exp_packed_rd_data_wire first 4 bytes=%02x %02x %02x %02x",
                     $time, o_disp_exp_right_wr_addr, o_disp_exp_right_wr_data, unpack_exp_packed_rd_addr_reg, exp_byte_offset, unpack_wr_idx, fetch_target_reg,
                     exp_packed_rd_data_wire[7:0], exp_packed_rd_data_wire[15:8], exp_packed_rd_data_wire[23:16], exp_packed_rd_data_wire[31:24]);
        end
    end
    `endif

    // ===================================================================
    // BRAM Write Logic (Port A - DDR to BRAM)
    // ===================================================================
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            bram_wr_addr_reg <= '0;
            bram_wr_data_reg <= '0;
            bram_wr_en_reg <= 1'b0;
            bram_wr_target_reg <= 1'b0;
        end else begin
            bram_wr_en_reg <= 1'b0;  // Default

            if ((state_reg == ST_FETCH_READ_EXP || state_reg == ST_FETCH_READ_MAN) && 
                axi_ddr_if.rvalid && axi_ddr_if.rready) begin
                // Write DDR data to BRAM
                // Use phase-relative addressing: exp phase uses exp_lines_fetched_reg, man phase uses man_lines_fetched_reg + 16
                if (state_reg == ST_FETCH_READ_EXP) begin
                    bram_wr_addr_reg <= {7'd0, exp_lines_fetched_reg[3:0]};  // 0-15 for exp_packed
                end else begin
                    bram_wr_addr_reg <= {2'd0, man_lines_fetched_reg[8:0]} + 11'd16;  // 16-527 for mantissas
                end
                bram_wr_data_reg <= axi_ddr_if.rdata;
                bram_wr_en_reg <= 1'b1;
                bram_wr_target_reg <= fetch_target_reg;  // Set target from captured fetch command

                // Debug: Track BRAM writes during FETCH
                if (beat_count_reg[3:0] == 0 || beat_count_reg[3:0] == 15) begin
                    $display("[DC_DEBUG] @%0t BRAM_WRITE: addr=%0d, data[63:0]=0x%h, phase=%s",
                             $time, bram_wr_addr_reg, axi_ddr_if.rdata[63:0],
                             (state_reg == ST_FETCH_READ_EXP) ? "EXP" : "MAN");
                end
            end
        end
    end

    // ===================================================================
    // BRAM Module Instantiation (Dual Read Ports)
    // ===================================================================
    dispatcher_bram #(
        .MAN_WIDTH           (MAN_WIDTH),
        .EXP_WIDTH           (EXP_WIDTH),
        .EXP_PACKED_DEPTH    (16),
        .BRAM_DEPTH          (512),
        .WR_ADDR_WIDTH       (11),
        .RD_ADDR_WIDTH       (TILE_ADDR_WIDTH)
        // EXP_PACKED_ADDR_WIDTH auto-calculated to 4
    ) u_dispatcher_bram (
        // Clock and reset
        .i_clk              (i_clk),
        .i_reset_n          (i_reset_n),

        // Write ports (from DDR fetch)
        .i_wr_data          (bram_wr_data_reg),
        .i_wr_addr          (bram_wr_addr_reg),
        .i_wr_en            (bram_wr_en_reg),
        .i_wr_target        (bram_wr_target_reg),  // 0=left, 1=right

        // Exponent aligned write ports (from unpacking logic)
        .i_exp_left_wr_addr  (o_disp_exp_left_wr_addr),
        .i_exp_left_wr_en    (o_disp_exp_left_wr_en),
        .i_exp_left_wr_data  (o_disp_exp_left_wr_data),

        .i_exp_right_wr_addr (o_disp_exp_right_wr_addr),
        .i_exp_right_wr_en   (o_disp_exp_right_wr_en),
        .i_exp_right_wr_data (o_disp_exp_right_wr_data),

        // Read ports (muxed: internal during DISPATCH, external during MATMUL)
        .i_man_left_rd_addr  (muxed_man_left_rd_addr),
        .i_man_left_rd_en    (muxed_man_left_rd_en),
        .o_man_left_rd_data  (o_disp_man_left_rd_data),

        .i_man_right_rd_addr (muxed_man_right_rd_addr),
        .i_man_right_rd_en   (muxed_man_right_rd_en),
        .o_man_right_rd_data (o_disp_man_right_rd_data),

        // Read ports (muxed: internal during DISPATCH, external during MATMUL)
        .i_exp_left_rd_addr  (muxed_exp_left_rd_addr),
        .i_exp_left_rd_en    (muxed_exp_left_rd_en),
        .o_exp_left_rd_data  (o_disp_exp_left_rd_data),

        .i_exp_right_rd_addr (muxed_exp_right_rd_addr),
        .i_exp_right_rd_en   (muxed_exp_right_rd_en),
        .o_exp_right_rd_data (o_disp_exp_right_rd_data),
        
        // Exp packed read interface (for unpacking logic)
        .i_exp_packed_rd_addr    (unpack_exp_packed_rd_addr_reg),
        .i_exp_packed_rd_target  (fetch_target_reg),
        .o_exp_packed_rd_data    (exp_packed_rd_data_wire)
);

    // ===================================================================
    // AXI Read Transaction Control
    // ===================================================================
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            axi_ar_req_reg <= 1'b0;
            axi_r_ready_reg <= 1'b0;
            beat_count_reg <= '0;
        end else begin
            // Read Address Channel
            if (state_reg == ST_FETCH_INIT) begin
                axi_ar_req_reg <= 1'b1;
                $display("[DC_DEBUG] @%0t Setting axi_ar_req_reg=1 in ST_FETCH_INIT", $time);
            end else if (state_reg == ST_FETCH_READ && axi_ddr_if.arvalid && axi_ddr_if.arready) begin
                axi_ar_req_reg <= 1'b0;
                $display("[DC_DEBUG] @%0t Clearing axi_ar_req_reg=0 after AR handshake", $time);
            end else if ((state_reg == ST_FETCH_READ_EXP || state_reg == ST_FETCH_READ_MAN) && 
                        axi_ddr_if.rvalid && axi_ddr_if.rready && axi_ddr_if.rlast) begin
                // Burst complete - issue next AR if more data needed
                if (state_reg == ST_FETCH_READ_EXP && exp_lines_fetched_reg >= 15) begin
                    // Exponent phase complete, need to start mantissa phase
                    axi_ar_req_reg <= 1'b1;
                    $display("[DC_DEBUG] @%0t EXP phase done, requesting first MAN burst", $time);
                end else if (state_reg == ST_FETCH_READ_EXP) begin
                    // More exponent bursts needed
                    axi_ar_req_reg <= 1'b1;
                end else if (state_reg == ST_FETCH_READ_MAN && man_lines_fetched_reg < 511) begin
                    // More mantissa bursts needed
                    axi_ar_req_reg <= 1'b1;
                end
            end

            // Read Data Channel
            axi_r_ready_reg <= (state_reg == ST_FETCH_READ_EXP || state_reg == ST_FETCH_READ_MAN);

            // Beat counter
            if (state_reg == ST_FETCH_READ) begin
                beat_count_reg <= '0;
            end else if ((state_reg == ST_FETCH_READ_EXP || state_reg == ST_FETCH_READ_MAN) && 
                        axi_ddr_if.rvalid && axi_ddr_if.rready) begin
                beat_count_reg <= beat_count_reg + 1;
            end
        end
    end

    // ===================================================================
    // AXI Interface Assignments
    // ===================================================================

    // AXI Read Address Channel
    assign axi_ddr_if.arvalid  = axi_ar_req_reg;
    assign axi_ddr_if.arid     = 8'hDC;  // Dispatcher Control ID
    // CRITICAL FIX: Include GDDR6_PAGE_ID in address for correct NoC routing
    // Address format: {Page_ID[9], Pad[2], Line[26], Byte[5]} = 42 bits total
    assign axi_ddr_if.araddr   = {GDDR6_PAGE_ID, 2'b00, (fetch_addr_reg + current_line_reg), {ADDR_BYTE_SHIFT{1'b0}}};
    assign axi_ddr_if.arlen    = FIXED_BURST_LEN;  // 16 beats
    assign axi_ddr_if.arsize   = 3'h5;             // 32 bytes per beat
    assign axi_ddr_if.arburst  = 2'b01;            // INCR burst
    assign axi_ddr_if.arlock   = 1'b0;
    assign axi_ddr_if.arcache  = 4'h0;             // Non-cacheable
    assign axi_ddr_if.arprot   = 3'b010;           // Unprivileged, non-secure, data
    assign axi_ddr_if.arqos    = 4'h0;
    assign axi_ddr_if.arregion = 4'h0;

    // AXI Read Data Channel
    assign axi_ddr_if.rready   = axi_r_ready_reg;

    // AXI Write Channels (unused - tie off)
    assign axi_ddr_if.awvalid  = 1'b0;
    assign axi_ddr_if.awid     = '0;
    assign axi_ddr_if.awaddr   = '0;
    assign axi_ddr_if.awlen    = '0;
    assign axi_ddr_if.awsize   = '0;
    assign axi_ddr_if.awburst  = '0;
    assign axi_ddr_if.awlock   = '0;
    assign axi_ddr_if.awcache  = '0;
    assign axi_ddr_if.awprot   = '0;
    assign axi_ddr_if.awqos    = '0;
    assign axi_ddr_if.awregion = '0;
    assign axi_ddr_if.wvalid   = 1'b0;
    assign axi_ddr_if.wdata    = '0;
    assign axi_ddr_if.wstrb    = '0;
    assign axi_ddr_if.wlast    = 1'b0;
    assign axi_ddr_if.bready   = 1'b0;

    // ===================================================================
    // Debug Outputs
    // ===================================================================
    assign o_dc_state = state_reg;
    assign o_disp_wr_count = current_line_reg;
    assign o_disp_wr_addr = bram_wr_addr_reg;   // Debug output (for gemm)
    assign o_disp_wr_en = bram_wr_en_reg;       // Debug output (for gemm)

    // ===================================================================
    // Assertions (for simulation only)
    // ===================================================================

    `ifdef SIM
        // Check BRAM write overflow
        property no_disp_overflow;
            @(posedge i_clk) disable iff (~i_reset_n)
            (bram_wr_en_reg) |-> (bram_wr_addr_reg < BRAM_DEPTH);
        endproperty
        assert property (no_disp_overflow) else
            $error("[DISPATCHER_CONTROL] BRAM write address overflow: %0d >= %0d",
                   bram_wr_addr_reg, BRAM_DEPTH);

        // Check BRAM read overflow
        property no_disp_read_overflow;
            @(posedge i_clk) disable iff (~i_reset_n)
            (i_disp_rd_en) |-> (i_disp_rd_addr < BRAM_DEPTH);
        endproperty
        assert property (no_disp_read_overflow) else
            $error("[DISPATCHER_CONTROL] BRAM read address overflow: %0d >= %0d",
                   i_disp_rd_addr, BRAM_DEPTH);

        // Check AXI burst alignment
        property axi_burst_aligned;
            @(posedge i_clk) disable iff (~i_reset_n)
            (axi_ddr_if.arvalid) |-> (axi_ddr_if.araddr[4:0] == 5'h0);
        endproperty
        assert property (axi_burst_aligned) else
            $error("[DISPATCHER_CONTROL] AXI address not 32-byte aligned: 0x%08x",
                   axi_ddr_if.araddr);
    `endif

    // ===================================================================
    // Debug Display (for simulation)
    // ===================================================================

    `ifdef SIM_VERBOSE
        always @(posedge i_clk) begin
            if (state_reg == ST_FETCH_INIT) begin
                $display("[DISPATCHER_CONTROL] FETCH: addr=0x%08x, len=%0d lines",
                         i_fetch_addr, i_fetch_len);
            end

            // Debug AXI handshaking
            if (state_reg == ST_FETCH_READ) begin
                $display("[DC_DEBUG] @%0t ST_FETCH_READ: arvalid=%b, arready=%b, araddr=0x%08x",
                         $time, axi_ddr_if.arvalid, axi_ddr_if.arready, axi_ddr_if.araddr);
            end

            if (bram_wr_en_reg) begin
                $display("[DISPATCHER_CONTROL] BRAM Write: addr=%0d, data=0x%064x",
                         bram_wr_addr_reg, bram_wr_data_reg);
            end

            if (state_reg == ST_FETCH_DONE) begin
                $display("[DISPATCHER_CONTROL] FETCH Complete: %0d lines written", current_line_reg);
            end

            if (state_reg == ST_DISP_DONE) begin
                $display("[DISPATCHER_CONTROL] DISPATCH Complete");
            end
        end
    `endif

endmodule : dispatcher_control
