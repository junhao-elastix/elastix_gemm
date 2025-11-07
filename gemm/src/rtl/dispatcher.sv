// ------------------------------------------------------------------
// Dispatcher Module - Dispatcher BRAM to Tile BRAM Transfer
//
// Purpose: Handles DISPATCH operations (dispatcher_bram → tile_bram)
// Features:
//  - DISPATCH state machine: IDLE → DISP_BUSY → DISP_DONE
//  - Multi-tile dispatch with broadcast/distribute modes
//  - Reads from dispatcher_bram, writes to tile_bram
//  - Parallel data paths (mantissa + exponent)
//
// Author: Junhao Pan
// Date: 10/31/2025
// ------------------------------------------------------------------

`include "nap_interfaces.svh"

module dispatcher
import gemm_pkg::*;
#(
    parameter MAN_WIDTH = 256,         // Mantissa data width
    parameter EXP_WIDTH = 8,           // Exponent data width
    parameter BRAM_DEPTH = 512,        // Dispatcher BRAM depth
    parameter TILE_DEPTH = 512,        // Tile BRAM depth per side
    parameter BRAM_ADDR_WIDTH = $clog2(BRAM_DEPTH),
    parameter TILE_ADDR_WIDTH = $clog2(TILE_DEPTH)
)
(
    // Clock and Reset
    input  logic                         i_clk,
    input  logic                         i_reset_n,

    // ====================================================================
    // Master Control Interface (DISPATCH command)
    // ====================================================================
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
    // Dispatcher BRAM Read Interface
    // ====================================================================
    // Read addresses and enables (outputs to dispatcher_bram)
    output logic [BRAM_ADDR_WIDTH-1:0]   o_disp_man_left_rd_addr,
    output logic                         o_disp_man_left_rd_en,
    input  logic [MAN_WIDTH-1:0]         i_disp_man_left_rd_data,

    output logic [BRAM_ADDR_WIDTH-1:0]   o_disp_man_right_rd_addr,
    output logic                         o_disp_man_right_rd_en,
    input  logic [MAN_WIDTH-1:0]         i_disp_man_right_rd_data,

    output logic [TILE_ADDR_WIDTH-1:0]   o_disp_exp_left_rd_addr,
    output logic                         o_disp_exp_left_rd_en,
    input  logic [EXP_WIDTH-1:0]         i_disp_exp_left_rd_data,

    output logic [TILE_ADDR_WIDTH-1:0]   o_disp_exp_right_rd_addr,
    output logic                         o_disp_exp_right_rd_en,
    input  logic [EXP_WIDTH-1:0]         i_disp_exp_right_rd_data,

    // ====================================================================
    // Tile BRAM Write Interface
    // ====================================================================
    // FOUR PARALLEL OUTPUTS - All driven by same counter
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
    // Debug Interface
    // ====================================================================
    output logic [3:0]                   o_dispatcher_state
);

    // ===================================================================
    // State Machine Definition
    // ===================================================================
    typedef enum logic [3:0] {
        ST_IDLE       = 4'd0,
        ST_DISP_BUSY  = 4'd6,  // Copy from dispatcher_bram to tile_bram (working state)
        ST_DISP_DONE  = 4'd7   // DISPATCH operation complete
    } state_t;

    state_t state_reg, state_next;

    // ===================================================================
    // Internal Signals
    // ===================================================================

    // Edge detection for command enable (prevent double-triggering)
    logic disp_en_prev;

    // DISPATCH operation control
    logic [7:0] disp_man_nv_cnt_reg;     // Stored man_nv_cnt parameter
    logic [9:0] disp_lines_to_copy_reg;  // man_nv_cnt × 4 (total lines to copy)
    logic       disp_man_done_reg;       // Mantissa dispatch complete flag
    logic       disp_exp_done_reg;       // Exponent dispatch complete flag

    // DISPATCH command parameters (captured at trigger)
    logic         disp_right_reg;            // Dispatch side (0=left, 1=right)
    logic         disp_broadcast_reg;        // Distribution mode (0=distribute, 1=broadcast)
    logic [23:0]  disp_col_en_reg;           // Column enable mask
    logic [4:0]   disp_col_start_reg;        // Distribution start column
    logic [7:0]   disp_ugd_vec_size_reg;     // UGD vector size (NVs per batch)

    // Multi-tile dispatch control
    logic [4:0]   disp_current_tile_idx_reg;
    logic [7:0]   disp_num_enabled_tiles_reg;    // Count of enabled tiles (popcount of col_en)
    logic [8:0]   disp_tile_start_reg;           // Source pointer in dispatcher_bram
    logic [15:0]  disp_receive_tile_start_reg;   // Destination pointer in tile_bram
    logic [9:0]   disp_ugd_batch_lines_reg;
    logic [7:0]   disp_batch_cnt_reg;            // Current batch being dispatched
    logic [7:0]   disp_total_batches_reg;        // Total batches to dispatch (man_nv_cnt / ugd_vec_size)
    logic [9:0]   disp_within_batch_cnt_reg;

    // Address calculation signals
    logic [10:0]  dispatcher_read_addr;          // Final read address in dispatcher_bram
    logic [10:0]  tile_write_addr;               // Final write address in tile_bram

    // DISPATCH pipeline signals
    logic [9:0] man_rd_addr_pipe;
    logic [9:0] man_wr_addr_pipe;
    logic [9:0] exp_rd_addr_pipe;
    logic [9:0] exp_wr_addr_pipe;
    logic signed [10:0] disp_write_cnt;  // Signed to allow -1 initial value
    logic       man_wr_valid_pipe;   // Valid signal for mantissa write
    logic       exp_wr_valid_pipe;   // Valid signal for exponent write
    logic       man_wr_valid_delayed;
    logic       exp_wr_valid_delayed;
    logic       batch_complete_pending;    // Flag to delay setting done by 1 cycle
    logic       set_batch_complete;        // Combinational flag indicating batch just completed

    // Multi-tile write enable - COMBINATIONAL (no pipeline delay)
    logic [23:0] tile_wr_en_comb;

    // Pipeline disp_right_reg for synchronization with write valid signals
    logic disp_right_pipe;

    // Status flags
    logic disp_done_reg;


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

    // ===================================================================
    // State Transition Logic
    // ===================================================================
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            state_reg <= ST_IDLE;
            disp_en_prev <= 1'b0;
        end else begin
            state_reg <= state_next;
            disp_en_prev <= i_disp_en;
        end
    end

    // Next state combinational logic
    always_comb begin
        state_next = state_reg;

        case (state_reg)
            ST_IDLE: begin
                // Only trigger on RISING edge of enable to prevent double-triggering
                if (i_disp_en && !disp_en_prev) begin
                    state_next = ST_DISP_BUSY;
                end
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
    // DISPATCH Command Processing
    // ===================================================================
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            disp_done_reg <= 1'b0;

            // Initialize multi-tile dispatch variables
            disp_man_done_reg <= 1'b0;
            disp_exp_done_reg <= 1'b0;
            disp_ugd_batch_lines_reg <= 10'd512;
            disp_num_enabled_tiles_reg <= 8'd1;
            disp_current_tile_idx_reg <= '0;
            disp_tile_start_reg <= '0;
            disp_receive_tile_start_reg <= '0;
            disp_batch_cnt_reg <= '0;
            disp_total_batches_reg <= '0;
            disp_within_batch_cnt_reg <= '0;
            batch_complete_pending <= 1'b0;
        end else begin

            case (state_reg)
                ST_IDLE: begin
                    // Only capture parameters on RISING edge
                    if (i_disp_en && !disp_en_prev) begin
                        // Initialize DISPATCH operation and capture parameters
                        disp_man_nv_cnt_reg <= i_disp_man_nv_cnt;
                        disp_lines_to_copy_reg <= {2'b00, i_disp_man_nv_cnt} << 2;  // man_nv_cnt × 4
                        disp_man_done_reg <= 1'b0;
                        disp_exp_done_reg <= 1'b0;
                        disp_done_reg <= 1'b0;

                        // Capture multi-tile dispatch parameters (per SINGLE_ROW_REFERENCE.md)
                        disp_right_reg <= i_disp_right;
                        disp_broadcast_reg <= i_disp_broadcast;
                        disp_col_en_reg <= i_disp_col_en;
                        disp_col_start_reg <= i_disp_col_start;
                        disp_ugd_vec_size_reg <= i_disp_ugd_vec_size;

                        // Calculate multi-tile dispatch parameters
                        disp_num_enabled_tiles_reg <= popcount_24bit(i_disp_col_en);
                        disp_ugd_batch_lines_reg <= {1'b0, i_disp_ugd_vec_size} << 2;  // ugd_vec_size × 4
                        disp_total_batches_reg <= i_disp_man_nv_cnt / i_disp_ugd_vec_size;
                        disp_current_tile_idx_reg <= 5'd0;

                        // Initialize pointers
                        disp_tile_start_reg <= '0;
                        disp_receive_tile_start_reg <= i_disp_tile_addr;
                        disp_batch_cnt_reg <= '0;
                        disp_within_batch_cnt_reg <= '0;
                        disp_write_cnt <= -11'sd1;

                        $display("[DISPATCHER] @%0t DISP triggered: man_nv_cnt=%0d, ugd_vec_size=%0d, total_batches=%0d, batch_lines=%0d, disp_right=%0b, broadcast=%0b, col_en=0x%06x, num_tiles=%0d",
                                 $time, i_disp_man_nv_cnt, i_disp_ugd_vec_size, i_disp_man_nv_cnt / i_disp_ugd_vec_size,
                                 {2'b00, i_disp_ugd_vec_size} << 2,
                                 i_disp_right, i_disp_broadcast, i_disp_col_en, popcount_24bit(i_disp_col_en));
                        // $display("[DISPATCHER] @%0t PERF: DISPATCH_START cycle=%0d", $time, $time / 10);
                    end
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
                                $display("[DISPATCHER] @%0t BROADCAST: Batch %0d to tile %0d complete",
                                        $time, disp_batch_cnt_reg, disp_current_tile_idx_reg);

                                if (disp_current_tile_idx_reg == (disp_num_enabled_tiles_reg - 1)) begin
                                    // Last tile received this batch, advance to next batch
                                    disp_tile_start_reg <= disp_tile_start_reg + disp_ugd_batch_lines_reg;
                                    disp_receive_tile_start_reg <= disp_receive_tile_start_reg + disp_ugd_batch_lines_reg;
                                    disp_batch_cnt_reg <= disp_batch_cnt_reg + 1;
                                    disp_current_tile_idx_reg <= 5'd0;  // Wrap to tile 0

                                    $display("[DISPATCHER] @%0t BROADCAST: All tiles done, advancing to batch %0d",
                                            $time, disp_batch_cnt_reg + 1);

                                    // Check if all batches dispatched
                                    if (disp_batch_cnt_reg == (disp_total_batches_reg - 1)) begin
                                        set_batch_complete = 1'b1;  // Mark for delayed done
                                        $display("[DISPATCHER] @%0t BROADCAST: All %0d batches complete (pending final write)",
                                                $time, disp_total_batches_reg);
                                    end
                                end else begin
                                    // Move to next tile with SAME data (source pointer unchanged)
                                    disp_current_tile_idx_reg <= disp_current_tile_idx_reg + 1;
                                    $display("[DISPATCHER] @%0t BROADCAST: Moving to tile %0d (same data)",
                                            $time, disp_current_tile_idx_reg + 1);
                                end
                            end else begin
                                // === DISTRIBUTE MODE ===
                                // Each tile gets different data batches in round-robin fashion
                                $display("[DISPATCHER] @%0t DISTRIBUTE: Batch %0d to tile %0d complete",
                                        $time, disp_batch_cnt_reg, disp_current_tile_idx_reg);

                                // Each tile gets different data, advance source pointer
                                disp_tile_start_reg <= disp_tile_start_reg + disp_ugd_batch_lines_reg;
                                disp_batch_cnt_reg <= disp_batch_cnt_reg + 1;

                                // Destination address increment logic:
                                // - Multi-tile (num_tiles > 1): Only increment when wrapping to tile 0
                                // - Single-tile (num_tiles == 1): Always increment
                                if (disp_num_enabled_tiles_reg == 8'd1) begin
                                    // Single-tile: Always increment destination address
                                    disp_receive_tile_start_reg <= disp_receive_tile_start_reg + disp_ugd_batch_lines_reg;
                                end else if (((disp_current_tile_idx_reg + 1) % disp_num_enabled_tiles_reg) == 5'd0 && disp_batch_cnt_reg > 0) begin
                                    // Multi-tile: Only increment when wrapping to tile 0
                                    disp_receive_tile_start_reg <= disp_receive_tile_start_reg + disp_ugd_batch_lines_reg;
                                    $display("[DISPATCHER] @%0t DISTRIBUTE: Wrapping to tile 0, incrementing dest_addr %0d -> %0d",
                                            $time, disp_receive_tile_start_reg,
                                            disp_receive_tile_start_reg + disp_ugd_batch_lines_reg);
                                end

                                // Move to next tile (simple modulo wrap-around)
                                disp_current_tile_idx_reg <= (disp_current_tile_idx_reg + 1) % disp_num_enabled_tiles_reg;
                                $display("[DISPATCHER] @%0t DISTRIBUTE: Tile index changing %0d -> %0d (num_tiles=%0d)",
                                        $time, disp_current_tile_idx_reg, (disp_current_tile_idx_reg + 1) % disp_num_enabled_tiles_reg,
                                        disp_num_enabled_tiles_reg);

                                // Check if all batches dispatched
                                if (disp_batch_cnt_reg == (disp_total_batches_reg - 1)) begin
                                    set_batch_complete = 1'b1;  // Mark for delayed done
                                    $display("[DISPATCHER] @%0t DISTRIBUTE: All %0d batches complete (pending final write)",
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
                        
                        $display("[DISPATCHER] @%0t Final delayed write complete, setting done", $time);
                    end else if (set_batch_complete) begin
                        batch_complete_pending <= 1'b1;
                    end
                end

                ST_DISP_DONE: begin
                    // Signal DISPATCH operation complete
                    disp_done_reg <= 1'b1;
                    $display("[DISPATCHER] @%0t DISP_DONE: All copies complete, signaling done", $time);
                end
            endcase
        end
    end

    assign o_disp_done = disp_done_reg;

    // ===================================================================
    // DISPATCH Copy - Address Generation and Pipeline
    // ===================================================================
    // During ST_DISP_BUSY, read from dispatcher_bram and write to tile_bram
    // The BRAM read has 1-cycle latency, so we pipeline: read cycle N, write cycle N+1

    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            man_rd_addr_pipe <= '0;
            man_wr_addr_pipe <= '0;
            exp_rd_addr_pipe <= '0;
            exp_wr_addr_pipe <= '0;
            man_wr_valid_pipe <= 1'b0;
            exp_wr_valid_pipe <= 1'b0;
            man_wr_valid_delayed <= 1'b0;
            exp_wr_valid_delayed <= 1'b0;
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
            // Use signed arithmetic since disp_write_cnt starts at -1
            tile_write_addr = disp_receive_tile_start_reg[10:0] + $signed(disp_write_cnt);

            // Assign to pipeline registers
            man_rd_addr_pipe <= dispatcher_read_addr[9:0];
            man_wr_addr_pipe <= tile_write_addr[9:0];
            exp_rd_addr_pipe <= dispatcher_read_addr[9:0];
            exp_wr_addr_pipe <= tile_write_addr[9:0];

            // Valid signals: HIGH when actively copying (not done)
            man_wr_valid_pipe <= (state_reg == ST_DISP_BUSY) && !disp_man_done_reg;
            exp_wr_valid_pipe <= (state_reg == ST_DISP_BUSY) && !disp_exp_done_reg;

            // Delay write valid by 1 cycle to account for BRAM read latency
            man_wr_valid_delayed <= man_wr_valid_pipe;
            exp_wr_valid_delayed <= exp_wr_valid_pipe;
        end
    end

    // Dispatcher BRAM read addresses and enables
    // Selective read addressing based on disp_right_reg
    // - disp_right_reg=0: Read from left dispatcher_bram only
    // - disp_right_reg=1: Read from right dispatcher_bram only
    always_comb begin
        if (state_reg == ST_DISP_BUSY && !disp_man_done_reg) begin
            if (disp_right_reg) begin
                // RIGHT DISPATCH: Read from right side only
                o_disp_man_left_rd_addr  = '0;
                o_disp_man_right_rd_addr = man_rd_addr_pipe[BRAM_ADDR_WIDTH-1:0];
                o_disp_man_left_rd_en    = 1'b0;
                o_disp_man_right_rd_en   = 1'b1;
            end else begin
                // LEFT DISPATCH: Read from left side only
                o_disp_man_left_rd_addr  = man_rd_addr_pipe[BRAM_ADDR_WIDTH-1:0];
                o_disp_man_right_rd_addr = '0;
                o_disp_man_left_rd_en    = 1'b1;
                o_disp_man_right_rd_en   = 1'b0;
            end

            // Exponent reads (same logic)
            if (disp_right_reg) begin
                o_disp_exp_left_rd_addr  = '0;
                o_disp_exp_right_rd_addr = exp_rd_addr_pipe[TILE_ADDR_WIDTH-1:0];
                o_disp_exp_left_rd_en    = 1'b0;
                o_disp_exp_right_rd_en   = 1'b1;
            end else begin
                o_disp_exp_left_rd_addr  = exp_rd_addr_pipe[TILE_ADDR_WIDTH-1:0];
                o_disp_exp_right_rd_addr = '0;
                o_disp_exp_left_rd_en    = 1'b1;
                o_disp_exp_right_rd_en   = 1'b0;
            end
        end else begin
            o_disp_man_left_rd_addr  = '0;
            o_disp_man_right_rd_addr = '0;
            o_disp_man_left_rd_en    = 1'b0;
            o_disp_man_right_rd_en   = 1'b0;
            o_disp_exp_left_rd_addr  = '0;
            o_disp_exp_right_rd_addr = '0;
            o_disp_exp_left_rd_en    = 1'b0;
            o_disp_exp_right_rd_en   = 1'b0;
        end
    end

    // Multi-tile write enable - COMBINATIONAL (no pipeline delay)
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

    // Tile BRAM selective write
    // SELECTIVE 2-PATH WRITE: Only write to selected side (left OR right)
    // disp_right_reg=0: Write to left side only
    // disp_right_reg=1: Write to right side only

    // Pipeline disp_right_reg for synchronization with write valid signals
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            disp_right_pipe <= 1'b0;
        end else begin
            disp_right_pipe <= disp_right_reg;
        end
    end

    // Tile BRAM write outputs
    // Left mantissa write (ONLY when disp_right_reg=0)
    assign o_tile_man_left_wr_addr = man_wr_addr_pipe[TILE_ADDR_WIDTH-1:0];
    assign o_tile_man_left_wr_data = i_disp_man_left_rd_data;        // From left BRAM read port
    assign o_tile_man_left_wr_en   = man_wr_valid_delayed && !disp_right_pipe;  // DELAYED write

    // Right mantissa write (ONLY when disp_right_reg=1)
    assign o_tile_man_right_wr_addr = man_wr_addr_pipe[TILE_ADDR_WIDTH-1:0];
    assign o_tile_man_right_wr_data = i_disp_man_right_rd_data;      // From right BRAM read port
    assign o_tile_man_right_wr_en   = man_wr_valid_delayed && disp_right_pipe;   // DELAYED write

    // Tile BRAM exponent writes
    assign o_tile_exp_left_wr_addr  = exp_wr_addr_pipe[TILE_ADDR_WIDTH-1:0];
    assign o_tile_exp_left_wr_data  = i_disp_exp_left_rd_data;       // From left_exp_bram
    assign o_tile_exp_left_wr_en    = exp_wr_valid_delayed && !disp_right_pipe;  // DELAYED write

    assign o_tile_exp_right_wr_addr = exp_wr_addr_pipe[TILE_ADDR_WIDTH-1:0];
    assign o_tile_exp_right_wr_data = i_disp_exp_right_rd_data;      // From right_exp_bram
    assign o_tile_exp_right_wr_en   = exp_wr_valid_delayed && disp_right_pipe;   // DELAYED write

    // Multi-tile write enable output
    assign o_tile_wr_en = tile_wr_en_comb;
    assign o_dispatcher_state = state_reg;

endmodule : dispatcher
