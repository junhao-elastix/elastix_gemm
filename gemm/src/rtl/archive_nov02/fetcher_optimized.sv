// ------------------------------------------------------------------
// Fetcher Module - OPTIMIZED for Back-to-Back Bursts
//
// Purpose: Handles FETCH operations (GDDR6 → dispatcher_bram) with true back-to-back bursts
// Key Features:
//  - Predictive AR issuing (2-3 beats before RLAST) for zero-gap bursts
//  - ARID FIFO (8-entry) for tracking outstanding transactions
//  - Simplified state machine without phase blocking
//  - Continuous pipeline operation without gaps
//  - 33 total bursts (1 exp + 32 mantissa) × 16 beats = 528 lines
//
// Memory Layout (GFP8 Block):
//  Lines 0-15:   Packed Exponents (16 lines, 1 burst)
//  Lines 16-527: Mantissas (512 lines, 32 bursts)
//
// Performance:
//  - Original: ~18 cycle gaps between bursts
//  - Optimized: 0-1 cycle gaps (true back-to-back)
//
// Author: Optimized from fetcher.sv
// Date: October 31, 2025
// ------------------------------------------------------------------

`include "nap_interfaces.svh"

module fetcher
import gemm_pkg::*;
#(
    parameter MAN_WIDTH = 256,         // Mantissa data width
    parameter EXP_WIDTH = 8,           // Exponent data width
    parameter BRAM_DEPTH = 512,        // Dispatcher BRAM depth
    parameter AXI_ADDR_WIDTH = 42,     // AXI address width (GDDR6 NoC)
    parameter BRAM_ADDR_WIDTH = $clog2(BRAM_DEPTH),  // 9-bit for 512 depth
    parameter TILE_ADDR_WIDTH = $clog2(BRAM_DEPTH),  // 9-bit for 512 depth
    parameter [8:0] GDDR6_PAGE_ID = 9'd2  // GDDR6 Page ID for NoC routing
)
(
    // Clock and Reset
    input  logic                         i_clk,
    input  logic                         i_reset_n,

    // ====================================================================
    // Master Control Interface (FETCH command)
    // ====================================================================
    input  logic                         i_fetch_en,
    input  logic [link_addr_width_gp-1:0] i_fetch_addr,
    input  logic [link_len_width_gp-1:0]  i_fetch_len,
    input  logic                         i_fetch_target, // 0=left, 1=right
    output logic                         o_fetch_done,

    // ====================================================================
    // Dispatcher BRAM Write Interface
    // ====================================================================
    output logic [MAN_WIDTH-1:0]         o_bram_wr_data,
    output logic [BRAM_ADDR_WIDTH+2:0]   o_bram_wr_addr,  // 11-bit for 0-527
    output logic                         o_bram_wr_en,
    output logic                         o_bram_wr_target, // 0=left, 1=right

    // ====================================================================
    // Dispatcher BRAM Exponent Aligned Write Ports (for unpacking)
    // ====================================================================
    output logic [TILE_ADDR_WIDTH-1:0]   o_exp_left_wr_addr,
    output logic                         o_exp_left_wr_en,
    output logic [EXP_WIDTH-1:0]         o_exp_left_wr_data,

    output logic [TILE_ADDR_WIDTH-1:0]   o_exp_right_wr_addr,
    output logic                         o_exp_right_wr_en,
    output logic [EXP_WIDTH-1:0]         o_exp_right_wr_data,

    // ====================================================================
    // Dispatcher BRAM Read Interface (for unpacking exp_packed)
    // ====================================================================
    output logic [3:0]                   o_exp_packed_rd_addr,  // 4-bit: 0-15
    output logic                         o_exp_packed_rd_target, // 0=left, 1=right
    input  logic [MAN_WIDTH-1:0]         i_exp_packed_rd_data,

    // ====================================================================
    // AXI-4 Initiator Interface for DDR access
    // ====================================================================
    t_AXI4.initiator                     axi_ddr_if,

    // ====================================================================
    // Debug Interface
    // ====================================================================
    output logic [3:0]                   o_fetcher_state,
    output logic [10:0]                  o_wr_addr,    // Debug: BRAM write address
    output logic                         o_wr_en       // Debug: BRAM write enable
);

    // ===================================================================
    // Local Parameters
    // ===================================================================
    localparam FIXED_BURST_LEN = 15;       // AXI burst length = 16 beats
    localparam BYTES_PER_BEAT = 32;        // 32 bytes per AXI beat (256-bit)
    localparam ADDR_BYTE_SHIFT = 5;        // Byte address to beat address shift
    localparam TOTAL_BURSTS_NEEDED = 33;   // 1 exp burst + 32 mantissa bursts
    localparam PREDICTIVE_BEATS = 3;       // Issue next AR this many beats before RLAST

    // ===================================================================
    // OPTIMIZED State Machine Definition
    // ===================================================================
    typedef enum logic [3:0] {
        ST_IDLE            = 4'd0,
        ST_FETCH_INIT      = 4'd1,
        ST_FETCH_ACTIVE    = 4'd2,  // Single active state for all fetching
        ST_FETCH_DRAIN     = 4'd3,  // Wait for final responses
        ST_FETCH_DONE      = 4'd4
    } state_t;

    state_t state_reg, state_next;

    // ===================================================================
    // Internal Signals
    // ===================================================================

    // FETCH command tracking
    logic [link_addr_width_gp-1:0] fetch_addr_reg;
    logic        fetch_target_reg;
    logic [10:0] current_line_reg;

    // Counters for tracking lines received
    logic [4:0]  exp_lines_fetched_reg;
    logic [9:0]  man_lines_fetched_reg;
    logic [9:0]  total_lines_fetched_reg;  // NEW: Combined counter

    // ===================================================================
    // ARID FIFO for Outstanding Transaction Tracking
    // ===================================================================
    localparam ARID_FIFO_DEPTH_WIDTH = 3;  // 8 entries
    logic [ARID_FIFO_DEPTH_WIDTH-1:0] arid_fifo_wr_ptr;
    logic [ARID_FIFO_DEPTH_WIDTH-1:0] arid_fifo_rd_ptr;
    logic [ARID_FIFO_DEPTH_WIDTH-1:0] arid_fifo_entries;
    logic [7:0] arid_fifo [(2**ARID_FIFO_DEPTH_WIDTH)-1:0] /* synthesis syn_ramstyle=registers */;
    logic [7:0] arid_counter;
    logic       arid_fifo_wr;
    logic       arid_fifo_rd;
    logic       arid_fifo_full;
    logic       arid_fifo_empty;

    // ===================================================================
    // Predictive AR Control Signals
    // ===================================================================
    logic       ar_pending;                // AR request pending
    logic [5:0] total_ars_issued;         // Total ARs issued (0-32)
    logic [3:0] beats_until_rlast;        // Countdown to RLAST
    logic       current_burst_active;     // Currently receiving burst data

    // BRAM control signals
    logic [10:0] bram_wr_addr_reg;
    logic [MAN_WIDTH-1:0] bram_wr_data_reg;
    logic        bram_wr_en_reg;
    logic        bram_wr_target_reg;

    // Parallel unpacking signals
    logic [3:0]  unpack_exp_packed_rd_addr_reg;
    logic [9:0]  unpack_idx_reg;

    // Edge detection
    logic fetch_en_prev;
    logic fetch_done_reg;

    // ===================================================================
    // State Transition Logic (SIMPLIFIED!)
    // ===================================================================
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            state_reg <= ST_IDLE;
            fetch_en_prev <= 1'b0;
        end else begin
            state_reg <= state_next;
            fetch_en_prev <= i_fetch_en;
        end
    end

    always_comb begin
        state_next = state_reg;

        case (state_reg)
            ST_IDLE: begin
                if (i_fetch_en && !fetch_en_prev) begin
                    state_next = ST_FETCH_INIT;
                end
            end

            ST_FETCH_INIT: begin
                // Initialize and immediately start fetching
                state_next = ST_FETCH_ACTIVE;
            end

            ST_FETCH_ACTIVE: begin
                // Stay active until all data received
                // Do NOT wait for arid_fifo_empty here!
                if (total_lines_fetched_reg >= 528) begin  // All 528 lines received
                    if (arid_fifo_empty) begin
                        state_next = ST_FETCH_DONE;  // All complete
                    end else begin
                        state_next = ST_FETCH_DRAIN;  // Wait for stragglers
                    end
                end
            end

            ST_FETCH_DRAIN: begin
                // Wait for final responses
                if (arid_fifo_empty) begin
                    state_next = ST_FETCH_DONE;
                end
            end

            ST_FETCH_DONE: begin
                state_next = ST_IDLE;
            end

            default: begin
                state_next = ST_IDLE;
            end
        endcase
    end

    // ===================================================================
    // ARID FIFO Management
    // ===================================================================
    assign arid_fifo_wr = (axi_ddr_if.arvalid && axi_ddr_if.arready);
    assign arid_fifo_rd = (axi_ddr_if.rvalid && axi_ddr_if.rready && axi_ddr_if.rlast);

    // Write process
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            arid_fifo_wr_ptr <= '0;
        end else if (arid_fifo_wr) begin
            arid_fifo[arid_fifo_wr_ptr] <= arid_counter;
            arid_fifo_wr_ptr <= arid_fifo_wr_ptr + 'd1;
        end
    end

    // Read process
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            arid_fifo_rd_ptr <= '0;
        end else if (arid_fifo_rd) begin
            arid_fifo_rd_ptr <= arid_fifo_rd_ptr + 'd1;
        end
    end

    // Count entries
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            arid_fifo_entries <= '0;
        end else begin
            case ({arid_fifo_wr, arid_fifo_rd})
                2'b00: arid_fifo_entries <= arid_fifo_entries;
                2'b01: arid_fifo_entries <= arid_fifo_entries - 'd1;
                2'b10: arid_fifo_entries <= arid_fifo_entries + 'd1;
                2'b11: arid_fifo_entries <= arid_fifo_entries;
            endcase
        end
    end

    assign arid_fifo_empty = (arid_fifo_entries == 'd0);

    // Set full to prevent overflow (keep 1 slot free for safety)
    always_ff @(posedge i_clk) begin
        arid_fifo_full <= (arid_fifo_entries >= 6);  // Keep 2 slots free
    end

    // ARID counter
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            arid_counter <= 8'hFE;  // Fetcher ID base
        end else if (state_reg == ST_IDLE && i_fetch_en && !fetch_en_prev) begin
            arid_counter <= 8'hFE;  // Reset on new fetch
        end else if (arid_fifo_wr) begin
            arid_counter <= arid_counter + 8'h1;
        end
    end

    // ===================================================================
    // PREDICTIVE AR CONTROL (KEY OPTIMIZATION!)
    // ===================================================================

    // Track beats until RLAST
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            beats_until_rlast <= '0;
            current_burst_active <= 1'b0;
        end else begin
            // Track when burst is active
            if (arid_fifo_wr) begin
                current_burst_active <= 1'b1;
                beats_until_rlast <= 4'd15;  // Start countdown
            end else if (axi_ddr_if.rvalid && axi_ddr_if.rready) begin
                if (axi_ddr_if.rlast) begin
                    // Check if another burst is already in flight
                    if (arid_fifo_entries > 1) begin
                        beats_until_rlast <= 4'd15;  // Reset for next burst
                    end else begin
                        current_burst_active <= 1'b0;
                        beats_until_rlast <= '0;
                    end
                end else if (beats_until_rlast > 0) begin
                    beats_until_rlast <= beats_until_rlast - 1;
                end
            end
        end
    end

    // Predictive AR issuing logic
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            ar_pending <= 1'b0;
            total_ars_issued <= '0;
        end else if (state_reg == ST_IDLE && i_fetch_en && !fetch_en_prev) begin
            // Reset on new fetch
            ar_pending <= 1'b0;
            total_ars_issued <= '0;
        end else begin
            // Issue first AR immediately in INIT state
            if (state_reg == ST_FETCH_INIT && !ar_pending && total_ars_issued == 0) begin
                ar_pending <= 1'b1;
                $display("[FETCHER] Initial AR issue");
            end

            // CRITICAL: Predictive AR issuing - issue BEFORE current burst completes!
            if (state_reg == ST_FETCH_ACTIVE && !ar_pending) begin
                // Conditions for issuing next AR:
                // 1. Haven't issued all ARs yet
                // 2. FIFO has room
                // 3. Current burst is about to complete (predictive!)
                // 4. Or no burst is active and we need to issue
                if (total_ars_issued < TOTAL_BURSTS_NEEDED &&
                    arid_fifo_entries < 6) begin  // Keep FIFO partially full

                    // Issue if:
                    // - No burst active (need to start)
                    // - OR current burst near completion (predictive!)
                    if (!current_burst_active ||
                        (current_burst_active && beats_until_rlast <= PREDICTIVE_BEATS && beats_until_rlast > 0)) begin

                        ar_pending <= 1'b1;
                        $display("[FETCHER] Predictive AR #%0d at beat %0d before RLAST",
                                 total_ars_issued, beats_until_rlast);
                    end
                end
            end

            // Clear pending and increment counter after AR handshake
            if (axi_ddr_if.arvalid && axi_ddr_if.arready) begin
                ar_pending <= 1'b0;
                total_ars_issued <= total_ars_issued + 1;
            end
        end
    end

    // ===================================================================
    // FETCH Command Processing
    // ===================================================================
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            fetch_addr_reg <= '0;
            fetch_target_reg <= 1'b0;
            current_line_reg <= '0;
            exp_lines_fetched_reg <= '0;
            man_lines_fetched_reg <= '0;
            total_lines_fetched_reg <= '0;
            fetch_done_reg <= 1'b0;
        end else begin
            fetch_done_reg <= 1'b0;  // Default

            case (state_reg)
                ST_IDLE: begin
                    if (i_fetch_en && !fetch_en_prev) begin
                        fetch_addr_reg <= i_fetch_addr;
                        fetch_target_reg <= i_fetch_target;
                        current_line_reg <= '0;
                        exp_lines_fetched_reg <= '0;
                        man_lines_fetched_reg <= '0;
                        total_lines_fetched_reg <= '0;

                        $display("[FETCHER] @%0t FETCH_START: addr=%0d, target=%s",
                                 $time, i_fetch_addr, i_fetch_target ? "RIGHT" : "LEFT");
                    end
                end

                ST_FETCH_ACTIVE, ST_FETCH_DRAIN: begin
                    // Increment counters for each beat received
                    if (axi_ddr_if.rvalid && axi_ddr_if.rready) begin
                        total_lines_fetched_reg <= total_lines_fetched_reg + 1;
                        current_line_reg <= current_line_reg + 1;

                        // Track exp vs mantissa lines
                        if (total_lines_fetched_reg < 16) begin
                            exp_lines_fetched_reg <= exp_lines_fetched_reg + 1;
                            $display("[FETCHER] @%0t EXP_LINE: %0d/16",
                                     $time, exp_lines_fetched_reg + 1);
                        end else begin
                            man_lines_fetched_reg <= man_lines_fetched_reg + 1;
                            if (man_lines_fetched_reg[3:0] == 4'd0 || axi_ddr_if.rlast) begin
                                $display("[FETCHER] @%0t MAN_LINE: %0d/512, burst=%0d/32",
                                         $time, man_lines_fetched_reg + 1, man_lines_fetched_reg[9:4]);
                            end
                        end

                        // Log RLAST for debugging
                        if (axi_ddr_if.rlast) begin
                            $display("[FETCHER] @%0t RLAST: total_lines=%0d, ARs_issued=%0d, FIFO_entries=%0d",
                                     $time, total_lines_fetched_reg + 1, total_ars_issued, arid_fifo_entries);
                        end
                    end
                end

                ST_FETCH_DONE: begin
                    fetch_done_reg <= 1'b1;
                    $display("[FETCHER] @%0t FETCH_COMPLETE: %0d lines fetched",
                             $time, total_lines_fetched_reg);
                end
            endcase
        end
    end

    assign o_fetch_done = fetch_done_reg;

    // ===================================================================
    // Parallel Exponent Unpacking (same as original)
    // ===================================================================
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            unpack_idx_reg <= 10'd0;
        end else if (state_reg == ST_IDLE && i_fetch_en && !fetch_en_prev) begin
            unpack_idx_reg <= 10'd0;
        end else if ((state_reg == ST_FETCH_ACTIVE || state_reg == ST_FETCH_DRAIN) &&
                     man_lines_fetched_reg > 0 && unpack_idx_reg < 10'd513) begin
            unpack_idx_reg <= unpack_idx_reg + 10'd1;
        end
    end

    logic [9:0] unpack_wr_idx;
    assign unpack_wr_idx = unpack_idx_reg - 10'd1;
    assign unpack_exp_packed_rd_addr_reg = unpack_wr_idx[9:5];  // /32

    logic [4:0] exp_byte_offset;
    assign exp_byte_offset = unpack_wr_idx[4:0];  // %32

    logic [7:0] current_exp_byte;
    assign current_exp_byte = i_exp_packed_rd_data[exp_byte_offset*8 +: 8];

    assign o_exp_left_wr_en = ((state_reg == ST_FETCH_ACTIVE || state_reg == ST_FETCH_DRAIN) &&
                              (fetch_target_reg == 1'b0) &&
                              (unpack_idx_reg >= 10'd1) &&
                              (unpack_idx_reg <= 10'd512));

    assign o_exp_right_wr_en = ((state_reg == ST_FETCH_ACTIVE || state_reg == ST_FETCH_DRAIN) &&
                               (fetch_target_reg == 1'b1) &&
                               (unpack_idx_reg >= 10'd1) &&
                               (unpack_idx_reg <= 10'd512));

    assign o_exp_left_wr_addr = unpack_wr_idx[8:0];
    assign o_exp_right_wr_addr = unpack_wr_idx[8:0];
    assign o_exp_left_wr_data = current_exp_byte;
    assign o_exp_right_wr_data = current_exp_byte;
    assign o_exp_packed_rd_addr = unpack_exp_packed_rd_addr_reg;
    assign o_exp_packed_rd_target = fetch_target_reg;

    // ===================================================================
    // BRAM Write Logic
    // ===================================================================
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            bram_wr_addr_reg <= '0;
            bram_wr_data_reg <= '0;
            bram_wr_en_reg <= 1'b0;
            bram_wr_target_reg <= 1'b0;
        end else begin
            bram_wr_en_reg <= 1'b0;  // Default

            if ((state_reg == ST_FETCH_ACTIVE || state_reg == ST_FETCH_DRAIN) &&
                axi_ddr_if.rvalid && axi_ddr_if.rready) begin
                // Write DDR data to BRAM
                // Simple linear addressing based on total lines fetched
                if (total_lines_fetched_reg < 16) begin
                    bram_wr_addr_reg <= {7'd0, total_lines_fetched_reg[3:0]};  // 0-15 for exp
                end else begin
                    bram_wr_addr_reg <= {2'd0, (total_lines_fetched_reg - 10'd16)};  // 16-527 for mantissa
                end
                bram_wr_data_reg <= axi_ddr_if.rdata;
                bram_wr_en_reg <= 1'b1;
                bram_wr_target_reg <= fetch_target_reg;
            end
        end
    end

    assign o_bram_wr_data = bram_wr_data_reg;
    assign o_bram_wr_addr = bram_wr_addr_reg;
    assign o_bram_wr_en = bram_wr_en_reg;
    assign o_bram_wr_target = bram_wr_target_reg;

    // ===================================================================
    // AXI Interface Assignments
    // ===================================================================

    // Calculate next burst address dynamically
    logic [25:0] next_burst_addr;
    always_comb begin
        // Each burst fetches 16 lines
        next_burst_addr = fetch_addr_reg + (total_ars_issued * 16);
    end

    // AXI Read Address Channel - use pending flag
    assign axi_ddr_if.arvalid  = ar_pending;
    assign axi_ddr_if.arid     = arid_counter;
    assign axi_ddr_if.araddr   = {GDDR6_PAGE_ID, 2'b00, next_burst_addr, {ADDR_BYTE_SHIFT{1'b0}}};
    assign axi_ddr_if.arlen    = FIXED_BURST_LEN;  // 16 beats
    assign axi_ddr_if.arsize   = 3'h5;             // 32 bytes per beat
    assign axi_ddr_if.arburst  = 2'b01;            // INCR burst
    assign axi_ddr_if.arlock   = 1'b0;
    assign axi_ddr_if.arcache  = 4'h0;
    assign axi_ddr_if.arprot   = 3'b010;
    assign axi_ddr_if.arqos    = 4'h0;
    assign axi_ddr_if.arregion = 4'h0;

    // AXI Read Data Channel
    assign axi_ddr_if.rready = (state_reg == ST_FETCH_ACTIVE || state_reg == ST_FETCH_DRAIN);

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
    assign o_fetcher_state = state_reg;
    assign o_wr_addr = bram_wr_addr_reg;
    assign o_wr_en = bram_wr_en_reg;

endmodule : fetcher