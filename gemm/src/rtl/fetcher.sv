// ------------------------------------------------------------------
// Fetcher Module - GDDR6 to Dispatcher BRAM Transfer
//
// Purpose: Handles FETCH operations (GDDR6 → dispatcher_bram)
// Features:
//  - FETCH state machine: IDLE → FETCH_INIT → FETCH_READ → FETCH_READ_EXP → FETCH_READ_MAN → FETCH_DONE
//  - AXI4 burst read interface for GDDR6 access
//  - BRAM write during fetch (exp_packed + mantissa)
//  - Parallel exponent unpacking (during mantissa fetch phase)
//
// Memory Layout (GFP8 Block):
//  Lines 0-15:   Packed Exponents (16 lines)
//  Lines 16-527: Mantissas (512 lines)
//
// Author: Refactored from dispatcher_control.sv
// Date: $(date +"%Y-%m-%d")
// ------------------------------------------------------------------

`include "nap_interfaces.svh"

module fetcher
import gemm_pkg::*;
#(
    parameter MAN_WIDTH = 256,         // Mantissa data width
    parameter EXP_WIDTH = 8,           // Exponent data width
    parameter BRAM_DEPTH = 512,        // Dispatcher BRAM depth
    parameter AXI_ADDR_WIDTH = 42,     // AXI address width (GDDR6 NoC: {Page[9], Line[26], Pad[2], Byte[5]})
    parameter BRAM_ADDR_WIDTH = $clog2(BRAM_DEPTH),  // 9-bit for 512 depth
    parameter TILE_ADDR_WIDTH = $clog2(BRAM_DEPTH),  // 9-bit for 512 depth
    parameter [8:0] GDDR6_PAGE_ID = 9'd2  // GDDR6 Page ID for NoC routing (Channel 1 default)
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
    // Main write port for exp_packed and mantissas
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
    // State Machine Definition
    // ===================================================================
    typedef enum logic [3:0] {
        ST_IDLE            = 4'd0,
        ST_FETCH_INIT      = 4'd1,
        ST_FETCH_READ      = 4'd2,
        ST_FETCH_READ_EXP  = 4'd3,  // Read exponent lines (0-15) into exp_packed
        ST_FETCH_READ_MAN  = 4'd4,  // Read mantissa lines (16-527) + parallel unpack
        ST_FETCH_DONE      = 4'd5
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

    // FETCH command tracking
    logic [link_addr_width_gp-1:0] fetch_addr_reg;
    logic        fetch_target_reg;  // 0=left, 1=right (captured from i_fetch_target)
    logic [10:0] current_line_reg;  // 11-bit for 2048-entry addressing

    // Counters for tracking exp and mantissa lines during fetch
    logic [4:0]  exp_lines_fetched_reg;   // 0-15: exponent lines fetched
    logic [9:0]  man_lines_fetched_reg;   // 0-511: mantissa lines fetched

    // AXI transaction control
    logic axi_ar_req_reg;
    logic axi_r_ready_reg;
    logic [7:0] beat_count_reg;

    // Status flags
    logic fetch_done_reg;

    // Edge detection for command enable (prevent double-triggering)
    logic fetch_en_prev;

    // BRAM control signals
    logic [10:0] bram_wr_addr_reg;
    logic [MAN_WIDTH-1:0] bram_wr_data_reg;
    logic        bram_wr_en_reg;
    logic        bram_wr_target_reg;  // 0=left, 1=right

    // Parallel unpacking signals
    logic [3:0]  unpack_exp_packed_rd_addr_reg; // 0-15: which exp_packed line to read
    logic [9:0]  unpack_idx_reg;

    // ===================================================================
    // State Transition Logic
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

    // Next state combinational logic
    always_comb begin
        state_next = state_reg;

        case (state_reg)
            ST_IDLE: begin
                // Only trigger on RISING edge of enable to prevent double-triggering
                if (i_fetch_en && !fetch_en_prev) begin
                    $display("[FETCHER] @%0t ST_IDLE: i_fetch_en RISING EDGE, transitioning to FETCH_INIT", $time);
                    state_next = ST_FETCH_INIT;
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
                        $display("[FETCHER] @%0t ST_FETCH_READ: AR handshake, moving to FETCH_READ_EXP", $time);
                        state_next = ST_FETCH_READ_EXP;
                    end else begin
                        $display("[FETCHER] @%0t ST_FETCH_READ: AR handshake, moving to FETCH_READ_MAN", $time);
                        state_next = ST_FETCH_READ_MAN;
                    end
                end
            end

            ST_FETCH_READ_EXP: begin
                // Read exponent burst (16 beats)
                if (axi_ddr_if.rvalid && axi_ddr_if.rready && axi_ddr_if.rlast) begin
                    if (exp_lines_fetched_reg >= 15) begin
                        $display("[FETCHER] @%0t FETCH_READ_EXP complete (%0d lines), moving to FETCH_READ for mantissas", $time, exp_lines_fetched_reg + 1);
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
                        $display("[FETCHER] @%0t FETCH_READ_MAN complete (%0d lines), moving to FETCH_DONE", $time, man_lines_fetched_reg + 1);
                        state_next = ST_FETCH_DONE;
                    end else begin
                        state_next = ST_FETCH_READ;  // Issue next AR for more mantissas
                    end
                end
            end

            ST_FETCH_DONE: begin
                // Fetch complete - exponents already unpacked in parallel!
                $display("[FETCHER] @%0t FETCH_DONE, returning to IDLE (unpacking done in parallel)", $time);
                state_next = ST_IDLE;
            end

            default: begin
                state_next = ST_IDLE;
            end
        endcase
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
            fetch_done_reg <= 1'b0;
        end else begin
            fetch_done_reg <= 1'b0;  // Default

            case (state_reg)
                ST_IDLE: begin
                    // Only capture parameters on RISING edge
                    if (i_fetch_en && !fetch_en_prev) begin
                        fetch_addr_reg <= i_fetch_addr;
                        fetch_target_reg <= i_fetch_target;  // Capture left/right target
                        `ifdef SIMULATION
                        $display("[FETCHER] @%0t FETCH params: addr=0x%08x, len=%0d, target=%0d (%s)",
                                 $time, i_fetch_addr, i_fetch_len, i_fetch_target, i_fetch_target ? "RIGHT" : "LEFT");
                        `endif
                        current_line_reg <= '0;

                        // Reset phase counters for new fetch
                        exp_lines_fetched_reg <= '0;
                        man_lines_fetched_reg <= '0;

                        $display("[FETCHER] @%0t FETCH_START: DDR_addr=%0d, len=%0d, current_line=%0d, target=%s",
                                 $time, i_fetch_addr, i_fetch_len, current_line_reg,
                                 i_fetch_target ? "RIGHT" : "LEFT");
                    end
                end

                ST_FETCH_READ_EXP: begin
                    // Increment exp line counter for each beat received
                    if (axi_ddr_if.rvalid && axi_ddr_if.rready) begin
                        exp_lines_fetched_reg <= exp_lines_fetched_reg + 1;
                        current_line_reg <= current_line_reg + 1;
                        $display("[FETCHER] @%0t EXP_LINE: %0d/16", $time, exp_lines_fetched_reg + 1);
                    end
                end

                ST_FETCH_READ_MAN: begin
                    // Increment man line counter for each beat received
                    if (axi_ddr_if.rvalid && axi_ddr_if.rready) begin
                        man_lines_fetched_reg <= man_lines_fetched_reg + 1;
                        current_line_reg <= current_line_reg + 1;
                        if (man_lines_fetched_reg[3:0] == 4'd0 || axi_ddr_if.rlast) begin
                            $display("[FETCHER] @%0t MAN_LINE: %0d/512", $time, man_lines_fetched_reg + 1);
                        end
                    end
                end

                ST_FETCH_DONE: begin
                    // Signal fetch_done immediately - unpacking done in parallel!
                    fetch_done_reg <= 1'b1;
                end
            endcase
        end
    end

    assign o_fetch_done = fetch_done_reg;

    // ===================================================================
    // Parallel Exponent Unpacking - CONTINUOUS (independent of AXI)
    // ===================================================================
    // Unpack exponents in parallel with mantissa fetch
    // Uses a continuous counter to avoid skipping addresses during AXI burst gaps
    
    // Continuous unpacking counter (runs every cycle during ST_FETCH_READ_MAN)
    // CRITICAL: Only reset at start of FETCH, not when transitioning to ST_FETCH_READ!
    
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
    assign current_exp_byte = i_exp_packed_rd_data[exp_byte_offset*8 +: 8];
    
    // Exponent write enables (active during unpacking, skip first 1 cycle for BRAM latency)
    // Write continuously from unpack_idx 1-512 (unpack_wr_idx 0-511)
    assign o_exp_left_wr_en = (state_reg == ST_FETCH_READ_MAN) && 
                              (fetch_target_reg == 1'b0) &&
                              (unpack_idx_reg >= 10'd1) &&
                              (unpack_idx_reg <= 10'd512);
    
    assign o_exp_right_wr_en = (state_reg == ST_FETCH_READ_MAN) && 
                               (fetch_target_reg == 1'b1) &&
                               (unpack_idx_reg >= 10'd1) &&
                               (unpack_idx_reg <= 10'd512);
    
    // Exponent write addresses
    assign o_exp_left_wr_addr = unpack_wr_idx[8:0];
    assign o_exp_right_wr_addr = unpack_wr_idx[8:0];
    
    // Exponent write data
    assign o_exp_left_wr_data = current_exp_byte;
    assign o_exp_right_wr_data = current_exp_byte;

    // Exp packed read interface
    assign o_exp_packed_rd_addr = unpack_exp_packed_rd_addr_reg;
    assign o_exp_packed_rd_target = fetch_target_reg;

    `ifdef SIMULATION
    always @(posedge i_clk) begin
        if (o_exp_left_wr_en) begin
            $display("[FETCHER] @%0t LEFT exp write: addr=%0d, data=0x%02x, packed_rd_addr=%0d, byte_offset=%0d, unpack_wr_idx=%0d",
                     $time, o_exp_left_wr_addr, o_exp_left_wr_data, unpack_exp_packed_rd_addr_reg, exp_byte_offset, unpack_wr_idx);
        end
        if (o_exp_right_wr_en) begin
            $display("[FETCHER] @%0t RIGHT exp write: addr=%0d, data=0x%02x, packed_rd_addr=%0d, byte_offset=%0d, unpack_wr_idx=%0d, fetch_target_reg=%0d",
                     $time, o_exp_right_wr_addr, o_exp_right_wr_data, unpack_exp_packed_rd_addr_reg, exp_byte_offset, unpack_wr_idx, fetch_target_reg);
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
                    $display("[FETCHER] @%0t BRAM_WRITE: addr=%0d, data[63:0]=0x%h, phase=%s",
                             $time, bram_wr_addr_reg, axi_ddr_if.rdata[63:0],
                             (state_reg == ST_FETCH_READ_EXP) ? "EXP" : "MAN");
                end
            end
        end
    end

    // BRAM write outputs
    assign o_bram_wr_data = bram_wr_data_reg;
    assign o_bram_wr_addr = bram_wr_addr_reg;
    assign o_bram_wr_en = bram_wr_en_reg;
    assign o_bram_wr_target = bram_wr_target_reg;

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
                $display("[FETCHER] @%0t Setting axi_ar_req_reg=1 in ST_FETCH_INIT", $time);
            end else if (state_reg == ST_FETCH_READ && axi_ddr_if.arvalid && axi_ddr_if.arready) begin
                axi_ar_req_reg <= 1'b0;
                $display("[FETCHER] @%0t Clearing axi_ar_req_reg=0 after AR handshake", $time);
            end else if ((state_reg == ST_FETCH_READ_EXP || state_reg == ST_FETCH_READ_MAN) && 
                        axi_ddr_if.rvalid && axi_ddr_if.rready && axi_ddr_if.rlast) begin
                // Burst complete - issue next AR if more data needed
                if (state_reg == ST_FETCH_READ_EXP && exp_lines_fetched_reg >= 15) begin
                    // Exponent phase complete, need to start mantissa phase
                    axi_ar_req_reg <= 1'b1;
                    $display("[FETCHER] @%0t EXP phase done, requesting first MAN burst", $time);
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
    assign axi_ddr_if.arid     = 8'hFE;  // Fetcher ID (changed from 0xDC)
    // CRITICAL: Include GDDR6_PAGE_ID in address for correct NoC routing
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
    assign o_fetcher_state = state_reg;
    assign o_wr_addr = bram_wr_addr_reg;
    assign o_wr_en = bram_wr_en_reg;

endmodule : fetcher

