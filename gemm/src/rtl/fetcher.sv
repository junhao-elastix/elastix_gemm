// ------------------------------------------------------------------
// Fetcher Module
//
// Purpose: FETCH operations with pipelined AR issuing
// Features:
//  - 32-deep FWFT FIFO for AR burst management
//  - Back-to-back AR issuing (up to 32 outstanding requests)
//  - Parallel exponent unpacking
//  - State machine: IDLE → ACTIVE → DONE
//
// Memory Layout (GFP8 Block):
//  Lines 0-15:   Packed Exponents (16 lines, 1 burst)
//  Lines 16-527: Mantissas (512 lines, 32 bursts)
//  Total: 33 bursts × 16 beats = 528 lines
//
// Author: Junhao Pan
// Date: 10/31/2025
// ------------------------------------------------------------------

`include "nap_interfaces.svh"

module fetcher
import gemm_pkg::*;
#(
    parameter MAN_WIDTH = 256,
    parameter EXP_WIDTH = 8,
    parameter BRAM_DEPTH = 512,
    parameter AXI_ADDR_WIDTH = 42,
    parameter BRAM_ADDR_WIDTH = $clog2(BRAM_DEPTH),
    parameter TILE_ADDR_WIDTH = $clog2(BRAM_DEPTH),
    parameter [8:0] GDDR6_PAGE_ID = 9'd2
)
(
    // Clock and Reset
    input  logic                         i_clk,
    input  logic                         i_reset_n,

    // Master Control Interface (FETCH command)
    input  logic                         i_fetch_en,
    input  logic [link_addr_width_gp-1:0] i_fetch_addr,
    input  logic [link_len_width_gp-1:0]  i_fetch_len,
    input  logic                         i_fetch_target, // 0=left, 1=right
    output logic                         o_fetch_done,

    // Dispatcher BRAM Write Interface
    output logic [MAN_WIDTH-1:0]         o_bram_wr_data,
    output logic [BRAM_ADDR_WIDTH+1:0]   o_bram_wr_addr,
    output logic                         o_bram_wr_en,
    output logic                         o_bram_wr_target,

    // Dispatcher BRAM Exponent Aligned Write Ports
    output logic [TILE_ADDR_WIDTH-1:0]   o_exp_left_wr_addr,
    output logic                         o_exp_left_wr_en,
    output logic [EXP_WIDTH-1:0]         o_exp_left_wr_data,
    
    output logic [TILE_ADDR_WIDTH-1:0]   o_exp_right_wr_addr,
    output logic                         o_exp_right_wr_en,
    output logic [EXP_WIDTH-1:0]         o_exp_right_wr_data,

    // Dispatcher BRAM Read Interface (for unpacking exp_packed)
    output logic [3:0]                   o_exp_packed_rd_addr,
    output logic                         o_exp_packed_rd_target,
    input  logic [MAN_WIDTH-1:0]         i_exp_packed_rd_data,

    // AXI-4 Initiator Interface
    t_AXI4.initiator                     axi_ddr_if,

    // Debug Interface
    output logic [3:0]                   o_fetcher_state,
    output logic [10:0]                  o_wr_addr,
    output logic                         o_wr_en
);

    // ===================================================================
    // State Machine Definition (SIMPLIFIED)
    // ===================================================================
    typedef enum logic [3:0] {
        ST_IDLE        = 4'd0,
        ST_FETCH_INIT  = 4'd1,
        ST_FETCH_ACTIVE= 4'd2,  // Single state for all AR issuing + R receiving
        ST_FETCH_DONE  = 4'd3
    } state_t;

    state_t state_reg, state_next;

    // ===================================================================
    // Local Parameters
    // ===================================================================
    localparam FIXED_BURST_LEN = 15;        // AXI arlen = 15 means 16 beats
    localparam BYTES_PER_BEAT = 32;
    localparam ADDR_BYTE_SHIFT = 5;
    localparam TOTAL_BURSTS = 33;           // 1 exp + 32 man
    localparam AR_FIFO_DEPTH = 64;          // 64-deep FIFO (increased for safety)

    // ===================================================================
    // Internal Signals
    // ===================================================================
    logic [link_addr_width_gp-1:0] fetch_addr_reg;
    logic        fetch_target_reg;
    logic        fetch_en_prev;  // Edge detection

    // AR issuing control
    logic [5:0]  ars_issued;          // 0-33 ARs issued
    logic [10:0] current_line_reg;    // Current line offset for AR address
    logic        ar_issue_req;        // Request to issue AR
    logic        ar_can_issue;        // FIFO not full, can issue

    // R data receiving control
    logic [9:0]  lines_received;
    logic [4:0]  exp_lines_received;  // 0-15 exponent lines
    logic [9:0]  man_lines_received;  // 0-511 mantissa lines
    logic [1:0]  settle_cycles;       // Cycles to wait after last line for BRAM write to complete

    // R-channel target tracking (for associating R responses with correct target)
    logic        r_target_fifo [0:AR_FIFO_DEPTH-1];  // Stores target for each AR burst
    logic [5:0]  r_target_wr_ptr;
    logic [5:0]  r_target_rd_ptr;
    logic [6:0]  r_target_count;
    logic        r_target_wr;
    logic        r_target_rd;
    logic        r_target_current_burst;  // Registered target for current burst
    logic [3:0]  r_burst_beat_count;      // Track beats within current burst (0-15)

    // ===================================================================
    // AR FIFO - 64-deep Regular FIFO (not FWFT)
    // ===================================================================
    // Stores burst start line offsets AND target for each AR issued
    // Registered output to avoid race conditions
    // Format: {target[11], address[10:0]}

    logic [11:0] ar_fifo [0:AR_FIFO_DEPTH-1];
    logic [5:0]  ar_fifo_wr_ptr;
    logic [5:0]  ar_fifo_rd_ptr;
    logic [6:0]  ar_fifo_count;
    logic [11:0] ar_fifo_rd_data_reg; // Registered output: {target, address}
    logic        ar_fifo_empty;
    logic        ar_fifo_full;
    logic        ar_fifo_wr;
    logic        ar_fifo_rd;

    assign ar_fifo_empty = (ar_fifo_count == 0);
    assign ar_fifo_full = (ar_fifo_count >= AR_FIFO_DEPTH);
    assign ar_fifo_wr = ar_issue_req && ar_can_issue;
    assign ar_fifo_rd = (axi_ddr_if.arvalid && axi_ddr_if.arready);  // Advance on AR handshake, not R completion
    assign ar_can_issue = !ar_fifo_full;

    // FIFO write and read with registered output
    // Strategy: Load output register when writing to empty FIFO (synchronous with write)
    //           This ensures output is valid one cycle later, before AR handshake
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            ar_fifo_wr_ptr <= '0;
            ar_fifo_rd_ptr <= '0;
            ar_fifo_rd_data_reg <= '0;
        end else if (state_reg == ST_FETCH_DONE) begin
            // Reset FIFO pointers when FETCH completes
            ar_fifo_wr_ptr <= '0;
            ar_fifo_rd_ptr <= '0;
            ar_fifo_rd_data_reg <= '0;
            `ifdef SIMULATION
            $display("[AR_FIFO_RESET] @%0t Resetting AR FIFO pointers in ST_FETCH_DONE", $time);
            `endif
        end else if (state_reg == ST_IDLE && i_fetch_en && !fetch_en_prev) begin
            // Pre-load first AR FIFO entry at FETCH_START
            // This ensures ar_fifo_rd_data_reg has correct {target, addr} for first AR
            ar_fifo[0] <= {i_fetch_target, 11'd0};  // {target, addr=0}
            ar_fifo_rd_data_reg <= {i_fetch_target, 11'd0};
            `ifdef SIMULATION
            $display("[AR_FIFO_INIT] @%0t Pre-loading AR_FIFO[0] with target=%s, addr=0",
                     $time, i_fetch_target ? "RIGHT" : " LEFT");
            `endif
        end else begin
            // Handle writes
            if (ar_fifo_wr) begin
                // Store both address and target: {target[11], address[10:0]}
                ar_fifo[ar_fifo_wr_ptr] <= {fetch_target_reg, current_line_reg};
                ar_fifo_wr_ptr <= ar_fifo_wr_ptr + 1;

                // If writing to empty FIFO, also load output register
                // This ensures data is valid next cycle when AR can issue
                if (ar_fifo_empty) begin
                    ar_fifo_rd_data_reg <= {fetch_target_reg, current_line_reg};
                    `ifdef SIMULATION
                    $display("[FIFO_WR_FIRST] @%0t wr_ptr=%0d, addr=%0d, target=%s, loading output reg immediately",
                             $time, ar_fifo_wr_ptr, current_line_reg, fetch_target_reg ? "RIGHT" : "LEFT");
                    `endif
                end else begin
                    `ifdef SIMULATION
                    $display("[FIFO_WR] @%0t wr_ptr=%0d, addr=%0d, target=%s",
                             $time, ar_fifo_wr_ptr, current_line_reg, fetch_target_reg ? "RIGHT" : "LEFT");
                    `endif
                end
            end

            // Handle reads (on AR handshake)
            if (ar_fifo_rd) begin
                ar_fifo_rd_ptr <= ar_fifo_rd_ptr + 1;
                // Load next value if available
                // Account for concurrent read/write: if count=1 but write happening, next value exists
                if ((ar_fifo_count > 1) || ar_fifo_wr) begin
                    // Bypass logic: if reading address being written, use write data directly
                    if (ar_fifo_wr && (ar_fifo_wr_ptr == (ar_fifo_rd_ptr + 1))) begin
                        ar_fifo_rd_data_reg <= {fetch_target_reg, current_line_reg};  // Bypass from write source
                        `ifdef SIMULATION
                        $display("[FIFO_RD_BYPASS] @%0t rd_ptr=%0d->%0d, bypassing wr_ptr=%0d, addr=%0d, target=%s",
                                 $time, ar_fifo_rd_ptr, ar_fifo_rd_ptr+1, ar_fifo_wr_ptr, current_line_reg, fetch_target_reg ? "RIGHT" : "LEFT");
                        `endif
                    end else begin
                        ar_fifo_rd_data_reg <= ar_fifo[ar_fifo_rd_ptr + 1];
                        `ifdef SIMULATION
                        $display("[FIFO_RD] @%0t rd_ptr=%0d->%0d, count=%0d, wr=%0d, addr=%0d, target=%s",
                                 $time, ar_fifo_rd_ptr, ar_fifo_rd_ptr+1, ar_fifo_count, ar_fifo_wr, ar_fifo[ar_fifo_rd_ptr + 1][10:0], ar_fifo[ar_fifo_rd_ptr + 1][11] ? "RIGHT" : "LEFT");
                        `endif
                    end
                end else begin
                    `ifdef SIMULATION
                    $display("[FIFO_RD_LAST] @%0t rd_ptr=%0d->%0d, count=%0d, wr=%0d (FIFO will be empty)",
                             $time, ar_fifo_rd_ptr, ar_fifo_rd_ptr+1, ar_fifo_count, ar_fifo_wr);
                    `endif
                end
            end
        end
    end

    // FIFO count
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            ar_fifo_count <= '0;
        end else begin
            case ({ar_fifo_wr, ar_fifo_rd})
                2'b00: ar_fifo_count <= ar_fifo_count;
                2'b01: ar_fifo_count <= ar_fifo_count - 1;
                2'b10: ar_fifo_count <= ar_fifo_count + 1;
                2'b11: ar_fifo_count <= ar_fifo_count;  // Net zero
            endcase
        end
    end

    // ===================================================================
    // R-Channel Target FIFO with Burst Tracking
    // ===================================================================
    // Push target when AR handshakes (one per burst)
    // Pop target and load register when first beat of new burst arrives
    // All 16 beats of a burst use the same registered target
    assign r_target_wr = (axi_ddr_if.arvalid && axi_ddr_if.arready);  // Push on AR handshake
    assign r_target_rd = (axi_ddr_if.rvalid && axi_ddr_if.rready && r_burst_beat_count == 0);  // Pop at burst start

    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            r_target_wr_ptr <= '0;
            r_target_rd_ptr <= '0;
            r_target_count <= '0;
            r_target_current_burst <= 1'b0;
            r_burst_beat_count <= '0;
        end else if (state_reg == ST_FETCH_DONE) begin
            // Reset R-target FIFO when FETCH completes
            // This ensures clean state for next FETCH (bursts arrive in order, no overlap)
            r_target_wr_ptr <= '0;
            r_target_rd_ptr <= '0;
            r_target_count <= '0;
            r_target_current_burst <= 1'b0;
            r_burst_beat_count <= '0;
            `ifdef SIMULATION
            $display("[R_TARGET_FIFO_RESET] @%0t Resetting R-target FIFO pointers in ST_FETCH_DONE", $time);
            `endif
        end else if (state_reg == ST_IDLE && i_fetch_en && !fetch_en_prev) begin
            // Pre-load first target at FETCH_START (R bursts may arrive before AR handshakes!)
            r_target_fifo[0] <= i_fetch_target;
            r_target_current_burst <= i_fetch_target;
            `ifdef SIMULATION
            $display("[R_TARGET_INIT] @%0t Pre-loading FIFO[0] with target=%s at FETCH_START",
                     $time, i_fetch_target ? "RIGHT" : " LEFT");
            `endif
        end else begin
            // FIFO operates: push on AR handshake, pop when starting new burst

            // Write: Push target when AR handshakes
            if (r_target_wr) begin
                r_target_fifo[r_target_wr_ptr] <= ar_target;  // Store target from AR FIFO output
                r_target_wr_ptr <= r_target_wr_ptr + 1;
                `ifdef SIMULATION
                $display("[R_TARGET_WR] @%0t wr_ptr=%0d, target=%s", $time, r_target_wr_ptr, ar_target ? "RIGHT" : "LEFT");
                `endif
            end

            // Burst beat counter and target loading
            if (axi_ddr_if.rvalid && axi_ddr_if.rready) begin
                if (r_burst_beat_count == 0) begin
                    // Start of new burst: load target from FIFO and advance read pointer
                    r_target_current_burst <= r_target_fifo[r_target_rd_ptr];
                    r_target_rd_ptr <= r_target_rd_ptr + 1;
                    `ifdef SIMULATION
                    $display("[R_TARGET_LOAD] @%0t rd_ptr=%0d, loading target=%s for new burst",
                             $time, r_target_rd_ptr, r_target_fifo[r_target_rd_ptr] ? "RIGHT" : "LEFT");
                    `endif
                end

                // Increment beat counter (wraps at 16)
                if (axi_ddr_if.rlast) begin
                    r_burst_beat_count <= '0;  // Reset on last beat
                end else begin
                    r_burst_beat_count <= r_burst_beat_count + 1;
                end
            end

            // Update count
            case ({r_target_wr, r_target_rd})
                2'b00: r_target_count <= r_target_count;
                2'b01: r_target_count <= r_target_count - 1;
                2'b10: r_target_count <= r_target_count + 1;
                2'b11: r_target_count <= r_target_count;  // Net zero
            endcase
        end
    end

    // ===================================================================
    // State Machine
    // ===================================================================
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            state_reg <= ST_IDLE;
            fetch_en_prev <= 1'b0;
        end else begin
            state_reg <= state_next;
            // Clear fetch_en_prev when FETCH completes to allow edge detection for next FETCH
            if (state_reg == ST_FETCH_DONE) begin
                fetch_en_prev <= 1'b0;
            end else begin
                fetch_en_prev <= i_fetch_en;
            end
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
                state_next = ST_FETCH_ACTIVE;
            end

            ST_FETCH_ACTIVE: begin
                // Stay active until all lines received AND unpacking complete AND BRAM writes settled
                // Unpacking needs unpack_idx_reg to reach 512 (512 exponents: indices 0-511)
                // BRAM writes are registered, so need 2 settle cycles after last line
                if (lines_received >= 528 && unpack_idx_reg >= 512 && settle_cycles >= 2) begin
                    `ifdef SIMULATION
                    $display("[FETCHER_OPT] @%0t FETCH_DONE: lines_received=%0d, unpack_idx_reg=%0d, settle=%0d",
                             $time, lines_received, unpack_idx_reg, settle_cycles);
                    `endif
                    state_next = ST_FETCH_DONE;
                end
                `ifdef SIMULATION
                else if (lines_received >= 528) begin
                    $display("[FETCHER_OPT] @%0t Waiting for settle: lines_received=%0d, unpack_idx=%0d, settle=%0d",
                             $time, lines_received, unpack_idx_reg, settle_cycles);
                end
                `endif
            end

            ST_FETCH_DONE: begin
                state_next = ST_IDLE;
            end

            default: state_next = ST_IDLE;
        endcase
    end

    // ===================================================================
    // FETCH Command Processing
    // ===================================================================
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            fetch_addr_reg <= '0;
            fetch_target_reg <= 1'b0;
            ars_issued <= '0;
            current_line_reg <= '0;
            lines_received <= '0;
            exp_lines_received <= '0;
            man_lines_received <= '0;
            settle_cycles <= '0;
        end else begin
            case (state_reg)
                ST_IDLE: begin
                    if (i_fetch_en && !fetch_en_prev) begin
                        fetch_addr_reg <= i_fetch_addr;
                        fetch_target_reg <= i_fetch_target;
                        ars_issued <= '0;
                        current_line_reg <= '0;
                        lines_received <= '0;
                        exp_lines_received <= '0;
                        man_lines_received <= '0;
                        `ifdef SIMULATION
                        $display("[FETCHER_OPT] @%0t FETCH_START: DDR_addr=%0d, len=%0d, current_line=%0d, target=%s",
                                 $time, i_fetch_addr, i_fetch_len, current_line_reg,
                                 i_fetch_target ? "RIGHT" : " LEFT");
                        $display("[FETCHER_OPT] @%0t Initializing r_target_fifo[0] with target=%s",
                                 $time, i_fetch_target ? "RIGHT" : " LEFT");
                        `endif
                        settle_cycles <= '0;
                        // Note: r_target_fifo initialization happens in R-target always_ff block
                    end
                end

                ST_FETCH_ACTIVE: begin
                    // AR issuing: Issue ARs as fast as FIFO accepts
                    if (ar_issue_req && ar_can_issue) begin
                        `ifdef SIMULATION
                        $display("[FETCHER_OPT_AR] @%0t Issue AR #%0d: fetch_addr=%0d, current_line=%0d, addr=%0d",
                                 $time, ars_issued, fetch_addr_reg, current_line_reg, fetch_addr_reg + current_line_reg);
                        `endif
                        current_line_reg <= current_line_reg + 16;  // Next burst
                        ars_issued <= ars_issued + 1;
                    end

                    // R data receiving: Count lines as they arrive (bursts arrive in order)
                    if (axi_ddr_if.rvalid && axi_ddr_if.rready && lines_received < 528) begin
                        lines_received <= lines_received + 1;

                        if (lines_received < 16) begin
                            exp_lines_received <= exp_lines_received + 1;
                        end else begin
                            man_lines_received <= man_lines_received + 1;
                        end
                    end

                    // Settling counter: Wait for BRAM writes to complete
                    if (lines_received >= 528 && settle_cycles < 2) begin
                        settle_cycles <= settle_cycles + 1;
                    end
                end

                ST_FETCH_DONE: begin
                    // Reset ALL FIFO pointers when FETCH completes
                    // This ensures clean state for next FETCH (no overlap issues)
                    `ifdef SIMULATION
                    $display("[FETCHER_OPT] @%0t ST_FETCH_DONE: Resetting AR and R-target FIFO pointers", $time);
                    `endif
                    // Note: FIFO resets happen in separate always_ff blocks below
                end

                default: begin
                    // No updates
                end
            endcase
        end
    end

    // AR issue request: Issue all 33 ARs as fast as possible
    always_comb begin
        ar_issue_req = 1'b0;
        if (state_reg == ST_FETCH_ACTIVE) begin
            ar_issue_req = (ars_issued < TOTAL_BURSTS);
        end
    end

    // ===================================================================
    // AXI Read Address Channel
    // ===================================================================
    logic ar_valid_reg;

    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            ar_valid_reg <= 1'b0;
        end else if (state_reg == ST_FETCH_DONE || state_reg == ST_IDLE) begin
            // Clear arvalid when FETCH completes or in IDLE
            ar_valid_reg <= 1'b0;
        end else begin
            // In ST_FETCH_ACTIVE: manage arvalid based on AR FIFO state
            if (ar_fifo_wr) begin
                ar_valid_reg <= 1'b1;  // Assert arvalid when AR enters FIFO
            end else if (axi_ddr_if.arvalid && axi_ddr_if.arready && ar_fifo_count == 1) begin
                // Clear after last AR handshakes (FIFO will be empty)
                ar_valid_reg <= 1'b0;
            end
        end
    end

    // AXI4 AR channel assignments
    // GDDR6 NAP Address Format (per Achronix spec):
    // [41:37] = Reserved (5 bits, from GDDR6_PAGE_ID[8:4], must be 0)
    // [36:33] = Ctrl ID (4 bits, from GDDR6_PAGE_ID[3:0])
    // [32:0]  = Memory Address (33 bits, contiguous)
    //   [32:31] = Upper 2 bits (for >2GB expansion)
    //   [30:5]  = Line address
    //   [4:0]   = Byte offset (must be 0 for 32-byte alignment)
    // Truncate line address to 26 bits to prevent overflow into ctrl_id field
    // Use registered value from FIFO, not live current_line_reg!
    // Extract address (bits [10:0]) and target (bit [11]) from FIFO output
    logic [25:0] line_addr_26bit;
    logic        ar_target;  // Target from AR FIFO
    always_comb begin
        line_addr_26bit = (fetch_addr_reg + ar_fifo_rd_data_reg[10:0]);  // Extract address from FIFO
        ar_target = ar_fifo_rd_data_reg[11];  // Extract target from FIFO
    end

    assign axi_ddr_if.arvalid = ar_valid_reg;
    assign axi_ddr_if.arid = 8'hFE;  // Fixed ID for fetcher
    assign axi_ddr_if.araddr = {GDDR6_PAGE_ID, 2'b00, line_addr_26bit, {ADDR_BYTE_SHIFT{1'b0}}};
    assign axi_ddr_if.arlen = FIXED_BURST_LEN;

    `ifdef SIMULATION
    always @(posedge i_clk) begin
        if (axi_ddr_if.arvalid && axi_ddr_if.arready) begin
            $display("[FETCHER_OPT_AXI] @%0t AR HANDSHAKE: araddr=0x%x, line_addr=%0d, fifo_out=%0d",
                     $time, axi_ddr_if.araddr, line_addr_26bit, ar_fifo_rd_data_reg);
        end
    end
    `endif
    assign axi_ddr_if.arsize = 3'h5;  // 32 bytes
    assign axi_ddr_if.arburst = 2'b01;  // INCR
    assign axi_ddr_if.arlock = 1'b0;
    assign axi_ddr_if.arcache = 4'h0;
    assign axi_ddr_if.arprot = 3'b010;
    assign axi_ddr_if.arqos = 4'h0;
    assign axi_ddr_if.arregion = 4'h0;

    // ===================================================================
    // AXI Read Data Channel
    // ===================================================================
    assign axi_ddr_if.rready = (state_reg == ST_FETCH_ACTIVE);

    // ===================================================================
    // BRAM Write Logic (Port A - GDDR6 to BRAM)
    // ===================================================================
    logic [10:0] bram_wr_addr_reg;
    logic [MAN_WIDTH-1:0] bram_wr_data_reg;
    logic        bram_wr_en_reg;
    logic        bram_wr_target_reg;

    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            bram_wr_addr_reg <= '0;
            bram_wr_data_reg <= '0;
            bram_wr_en_reg <= 1'b0;
            bram_wr_target_reg <= 1'b0;
        end else begin
            bram_wr_en_reg <= 1'b0;  // Default

            if (state_reg == ST_FETCH_ACTIVE && axi_ddr_if.rvalid && axi_ddr_if.rready && lines_received < 528) begin
                `ifdef SIMULATION
                // Detailed debug for all BRAM writes
                $display("[FETCHER_OPT_BRAM] @%0t lines_rcv=%0d, exp_cnt=%0d, man_cnt=%0d, cond=%b, addr_calc=%0d, data[31:0]=0x%08x",
                         $time, lines_received, exp_lines_received, man_lines_received,
                         (lines_received < 16),
                         (lines_received < 16) ? {7'd0, exp_lines_received[3:0]} : ({2'd0, man_lines_received[8:0]} + 11'd16),
                         axi_ddr_if.rdata[31:0]);
                `endif

                // Write data to BRAM
                if (lines_received < 16) begin
                    bram_wr_addr_reg <= {7'd0, exp_lines_received[3:0]};  // 0-15
                end else begin
                    bram_wr_addr_reg <= {2'd0, man_lines_received[8:0]} + 11'd16;  // 16-527
                end
                bram_wr_data_reg <= axi_ddr_if.rdata;
                bram_wr_en_reg <= 1'b1;
                // FIX: Use registered target for current burst
                // r_target_current_burst is loaded at first beat of each burst from R-target FIFO
                // This ensures correct target even when new FETCH overwrites fetch_target_reg
                bram_wr_target_reg <= r_target_current_burst;
            end
        end
    end

    assign o_bram_wr_data = bram_wr_data_reg;
    assign o_bram_wr_addr = bram_wr_addr_reg;
    assign o_bram_wr_en = bram_wr_en_reg;
    assign o_bram_wr_target = bram_wr_target_reg;

    // ===================================================================
    // Parallel Exponent Unpacking (PRESERVED FROM ORIGINAL)
    // ===================================================================
    logic [3:0]  unpack_exp_packed_rd_addr_reg;
    logic [9:0]  unpack_idx_reg;

    // Continuous unpacking counter (runs every cycle during mantissa phase)
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            unpack_idx_reg <= 10'd0;
        end else if (state_reg == ST_IDLE && i_fetch_en && !fetch_en_prev) begin
            unpack_idx_reg <= 10'd0;
        end else if (state_reg == ST_FETCH_ACTIVE && lines_received >= 16 && unpack_idx_reg < 10'd512) begin
            // Start unpacking once we're in mantissa phase (stop at 511, total 512 exponents)
            unpack_idx_reg <= unpack_idx_reg + 10'd1;
        end
    end

    // Calculate unpacking write index (1 cycle for BRAM read latency)
    logic [9:0] unpack_wr_idx;
    assign unpack_wr_idx = unpack_idx_reg - 10'd1;

    // Read address for exp_packed
    assign unpack_exp_packed_rd_addr_reg = unpack_wr_idx[9:5];  // /32

    // Extract byte offset
    logic [4:0] exp_byte_offset;
    assign exp_byte_offset = unpack_wr_idx[4:0];  // %32

    // Extract current exponent byte
    logic [7:0] current_exp_byte;
    assign current_exp_byte = i_exp_packed_rd_data[exp_byte_offset*8 +: 8];

    // Exponent write enables
    assign o_exp_left_wr_en = (state_reg == ST_FETCH_ACTIVE) &&
                              (fetch_target_reg == 1'b0) &&
                              (unpack_idx_reg >= 10'd1) &&
                              (unpack_idx_reg <= 10'd512);

    assign o_exp_right_wr_en = (state_reg == ST_FETCH_ACTIVE) &&
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

    // Debug: Trace exponent writes
    `ifdef SIMULATION
    always @(posedge i_clk) begin
        if (o_exp_left_wr_en) begin
            $display("[FETCHER_EXP_WR] @%0t LEFT exp[%0d] <= 0x%02x (unpack_idx=%0d, packed_rd_addr=%0d)",
                     $time, o_exp_left_wr_addr, o_exp_left_wr_data, unpack_idx_reg, unpack_exp_packed_rd_addr_reg);
        end
        if (o_exp_right_wr_en) begin
            $display("[FETCHER_EXP_WR] @%0t RIGHT exp[%0d] <= 0x%02x (unpack_idx=%0d, packed_rd_addr=%0d)",
                     $time, o_exp_right_wr_addr, o_exp_right_wr_data, unpack_idx_reg, unpack_exp_packed_rd_addr_reg);
        end
    end
    `endif

    `ifdef SIMULATION
    // Debug exponent writes
    always @(posedge i_clk) begin
        if (o_exp_left_wr_en) begin
            $display("[FETCHER_OPT_EXP] @%0t LEFT exp write: addr=%0d, data=0x%02x, unpack_idx=%0d, unpack_wr_idx=%0d",
                     $time, o_exp_left_wr_addr, o_exp_left_wr_data, unpack_idx_reg, unpack_wr_idx);
        end
        if (o_exp_right_wr_en) begin
            $display("[FETCHER_OPT_EXP] @%0t RIGHT exp write: addr=%0d, data=0x%02x, unpack_idx=%0d, unpack_wr_idx=%0d",
                     $time, o_exp_right_wr_addr, o_exp_right_wr_data, unpack_idx_reg, unpack_wr_idx);
        end
    end
    `endif

    // ===================================================================
    // AXI Write Channels (unused - tie off)
    // ===================================================================
    assign axi_ddr_if.awvalid = 1'b0;
    assign axi_ddr_if.awid = '0;
    assign axi_ddr_if.awaddr = '0;
    assign axi_ddr_if.awlen = '0;
    assign axi_ddr_if.awsize = '0;
    assign axi_ddr_if.awburst = '0;
    assign axi_ddr_if.awlock = '0;
    assign axi_ddr_if.awcache = '0;
    assign axi_ddr_if.awprot = '0;
    assign axi_ddr_if.awqos = '0;
    assign axi_ddr_if.awregion = '0;
    assign axi_ddr_if.wvalid = 1'b0;
    assign axi_ddr_if.wdata = '0;
    assign axi_ddr_if.wstrb = '0;
    assign axi_ddr_if.wlast = 1'b0;
    assign axi_ddr_if.bready = 1'b0;

    // ===================================================================
    // Fetch Done Signal
    // ===================================================================
    logic fetch_done_reg;

    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            fetch_done_reg <= 1'b0;
        end else begin
            fetch_done_reg <= (state_reg == ST_FETCH_DONE);
        end
    end

    assign o_fetch_done = fetch_done_reg;

    // ===================================================================
    // Debug Outputs
    // ===================================================================
    assign o_fetcher_state = state_reg;
    assign o_wr_addr = bram_wr_addr_reg;
    assign o_wr_en = bram_wr_en_reg;

endmodule
