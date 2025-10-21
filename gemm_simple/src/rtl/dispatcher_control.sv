// ------------------------------------------------------------------
// Dispatcher Control Module (MS2.0)
//
// Purpose: DDR fetch and BRAM buffering for MS2.0 architecture
// Features:
//  - FETCH command: Read GFP8 block (528 lines × 256-bit) from DDR to BRAM
//  - DISP command: Acknowledge vector dispatch configuration
//  - Dual-port BRAM: Port A (write from DDR), Port B (read by CE)
//  - AXI4 burst read interface for DDR access
//  - Sequential buffer access: Fetch complete → done → CE reads
//
// Memory Layout (GFP8 Block):
//  Lines 0-15:   Exponents (512 total, 32 per line)
//  Lines 16-527: Mantissas (128 rows × 4 groups/row = 512 lines)
//
// Author: MS2.0 Migration
// Date: Thu Oct 2 00:14:43 AM PDT 2025
// ------------------------------------------------------------------

`include "nap_interfaces.svh"

module dispatcher_control
import gemm_pkg::*;
#(
    parameter TGT_DATA_WIDTH = 256,    // Target data width (256-bit AXI)
    parameter AXI_ADDR_WIDTH = 42,     // AXI address width (42-bit for GDDR6 NoC: {Page[9], Line[26], Pad[2], Byte[5]})
    parameter BRAM_DEPTH = 2048,       // Increased from 528 to support both left+right matrices (1056 total, rounded to power of 2)
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
    input  logic [tile_mem_addr_width_gp-1:0] i_disp_addr,
    input  logic [tile_mem_addr_width_gp-1:0] i_disp_len,
    input  logic                         i_man_4b_8b_n,
    output logic                         o_disp_done,

    // ====================================================================
    // Dual BRAM Read Ports (for Compute Engine - parallel access)
    // ====================================================================
    // Port B: Left matrix mantissa read
    input  logic [10:0]                  i_bram_rd_addr_left,
    output logic [TGT_DATA_WIDTH-1:0]    o_bram_rd_data_left,
    input  logic                         i_bram_rd_en_left,
    
    // Port C: Right matrix mantissa read
    input  logic [10:0]                  i_bram_rd_addr_right,
    output logic [TGT_DATA_WIDTH-1:0]    o_bram_rd_data_right,
    input  logic                         i_bram_rd_en_right,
    
    // ====================================================================
    // NEW: Exponent BRAM Write Ports (for post-fetch unpacking)
    // ====================================================================
    output logic [8:0]                   o_left_exp_wr_addr,
    output logic [7:0]                   o_left_exp_wr_data,
    output logic                         o_left_exp_wr_en,
    
    output logic [8:0]                   o_right_exp_wr_addr,
    output logic [7:0]                   o_right_exp_wr_data,
    output logic                         o_right_exp_wr_en,

    // ====================================================================
    // NEW: Exponent BRAM Read Ports (from Compute Engine)
    // ====================================================================
    input  logic [8:0]                   i_left_exp_rd_addr,
    output logic [7:0]                   o_left_exp_rd_data,
    
    input  logic [8:0]                   i_right_exp_rd_addr,
    output logic [7:0]                   o_right_exp_rd_data,

    // ====================================================================
    // AXI-4 Initiator Interface for DDR access
    // ====================================================================
    t_AXI4.initiator                     axi_ddr_if,

    // ====================================================================
    // Debug Interface
    // ====================================================================
    output logic [3:0]                   o_dc_state,
    output logic [9:0]                   o_bram_wr_count,
    output logic [10:0]                  o_bram_wr_addr,    // Debug: BRAM write address (for gemm)
    output logic                         o_bram_wr_en       // Debug: BRAM write enable (for gemm)
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
        ST_DISP_ACK        = 4'd6
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
    logic [TGT_DATA_WIDTH-1:0] bram_wr_data_reg;
    logic        bram_wr_en_reg;
    logic        bram_wr_target_reg;  // 0=left, 1=right
    logic [TGT_DATA_WIDTH-1:0] bram_rd_data_wire;

    // FETCH command tracking
    logic [link_addr_width_gp-1:0] fetch_addr_reg;
    logic        fetch_target_reg;  // 0=left, 1=right (captured from i_fetch_target)
    logic [10:0] current_line_reg;  // Increased from 10 to 11 bits for 2048-entry BRAM
    
    // NEW: Counters for tracking exp and mantissa lines during fetch
    logic [4:0]  exp_lines_fetched_reg;   // 0-15: exponent lines fetched
    logic [9:0]  man_lines_fetched_reg;   // 0-511: mantissa lines fetched

    // AXI transaction control
    logic axi_ar_req_reg;
    logic axi_r_ready_reg;
    logic [7:0] beat_count_reg;

    // DISP command tracking
    logic [tile_mem_addr_width_gp-1:0] disp_addr_reg;
    logic [tile_mem_addr_width_gp-1:0] disp_len_reg;
    logic disp_man_4b_reg;

    // Status flags
    logic fetch_done_reg;
    logic disp_done_reg;

    // Edge detection for command enables (prevent double-triggering)
    logic fetch_en_prev;
    logic disp_en_prev;
    
    // NEW: Parallel unpacking signals (for 3-buffer architecture)
    logic [3:0]  unpack_exp_packed_rd_addr_reg; // 0-15: which exp_packed line to read
    logic [TGT_DATA_WIDTH-1:0] exp_packed_rd_data_wire; // Data from exp_packed BRAM

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
                    state_next = ST_DISP_ACK;
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
                // Read mantissa bursts (32 bursts × 16 beats = 512 lines) + parallel unpack
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

            ST_DISP_ACK: begin
                // Acknowledge DISP command (1 cycle)
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

            disp_addr_reg <= '0;
            disp_len_reg <= '0;
            disp_man_4b_reg <= 1'b0;
            disp_done_reg <= 1'b0;
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
                    end

                    if (i_disp_en) begin
                        disp_addr_reg <= i_disp_addr;
                        disp_len_reg <= i_disp_len;
                        disp_man_4b_reg <= i_man_4b_8b_n;
                        
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

                ST_DISP_ACK: begin
                    // Acknowledge DISP command (configuration stored)
                    disp_done_reg <= 1'b1;
                    current_line_reg <= '0;
                    
                    // Reset phase counters for new fetch
                    exp_lines_fetched_reg <= '0;
                    man_lines_fetched_reg <= '0;
                end
            endcase
        end
    end

    assign o_fetch_done = fetch_done_reg;

    // // ===================================================================
    // // DISP Command Processing
    // // ===================================================================
    // always_ff @(posedge i_clk) begin
    //     if (~i_reset_n) begin
    //         disp_addr_reg <= '0;
    //         disp_len_reg <= '0;
    //         disp_man_4b_reg <= 1'b0;
    //         disp_done_reg <= 1'b0;
    //     end else begin
    //         disp_done_reg <= 1'b0;  // Default

    //         case (state_reg)
    //             ST_IDLE: begin
    //                 if (i_disp_en) begin
    //                     disp_addr_reg <= i_disp_addr;
    //                     disp_len_reg <= i_disp_len;
    //                     disp_man_4b_reg <= i_man_4b_8b_n;
                        
    //                 end

    //             end

    //             ST_DISP_ACK: begin
    //                 // Acknowledge DISP command (configuration stored)
    //                 disp_done_reg <= 1'b1;
    //                 current_line_reg <= '0;
                    
    //                 // Reset phase counters for new fetch
    //                 exp_lines_fetched_reg <= '0;
    //                 man_lines_fetched_reg <= '0;
    //             end
    //         endcase
    //     end
    // end

    assign o_disp_done = disp_done_reg;

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
    assign o_left_exp_wr_en = (state_reg == ST_FETCH_READ_MAN) && 
                              (fetch_target_reg == 1'b0) &&
                              (unpack_idx_reg >= 10'd1) &&
                              (unpack_idx_reg <= 10'd512);
    
    assign o_right_exp_wr_en = (state_reg == ST_FETCH_READ_MAN) && 
                               (fetch_target_reg == 1'b1) &&
                               (unpack_idx_reg >= 10'd1) &&
                               (unpack_idx_reg <= 10'd512);
    
    // Exponent write addresses
    assign o_left_exp_wr_addr = unpack_wr_idx[8:0];
    assign o_right_exp_wr_addr = unpack_wr_idx[8:0];
    
    // Exponent write data
    assign o_left_exp_wr_data = current_exp_byte;
    assign o_right_exp_wr_data = current_exp_byte;

    `ifdef SIMULATION
    always @(posedge i_clk) begin
        if (o_left_exp_wr_en) begin
            $display("[DISP_UNPACK] @%0t LEFT exp write: addr=%0d, data=0x%02x, packed_rd_addr=%0d, byte_offset=%0d, unpack_wr_idx=%0d",
                     $time, o_left_exp_wr_addr, o_left_exp_wr_data, unpack_exp_packed_rd_addr_reg, exp_byte_offset, unpack_wr_idx);
        end
        if (o_right_exp_wr_en) begin
            $display("[DISP_UNPACK] @%0t RIGHT exp write: addr=%0d, data=0x%02x, packed_rd_addr=%0d, byte_offset=%0d, unpack_wr_idx=%0d, fetch_target_reg=%0d, exp_packed_rd_data_wire first 4 bytes=%02x %02x %02x %02x",
                     $time, o_right_exp_wr_addr, o_right_exp_wr_data, unpack_exp_packed_rd_addr_reg, exp_byte_offset, unpack_wr_idx, fetch_target_reg,
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
    dispatcher_bram_dual_read #(
        .DATA_WIDTH          (TGT_DATA_WIDTH),
        .EXP_PACKED_DEPTH    (16),
        .EXP_ALIGNED_DEPTH   (512),
        .MANTISSA_DEPTH      (512),
        .ADDR_WIDTH          (11)
    ) u_dispatcher_bram (
        // Single clock for all ports
        .i_clk              (i_clk),
        
        // Write ports (from DDR fetch)
        .i_wr_data          (bram_wr_data_reg),
        .i_wr_addr          (bram_wr_addr_reg),
        .i_wr_en            (bram_wr_en_reg),
        .i_wr_target        (bram_wr_target_reg),  // NEW: 0=left, 1=right
        
        // Exponent aligned write ports (from unpacking logic)
        .i_left_exp_aligned_wr_addr  (o_left_exp_wr_addr),
        .i_left_exp_aligned_wr_data  (o_left_exp_wr_data),
        .i_left_exp_aligned_wr_en    (o_left_exp_wr_en),
        
        .i_right_exp_aligned_wr_addr (o_right_exp_wr_addr),
        .i_right_exp_aligned_wr_data (o_right_exp_wr_data),
        .i_right_exp_aligned_wr_en   (o_right_exp_wr_en),
    
        // Read ports (to CE) - mantissas
        .i_rd_addr_left     (i_bram_rd_addr_left),  // Use full 11-bit address
        .i_rd_en_left       (i_bram_rd_en_left),
        .o_rd_data_left     (o_bram_rd_data_left),
        
        .i_rd_addr_right    (i_bram_rd_addr_right), // Use full 11-bit address
        .i_rd_en_right      (i_bram_rd_en_right),
        .o_rd_data_right    (o_bram_rd_data_right),
        
        // Read ports (to CE) - exponents
        .i_left_exp_rd_addr  (i_left_exp_rd_addr),
        .o_left_exp_rd_data  (o_left_exp_rd_data),
        
        .i_right_exp_rd_addr (i_right_exp_rd_addr),
        .o_right_exp_rd_data (o_right_exp_rd_data),
        
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
    assign o_bram_wr_count = current_line_reg;
    assign o_bram_wr_addr = bram_wr_addr_reg;   // Debug output (for gemm)
    assign o_bram_wr_en = bram_wr_en_reg;       // Debug output (for gemm)

    // ===================================================================
    // Assertions (for simulation only)
    // ===================================================================

    `ifdef SIM
        // Check BRAM write overflow
        property no_bram_overflow;
            @(posedge i_clk) disable iff (~i_reset_n)
            (bram_wr_en_reg) |-> (bram_wr_addr_reg < BRAM_DEPTH);
        endproperty
        assert property (no_bram_overflow) else
            $error("[DISPATCHER_CONTROL] BRAM write address overflow: %0d >= %0d",
                   bram_wr_addr_reg, BRAM_DEPTH);

        // Check BRAM read overflow
        property no_bram_read_overflow;
            @(posedge i_clk) disable iff (~i_reset_n)
            (i_bram_rd_en) |-> (i_bram_rd_addr < BRAM_DEPTH);
        endproperty
        assert property (no_bram_read_overflow) else
            $error("[DISPATCHER_CONTROL] BRAM read address overflow: %0d >= %0d",
                   i_bram_rd_addr, BRAM_DEPTH);

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

            if (state_reg == ST_DISP_ACK) begin
                $display("[DISPATCHER_CONTROL] DISP: addr=%0d, len=%0d, man_4b=%0b",
                         disp_addr_reg, disp_len_reg, disp_man_4b_reg);
            end
        end
    `endif

endmodule : dispatcher_control
