// ------------------------------------------------------------------
// Dispatcher Module (New)
//
// Purpose: 2-stage stream processing from Fetcher FIFO to BRAMs
// Features:
//  - Stage-1: Buffer 16 exponent lines to local exp_bram
//  - Stage-2: Route mantissa lines with attached exponents
//  - Left path (target=0): Write to row_bram (activations)
//  - Right path (target=1): Write to mlp_bram (weights) via ready-valid
//
// Data Flow: Streaming FIFO -> Dispatcher -> row_bram / mlp_bram
//
// Memory Layout (GFP8 Block):
//  Lines 0-15:   Packed Exponents (32 bytes per line = 32 exponents)
//                Total: 16 lines × 32 = 512 exponents for 128 NVs
//  Lines 16-527: Mantissas (32 bytes per line)
//                Total: 512 lines (4 lines per NV × 128 NVs)
//
// Author: Junhao Pan
// Date: Jan 2026
// ------------------------------------------------------------------

`include "nap_interfaces.svh"

module dispatcher
import gemm_pkg::*;
#(
    parameter MAN_WIDTH = 256,
    parameter EXP_WIDTH = 8,
    parameter BRAM_DEPTH = 512,
    parameter ADDR_WIDTH = $clog2(BRAM_DEPTH)
)
(
    // Clock and Reset
    input  logic                     i_clk,
    input  logic                     i_reset_n,

    // Streaming FIFO Input Interface (ready-valid)
    input  logic                     i_fifo_valid,
    output logic                     o_fifo_ready,
    input  logic [MAN_WIDTH-1:0]     i_fifo_data,
    input  logic                     i_fifo_is_exp,    // 1=exponent line, 0=mantissa
    input  logic [9:0]               i_fifo_line_idx,  // Line index (0-527)
    input  logic                     i_fifo_target,    // 0=left, 1=right
    input  logic                     i_fifo_last,      // Last line of block

    // Block completion signal
    output logic                     o_block_done,

    // Left path: row_bram Write Interface (activations - direct write)
    output logic [ADDR_WIDTH-1:0]    o_left_man_wr_addr,
    output logic                     o_left_man_wr_en,
    output logic [MAN_WIDTH-1:0]     o_left_man_wr_data,
    output logic [ADDR_WIDTH-1:0]    o_left_exp_wr_addr,
    output logic                     o_left_exp_wr_en,
    output logic [EXP_WIDTH-1:0]     o_left_exp_wr_data,

    // Right path: mlp_bram Write Interface (weights - direct write, same as LEFT)
    output logic [ADDR_WIDTH-1:0]    o_right_man_wr_addr,
    output logic                     o_right_man_wr_en,
    output logic [MAN_WIDTH-1:0]     o_right_man_wr_data,
    output logic [ADDR_WIDTH-1:0]    o_right_exp_wr_addr,
    output logic                     o_right_exp_wr_en,
    output logic [EXP_WIDTH-1:0]     o_right_exp_wr_data,

    // Debug Interface
    output logic [3:0]               o_disp_state,
    output logic [9:0]               o_lines_processed
);

    // ===================================================================
    // State Machine Definition
    // ===================================================================
    typedef enum logic [3:0] {
        ST_IDLE        = 4'd0,
        ST_EXP_BUFFER  = 4'd1,  // Stage-1: Buffer exponent lines
        ST_MAN_ROUTE   = 4'd2,  // Stage-2: Route mantissa lines
        ST_DONE        = 4'd3
    } state_t;

    state_t state_reg, state_next;

    // ===================================================================
    // Local Parameters
    // ===================================================================
    localparam EXP_LINES = 16;           // 16 exponent lines per block
    localparam MAN_LINES = 512;          // 512 mantissa lines per block
    localparam TOTAL_LINES = 528;        // Total lines per block
    localparam EXP_PER_LINE = 32;        // 32 exponents per 256-bit line

    // ===================================================================
    // Local Exponent BRAM
    // ===================================================================
    // 16 lines × 256 bits = stores all 512 exponents (4 bytes per NV × 128 NVs)
    logic [MAN_WIDTH-1:0] exp_bram [0:EXP_LINES-1];

    // ===================================================================
    // Internal Signals
    // ===================================================================
    logic [9:0]  lines_processed;
    logic [3:0]  exp_line_cnt;       // 0-15 exponent lines buffered
    logic [8:0]  man_line_cnt;       // 0-511 mantissa lines processed
    logic        block_target_reg;   // Target for current block (latched on first line)
    logic        block_started;      // Flag: block processing started

    // Exponent lookup signals
    logic [6:0]  nv_idx;             // NV index (0-127) for current mantissa line
    logic [3:0]  exp_line_addr;      // Which exp line (0-15) contains this NV's exponent
    logic [4:0]  exp_byte_offset;    // Which byte within exp line (0-31)
    logic [7:0]  current_exp;        // Extracted exponent for current mantissa

    // FIFO interface
    logic        fifo_transfer;      // Successful transfer from FIFO

    // Output path control
    logic        left_path_active;
    logic        right_path_active;
    logic        right_path_stall;   // Back-pressure from mlp_bram

    // ===================================================================
    // Combinational Logic
    // ===================================================================

    // FIFO transfer occurs when valid and ready
    assign fifo_transfer = i_fifo_valid && o_fifo_ready;

    // Path selection based on target
    assign left_path_active = !block_target_reg;   // target=0 -> left (row_bram)
    assign right_path_active = block_target_reg;   // target=1 -> right (mlp_bram)

    // Right path stalls on back-pressure (only during mantissa routing)
    assign right_path_stall = (state_reg == ST_MAN_ROUTE) && right_path_active && !i_right_ready;

    // FIFO ready: accept data unless right path is stalling
    always_comb begin
        o_fifo_ready = 1'b0;

        case (state_reg)
            ST_IDLE: begin
                // Not ready in IDLE - wait for ST_EXP_BUFFER to accept data
                // This prevents losing the first exponent line during state transition
                o_fifo_ready = 1'b0;
            end

            ST_EXP_BUFFER: begin
                // Always accept exponent lines (no back-pressure)
                o_fifo_ready = 1'b1;
            end

            ST_MAN_ROUTE: begin
                // Accept mantissa lines unless right path is stalling
                o_fifo_ready = !right_path_stall;
            end

            ST_DONE: begin
                o_fifo_ready = 1'b0;
            end

            default: o_fifo_ready = 1'b0;
        endcase
    end

    // NV index calculation from mantissa line index
    // Mantissa lines 16-527 map to NV 0-127 (4 lines per NV)
    // nv_idx = (line_idx - 16) / 4
    assign nv_idx = man_line_cnt[8:2];  // Divide by 4

    // Exponent lookup: which exp line and byte offset
    // Each exp line has 32 exponents (one per byte)
    // exp_line_addr = nv_idx / 32, exp_byte_offset = nv_idx % 32
    assign exp_line_addr = nv_idx[6:5];   // Upper 2 bits: 0-3 (but we have 16 lines, so need full mapping)
    assign exp_byte_offset = nv_idx[4:0]; // Lower 5 bits: 0-31

    // Actually, with 128 NVs and 16 exp lines:
    // Each line has 32 exponents
    // NV 0-31 -> line 0, NV 32-63 -> line 1, etc.
    // So exp_line_addr = nv_idx[6:5] is only 2 bits, giving 0-3
    // But we have 16 lines storing 512 exponents (4 exp per NV? No, 1 exp per NV)
    // Wait, 128 NVs with 1 exp each = 128 exponents
    // But the memory format says 16 lines × 32 bytes = 512 exponents
    // This is because each NV has 4 bytes of exponent (for 128 GFP8 numbers, grouped by 32)
    // So each NV has 128/32 = 4 group exponents
    // Let me recalculate:
    // - Each NV = 128 GFP8 numbers
    // - Group size = 32, so 128/32 = 4 groups per NV
    // - Each group has 1 exponent (1 byte)
    // - So 4 exponents per NV × 128 NVs = 512 exponents total
    // - 512 exponents / 32 per line = 16 exp lines ✓

    // For mantissa line within NV (0-3), we need to pick the right exponent
    // man_line_cnt[1:0] tells us which of the 4 mantissa lines within the NV
    // Each mantissa line corresponds to one group exponent
    logic [1:0] group_within_nv;
    assign group_within_nv = man_line_cnt[1:0];  // 0-3

    // Full exponent address: (nv_idx * 4 + group_within_nv) / 32 = which line
    // (nv_idx * 4 + group_within_nv) % 32 = which byte
    logic [8:0] full_exp_idx;
    assign full_exp_idx = {nv_idx, group_within_nv};  // nv_idx * 4 + group
    // full_exp_idx is 0-511
    // Line = full_exp_idx / 32 = full_exp_idx[8:5]
    // Byte = full_exp_idx % 32 = full_exp_idx[4:0]

    // Extract exponent from buffered exp_bram
    always_comb begin
        current_exp = exp_bram[full_exp_idx[8:5]][full_exp_idx[4:0] * 8 +: 8];
    end

    // ===================================================================
    // State Machine
    // ===================================================================
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            state_reg <= ST_IDLE;
        end else begin
            state_reg <= state_next;
        end
    end

    always_comb begin
        state_next = state_reg;

        case (state_reg)
            ST_IDLE: begin
                if (i_fifo_valid) begin
                    // First line of new block - should be exponent line
                    state_next = ST_EXP_BUFFER;
                    `ifdef SIMULATION
                    $display("[DISPATCHER] @%0t START: target=%0d, line_idx=%0d",
                             $time, i_fifo_target, i_fifo_line_idx);
                    `endif
                end
            end

            ST_EXP_BUFFER: begin
                // Buffer exponent lines until all 16 received
                if (fifo_transfer && exp_line_cnt == (EXP_LINES - 1)) begin
                    state_next = ST_MAN_ROUTE;
                    `ifdef SIMULATION
                    $display("[DISPATCHER] @%0t EXP_BUFFER complete: %0d lines buffered", $time, exp_line_cnt+1);
                    `endif
                end
            end

            ST_MAN_ROUTE: begin
                // Route mantissa lines until all 512 processed or last flag
                if (fifo_transfer && (man_line_cnt == (MAN_LINES - 1) || i_fifo_last)) begin
                    state_next = ST_DONE;
                    `ifdef SIMULATION
                    $display("[DISPATCHER] @%0t MAN_ROUTE complete: %0d lines, last=%0b", $time, man_line_cnt+1, i_fifo_last);
                    `endif
                end
            end

            ST_DONE: begin
                state_next = ST_IDLE;
                `ifdef SIMULATION
                $display("[DISPATCHER] @%0t BLOCK DONE: total_lines=%0d", $time, lines_processed);
                `endif
            end

            default: state_next = ST_IDLE;
        endcase
    end

    // ===================================================================
    // Data Path Processing
    // ===================================================================
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            exp_line_cnt <= '0;
            man_line_cnt <= '0;
            lines_processed <= '0;
            block_target_reg <= 1'b0;
            block_started <= 1'b0;

            // Clear exp_bram
            for (int i = 0; i < EXP_LINES; i++) begin
                exp_bram[i] <= '0;
            end
        end else begin
            case (state_reg)
                ST_IDLE: begin
                    if (i_fifo_valid) begin
                        // Latch target from first line
                        block_target_reg <= i_fifo_target;
                        block_started <= 1'b1;
                        exp_line_cnt <= '0;
                        man_line_cnt <= '0;
                        lines_processed <= '0;
                    end
                end

                ST_EXP_BUFFER: begin
                    if (fifo_transfer) begin
                        // Store exponent line in local buffer
                        exp_bram[exp_line_cnt] <= i_fifo_data;
                        exp_line_cnt <= exp_line_cnt + 1;
                        lines_processed <= lines_processed + 1;
                        `ifdef SIMULATION
                        if (exp_line_cnt < 2)
                            $display("[DISPATCHER] @%0t EXP_STORE: exp_bram[%0d] = line_idx=%0d, data[31:0]=0x%08x",
                                     $time, exp_line_cnt, i_fifo_line_idx, i_fifo_data[31:0]);
                        `endif
                    end
                end

                ST_MAN_ROUTE: begin
                    if (fifo_transfer) begin
                        man_line_cnt <= man_line_cnt + 1;
                        lines_processed <= lines_processed + 1;
                        `ifdef SIMULATION
                        if (man_line_cnt < 5 || man_line_cnt >= 507)
                            $display("[DISPATCHER] @%0t MAN_ROUTE: man_line=%0d, valid=%0b, ready=%0b",
                                     $time, man_line_cnt, i_fifo_valid, o_fifo_ready);
                        `endif
                    end
                end

                ST_DONE: begin
                    block_started <= 1'b0;
                end

                default: begin
                end
            endcase
        end
    end

    // ===================================================================
    // Left Path Output (row_bram - Direct Write)
    // ===================================================================
    // Mantissa write
    logic        left_man_wr_en_reg;
    logic [8:0]  left_man_wr_addr_reg;
    logic [MAN_WIDTH-1:0] left_man_wr_data_reg;

    // Exponent write
    logic        left_exp_wr_en_reg;
    logic [8:0]  left_exp_wr_addr_reg;
    logic [7:0]  left_exp_wr_data_reg;

    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            left_man_wr_en_reg <= 1'b0;
            left_man_wr_addr_reg <= '0;
            left_man_wr_data_reg <= '0;
            left_exp_wr_en_reg <= 1'b0;
            left_exp_wr_addr_reg <= '0;
            left_exp_wr_data_reg <= '0;
        end else begin
            // Default: no writes
            left_man_wr_en_reg <= 1'b0;
            left_exp_wr_en_reg <= 1'b0;

            if (state_reg == ST_MAN_ROUTE && fifo_transfer && left_path_active) begin
                // Write mantissa to row_bram
                left_man_wr_en_reg <= 1'b1;
                left_man_wr_addr_reg <= man_line_cnt[8:0];
                left_man_wr_data_reg <= i_fifo_data;

                // Write exponent to row_bram
                left_exp_wr_en_reg <= 1'b1;
                left_exp_wr_addr_reg <= man_line_cnt[8:0];
                left_exp_wr_data_reg <= current_exp;
                `ifdef SIMULATION
                if (man_line_cnt < 4)
                    $display("[DISPATCHER] @%0t LEFT_WR: addr=%0d, exp=0x%02x (exp_idx=%0d, nv=%0d, grp=%0d), man[31:0]=0x%08x, line_idx=%0d",
                             $time, man_line_cnt[8:0], current_exp, full_exp_idx, nv_idx, group_within_nv,
                             i_fifo_data[31:0], i_fifo_line_idx);
                `endif
            end
        end
    end

    // Output assignments
    assign o_left_man_wr_en = left_man_wr_en_reg;
    assign o_left_man_wr_addr = left_man_wr_addr_reg;
    assign o_left_man_wr_data = left_man_wr_data_reg;
    assign o_left_exp_wr_en = left_exp_wr_en_reg;
    assign o_left_exp_wr_addr = left_exp_wr_addr_reg;
    assign o_left_exp_wr_data = left_exp_wr_data_reg;

    // ===================================================================
    // Right Path Output (mlp_bram - Ready-Valid)
    // ===================================================================
    logic        right_valid_reg;
    logic [MAN_WIDTH-1:0] right_man_data_reg;
    logic [7:0]  right_exp_data_reg;
    logic [8:0]  right_addr_reg;
    logic        right_last_reg;

    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            right_valid_reg <= 1'b0;
            right_man_data_reg <= '0;
            right_exp_data_reg <= '0;
            right_addr_reg <= '0;
            right_last_reg <= 1'b0;
        end else begin
            // Handle valid signal with handshake
            if (right_valid_reg && i_right_ready) begin
                // Transfer complete, clear valid and last
                right_valid_reg <= 1'b0;
                right_last_reg <= 1'b0;
            end

            if (state_reg == ST_MAN_ROUTE && fifo_transfer && right_path_active) begin
                // New data to send
                right_valid_reg <= 1'b1;
                right_man_data_reg <= i_fifo_data;
                right_exp_data_reg <= current_exp;
                right_addr_reg <= man_line_cnt[8:0];
                // Set last flag if this is the final line (count reaches 511 or fifo signals last)
                right_last_reg <= (man_line_cnt == (MAN_LINES - 1)) || i_fifo_last;
                `ifdef SIMULATION
                if (man_line_cnt < 4)
                    $display("[DISPATCHER] @%0t RIGHT_WR: addr=%0d, exp=0x%02x, man[31:0]=0x%08x, ready=%0b",
                             $time, man_line_cnt[8:0], current_exp, i_fifo_data[31:0], i_right_ready);
                `endif
            end
        end
    end

    // Output assignments
    assign o_right_valid = right_valid_reg;
    assign o_right_man_data = right_man_data_reg;
    assign o_right_exp_data = right_exp_data_reg;
    assign o_right_addr = right_addr_reg;
    assign o_right_last = right_last_reg;

    // ===================================================================
    // Block Done Signal
    // ===================================================================
    logic block_done_reg;

    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            block_done_reg <= 1'b0;
        end else begin
            block_done_reg <= (state_reg == ST_DONE);
        end
    end

    assign o_block_done = block_done_reg;

    // ===================================================================
    // Debug Outputs
    // ===================================================================
    assign o_disp_state = state_reg;
    assign o_lines_processed = lines_processed;

endmodule
