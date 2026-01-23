// ------------------------------------------------------------------
// Dispatcher 2D Module (Revised)
//
// Purpose: 2-stage stream processing from Fetcher FIFO to BRAMs
// Features:
//  - Stage-1: Buffer 16 exponent lines to local exp_bram
//  - Stage-2: Route mantissa lines with attached exponents
//  - Left path (disp_right=0): Write to row_bram (activations) - sequential
//  - Right path (disp_right=1): Write to 16 col_brams (weights) - round-robin
//
// FIFO Interface Note:
//  - flex_fifo has 1-cycle read latency
//  - Cycle N: Assert rd_en when FIFO not empty
//  - Cycle N+1: Data is valid on rd_data
//  - Use data_valid pipeline signal to track valid data
//
// Data Flow: flex_fifo -> Dispatcher -> row_bram / col_brams
//
// Memory Layout (GFP8 Block - 528 lines):
//  Lines 0-15:   Packed Exponents (32 bytes per line = 32 exponents)
//                Total: 16 lines x 32 = 512 exponents for 128 NVs
//  Lines 16-527: Mantissas (32 bytes per line)
//                Total: 512 lines (4 lines per NV x 128 NVs)
//
// LEFT Path (Activations):
//  - Sequential write to row_bram
//  - Address: tile_addr + line_idx (0, 1, 2, ...)
//
// RIGHT Path (Weights):
//  - Round-robin distribution to 16 column BRAMs
//  - col_sel cycles 0 -> (nv_cnt-1), wraps and increments wraddr_start
//  - Address: wraddr_start + v*4 + l
//  - 16 separate write enables (one-hot)
//
// Author: Junhao Pan
// Date: Jan 2026
// ------------------------------------------------------------------

`timescale 1ps / 1ps
`default_nettype none

module dispatcher_2d
#(
    parameter MAN_WIDTH  = 256,
    parameter EXP_WIDTH  = 8,
    parameter BRAM_DEPTH = 512,
    parameter NUM_COLS   = 16,           // Number of columns for RIGHT path round-robin wrap
    parameter ADDR_WIDTH = $clog2(BRAM_DEPTH)
)(
    // Clock and Reset
    input  logic                     i_clk,
    input  logic                     i_reset_n,

    // =========================================================================
    // Command Parameters (from wrapper)
    // =========================================================================
    input  logic                     i_disp_start,      // Trigger dispatch
    input  logic [15:0]              i_nv_cnt,          // B (left) or C (right) count
    input  logic [15:0]              i_ugd_len,         // V count (NVs per UGD)
    input  logic [3:0]               i_col_start,       // Starting column for round-robin (0-15)
    input  logic                     i_disp_right,      // 0=Left, 1=Right
    input  logic [ADDR_WIDTH-1:0]    i_tile_addr,       // Base write address
    output logic                     o_disp_done,       // Dispatch complete

    // =========================================================================
    // FIFO Read Interface (from flex_fifo - 1 cycle read latency)
    // =========================================================================
    input  logic [MAN_WIDTH-1:0]     i_fifo_rd_data,
    input  logic                     i_fifo_empty,
    output logic                     o_fifo_rd_en,

    // =========================================================================
    // Left Path: row_bram Write Interface (activations - direct write)
    // =========================================================================
    output logic [ADDR_WIDTH-1:0]    o_left_man_wr_addr,
    output logic                     o_left_man_wr_en,
    output logic [MAN_WIDTH-1:0]     o_left_man_wr_data,
    output logic [ADDR_WIDTH-1:0]    o_left_exp_wr_addr,
    output logic                     o_left_exp_wr_en,
    output logic [EXP_WIDTH-1:0]     o_left_exp_wr_data,

    // =========================================================================
    // Right Path: 16 Column BRAMs Write Interface (weights - direct write)
    // =========================================================================
    output logic [ADDR_WIDTH-1:0]    o_right_wr_addr,       // Shared address bus
    output logic [NUM_COLS-1:0]      o_right_wr_en,         // 16 separate write enables (one-hot)
    output logic [MAN_WIDTH-1:0]     o_right_man_wr_data,   // Shared data bus
    output logic [EXP_WIDTH-1:0]     o_right_exp_wr_data,   // Shared exponent

    // =========================================================================
    // Debug Interface
    // =========================================================================
    output logic [3:0]               o_disp_state,
    output logic [15:0]              o_lines_processed
);

    // ===================================================================
    // State Machine Definition
    // ===================================================================
    typedef enum logic [3:0] {
        ST_IDLE        = 4'd0,
        ST_EXP_BUFFER  = 4'd1,  // Stage-1: Buffer exponent lines
        ST_MAN_ROUTE   = 4'd2,  // Stage-2: Route mantissa lines
        ST_DRAIN       = 4'd3,  // Stage-3: Drain leftover FIFO data (for partial blocks)
        ST_DONE        = 4'd4
    } state_t;

    state_t state_reg, state_next;

    // ===================================================================
    // Local Parameters
    // ===================================================================
    localparam EXP_LINES = 16;           // 16 exponent lines per block
    localparam LINES_PER_NV = 4;         // 4 mantissa lines per NV

    // ===================================================================
    // Local Exponent BRAM
    // ===================================================================
    // 16 lines x 256 bits = stores all 512 exponents (4 bytes per NV x 128 NVs)
    logic [MAN_WIDTH-1:0] exp_bram [0:EXP_LINES-1];

    // Simulation: initialize exp_bram to zero
    `ifdef SIMULATION
    initial begin
        for (int i = 0; i < EXP_LINES; i++) begin
            exp_bram[i] = '0;
        end
    end
    `endif

    // ===================================================================
    // Command Registers (latched on i_disp_start)
    // ===================================================================
    logic [15:0]             nv_cnt_reg;         // B or C count
    logic [15:0]             ugd_len_reg;        // V count
    logic [3:0]              col_start_reg;      // Starting column
    logic                    disp_right_reg;     // 0=Left, 1=Right
    logic [ADDR_WIDTH-1:0]   tile_addr_reg;      // Base write address

    // ===================================================================
    // Counter Registers
    // ===================================================================
    logic [3:0]              exp_line_cnt;       // 0-15 exponent lines received
    logic [4:0]              exp_reads_issued;   // 0-16 exp reads issued (use 5 bits for 16)
    logic [15:0]             man_reads_issued;   // Mantissa reads issued
    logic [15:0]             lines_processed;    // Total lines processed
    
    // Loop counters for mantissa routing
    logic [15:0]             c_cnt;              // C or B counter (outer loop)
    logic [15:0]             v_cnt;              // V counter (middle loop)
    logic [1:0]              l_cnt;              // L counter (inner loop, 0-3)
    
    // RIGHT path specific
    logic [3:0]              col_sel;            // Current column (0-15)
    logic [ADDR_WIDTH-1:0]   wraddr_start;       // Base address (increments on wrap)

    // ===================================================================
    // FIFO Read Pipeline (handles 1-cycle read latency)
    // ===================================================================
    logic                    fifo_rd_en_reg;     // Registered rd_en output
    logic                    data_valid;         // Data is valid (rd_en delayed by 1)
    logic                    data_valid_d1;      // For state transition tracking
    logic                    data_is_exp;        // Data arriving is for exp phase (pipelined from in_exp_phase)
    
    // Pipeline the rd_en to create data_valid
    // Also pipeline in_exp_phase to track whether data is exp or mantissa
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            data_valid <= 1'b0;
            data_valid_d1 <= 1'b0;
            data_is_exp <= 1'b1;
        end else begin
            data_valid <= fifo_rd_en_reg;
            data_valid_d1 <= data_valid;
            // When we issue a read, record whether it's exp or mantissa phase
            // This follows the data through the pipeline
            if (fifo_rd_en_reg) begin
                data_is_exp <= in_exp_phase;
            end
        end
    end

    // ===================================================================
    // Computed Values
    // ===================================================================
    logic [15:0]             total_man_lines;    // nv_cnt * ugd_len * 4
    logic                    is_last_line;       // Last mantissa line
    logic [ADDR_WIDTH-1:0]   left_addr;          // LEFT: sequential address
    logic [ADDR_WIDTH-1:0]   right_addr;         // RIGHT: wraddr_start + v*4 + l

    // Total mantissa lines = nv_cnt * ugd_len * 4
    assign total_man_lines = nv_cnt_reg * ugd_len_reg * LINES_PER_NV;
    
    // Last line detection - based on counters, not data
    assign is_last_line = (c_cnt == nv_cnt_reg - 1) && 
                          (v_cnt == ugd_len_reg - 1) && 
                          (l_cnt == LINES_PER_NV - 1);

    // LEFT: Sequential address = tile_addr + line_idx
    // line_idx = c_cnt * ugd_len * 4 + v_cnt * 4 + l_cnt
    logic [15:0] left_line_idx;
    assign left_line_idx = c_cnt * ugd_len_reg * LINES_PER_NV + v_cnt * LINES_PER_NV + l_cnt;
    assign left_addr = tile_addr_reg + left_line_idx[ADDR_WIDTH-1:0];

    // RIGHT: wraddr = wraddr_start + v*4 + l
    assign right_addr = wraddr_start + v_cnt[ADDR_WIDTH-3:0] * LINES_PER_NV + l_cnt;

    // ===================================================================
    // Exponent Lookup
    // ===================================================================
    // Reference: MULTI_ROW_REFERENCE.md - "Exponent Indexing" section
    //
    // Memory Block stores 128 NVs in UGD-major order (B-major for left, C-major for right).
    // Exponents are packed in the first 16 lines (512 bytes = 128 NVs x 4 bytes/NV).
    //
    // Layout for nv_cnt UGDs, each with ugd_len NVs:
    //   Bytes 0 to (ugd_len*4 - 1):               UGD 0, V=[0..ugd_len-1], L=[0..3]
    //   Bytes (ugd_len*4) to (2*ugd_len*4 - 1):   UGD 1, V=[0..ugd_len-1], L=[0..3]
    //   ...
    //
    // Formula: exp_idx = c_cnt * ugd_len * 4 + v_cnt * 4 + l_cnt
    //          (same structure as mantissa line indexing within a block)
    //
    // Constraint: nv_cnt * ugd_len <= 128 (one memory block = 128 NVs max)
    //             => max exp_idx = 511, fits in 9 bits
    // ===================================================================
    logic [15:0] exp_idx_full;   // Full-width calculation to avoid overflow
    logic [8:0]  full_exp_idx;   // Truncated to valid range [0..511]
    logic [7:0]  current_exp;
    
    // Exponent index = c_cnt * ugd_len * 4 + v_cnt * 4 + l_cnt
    assign exp_idx_full = c_cnt * ugd_len_reg * LINES_PER_NV + v_cnt * LINES_PER_NV + {14'b0, l_cnt};
    assign full_exp_idx = exp_idx_full[8:0];
    
    // Extract exponent byte from buffered exp_bram
    // exp_bram[line][byte]: line = exp_idx / 32, byte = exp_idx % 32
    always_comb begin
        current_exp = exp_bram[full_exp_idx[8:5]][full_exp_idx[4:0] * 8 +: 8];
    end

    // ===================================================================
    // FIFO Read Control
    // ===================================================================
    // Assert rd_en when we can accept data (state allows it and FIFO not empty)
    // Use reads_issued counters to prevent issuing extra reads during transitions
    logic can_read;
    logic [15:0] total_man_reads_needed;
    
    assign total_man_reads_needed = nv_cnt_reg * ugd_len_reg * LINES_PER_NV;
    
    always_comb begin
        can_read = 1'b0;

        case (state_reg)
            ST_EXP_BUFFER: begin
                // Read exponent lines - stop when we've issued all 16
                can_read = !i_fifo_empty && (exp_reads_issued < EXP_LINES);
            end

            ST_MAN_ROUTE: begin
                // Read mantissa lines - stop when we've issued all needed
                can_read = !i_fifo_empty && (man_reads_issued < total_man_reads_needed);
            end

            ST_DRAIN: begin
                // Drain any leftover data from FIFO (discarded, not processed)
                // This handles partial blocks where nv_cnt*ugd_len*4 < 512
                can_read = !i_fifo_empty;
            end

            default: begin
                can_read = 1'b0;
            end
        endcase
    end

    // Register the rd_en output
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            fifo_rd_en_reg <= 1'b0;
        end else begin
            fifo_rd_en_reg <= can_read;
            
        end
    end
    
    assign o_fifo_rd_en = fifo_rd_en_reg;

    // ===================================================================
    // State Machine - Transition Logic
    // ===================================================================
    always_comb begin
        state_next = state_reg;

        case (state_reg)
            ST_IDLE: begin
                if (i_disp_start) begin
                    state_next = ST_EXP_BUFFER;
                end
            end

            ST_EXP_BUFFER: begin
                // Transition when we've received the last exponent line
                // exp_line_cnt is incremented when data_valid, so check if we just received line 15
                if (data_valid && data_is_exp && exp_line_cnt == EXP_LINES - 1) begin
                    state_next = ST_MAN_ROUTE;
                end
            end

            ST_MAN_ROUTE: begin
                // Transition when we've processed all mantissa lines
                // Use lines_processed count for robust completion detection
                // (avoids timing race between is_last_line and counter updates)
                if (data_valid && !data_is_exp && (lines_processed >= total_man_lines - 1)) begin
                    // Go to DRAIN state to empty any leftover FIFO data
                    // This is critical for partial blocks where nv_cnt*ugd_len*4 < 512
                    state_next = ST_DRAIN;

                    // synthesis translate_off
                    `ifdef DEBUG_DISPATCHER
                    $display("[DISPATCHER] @%0t COMPLETING MAN_ROUTE: lines_processed=%0d, total_man_lines=%0d -> DRAIN",
                             $time, lines_processed, total_man_lines);
                    `endif
                    // synthesis translate_on
                end
            end

            ST_DRAIN: begin
                // Drain any leftover FIFO data (discarded, not processed)
                // Transition to DONE when FIFO is empty (or after pipeline drains)
                // data_valid being low for 2 cycles indicates FIFO is drained
                if (i_fifo_empty && !data_valid && !fifo_rd_en_reg) begin
                    state_next = ST_DONE;

                    // synthesis translate_off
                    `ifdef DEBUG_DISPATCHER
                    $display("[DISPATCHER] @%0t DRAIN complete -> DONE", $time);
                    `endif
                    // synthesis translate_on
                end
            end

            ST_DONE: begin
                state_next = ST_IDLE;
            end

            default: state_next = ST_IDLE;
        endcase
    end

    // ===================================================================
    // State Machine - Sequential Logic
    // ===================================================================
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            state_reg <= ST_IDLE;
        end else begin
            state_reg <= state_next;
        end
    end

    // ===================================================================
    // Read Issue Counter Management
    // ===================================================================
    // Track reads issued separately from data received
    // Use exp_reads_issued < EXP_LINES to determine if we're in exp phase
    logic in_exp_phase;
    assign in_exp_phase = (exp_reads_issued < EXP_LINES);
    
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            exp_reads_issued <= '0;
            man_reads_issued <= '0;
        end else begin
            if (state_reg == ST_IDLE && i_disp_start) begin
                exp_reads_issued <= '0;
                man_reads_issued <= '0;
            end else if (fifo_rd_en_reg) begin
                // Increment based on phase (determined by how many exp reads issued)
                if (in_exp_phase) begin
                    exp_reads_issued <= exp_reads_issued + 1;
                end else begin
                    man_reads_issued <= man_reads_issued + 1;
                end
            end
        end
    end

    // ===================================================================
    // Command Latching and Counter Management
    // ===================================================================
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            // Command registers
            nv_cnt_reg      <= '0;
            ugd_len_reg     <= '0;
            col_start_reg   <= '0;
            disp_right_reg  <= 1'b0;
            tile_addr_reg   <= '0;
            
            // Counters
            exp_line_cnt    <= '0;
            lines_processed <= '0;
            c_cnt           <= '0;
            v_cnt           <= '0;
            l_cnt           <= '0;
            col_sel         <= '0;
            wraddr_start    <= '0;
            
            // Clear exp_bram
            for (int i = 0; i < EXP_LINES; i++) begin
                exp_bram[i] <= '0;
            end
        end else begin
            case (state_reg)
                ST_IDLE: begin
                    if (i_disp_start) begin
                        // Latch command parameters
                        nv_cnt_reg      <= i_nv_cnt;
                        ugd_len_reg     <= i_ugd_len;
                        col_start_reg   <= i_col_start;
                        disp_right_reg  <= i_disp_right;
                        tile_addr_reg   <= i_tile_addr;
                        
                        // Initialize counters
                        exp_line_cnt    <= '0;
                        lines_processed <= '0;
                        c_cnt           <= '0;
                        v_cnt           <= '0;
                        l_cnt           <= '0;
                        col_sel         <= i_col_start;
                        wraddr_start    <= i_tile_addr;

                        // synthesis translate_off
                        `ifdef DEBUG_DISPATCHER
                        $display("[DISPATCHER] @%0t START: right=%0d, nv_cnt=%0d, ugd_len=%0d, col_start=%0d, tile_addr=%0d",
                                 $time, i_disp_right, i_nv_cnt, i_ugd_len, i_col_start, i_tile_addr);
                        `endif
                        // synthesis translate_on
                    end
                end

                ST_EXP_BUFFER, ST_MAN_ROUTE: begin
                    // Process data based on data_is_exp (pipelined from in_exp_phase when read was issued)
                    // This handles the boundary case where read was issued in exp phase
                    // but data arrives after state transition
                    
                    if (data_valid && data_is_exp) begin
                        // Store exponent line in local buffer
                        exp_bram[exp_line_cnt] <= i_fifo_rd_data;
                        exp_line_cnt <= exp_line_cnt + 1;
                        // NOTE: Do NOT increment lines_processed here!
                        // lines_processed tracks mantissa lines only, and the completion
                        // check compares against total_man_lines (mantissa count).
                        // Incrementing here causes premature completion.

                        // synthesis translate_off
                        `ifdef DEBUG_DISPATCHER
                        if (exp_line_cnt < 2)
                            $display("[DISPATCHER] @%0t EXP_STORE: exp_bram[%0d], data[31:0]=0x%08x",
                                     $time, exp_line_cnt, i_fifo_rd_data[31:0]);
                        `endif
                        // synthesis translate_on
                    end
                    
                    if (data_valid && !data_is_exp) begin
                        lines_processed <= lines_processed + 1;

                        // Advance loop counters: l -> v -> c
                        if (l_cnt == LINES_PER_NV - 1) begin
                            l_cnt <= '0;

                            if (v_cnt == ugd_len_reg - 1) begin
                                v_cnt <= '0;

                                // End of one UGD (B or C iteration)
                                if (c_cnt < nv_cnt_reg - 1) begin
                                    c_cnt <= c_cnt + 1;
                                end

                                // RIGHT path: advance col_sel after completing each UGD
                                // Data is organized by UGD: all col0 data, then all col1 data, etc.
                                // col_sel wraps at NUM_COLS (16), not nv_cnt
                                // When C > NUM_COLS, wraddr_start advances on wrap
                                if (disp_right_reg) begin
                                    if (col_sel == NUM_COLS - 1) begin
                                        // Wrap around: reset col_sel, advance wraddr_start
                                        col_sel <= '0;
                                        wraddr_start <= wraddr_start + ugd_len_reg[ADDR_WIDTH-3:0] * LINES_PER_NV;

                                        // synthesis translate_off
                                        `ifdef DEBUG_DISPATCHER
                                        $display("[DISPATCHER] @%0t COL_WRAP: col_sel->0, wraddr_start->%0d",
                                                 $time, wraddr_start + ugd_len_reg * LINES_PER_NV);
                                        `endif
                                        // synthesis translate_on
                                    end else begin
                                        col_sel <= col_sel + 1;
                                        // synthesis translate_off
                                        `ifdef DEBUG_DISPATCHER
                                        $display("[DISPATCHER] @%0t COL_INC: col_sel=%0d->%0d, c_cnt=%0d",
                                                 $time, col_sel, col_sel + 1, c_cnt);
                                        `endif
                                        // synthesis translate_on
                                    end
                                end
                            end else begin
                                v_cnt <= v_cnt + 1;
                                // synthesis translate_off
                                `ifdef DEBUG_DISPATCHER
                                if (v_cnt < 5 || v_cnt == ugd_len_reg - 2)
                                    $display("[DISPATCHER] @%0t V_INC: v=%0d->%0d, col_sel=%0d",
                                             $time, v_cnt, v_cnt + 1, col_sel);
                                `endif
                                // synthesis translate_on
                            end
                        end else begin
                            l_cnt <= l_cnt + 1;
                        end

                        // synthesis translate_off
                        `ifdef DEBUG_DISPATCHER
                        if (lines_processed < 20 || is_last_line)
                            $display("[DISPATCHER] @%0t MAN_ROUTE: c=%0d, v=%0d, l=%0d, col_sel=%0d, right_addr=%0d, left_addr=%0d",
                                     $time, c_cnt, v_cnt, l_cnt, col_sel, right_addr, left_addr);
                        `endif
                        // synthesis translate_on
                    end
                end

                ST_DONE: begin
                    // synthesis translate_off
                    `ifdef DEBUG_DISPATCHER
                    $display("[DISPATCHER] @%0t DONE: total_lines=%0d", $time, lines_processed);
                    `endif
                    // synthesis translate_on
                end

                default: begin
                end
            endcase
        end
    end

    // ===================================================================
    // Left Path Output (row_bram - Direct Write)
    // ===================================================================
    logic                     left_man_wr_en_reg;
    logic [ADDR_WIDTH-1:0]    left_man_wr_addr_reg;
    logic [MAN_WIDTH-1:0]     left_man_wr_data_reg;
    logic                     left_exp_wr_en_reg;
    logic [ADDR_WIDTH-1:0]    left_exp_wr_addr_reg;
    logic [EXP_WIDTH-1:0]     left_exp_wr_data_reg;

    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            left_man_wr_en_reg   <= 1'b0;
            left_man_wr_addr_reg <= '0;
            left_man_wr_data_reg <= '0;
            left_exp_wr_en_reg   <= 1'b0;
            left_exp_wr_addr_reg <= '0;
            left_exp_wr_data_reg <= '0;
        end else begin
            // Default: no writes
            left_man_wr_en_reg <= 1'b0;
            left_exp_wr_en_reg <= 1'b0;

            // Write when data is valid, data_is_exp is false (mantissa phase), path is LEFT,
            // and we're still in an active state (not IDLE or DONE)
            if (data_valid && !data_is_exp && !disp_right_reg && 
                (state_reg == ST_EXP_BUFFER || state_reg == ST_MAN_ROUTE)) begin
                // LEFT path: Write to row_bram
                left_man_wr_en_reg   <= 1'b1;
                left_man_wr_addr_reg <= left_addr;
                left_man_wr_data_reg <= i_fifo_rd_data;
                
                left_exp_wr_en_reg   <= 1'b1;
                left_exp_wr_addr_reg <= left_addr;
                left_exp_wr_data_reg <= current_exp;

                // synthesis translate_off
                `ifdef DEBUG_DISPATCHER
                if (lines_processed < 25)
                    $display("[DISPATCHER] @%0t LEFT_WR: addr=%0d, exp=0x%02x, man[31:0]=0x%08x",
                             $time, left_addr, current_exp, i_fifo_rd_data[31:0]);
                `endif
                // synthesis translate_on
            end
        end
    end

    // Output assignments - LEFT
    assign o_left_man_wr_en   = left_man_wr_en_reg;
    assign o_left_man_wr_addr = left_man_wr_addr_reg;
    assign o_left_man_wr_data = left_man_wr_data_reg;
    assign o_left_exp_wr_en   = left_exp_wr_en_reg;
    assign o_left_exp_wr_addr = left_exp_wr_addr_reg;
    assign o_left_exp_wr_data = left_exp_wr_data_reg;

    // ===================================================================
    // Right Path Output (16 Column BRAMs - Direct Write with One-Hot Enable)
    // ===================================================================
    logic [ADDR_WIDTH-1:0]    right_wr_addr_reg;
    logic [NUM_COLS-1:0]      right_wr_en_reg;
    logic [MAN_WIDTH-1:0]     right_man_wr_data_reg;
    logic [EXP_WIDTH-1:0]     right_exp_wr_data_reg;

    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            right_wr_addr_reg     <= '0;
            right_wr_en_reg       <= '0;
            right_man_wr_data_reg <= '0;
            right_exp_wr_data_reg <= '0;
        end else begin
            // Default: no writes (all enables off)
            right_wr_en_reg <= '0;

            // Write when data is valid, data_is_exp is false (mantissa phase), path is RIGHT,
            // and we're still in an active state (not IDLE or DONE)
            if (data_valid && !data_is_exp && disp_right_reg &&
                (state_reg == ST_EXP_BUFFER || state_reg == ST_MAN_ROUTE)) begin
                // RIGHT path: Write to selected column BRAM
                right_wr_addr_reg     <= right_addr;
                right_wr_en_reg       <= (16'b1 << col_sel);  // One-hot enable
                right_man_wr_data_reg <= i_fifo_rd_data;
                right_exp_wr_data_reg <= current_exp;

                // synthesis translate_off
                `ifdef DEBUG_DISPATCHER
                if (lines_processed < 20)
                    $display("[DISPATCHER] @%0t RIGHT_WR: col=%0d, addr=%0d, exp=0x%02x, man[31:0]=0x%08x, wr_en=0x%04x",
                             $time, col_sel, right_addr, current_exp, i_fifo_rd_data[31:0], (16'b1 << col_sel));
                `endif
                // synthesis translate_on
            end
        end
    end

    // Output assignments - RIGHT
    assign o_right_wr_addr     = right_wr_addr_reg;
    assign o_right_wr_en       = right_wr_en_reg;
    assign o_right_man_wr_data = right_man_wr_data_reg;
    assign o_right_exp_wr_data = right_exp_wr_data_reg;

    // ===================================================================
    // Dispatch Done Signal
    // ===================================================================
    logic disp_done_reg;

    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            disp_done_reg <= 1'b0;
        end else begin
            disp_done_reg <= (state_reg == ST_DONE);
        end
    end

    assign o_disp_done = disp_done_reg;

    // ===================================================================
    // Debug Outputs
    // ===================================================================
    assign o_disp_state = state_reg;
    assign o_lines_processed = lines_processed;

endmodule

`default_nettype wire
