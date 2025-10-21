// ------------------------------------------------------------------
// Compute Engine Module with V-Loop Support (MS2.0) - Integer-Only GFP
//
// Purpose: Parameterizable GEMM compute engine with V-loop iteration
// Features:
//  - **V-loop support**: Accumulates across multiple Native Vectors (V>1)
//  - **Parallel group-based dot product** (4 groups × 32 elements = 128 per NV)
//  - **Integer-only GFP arithmetic** (based on matrix_engine_w4gfp8/group_fp_full_int.sv)
//  - **Runtime configurable dimensions** via TILE commands (B, C, V parameters)
//  - Integer-only accumulation per group with exponent alignment
//  - FP16 output with overflow clamping
//
// Matrix Dimensions (configurable via TILE command):
//  - Matrix A: B rows × (128×V) columns, uses B×V Native Vectors
//  - Matrix B: (128×V) rows × C columns, uses C×V Native Vectors
//  - Output: B × C results
//  - Constraints: B×V ≤ 128, C×V ≤ 128
//
// Performance:
//  - Single NV dot product: ~30 cycles (4 parallel group MACs + control)
//  - V-loop overhead: ~25 cycles per iteration (load + accumulate)
//  - Total for V iterations: ~30 + (V-1)×25 cycles per output element
//
// Data Layout (528-line Native Vector format):
//  - Lines 0-15: Exponents (512 total, 32 per line, 5-bit each, bias=15)
//  - Lines 16-527: Mantissas (512 lines, 32 per line, 8-bit signed)
//  - Each NV: 128 elements = 4 groups of 32 elements
//  - Supports 128 NVs per memory block (left @ 0-527, right @ 528-1055)
//
// GFP Arithmetic (integer-only):
//  - Per-group integer accumulation: acc[g] = Σ(mant_a[i] × mant_b[i])
//  - Per-group exponent: exp_result[g] = exp_a[g] + exp_b[g] (no bias subtraction)
//  - Per-group result: gfp_result[g] = {mantissa: acc[g], exponent: exp_result[g]}
//  - Dot product: align exponents and sum mantissas across groups
//  - V-loop accumulation: align exponents and sum mantissas across V iterations
//  - Final conversion: gfp_result → FP16 for output
//
// Last Updated: Thu Oct 9 2025 - Integer-only GFP implementation complete
// ------------------------------------------------------------------

module compute_engine
import gemm_pkg::*;
(
    // Clock and Reset
    input  logic        i_clk,
    input  logic        i_reset_n,

    // ====================================================================
    // Master Control Interface (TILE command)
    // ====================================================================
    input  logic                          i_tile_en,
    input  logic [tile_mem_addr_width_gp-1:0] i_left_addr,
    input  logic [tile_mem_addr_width_gp-1:0] i_right_addr,
    input  logic [tile_mem_addr_width_gp-1:0] i_left_ugd_len,
    input  logic [tile_mem_addr_width_gp-1:0] i_right_ugd_len,
    input  logic [tile_mem_addr_width_gp-1:0] i_vec_len,
    input  logic [7:0]                    i_dim_b,    // Output rows (batch dimension)
    input  logic [7:0]                    i_dim_c,    // Output columns
    input  logic [7:0]                    i_dim_v,    // Inner dimension multiplier (K = 128*V)
    input  logic                          i_left_man_4b,
    input  logic                          i_right_man_4b,
    input  logic                          i_main_loop_over_left,
    output logic                          o_tile_done,

    // ====================================================================
    // BRAM Read Interface (from Dispatcher Control)
    // ====================================================================
    output logic [10:0]                   o_bram_rd_addr,  // 11 bits for 1056 addresses
    input  logic [255:0]                  i_bram_rd_data,
    output logic                          o_bram_rd_en,

    // ====================================================================
    // Result FIFO Write Interface
    // ====================================================================
    output logic [23:0]                   o_result_data,   // FP24 format
    output logic                          o_result_valid,
    input  logic                          i_result_full,
    input  logic                          i_result_afull,

    // ====================================================================
    // Debug Interface
    // ====================================================================
    output logic [3:0]                    o_ce_state,
    output logic [15:0]                   o_result_count
);

    // ===================================================================
    // State Machine Definition
    // ===================================================================
    typedef enum logic [3:0] {
        ST_IDLE           = 4'd0,
        ST_LOAD_LEFT_EXP  = 4'd1,  // Load left vector exponents (1 line, 4 groups)
        ST_LOAD_RIGHT_EXP = 4'd2,  // Load right vector exponents (1 line, 4 groups)
        ST_LOAD_LEFT_MAN  = 4'd3,  // Load left vector mantissas (4 lines, 128 elements)
        ST_LOAD_RIGHT_MAN = 4'd4,  // Load right vector mantissas (4 lines, 128 elements)
        ST_COMPUTE        = 4'd5,  // Parallel group multiply-add + FP sum (1 cycle)
        ST_CONVERT        = 4'd6,  // Convert accumulated result to FP16
        ST_OUTPUT         = 4'd7,  // Write FP16 result to FIFO
        ST_NEXT_DOT       = 4'd8,  // Move to next dot product
        ST_DONE           = 4'd9
    } state_t;

    state_t state_reg, state_next;

    // ===================================================================
    // Local Parameters
    // ===================================================================
    localparam MAX_M = 128;     // Maximum output rows (for buffer sizing)
    localparam MAX_N = 128;     // Maximum output columns (for buffer sizing)
    localparam K = 128;         // Inner dimension (dot product length per NV)
    localparam GROUP_SIZE = 32; // GFP group size
    localparam NUM_GROUPS = 4;  // K / GROUP_SIZE = 128 / 32
    localparam EXP_BITS = 5;    // 5-bit exponents (from mem_layout.py)
    localparam BIAS = 15;       // Exponent bias for 5-bit exp: 2^(5-1) - 1

    // ===================================================================
    // Internal Storage - Vector Buffers
    // ===================================================================

    // Exponent buffers (4 groups per vector, 5-bit exponents, bias=15)
    // Native vectors store 5-bit exponents, we keep them as 5-bit for hardware formula
    logic [4:0] left_exp [0:NUM_GROUPS-1];   // 4 exponents for left vector
    logic [4:0] right_exp [0:NUM_GROUPS-1];  // 4 exponents for right vector

    // Mantissa buffers (128 elements per vector, 8-bit signed)
    logic signed [7:0] left_mant [0:K-1];    // 128 mantissas
    logic signed [7:0] right_mant [0:K-1];   // 128 mantissas

    // Single result register for streaming (replaces massive array)
    logic [15:0] current_result_fp16;  // Current output being computed

    // ===================================================================
    // Control Registers
    // ===================================================================
    logic [7:0] dim_b_reg;      // Registered B dimension (output rows)
    logic [7:0] dim_c_reg;      // Registered C dimension (output cols)
    logic [7:0] dim_v_reg;      // Registered V dimension (inner NV count)
    logic [7:0] row_idx;        // Current output row (0 to B-1)
    logic [7:0] col_idx;        // Current output column (0 to C-1)
    logic [7:0] v_idx;          // Current NV index within inner dimension (0 to V-1)
    logic [2:0] load_count;     // Counter for loading lines
    logic [15:0] result_count_reg;

    // BRAM access
    logic [10:0] bram_addr_reg;
    logic bram_rd_en_reg;

    // Integer-only GFP computation results
    typedef struct packed {
        logic signed [31:0] mantissa;  // Accumulated mantissa (signed 32-bit)
        logic signed [7:0] exponent;   // Exponent (signed 8-bit, can be negative)
    } gfp_result_int_t;
    
    gfp_result_int_t group_result [0:NUM_GROUPS-1];  // 4 group results (integer-only GFP)
    gfp_result_int_t dot_product_result;             // Final summed result (single iteration)
    gfp_result_int_t accumulated_result;             // Persistent accumulator across V iterations
    gfp_result_int_t final_result;                   // Final result for current output (combinatorial)
    
    // Integer-only GFP parameters (matching hardware_gfp_reference.py)
    localparam integer GFP_INT_SIZE = 8;        // 8-bit mantissas
    localparam integer GFP_GROUP_SIZE = 32;     // 32 elements per group
    localparam integer GFP_EXP_SIZE = 5;        // 5-bit exponents
    localparam integer GFP_BIAS = 15;           // Exponent bias for 5-bit exp: 2^(5-1) - 1
    localparam integer GFP_EXP_INF = 5'h1F;     // Infinity exponent (31)
    localparam integer GFP_EXP_ZERO = 5'h00;    // Zero exponent

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

    // State Machine - Next State Logic
    always_comb begin
        state_next = state_reg;

        case (state_reg)
            ST_IDLE: begin
                if (i_tile_en) begin
                    $display("[CE_DEBUG] @%0t TILE command received: B=%0d, C=%0d, V=%0d, left_addr=%0d, right_addr=%0d",
                             $time, i_dim_b, i_dim_c, i_dim_v, i_left_addr, i_right_addr);
                    state_next = ST_LOAD_LEFT_EXP;
                end
            end

            ST_LOAD_LEFT_EXP: begin
                // Load 1 line: read request (cycle 0) + data valid (cycle 1) + one more for transition
                // Total: 3 cycles to ensure data is captured before state change
                if (load_count >= 3'd3) begin
                    state_next = ST_LOAD_RIGHT_EXP;
                end
            end

            ST_LOAD_RIGHT_EXP: begin
                // Need time for data to be captured
                if (load_count >= 3'd3) begin
                    state_next = ST_LOAD_LEFT_MAN;
                end
            end

            ST_LOAD_LEFT_MAN: begin
                // Load 4 lines: 4 reads + 1 latency + 1 extra = 6 cycles total
                if (load_count >= 3'd6) begin
                    state_next = ST_LOAD_RIGHT_MAN;
                end
            end

            ST_LOAD_RIGHT_MAN: begin
                if (load_count >= 3'd6) begin
                    state_next = ST_COMPUTE;
                end
            end

            ST_COMPUTE: begin
                // Parallel group multiply-add (combinational, 1 cycle)
                state_next = ST_CONVERT;
            end

            ST_CONVERT: begin
                // Convert real accumulator to FP16 (1 cycle)
                state_next = ST_OUTPUT;
            end

            ST_OUTPUT: begin
                // Check if more V iterations needed or move to next dot product
                if (!i_result_afull) begin
                    if (v_idx < dim_v_reg - 1) begin
                        // More V iterations needed - loop back to load next NV
                        state_next = ST_LOAD_LEFT_EXP;
                    end else begin
                        // Completed all V iterations - move to next dot product
                        state_next = ST_NEXT_DOT;
                    end
                end
            end

            ST_NEXT_DOT: begin
                // Check if more dot products needed
                $display("[CE_DEBUG] @%0t ST_NEXT_DOT: row=%0d, col=%0d, dim_b=%0d, dim_c=%0d, check: col>=%0d && row>=%0d = %b",
                         $time, row_idx, col_idx, dim_b_reg, dim_c_reg,
                         dim_c_reg-1, dim_b_reg-1,
                         (col_idx >= dim_c_reg-1) && (row_idx >= dim_b_reg-1));
                if (col_idx >= dim_c_reg-1 && row_idx >= dim_b_reg-1) begin
                    // Completed all B×C dot products
                    $display("[CE_DEBUG] @%0t   Terminating - all %0d x %0d results complete", $time, dim_b_reg, dim_c_reg);
                    state_next = ST_DONE;
                end else begin
                    // Start next dot product
                    state_next = ST_LOAD_LEFT_EXP;
                end
            end

            ST_DONE: begin
                state_next = ST_IDLE;
            end

            default: state_next = ST_IDLE;
        endcase
    end

    // ===================================================================
    // BRAM Read Control Logic
    // ===================================================================
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            bram_rd_en_reg <= 1'b0;
            bram_addr_reg <= '0;
            load_count <= '0;
        end else begin
            // Default
            bram_rd_en_reg <= 1'b0;

            case (state_reg)
                ST_IDLE: begin
                    load_count <= '0;
                end

                ST_LOAD_LEFT_EXP: begin
                    if (load_count == 3'd0) begin
                        // Read exponent line for left vector (current row)
                        // Exponents are interleaved - calculate which line contains this row's exponents
                        automatic integer byte_offset_exp, line_num_exp;
                        byte_offset_exp = get_exp_byte_offset(row_idx, v_idx, dim_v_reg);
                        line_num_exp = byte_offset_exp / 32;  // Which of the 16 exponent lines
                        bram_addr_reg <= i_left_addr + line_num_exp[10:0];
                        bram_rd_en_reg <= 1'b1;
                        $display("[CE_DEBUG] @%0t Load LEFT EXP: row=%0d, byte_offset=%0d, line_num=%0d, bram_addr=%0d",
                                 $time, row_idx, byte_offset_exp, line_num_exp, i_left_addr + line_num_exp[10:0]);
                    end

                    // Reset load_count when transitioning to next state
                    if (load_count >= 3'd3) begin
                        load_count <= '0;
                    end else begin
                        load_count <= load_count + 1;
                    end
                end

                ST_LOAD_RIGHT_EXP: begin
                    if (load_count == 3'd0) begin
                        // Read exponent line for right vector (current column)
                        // Right matrix starts at i_right_addr
                        automatic integer byte_offset_exp, line_num_exp;
                        byte_offset_exp = get_exp_byte_offset(col_idx, v_idx, dim_v_reg);
                        line_num_exp = byte_offset_exp / 32;
                        bram_addr_reg <= i_right_addr + line_num_exp[10:0];
                        bram_rd_en_reg <= 1'b1;
                        $display("[CE_DEBUG] @%0t Load RIGHT EXP: col=%0d, byte_offset=%0d, line_num=%0d, bram_addr=%0d",
                                 $time, col_idx, byte_offset_exp, line_num_exp, i_right_addr + line_num_exp[10:0]);
                    end

                    // Reset load_count when transitioning to next state
                    if (load_count >= 3'd3) begin
                        load_count <= '0;
                    end else begin
                        load_count <= load_count + 1;
                    end
                end

                ST_LOAD_LEFT_MAN: begin
                    // Load 4 consecutive lines for 128 mantissas
                    // Mantissa lines start at line 16
                    // For V>1: NV index = row*dim_v + v, NV occupies lines: 16 + nv_idx*4 to 16 + nv_idx*4+3
                    if (load_count < 3'd4) begin
                        automatic logic [10:0] left_man_addr;
                        automatic logic [15:0] nv_index;
                        nv_index = row_idx * dim_v_reg + v_idx;
                        left_man_addr = i_left_addr + 11'd16 + ({nv_index[8:0], 2'b00} + {9'd0, load_count[1:0]});
                        bram_addr_reg <= left_man_addr;
                        bram_rd_en_reg <= 1'b1;
                        $display("[CE_DEBUG] @%0t LEFT MAN READ: row=%0d, v=%0d, nv_idx=%0d, load_count=%0d, addr=%0d",
                                 $time, row_idx, v_idx, nv_index, load_count, left_man_addr);
                    end

                    // Reset load_count when transitioning to next state
                    if (load_count >= 3'd6) begin
                        load_count <= '0;
                    end else begin
                        load_count <= load_count + 1;
                    end
                end

                ST_LOAD_RIGHT_MAN: begin
                    if (load_count < 3'd4) begin
                        automatic logic [10:0] right_man_addr;
                        automatic logic [15:0] nv_index;
                        nv_index = col_idx * dim_v_reg + v_idx;
                        right_man_addr = i_right_addr + 11'd16 + ({nv_index[8:0], 2'b00} + {9'd0, load_count[1:0]});
                        bram_addr_reg <= right_man_addr;
                        bram_rd_en_reg <= 1'b1;
                        $display("[CE_DEBUG] @%0t RIGHT MAN READ: col=%0d, v=%0d, nv_idx=%0d, load_count=%0d, addr=%0d",
                                 $time, col_idx, v_idx, nv_index, load_count, right_man_addr);
                    end

                    // Reset load_count when transitioning to next state
                    if (load_count >= 3'd6) begin
                        load_count <= '0;
                    end else begin
                        load_count <= load_count + 1;
                    end
                end

                ST_COMPUTE: begin
                    load_count <= '0;
                end

                ST_NEXT_DOT: begin
                    load_count <= '0;
                end

                default: begin
                    load_count <= '0;
                end
            endcase
        end
    end

    assign o_bram_rd_addr = bram_addr_reg;
    assign o_bram_rd_en = bram_rd_en_reg;

    // ===================================================================
    // Data Capture Logic
    // ===================================================================

    // Helper function to compute exponent byte offset
    // For V>1: NV index = row * dim_v + v_idx
    // Each NV has 4 groups, so NV uses exponents at indices: nv_idx*4 to nv_idx*4+3
    function automatic integer get_exp_byte_offset(input integer row, input integer v, input integer dim_v);
        integer nv_index, exp_index;
        nv_index = row * dim_v + v;  // Which NV in the matrix
        exp_index = nv_index * 4;    // First exponent for this NV (4 per NV)
        return exp_index;
    endfunction

    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            // Clear exponent buffers
            for (int i = 0; i < NUM_GROUPS; i++) begin
                left_exp[i] <= '0;
                right_exp[i] <= '0;
            end
            // Clear mantissa buffers
            for (int i = 0; i < K; i++) begin
                left_mant[i] <= '0;
                right_mant[i] <= '0;
            end
        end else begin
            case (state_reg)
                ST_LOAD_LEFT_EXP: begin
                    // Capture exponents on third cycle (data valid after 1-cycle BRAM latency + 1 cycle propagation)
                    // Exponents are interleaved - need to extract correct 4 bytes
                    if (load_count == 3'd2) begin
                        automatic integer byte_offset, byte_in_line, abs_byte_idx;

                        // Get flat byte offset for this row using interleaved pattern
                        byte_offset = get_exp_byte_offset(row_idx, v_idx, dim_v_reg);

                        // Within the current line (256 bits = 32 bytes), find position
                        byte_in_line = byte_offset % 32;

                        $display("[CE_DEBUG] @%0t LEFT EXP DATA: row=%0d, byte_offset=%0d, byte_in_line=%0d",
                                 $time, row_idx, byte_offset, byte_in_line);
                        $display("[CE_DEBUG]   BRAM data[7:0] = 0x%02h %02h %02h %02h %02h %02h %02h %02h",
                                 i_bram_rd_data[7:0], i_bram_rd_data[15:8], i_bram_rd_data[23:16], i_bram_rd_data[31:24],
                                 i_bram_rd_data[39:32], i_bram_rd_data[47:40], i_bram_rd_data[55:48], i_bram_rd_data[63:56]);

                        // Extract 4 consecutive exponents (5-bit each, stored in 8-bit bytes)
                        for (int i = 0; i < NUM_GROUPS; i++) begin
                            abs_byte_idx = byte_in_line + i;
                            if (abs_byte_idx < 32) begin
                                // Keep 5-bit exponent as-is (hardware formula uses 5-bit directly)
                                left_exp[i] <= i_bram_rd_data[(abs_byte_idx*8) +: 5];
                                $display("[CE_DEBUG]   left_exp[%0d] = 0x%02h (5-bit, from byte %0d)",
                                         i, i_bram_rd_data[(abs_byte_idx*8) +: 5], abs_byte_idx);
                            end else begin
                                // Shouldn't happen for rows 0-3, but handle gracefully
                                left_exp[i] <= 5'h00;
                                $display("[CE_DEBUG]   left_exp[%0d] = 0x00 (out of bounds)", i);
                            end
                        end
                    end
                end

                ST_LOAD_RIGHT_EXP: begin
                    // Capture exponents on third cycle (same timing as left exponents)
                    if (load_count == 3'd2) begin
                        automatic integer byte_offset, byte_in_line, abs_byte_idx;

                        byte_offset = get_exp_byte_offset(col_idx, v_idx, dim_v_reg);
                        byte_in_line = byte_offset % 32;

                        $display("[CE_DEBUG] @%0t RIGHT EXP DATA: col=%0d, byte_offset=%0d, byte_in_line=%0d",
                                 $time, col_idx, byte_offset, byte_in_line);
                        $display("[CE_DEBUG]   BRAM data[7:0] = 0x%02h %02h %02h %02h %02h %02h %02h %02h",
                                 i_bram_rd_data[7:0], i_bram_rd_data[15:8], i_bram_rd_data[23:16], i_bram_rd_data[31:24],
                                 i_bram_rd_data[39:32], i_bram_rd_data[47:40], i_bram_rd_data[55:48], i_bram_rd_data[63:56]);

                        for (int i = 0; i < NUM_GROUPS; i++) begin
                            abs_byte_idx = byte_in_line + i;
                            if (abs_byte_idx < 32) begin
                                // Keep 5-bit exponent as-is (hardware formula uses 5-bit directly)
                                right_exp[i] <= i_bram_rd_data[(abs_byte_idx*8) +: 5];
                                $display("[CE_DEBUG]   right_exp[%0d] = 0x%02h (5-bit, from byte %0d)",
                                         i, i_bram_rd_data[(abs_byte_idx*8) +: 5], abs_byte_idx);
                            end else begin
                                right_exp[i] <= 5'h00;
                                $display("[CE_DEBUG]   right_exp[%0d] = 0x00 (out of bounds)", i);
                            end
                        end
                    end
                end

                ST_LOAD_LEFT_MAN: begin
                    // Capture mantissas with BRAM latency + propagation delay
                    // load_count: 0=read req line 0, 1=pipeline, 2=data valid line 0, 3=data valid line 1, ...
                    if (load_count >= 3'd2 && load_count <= 3'd5) begin
                        automatic integer line_offset, elem_idx;
                        line_offset = (load_count - 2) * GROUP_SIZE;
                        $display("[CE_DEBUG] @%0t LEFT MAN DATA: load_count=%0d, line_offset=%0d",
                                 $time, load_count, line_offset);
                        $display("[CE_DEBUG]   First 8 mantissas: %0d %0d %0d %0d %0d %0d %0d %0d",
                                 $signed(i_bram_rd_data[7:0]), $signed(i_bram_rd_data[15:8]),
                                 $signed(i_bram_rd_data[23:16]), $signed(i_bram_rd_data[31:24]),
                                 $signed(i_bram_rd_data[39:32]), $signed(i_bram_rd_data[47:40]),
                                 $signed(i_bram_rd_data[55:48]), $signed(i_bram_rd_data[63:56]));
                        for (int i = 0; i < GROUP_SIZE; i++) begin
                            // Extract signed 8-bit mantissa
                            elem_idx = line_offset + i;
                            left_mant[elem_idx] <= $signed(i_bram_rd_data[(i*8) +: 8]);
                        end
                    end
                end

                ST_LOAD_RIGHT_MAN: begin
                    // Same timing as left mantissas - wait for BRAM latency + propagation
                    if (load_count >= 3'd2 && load_count <= 3'd5) begin
                        automatic integer line_offset, elem_idx;
                        line_offset = (load_count - 2) * GROUP_SIZE;
                        $display("[CE_DEBUG] @%0t RIGHT MAN DATA: load_count=%0d, line_offset=%0d",
                                 $time, load_count, line_offset);
                        $display("[CE_DEBUG]   First 8 mantissas: %0d %0d %0d %0d %0d %0d %0d %0d",
                                 $signed(i_bram_rd_data[7:0]), $signed(i_bram_rd_data[15:8]),
                                 $signed(i_bram_rd_data[23:16]), $signed(i_bram_rd_data[31:24]),
                                 $signed(i_bram_rd_data[39:32]), $signed(i_bram_rd_data[47:40]),
                                 $signed(i_bram_rd_data[55:48]), $signed(i_bram_rd_data[63:56]));
                        for (int i = 0; i < GROUP_SIZE; i++) begin
                            elem_idx = line_offset + i;
                            right_mant[elem_idx] <= $signed(i_bram_rd_data[(i*8) +: 8]);
                        end
                    end
                end
            endcase
        end
    end

    // ===================================================================
    // Integer-Only GFP Group Multiply-Add (Combinational)
    // Based on matrix_engine_w4gfp8/src/tb_new/group_fp_full_int.sv::mult_add_gfp()
    // ===================================================================

    // Hardware GFP multiply-add function for a single group
    // Matches hardware_gfp_reference.py algorithm
    // Bitwidth Analysis:
    // - Input mantissas: 8-bit signed (GFP_INT_SIZE = 8)
    // - Input exponents: 5-bit (bias = 15)
    // - Element-wise product: 8×8 = 16-bit signed
    // - Group accumulator: 16-bit + log2(32) = 21-bit signed
    // - Exponent sum: 5+5-30 = signed 6-bit (range -30 to +32)
    // - Group result mantissa: 32-bit signed (stored)
    // - Group result exponent: 8-bit signed (to store negative values)
    function automatic gfp_result_int_t mult_add_gfp_group(
        input logic [GFP_GROUP_SIZE*GFP_INT_SIZE-1:0] a_mantissa,
        input logic [4:0] a_exp,  // 5-bit exponent
        input logic [GFP_GROUP_SIZE*GFP_INT_SIZE-1:0] b_mantissa,
        input logic [4:0] b_exp   // 5-bit exponent
    );
        logic signed [2*GFP_INT_SIZE + $clog2(GFP_GROUP_SIZE) - 1:0] accumulator;  // 21-bit accumulator
        int i;
        logic signed [GFP_INT_SIZE-1:0] a_element;  // 8-bit signed
        logic signed [GFP_INT_SIZE-1:0] b_element;  // 8-bit signed
        logic signed [2*GFP_INT_SIZE-1:0] product;  // 16-bit signed
        logic signed [7:0] exp_sum;         // Signed 8-bit for negative values
        gfp_result_int_t result;

        // Handle special cases: zero exponents
        if (a_exp == 5'h00 || b_exp == 5'h00) begin
            result.mantissa = 0;
            result.exponent = 0;
            return result;
        end
        
        // Initialize accumulator
        accumulator = 0;
        
        // Perform dot product: sum of element-wise products
        for (i = 0; i < GFP_GROUP_SIZE; i = i + 1) begin
            // Extract mantissa elements as signed integers (GFP format)
            a_element = a_mantissa[i*GFP_INT_SIZE +: GFP_INT_SIZE];
            b_element = b_mantissa[i*GFP_INT_SIZE +: GFP_INT_SIZE];
            
            // Calculate element-wise product
            product = a_element * b_element;
            
            accumulator = accumulator + product;
        end
        
        // Handle zero result
        if (accumulator == 0) begin
            result.mantissa = 0;
            result.exponent = 0;
            return result;
        end

        // Calculate exponent using hardware formula: exp_a + exp_b - 2*bias
        // With bias=15: exp_sum = exp_a + exp_b - 30
        // Exponents are UNSIGNED 5-bit, so we keep them unsigned for the sum
        // Result can be negative (when small exponents), so we use signed for storage
        exp_sum = $signed({3'b0, a_exp} + {3'b0, b_exp}) - 8'sd30;
        
        // Return GFP format result
        // Exponent: exp_sum (can be negative!)
        // Mantissa: accumulator (sum of products)
        result.exponent = exp_sum;
        result.mantissa = accumulator;
        
        return result;
    endfunction

    // Integer-only GFP group computation (combinational)
    genvar g;
    generate
        for (g = 0; g < NUM_GROUPS; g++) begin : gen_group_mult_add
            // Pack mantissas into vectors for function call
            logic [GFP_GROUP_SIZE*GFP_INT_SIZE-1:0] left_mant_packed;
            logic [GFP_GROUP_SIZE*GFP_INT_SIZE-1:0] right_mant_packed;
            
            always_comb begin
                integer i;
                
                // Pack mantissas for this group
                for (i = 0; i < GFP_GROUP_SIZE; i++) begin
                    left_mant_packed[i*GFP_INT_SIZE +: GFP_INT_SIZE] = left_mant[g*GFP_GROUP_SIZE + i];
                    right_mant_packed[i*GFP_INT_SIZE +: GFP_INT_SIZE] = right_mant[g*GFP_GROUP_SIZE + i];
                end
                
                // Call integer-only GFP multiply-add
                group_result[g] = mult_add_gfp_group(
                    left_mant_packed,
                    left_exp[g],
                    right_mant_packed,
                    right_exp[g]
                );
            end
        end
    endgenerate

    // Sum the 4 group results using integer-only GFP arithmetic
    // This requires exponent alignment - find maximum exponent first
    // Bitwidth Analysis for Group Summation:
    // - Group result mantissas: 32-bit signed each
    // - Group result exponents: 8-bit each (5-bit stored as 8-bit)
    // - Exponent differences: 8-bit (max difference = 31)
    // - Aligned mantissas: 32-bit signed (right-shifted by exp_diff)
    // - Sum mantissa: 32-bit signed (sum of 4 aligned mantissas)
    // - Final exponent: 8-bit (maximum of group exponents)
    always_comb begin
        logic [7:0] max_exp;
        logic [7:0] exp_diff [0:NUM_GROUPS-1];
        logic signed [31:0] aligned_mantissa [0:NUM_GROUPS-1];
        logic signed [31:0] sum_mantissa;
        
        // Find maximum exponent among all groups
        max_exp = group_result[0].exponent;
        for (int i = 1; i < NUM_GROUPS; i++) begin
            if (group_result[i].exponent > max_exp) begin
                max_exp = group_result[i].exponent;
            end
        end
        
        // Align all mantissas to the maximum exponent
        for (int i = 0; i < NUM_GROUPS; i++) begin
            exp_diff[i] = max_exp - group_result[i].exponent;
            if (exp_diff[i] > 31) begin
                // Underflow - set to zero
                aligned_mantissa[i] = 0;
            end else begin
                // Arithmetic right-shift to preserve sign
                aligned_mantissa[i] = $signed(group_result[i].mantissa) >>> exp_diff[i];
            end
        end
        
        // Sum aligned mantissas
        sum_mantissa = aligned_mantissa[0] + aligned_mantissa[1] + aligned_mantissa[2] + aligned_mantissa[3];
        
        // Final result
        dot_product_result.mantissa = sum_mantissa;
        dot_product_result.exponent = max_exp;
    end

    // ===================================================================
    // Computation Control and FP16 Conversion
    // ===================================================================

    // Function to convert integer-only GFP result to FP16
    // Input: 32-bit signed mantissa, 8-bit signed exponent (unbiased, can be negative)
    // Output: 16-bit FP16 (1 sign, 5 exp, 10 mantissa)
    // Formula: fp_value = mantissa * 2^(signed_exponent)
    // Approach: Normalize mantissa to [1.0, 2.0), adjust exponent, encode as FP16
    function logic [15:0] gfp_int_to_fp16(input gfp_result_int_t gfp_result);
        logic sign;
        logic signed [31:0] abs_mantissa;
        logic signed [7:0] exp_signed;  // Signed exponent (unbiased)
        logic signed [8:0] fp16_exp_signed;  // FP16 exponent (with bias, can overflow)
        logic [4:0] fp16_exp;
        logic [9:0] fp16_mant;
        logic [15:0] result;
        integer leading_zeros;
        
        // Handle zero
        if (gfp_result.mantissa == 0) begin
            return 16'h0000;
        end
        
        // Extract sign and absolute value
        sign = gfp_result.mantissa[31];
        abs_mantissa = sign ? -gfp_result.mantissa : gfp_result.mantissa;
        exp_signed = $signed(gfp_result.exponent);  // Interpret as signed
        
        // Find leading zeros to normalize mantissa
        // We want to shift mantissa so the leading 1 is in position 31 (MSB)
        // Then extract top 11 bits (including implicit leading 1) for FP16
        leading_zeros = 0;
        if (abs_mantissa[31]) begin
            leading_zeros = 0;
        end else if (abs_mantissa[30]) begin
            leading_zeros = 1;
        end else if (abs_mantissa[29]) begin
            leading_zeros = 2;
        end else if (abs_mantissa[28]) begin
            leading_zeros = 3;
        end else if (abs_mantissa[27]) begin
            leading_zeros = 4;
        end else if (abs_mantissa[26]) begin
            leading_zeros = 5;
        end else if (abs_mantissa[25]) begin
            leading_zeros = 6;
        end else if (abs_mantissa[24]) begin
            leading_zeros = 7;
        end else if (abs_mantissa[23]) begin
            leading_zeros = 8;
        end else if (abs_mantissa[22]) begin
            leading_zeros = 9;
        end else if (abs_mantissa[21]) begin
            leading_zeros = 10;
        end else if (abs_mantissa[20]) begin
            leading_zeros = 11;
        end else if (abs_mantissa[19]) begin
            leading_zeros = 12;
        end else if (abs_mantissa[18]) begin
            leading_zeros = 13;
        end else if (abs_mantissa[17]) begin
            leading_zeros = 14;
        end else if (abs_mantissa[16]) begin
            leading_zeros = 15;
        end else if (abs_mantissa[15]) begin
            leading_zeros = 16;
        end else if (abs_mantissa[14]) begin
            leading_zeros = 17;
        end else if (abs_mantissa[13]) begin
            leading_zeros = 18;
        end else if (abs_mantissa[12]) begin
            leading_zeros = 19;
        end else if (abs_mantissa[11]) begin
            leading_zeros = 20;
        end else if (abs_mantissa[10]) begin
            leading_zeros = 21;
        end else if (abs_mantissa[9]) begin
            leading_zeros = 22;
        end else if (abs_mantissa[8]) begin
            leading_zeros = 23;
        end else if (abs_mantissa[7]) begin
            leading_zeros = 24;
        end else if (abs_mantissa[6]) begin
            leading_zeros = 25;
        end else if (abs_mantissa[5]) begin
            leading_zeros = 26;
        end else if (abs_mantissa[4]) begin
            leading_zeros = 27;
        end else if (abs_mantissa[3]) begin
            leading_zeros = 28;
        end else if (abs_mantissa[2]) begin
            leading_zeros = 29;
        end else if (abs_mantissa[1]) begin
            leading_zeros = 30;
        end else if (abs_mantissa[0]) begin
            leading_zeros = 31;
        end else begin
            // Should not happen since we checked for zero above
            return 16'h0000;
        end
        
        // Normalize mantissa to [1.0, 2.0) by shifting left
        // After shift, bit 31 has the leading 1
        abs_mantissa = abs_mantissa << leading_zeros;
        
        // Calculate FP16 exponent
        // GFP: value = mantissa * 2^(exp_signed)
        // After normalization: mantissa is in range [2^31, 2^32)
        // So: value = (mantissa / 2^31) * 2^(exp_signed) = (mantissa / 2^31) * 2^(exp_signed)
        //           = mantissa_normalized * 2^(exp_signed + 31 - leading_zeros)
        // FP16: value = 1.mantissa_fraction * 2^(exp_unbiased)
        // So: exp_unbiased = exp_signed + 31 - leading_zeros
        // FP16 biased exponent (bias=15): fp16_exp = exp_unbiased + 15
        fp16_exp_signed = exp_signed + 31 - leading_zeros + 15;
        
        // Handle exponent range
        // FP16 exponent field: 0 = denormal/zero, 1-30 = normal, 31 = inf/NaN
        if (fp16_exp_signed <= 0) begin
            // Underflow to zero or denormal
            return 16'h0000;
        end else if (fp16_exp_signed > 30) begin
            // Overflow to infinity (exponent 31 is reserved for inf/NaN)
            return {sign, 5'b11111, 10'b0};
        end else begin
            fp16_exp = fp16_exp_signed[4:0];
            // Extract 10-bit mantissa (bits 30:21, excluding implicit leading 1 at bit 31)
            fp16_mant = abs_mantissa[30:21];
            
            result = {sign, fp16_exp, fp16_mant};
            return result;
        end
    endfunction


    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            dim_b_reg <= '0;
            dim_c_reg <= '0;
            dim_v_reg <= '0;
            row_idx <= '0;
            col_idx <= '0;
            v_idx <= '0;
            result_count_reg <= '0;
            current_result_fp16 <= 16'h0000;  // Clear single result register
        end else begin
            case (state_reg)
                ST_IDLE: begin
                    if (i_tile_en) begin
                        // Capture B, C, V dimensions
                        dim_b_reg <= i_dim_b;
                        dim_c_reg <= i_dim_c;
                        dim_v_reg <= i_dim_v;
                        row_idx <= '0;
                        col_idx <= '0;
                        v_idx <= '0;
                        result_count_reg <= '0;
                    end
                end

                ST_CONVERT: begin
                    // Accumulate dot product across V iterations using integer-only GFP
                    $display("[CE_DEBUG] @%0t CONVERT: row=%0d, col=%0d, v=%0d/%0d", $time, row_idx, col_idx, v_idx, dim_v_reg-1);
                    $display("[CE_DEBUG]   Loaded exponents: left=[0x%02h, 0x%02h, 0x%02h, 0x%02h], right=[0x%02h, 0x%02h, 0x%02h, 0x%02h]",
                             left_exp[0], left_exp[1], left_exp[2], left_exp[3],
                             right_exp[0], right_exp[1], right_exp[2], right_exp[3]);
                    $display("[CE_DEBUG]   First 8 left mantissas: %0d %0d %0d %0d %0d %0d %0d %0d",
                             left_mant[0], left_mant[1], left_mant[2], left_mant[3],
                             left_mant[4], left_mant[5], left_mant[6], left_mant[7]);
                    $display("[CE_DEBUG]   First 8 right mantissas: %0d %0d %0d %0d %0d %0d %0d %0d",
                             right_mant[0], right_mant[1], right_mant[2], right_mant[3],
                             right_mant[4], right_mant[5], right_mant[6], right_mant[7]);
                    $display("[CE_DEBUG]   Group results (int): [mant=%0d,exp=0x%02h] [mant=%0d,exp=0x%02h] [mant=%0d,exp=0x%02h] [mant=%0d,exp=0x%02h]",
                             group_result[0].mantissa, group_result[0].exponent,
                             group_result[1].mantissa, group_result[1].exponent,
                             group_result[2].mantissa, group_result[2].exponent,
                             group_result[3].mantissa, group_result[3].exponent);
                    $display("[CE_DEBUG]   Dot product result (int): mant=%0d, exp=0x%02h", 
                             dot_product_result.mantissa, dot_product_result.exponent);

                    // Accumulate across V iterations using integer-only GFP arithmetic
                    // For the last iteration, we need the final sum INCLUDING current dot_product
                    // Bitwidth Analysis for V-loop Accumulation:
                    // - Accumulated mantissa: 32-bit signed
                    // - Current dot product mantissa: 32-bit signed
                    // - Exponent differences: 8-bit (max difference = 31)
                    // - Aligned mantissas: 32-bit signed (right-shifted by exp_diff)
                    // - Sum mantissa: 32-bit signed (sum of 2 aligned mantissas)
                    // - Final exponent: 8-bit (maximum of accumulated and current exponents)
                    if (v_idx == 8'd0) begin
                        accumulated_result <= dot_product_result;  // Initialize for next iteration
                        final_result = dot_product_result;  // For output if this is also last iteration (V=1)
                        $display("[CE_DEBUG]   V-loop INIT: accumulated_result = mant=%0d, exp=0x%02h", 
                                 dot_product_result.mantissa, dot_product_result.exponent);
                    end else begin
                        // Integer-only GFP addition with exponent alignment
                        logic signed [7:0] max_exp;
                        logic [7:0] exp_diff_accum, exp_diff_dot;
                        logic signed [31:0] aligned_accum, aligned_dot;
                        gfp_result_int_t sum_result;
                        
                        // Find maximum exponent (using signed comparison for negative exponents)
                        if ($signed(accumulated_result.exponent) > $signed(dot_product_result.exponent)) begin
                            max_exp = accumulated_result.exponent;
                        end else begin
                            max_exp = dot_product_result.exponent;
                        end
                        
                        // Align mantissas
                        exp_diff_accum = max_exp - accumulated_result.exponent;
                        exp_diff_dot = max_exp - dot_product_result.exponent;
                        
                        if (exp_diff_accum > 31) begin
                            aligned_accum = 0;
                        end else begin
                            aligned_accum = $signed(accumulated_result.mantissa) >>> exp_diff_accum;
                        end
                        
                        if (exp_diff_dot > 31) begin
                            aligned_dot = 0;
                        end else begin
                            aligned_dot = $signed(dot_product_result.mantissa) >>> exp_diff_dot;
                        end
                        
                        // Sum aligned mantissas
                        sum_result.mantissa = aligned_accum + aligned_dot;
                        sum_result.exponent = max_exp;
                        
                        accumulated_result <= sum_result;  // Accumulate for next iteration
                        final_result = sum_result;  // For output on last iteration
                        $display("[CE_DEBUG]   V-loop ADD: mant=%0d (0x%08h), exp=%0d (0x%02h), aligned_accum=%0d, aligned_dot=%0d", 
                                 $signed(sum_result.mantissa), sum_result.mantissa, 
                                 $signed(sum_result.exponent), sum_result.exponent,
                                 $signed(aligned_accum), $signed(aligned_dot));
                    end

                    // Only store result on last V iteration (streaming architecture)
                    if (v_idx == dim_v_reg - 1) begin
                        // Convert integer-only GFP result to FP16
                        current_result_fp16 <= gfp_int_to_fp16(final_result);
                        $display("[CE_DEBUG]   FINAL result (v=%0d/%0d): mant=%0d, exp=0x%02h -> FP16: 0x%04h",
                                 v_idx, dim_v_reg-1, final_result.mantissa, final_result.exponent, gfp_int_to_fp16(final_result));
                    end
                end

                ST_OUTPUT: begin
                    if (!i_result_afull) begin
                        // Handle V-loop iteration or advance to next dot product
                        if (v_idx < dim_v_reg - 1) begin
                            // More V iterations - increment v_idx and loop back
                            v_idx <= v_idx + 1;
                            $display("[CE_DEBUG] V-loop: incrementing v_idx from %0d to %0d", v_idx, v_idx + 1);
                        end else begin
                            // Completed all V - output result and reset v_idx
                            result_count_reg <= result_count_reg + 1;
                            v_idx <= '0;
                            $display("[CE_DEBUG] V-loop COMPLETE: outputting result, resetting v_idx to 0");
                        end
                    end
                end

                ST_NEXT_DOT: begin
                    // Move to next dot product position (row-major order)
                    if (col_idx >= dim_c_reg-1) begin
                        col_idx <= '0;
                        if (row_idx >= dim_b_reg-1) begin
                            row_idx <= '0;  // Done, will transition to DONE
                        end else begin
                            row_idx <= row_idx + 1;
                        end
                    end else begin
                        col_idx <= col_idx + 1;
                    end
                end
            endcase
        end
    end

    // ===================================================================
    // Output Logic
    // ===================================================================
    logic [23:0] result_data_reg;
    logic result_valid_reg;

    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            result_data_reg <= '0;
            result_valid_reg <= 1'b0;
        end else begin
            result_valid_reg <= 1'b0;

            // Only write to result FIFO on the last V iteration
            if (state_reg == ST_OUTPUT && !i_result_afull && (v_idx == dim_v_reg - 1)) begin
                // Convert FP16 to FP24 for output interface compatibility
                // FP16: sign(1) + exp(5) + mantissa(10)
                // FP24: sign(1) + exp(8) + mantissa(15)
                logic [15:0] fp16_val;
                logic sign;
                logic [4:0] exp5;
                logic [9:0] man10;
                logic [7:0] exp8;

                fp16_val = current_result_fp16;  // Read from streaming register
                sign = fp16_val[15];
                exp5 = fp16_val[14:10];
                man10 = fp16_val[9:0];

                // Re-bias exponent: FP16 bias=15, FP24 bias=127
                // exp24 = exp16 - 15 + 127 = exp16 + 112 (if exp16 != 0)
                if (exp5 == 5'd0) begin
                    exp8 = 8'd0;  // Zero/denormal
                end else if (exp5 == 5'd31) begin
                    exp8 = 8'd255;  // Inf/NaN
                end else begin
                    exp8 = {3'b0, exp5} + 8'd112;
                end

                result_data_reg <= {sign, exp8, man10, 5'b0};
                result_valid_reg <= 1'b1;
                $display("[CE_DEBUG] FIFO WRITE: Writing result[%0d][%0d] = FP16: 0x%04h (FP24: 0x%06x) after V=%0d iterations",
                         row_idx, col_idx, fp16_val, {sign, exp8, man10, 5'b0}, dim_v_reg);
            end
        end
    end

    // Output assignments
    assign o_result_data = result_data_reg;
    assign o_result_valid = result_valid_reg;
    assign o_result_count = result_count_reg;
    assign o_ce_state = state_reg;
    assign o_tile_done = (state_reg == ST_DONE);

endmodule : compute_engine
