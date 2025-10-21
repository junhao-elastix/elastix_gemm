// ------------------------------------------------------------------
// Compute Engine Module with V-Loop Support (MS2.0)
//
// Purpose: Parameterizable GEMM compute engine with V-loop iteration
// Features:
//  - **V-loop support**: Accumulates across multiple Native Vectors (V>1)
//  - **Parallel group-based dot product** (4 groups × 32 elements = 128 per NV)
//  - **Hardware-compatible GFP arithmetic** (based on matrix_engine_w4gfp8/group_fp.sv)
//  - **Runtime configurable dimensions** via TILE commands (B, C, V parameters)
//  - Integer accumulation per group followed by FP summation
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
// GFP Arithmetic (hardware-compatible):
//  - Per-group integer accumulation: acc[g] = Σ(mant_a[i] × mant_b[i])
//  - Per-group exponent: exp_result[g] = exp_a[g] + exp_b[g] - 2×bias
//  - Per-group result: result[g] = acc[g] × 2^exp_result[g]
//  - Dot product: Σ(result[g]) for g=0 to 3
//  - V-loop accumulation: Σ(dot_product[v]) for v=0 to V-1
//
// Last Updated: Sun Oct 6 2025 - V-loop implementation complete and validated
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

    // Exponent buffers (4 groups per vector, 5-bit exponents)
    logic [EXP_BITS-1:0] left_exp [0:NUM_GROUPS-1];   // 4 exponents for left vector
    logic [EXP_BITS-1:0] right_exp [0:NUM_GROUPS-1];  // 4 exponents for right vector

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

    // Group computation results (real for simulation)
    real group_result [0:NUM_GROUPS-1];  // 4 group results
    real dot_product_result;             // Final summed result (single iteration)
    real accumulated_result;             // Persistent accumulator across V iterations
    real final_result;                   // Final result for current output (combinatorial)

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
                                left_exp[i] <= i_bram_rd_data[(abs_byte_idx*8) +: 8] & 8'h1F;
                                $display("[CE_DEBUG]   left_exp[%0d] = 0x%02h (from byte %0d)",
                                         i, i_bram_rd_data[(abs_byte_idx*8) +: 8] & 8'h1F, abs_byte_idx);
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
                                right_exp[i] <= i_bram_rd_data[(abs_byte_idx*8) +: 8] & 8'h1F;
                                $display("[CE_DEBUG]   right_exp[%0d] = 0x%02h (from byte %0d)",
                                         i, i_bram_rd_data[(abs_byte_idx*8) +: 8] & 8'h1F, abs_byte_idx);
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
    // Parallel GFP Group Multiply-Add (Combinational)
    // Based on matrix_engine_w4gfp8/src/tb_new/group_fp.sv::mult_add()
    // ===================================================================

    genvar g;
    generate
        for (g = 0; g < NUM_GROUPS; g++) begin : gen_group_mult_add
            // Per-group accumulator (sum of 32 products)
            logic signed [7+7+5-1:0] accumulator;  // 2*int_size + log2(group_size) = 2*8 + 5 = 19 bits
            real group_scale;

            always_comb begin
                integer i;
                integer exp_sum;
                real scale_factor;

                // Initialize accumulator
                accumulator = 0;

                // Accumulate 32 products in integer domain
                for (i = 0; i < GROUP_SIZE; i++) begin
                    integer elem_idx;
                    elem_idx = g * GROUP_SIZE + i;
                    accumulator = accumulator + (left_mant[elem_idx] * right_mant[elem_idx]);
                end

                // Handle special cases
                // NOTE: In GFP8 format with 5-bit exponents and bias=15,
                //       ALL exponent values 0-31 are valid (no reserved values for inf/nan)
                //       exp=31 (0x1f) represents 2^(31-15) = 2^16 = 65536, NOT infinity!
                if (left_exp[g] == '0 || right_exp[g] == '0) begin
                    // Zero exponent represents zero (denormal handling)
                    group_result[g] = 0.0;
                end else if (accumulator == 0) begin
                    // Zero result
                    group_result[g] = 0.0;
                end else begin
                    // Calculate exponent: exp_result = exp_a + exp_b - 2*bias
                    // For 5-bit exponent with bias=15:
                    // scale_factor = 2^(exp_a + exp_b - 2*15) = 2^(exp_a + exp_b - 30)
                    exp_sum = $signed({3'd0, left_exp[g]}) + $signed({3'd0, right_exp[g]}) - 2*BIAS;
                    scale_factor = 2.0 ** exp_sum;

                    // Apply scaling to integer accumulator
                    group_result[g] = $itor(accumulator) * scale_factor;

                    `ifdef SIMULATION
                    // Debug when result is abnormally large
                    if (group_result[g] > 1.0e10 || group_result[g] < -1.0e10) begin
                        $display("[CE_DEBUG_LARGE] Group %0d: left_exp=0x%02x, right_exp=0x%02x, exp_sum=%0d, scale_factor=%e, accum=%0d, result=%e",
                                 g, left_exp[g], right_exp[g], exp_sum, scale_factor, accumulator, group_result[g]);
                    end
                    `endif
                end
            end
        end
    endgenerate

    // Sum the 4 group results (simple FP addition - groups already scaled correctly)
    always_comb begin
        dot_product_result = group_result[0] + group_result[1] + group_result[2] + group_result[3];
    end

    // ===================================================================
    // Computation Control and FP16 Conversion
    // ===================================================================

    // Function to convert real to FP16
    function logic [15:0] real_to_fp16(input real val);
        logic sign;
        real abs_val;
        real norm;
        integer exp;
        logic [9:0] mantissa;
        real clamped_val;

        // Clamp to FP16 range BEFORE conversion to avoid overflow
        // FP16 max = 65504.0, but we clamp slightly earlier to avoid edge cases
        if (val > 65504.0) begin
            clamped_val = 65504.0;
        end else if (val < -65504.0) begin
            clamped_val = -65504.0;
        end else begin
            clamped_val = val;
        end

        sign = (clamped_val < 0.0);
        abs_val = sign ? -clamped_val : clamped_val;

        if (abs_val == 0.0) begin
            return 16'h0000;
        end else if (abs_val >= 65504.0) begin  // Max FP16
            return {sign, 5'b11110, 10'b1111111111};  // ±Max (not Inf)
        end else begin
            // Normalize to [1.0, 2.0)
            exp = 0;
            norm = abs_val;
            while (norm >= 2.0 && exp < 30) begin
                norm = norm / 2.0;
                exp = exp + 1;
            end
            while (norm < 1.0 && exp > -14) begin
                norm = norm * 2.0;
                exp = exp - 1;
            end

            // Apply FP16 bias (15)
            exp = exp + 15;

            if (exp <= 0) begin
                // Denormal/underflow
                return 16'h0000;
            end else if (exp >= 31) begin
                // Overflow to infinity
                return {sign, 5'b11110, 10'b0};
            end

            // Extract 10-bit mantissa (remove implicit leading 1)
            mantissa = $rtoi((norm - 1.0) * 1024.0);

            return {sign, exp[4:0], mantissa};
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
                    // Accumulate dot product across V iterations
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
                    $display("[CE_DEBUG]   Group results: [%f, %f, %f, %f]",
                             group_result[0], group_result[1], group_result[2], group_result[3]);
                    $display("[CE_DEBUG]   Dot product result (real): %f", dot_product_result);

                    // Accumulate across V iterations
                    // For the last iteration, we need the final sum INCLUDING current dot_product
                    if (v_idx == 8'd0) begin
                        accumulated_result <= dot_product_result;  // Initialize for next iteration
                        final_result = dot_product_result;  // For output if this is also last iteration (V=1)
                        $display("[CE_DEBUG]   V-loop INIT: accumulated_result = %f", dot_product_result);
                    end else begin
                        accumulated_result <= accumulated_result + dot_product_result;  // Accumulate for next iteration
                        final_result = accumulated_result + dot_product_result;  // For output on last iteration
                        $display("[CE_DEBUG]   V-loop ADD: accumulated_result = %f + %f = %f",
                                 accumulated_result, dot_product_result, accumulated_result + dot_product_result);
                    end

                    // Only store result on last V iteration (streaming architecture)
                    if (v_idx == dim_v_reg - 1) begin
                        current_result_fp16 <= real_to_fp16(final_result);
                        $display("[CE_DEBUG]   FINAL result (v=%0d/%0d): %f -> FP16: 0x%04h",
                                 v_idx, dim_v_reg-1, final_result,
                                 real_to_fp16(final_result));
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
                $display("[CE_DEBUG] FIFO WRITE: Writing result[%0d][%0d] = %f (FP24: 0x%06x) after V=%0d iterations",
                         row_idx, col_idx, $bitstoshortreal({sign, exp8, man10, 5'b0}), {sign, exp8, man10, 5'b0}, dim_v_reg);
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
