// ------------------------------------------------------------------
// GFP8 Native Vector Dot Product
//
// Purpose: GFP8 Native Vector dot product computation
// Architecture:
//  - Pipeline stages for timing closure
//  - Parallel tree-based max-finding
//  - Direct MLP connection from inputs
//
// Pipeline Stages (not optimized):
//  - Cycle 0: Input capture
//  - Cycle 1: MLP computation + group accumulation
//  - Cycle 2: Parallel max-finding + alignment + final summation
//  - Cycle 3: Final output registered
//
// Latency: 4 clock cycles
//
// Author: Junhao Pan
// Date: 10/31/2025
// ------------------------------------------------------------------

module gfp8_nv_dot (
    // Clock and Reset
    input  logic         i_clk,
    input  logic         i_reset_n,

    // Input Enable (triggers pipeline computation)
    input  logic         i_input_valid,       // Pulse high to start computation

    // Left Native Vector (128 elements = 4 groups)
    input  logic [31:0]  i_exp_left,          // 4 bytes: [31:24]=G3, [23:16]=G2, [15:8]=G1, [7:0]=G0
    input  logic [255:0] i_man_left [0:3],    // 4 x 256-bit mantissas

    // Right Native Vector (128 elements = 4 groups)
    input  logic [31:0]  i_exp_right,         // 4 bytes: [31:24]=G3, [23:16]=G2, [15:8]=G1, [7:0]=G0
    input  logic [255:0] i_man_right [0:3],   // 4 x 256-bit mantissas

    // Result (GFP format) - registered outputs
    output logic signed [31:0] o_result_mantissa,  // Sum of 4 group results
    output logic signed [7:0]  o_result_exponent   // Maximum exponent
);

    // ===================================================================
    // STAGE 0: Input Capture
    // ===================================================================
    logic [31:0]  exp_left_captured, exp_right_captured;
    logic [255:0] man_left_captured [0:3], man_right_captured [0:3];
    
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            exp_left_captured <= 32'd0;
            exp_right_captured <= 32'd0;
            for (int i = 0; i < 4; i++) begin
                man_left_captured[i] <= 256'd0;
                man_right_captured[i] <= 256'd0;
            end
        end else begin
            if (i_input_valid) begin
                exp_left_captured <= i_exp_left;
                exp_right_captured <= i_exp_right;
                man_left_captured <= i_man_left;
                man_right_captured <= i_man_right;
            end
        end
    end

    // ===================================================================
    // Exponent Unpacking (from captured inputs)
    // ===================================================================
    logic [7:0] exp_left_unpacked [0:3];
    logic [7:0] exp_right_unpacked [0:3];
    logic signed [7:0] group_exp_sum [0:3];

    // Unpack byte-aligned exponents
    assign exp_left_unpacked[0] = exp_left_captured[7:0];
    assign exp_left_unpacked[1] = exp_left_captured[15:8];
    assign exp_left_unpacked[2] = exp_left_captured[23:16];
    assign exp_left_unpacked[3] = exp_left_captured[31:24];

    assign exp_right_unpacked[0] = exp_right_captured[7:0];
    assign exp_right_unpacked[1] = exp_right_captured[15:8];
    assign exp_right_unpacked[2] = exp_right_captured[23:16];
    assign exp_right_unpacked[3] = exp_right_captured[31:24];

    // Pre-compute group exponents
    genvar g;
    generate
        for (g = 0; g < 4; g++) begin : gen_exp_sum
            assign group_exp_sum[g] = $signed({1'b0, exp_left_unpacked[g]}) +
                                      $signed({1'b0, exp_right_unpacked[g]}) - 8'sd30;
        end
    endgenerate

    // ===================================================================
    // STAGE 1: MLP Computation + Group Accumulation (Combinational)
    // Computes from CAPTURED inputs (breaks timing path from tile_bram)
    // ===================================================================

    // MLP primitive outputs (4 groups x 4 MLPs each = 16 total)
    logic signed [31:0] mlp_result [0:3][0:3];  // [group][mlp_instance]

    // Group accumulators (combinational sum of 4 MLPs per group)
    logic signed [31:0] group_accumulator [0:3];

    // Generate 4 groups, each with 4 MLP instances
    genvar inst;
    generate
        for (g = 0; g < 4; g++) begin : gen_groups
            for (inst = 0; inst < 4; inst++) begin : gen_mlp
                localparam int ELEM_START = inst * 8;
                localparam int ELEM_END = ELEM_START + 7;

                // ACX_INT_MULT_ADD primitive - from CAPTURED inputs
                ACX_INT_MULT_ADD #(
                    .int_size(8),               // 8-bit signed integers
                    .num_mult(8),               // 8 parallel multiplications
                    .int_unsigned_a(0),         // Signed input A
                    .int_unsigned_b(0),         // Signed input B
                    .accumulate(0),             // No multi-cycle accumulation
                    .in_reg_enable(0),          // No input registers
                    .pipeline_regs(0),          // No pipeline registers
                    .dout_size(32)              // 32-bit output
                ) i_mult_add (
                    .i_clk(i_clk),
                    // From CAPTURED inputs (timing path broken)
                    .i_din_a(man_left_captured[g][(ELEM_END*8)+7:ELEM_START*8]),
                    .i_din_b(man_right_captured[g][(ELEM_END*8)+7:ELEM_START*8]),
                    .i_in_reg_a_ce(1'b0),
                    .i_in_reg_b_ce(1'b0),
                    .i_in_reg_rstn(1'b1),
                    .i_pipeline_ce(1'b0),
                    .i_pipeline_rstn(1'b1),
                    .i_load(1'b0),
                    .o_dout(mlp_result[g][inst])
                );
            end

            // // Group accumulator: sum 4 MLP partial results
            // assign group_accumulator[g] = mlp_result[g][0] + mlp_result[g][1] +
            //                              mlp_result[g][2] + mlp_result[g][3];
        end
    endgenerate

    // ===================================================================
    // STAGE 2 REGISTERS: Group Results (Second Pipeline Register)
    // ===================================================================
    logic signed [31:0] group_mantissa_reg [0:3];
    logic signed [7:0]  group_exponent_reg [0:3];
    logic               stage1_valid, stage2_valid;

    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            stage1_valid <= 1'b0;
            stage2_valid <= 1'b0;
            for (int i = 0; i < 4; i++) begin
                group_mantissa_reg[i] <= 32'sd0;
                group_exponent_reg[i] <= 8'sd0;
            end
        end else begin
            stage1_valid <= i_input_valid;  // Track input_valid through pipeline
            stage2_valid <= stage1_valid;   // Advance to stage 2
            
            // Register MLP results after they're computed
            for (int i = 0; i < 4; i++) begin
                // group_mantissa_reg[i] <= group_accumulator[i];
                group_mantissa_reg[i] <= mlp_result[i][0] + mlp_result[i][1] + mlp_result[i][2] + mlp_result[i][3];
                group_exponent_reg[i] <= group_exp_sum[i];
            end
        end
    end

    // ===================================================================
    // Parallel Tree-Based Max Finding (Combinational)
    // Find maximum exponent using 2-level tree for speed
    // ===================================================================
    logic signed [7:0] max_exp_01, max_exp_23, max_exponent;

    // Level 1: Compare pairs in parallel
    always_comb begin
        // Compare groups 0 and 1
        max_exp_01 = (group_exponent_reg[0] > group_exponent_reg[1]) ?
                     group_exponent_reg[0] : group_exponent_reg[1];

        // Compare groups 2 and 3
        max_exp_23 = (group_exponent_reg[2] > group_exponent_reg[3]) ?
                     group_exponent_reg[2] : group_exponent_reg[3];
    end

    // Level 2: Final comparison
    always_comb begin
        max_exponent = (max_exp_01 > max_exp_23) ? max_exp_01 : max_exp_23;
    end

    // ===================================================================
    // STAGE 2: Exponent Alignment and NV Summation (Combinational)
    // ===================================================================

    // Aligned mantissas
    logic signed [31:0] aligned_mantissa [0:3];

    // Exponent differences for alignment
    logic [7:0] exp_diff [0:3];

    // Parallel alignment computation
    generate
        for (g = 0; g < 4; g++) begin : gen_align
            always_comb begin
                exp_diff[g] = max_exponent - group_exponent_reg[g];

                if (exp_diff[g] > 31) begin
                    // Underflow - set to zero
                    aligned_mantissa[g] = 32'sd0;
                end else begin
                    // Arithmetic right-shift to preserve sign
                    aligned_mantissa[g] = $signed(group_mantissa_reg[g]) >>> exp_diff[g];
                end
            end
        end
    endgenerate

    // Sum all aligned mantissas using adder tree for speed
    logic signed [31:0] sum_01, sum_23, nv_sum_mantissa;
    assign sum_01 = aligned_mantissa[0] + aligned_mantissa[1];
    assign sum_23 = aligned_mantissa[2] + aligned_mantissa[3];
    assign nv_sum_mantissa = sum_01 + sum_23;

    // ===================================================================
    // STAGE 3 REGISTERS: Final Output (Third Pipeline Register)
    // ===================================================================
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            o_result_mantissa <= 32'sd0;
            o_result_exponent <= 8'sd0;
        end else begin
            if (stage2_valid) begin
                o_result_mantissa <= nv_sum_mantissa;
                o_result_exponent <= max_exponent;
            end
        end
    end

    // ===================================================================
    // Debug Output (Simulation Only)
    // ===================================================================
    `ifdef SIMULATION
    always @(posedge i_clk) begin
        if (i_input_valid) begin
            $display("[NV_DOT_ULTRA] @%0t Cycle 0: Capturing inputs (timing fix)", $time);
            $display("[NV_DOT_ULTRA]   Left exp: 0x%08x, Right exp: 0x%08x",
                     i_exp_left, i_exp_right);
        end
        if (stage1_valid) begin
            $display("[NV_DOT_ULTRA] @%0t Cycle 1: MLP compute from captured inputs", $time);
        end
        if (stage2_valid) begin
            $display("[NV_DOT_ULTRA] @%0t Cycle 2: Alignment, max_exp=%0d",
                     $time, max_exponent);
            for (int i = 0; i < 4; i++) begin
                $display("[NV_DOT_ULTRA]   Group[%0d]: mant=%0d, exp=%0d",
                         i, group_mantissa_reg[i], group_exponent_reg[i]);
            end
        end
    end
    `endif

endmodule