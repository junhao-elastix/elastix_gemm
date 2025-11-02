// ------------------------------------------------------------------
// GFP8 Native Vector Dot Product Module (Fully Merged & Optimized)
//
// Purpose: Compute dot product of 128-pair GFP8 vectors (one Native Vector)
// Architecture: Merged MLP primitives + group accumulation + NV accumulation
//
// Optimization: Fully pipelined 3-cycle implementation
//  - Merged gfp8_group_dot_mlp logic directly into this module
//  - Eliminated intermediate group_dot output registers
//  - Single pipeline stage for all group computations
//
// Input Format:
//  - 32-bit packed exponents per side (4 bytes, one per group, byte-aligned)
//  - Four 256-bit mantissa vectors per side (4 groups x 32 elements = 128 elements)
//
// Exponent Packing (byte-aligned):
//  [31:24] = Group 3 exponent
//  [23:16] = Group 2 exponent
//  [15:8]  = Group 1 exponent
//  [7:0]   = Group 0 exponent
//
// Output Format:
//  - Result mantissa: 32-bit signed integer (sum of 4 group results)
//  - Result exponent: 8-bit signed integer (aligned to maximum exponent)
//
// Latency: 3 clock cycles (fully optimized)
//  - Cycle 0: input_valid assertion + input capture
//  - Cycle 1: MLP computation + group accumulation + exp calculation (REGISTERED)
//  - Cycle 2: Exponent alignment + NV summation (REGISTERED) + output valid
//
// Author: Merged optimization
// Date: Oct 29 2025
// ------------------------------------------------------------------

module gfp8_nv_dot (
    // Clock and Reset
    input  logic         i_clk,
    input  logic         i_reset_n,
    
    // Input Enable (register inputs only when high)
    input  logic         i_input_valid,       // Pulse high to latch new inputs
    
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
    // INPUT REGISTERS (Single stage - Cycle 0)
    // ===================================================================
    // BCV controller guarantees stable inputs during ST_COMPUTE_NV state
    
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
    // Unpack Byte-Aligned Exponents
    // ===================================================================
    
    logic [7:0] exp_left_unpacked [0:3];
    logic [7:0] exp_right_unpacked [0:3];
    
    assign exp_left_unpacked[0] = exp_left_captured[7:0];
    assign exp_left_unpacked[1] = exp_left_captured[15:8];
    assign exp_left_unpacked[2] = exp_left_captured[23:16];
    assign exp_left_unpacked[3] = exp_left_captured[31:24];
    
    assign exp_right_unpacked[0] = exp_right_captured[7:0];
    assign exp_right_unpacked[1] = exp_right_captured[15:8];
    assign exp_right_unpacked[2] = exp_right_captured[23:16];
    assign exp_right_unpacked[3] = exp_right_captured[31:24];
    
    // ===================================================================
    // STAGE 1: MLP Computation + Group Accumulation (Combinational)
    // ===================================================================
    // This is the heart of the optimization: all 4 groups computed in parallel
    // Each group: 4x MLP primitives -> accumulate -> single group result
    // All combinational, registered at the end
    
    // MLP primitive outputs (4 groups x 4 MLPs each = 16 total)
    logic signed [31:0] mlp_result [0:3][0:3];  // [group][mlp_instance]
    
    // Group accumulators (combinational sum of 4 MLPs per group)
    logic signed [31:0] group_accumulator [0:3];
    
    // Group exponents (combinational calculation)
    logic signed [7:0] group_exp_calc [0:3];
    
    // Generate 4 groups, each with 4 MLP instances
    genvar g, inst;
    generate
        for (g = 0; g < 4; g++) begin : gen_groups
            for (inst = 0; inst < 4; inst++) begin : gen_mlp
                localparam int ELEM_START = inst * 8;
                localparam int ELEM_END = ELEM_START + 7;
                
                // ACX_INT_MULT_ADD primitive (hardware MLP72)
                ACX_INT_MULT_ADD #(
                    .int_size(8),               // 8-bit signed integers
                    .num_mult(8),               // 8 parallel multiplications per instance
                    .int_unsigned_a(0),         // Signed input A
                    .int_unsigned_b(0),         // Signed input B
                    .accumulate(0),             // No multi-cycle accumulation
                    .in_reg_enable(0),          // No input registers
                    .pipeline_regs(0),          // No pipeline registers (fully combinational)
                    .dout_size(32)              // 32-bit output for sum
                ) i_mult_add (
                    .i_clk(i_clk),
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
            
            // Group accumulator: sum 4 MLP partial results (combinational)
            assign group_accumulator[g] = mlp_result[g][0] + mlp_result[g][1] + 
                                         mlp_result[g][2] + mlp_result[g][3];
            
            // Group exponent calculation (combinational)
            assign group_exp_calc[g] = $signed(exp_left_unpacked[g] + exp_right_unpacked[g]) - 8'sd30;
        end
    endgenerate
    
    // ===================================================================
    // STAGE 1 REGISTERS: Group Results (End of Cycle 1)
    // ===================================================================
    logic signed [31:0] group_mantissa_reg [0:3];
    logic signed [7:0]  group_exponent_reg [0:3];
    
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            for (int i = 0; i < 4; i++) begin
                group_mantissa_reg[i] <= 32'sd0;
                group_exponent_reg[i] <= 8'sd0;
            end
        end else begin
            for (int i = 0; i < 4; i++) begin
                group_mantissa_reg[i] <= group_accumulator[i];
                group_exponent_reg[i] <= group_exp_calc[i];
            end
        end
    end
    
    // ===================================================================
    // STAGE 2: Exponent Alignment and NV Summation (Combinational)
    // ===================================================================
    
    // Find maximum exponent
    logic signed [7:0] max_exponent;
    
    // Aligned mantissas
    logic signed [31:0] aligned_mantissa [0:3];
    
    // Exponent differences
    logic [7:0] exp_diff [0:3];
    
    // Final NV sum
    logic signed [31:0] nv_sum_mantissa;
    
    always_comb begin
        // Find maximum exponent among all 4 groups
        max_exponent = group_exponent_reg[0];
        for (int i = 1; i < 4; i++) begin
            if (group_exponent_reg[i] > max_exponent) begin
                max_exponent = group_exponent_reg[i];
            end
        end
        
        // Align all mantissas to the maximum exponent
        for (int i = 0; i < 4; i++) begin
            exp_diff[i] = max_exponent - group_exponent_reg[i];
            
            if (exp_diff[i] > 31) begin
                // Underflow - set to zero
                aligned_mantissa[i] = 32'sd0;
            end else begin
                // Arithmetic right-shift to preserve sign
                aligned_mantissa[i] = $signed(group_mantissa_reg[i]) >>> exp_diff[i];
            end
        end
        
        // Sum all aligned mantissas
        nv_sum_mantissa = aligned_mantissa[0] + aligned_mantissa[1] + 
                          aligned_mantissa[2] + aligned_mantissa[3];
    end
    
    // ===================================================================
    // STAGE 2 REGISTERS: Final Output (End of Cycle 2)
    // ===================================================================
    logic signed [31:0] result_mantissa_reg;
    logic signed [7:0]  result_exponent_reg;
    
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            result_mantissa_reg <= 32'sd0;
            result_exponent_reg <= 8'sd0;
        end else begin
            result_mantissa_reg <= nv_sum_mantissa;
            result_exponent_reg <= max_exponent;
        end
    end
    
    // ===================================================================
    // Output Assignment
    // ===================================================================
    assign o_result_mantissa = result_mantissa_reg;
    assign o_result_exponent = result_exponent_reg;

endmodule



