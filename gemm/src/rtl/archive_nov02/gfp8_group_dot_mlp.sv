// ------------------------------------------------------------------
// GFP8 Group Dot Product Module (MLP72 Hardware Accelerated)
//
// Purpose: Compute dot product of 32-pair GFP8 vectors (one group)
// Algorithm: Hardware-accelerated multiply-accumulate using ACX_INT_MULT_ADD primitives
//
// Input Format:
//  - Two 5-bit exponents (bias=15, shared across 32 elements)
//  - Two 256-bit mantissa vectors (32 x 8-bit signed integers)
//
// Output Format:
//  - Result mantissa: 32-bit signed integer (accumulated sum of products)
//  - Result exponent: 8-bit signed integer (can be negative)
//
// Data Layout (256-bit mantissa):
//  mantissa[7:0]     = element[0]
//  mantissa[15:8]    = element[1]
//  ...
//  mantissa[255:248] = element[31]
//
// GFP8 Arithmetic:
//  1. For each element pair (i=0 to 31):
//     product[i] = man_left[i] x man_right[i]  (8x8 = 16-bit signed)
//  2. Accumulate: acc = Σ(product[i])          (32-bit signed)
//  3. Exponent: exp_result = exp_left + exp_right - 30
//  4. Return: {mantissa: acc, exponent: exp_result}
//
// Hardware Implementation:
//  - Uses 4x ACX_INT_MULT_ADD primitives (8 multiplications each)
//  - Each primitive handles 8 element pairs in parallel
//  - Final sum combines all 4 partial results
//  - Leverages dedicated MLP72 blocks for optimal performance
//
// Performance: 1-cycle latency (registered outputs)
//
// Author: Junhao Pan
// Date: 10/09/2025
// ------------------------------------------------------------------

module gfp8_group_dot_mlp #(
    parameter int GROUP_ID = 0  // For debug messages
)(
    // Clock and Reset
    input  logic         i_clk,
    input  logic         i_reset_n,
    
    // Group A (left vector)
    input  logic [7:0]   i_exp_left,      // 8-bit exponent (bias=15)
    input  logic [255:0] i_man_left,      // 32 x 8-bit signed mantissas
    
    // Group B (right vector)  
    input  logic [7:0]   i_exp_right,     // 8-bit exponent (bias=15)
    input  logic [255:0] i_man_right,     // 32 x 8-bit signed mantissas
    
    // Result (GFP format) - registered outputs
    output logic signed [31:0] o_result_mantissa,  // Accumulated sum of products
    output logic signed [7:0]  o_result_exponent   // exp_left + exp_right - 30
);

    // ===================================================================
    // Local Parameters
    // ===================================================================
    localparam int GFP_GROUP_SIZE = 32;  // Elements per group
    localparam int GFP_INT_SIZE = 8;     // Bits per mantissa element
    localparam int GFP_BIAS = 15;        // Exponent bias
    
    // ===================================================================
    // Internal Signals
    // ===================================================================
    
    // MLP primitive outputs (4 instances, 8 multiplications each)
    logic signed [31:0] mult_add_result [0:3];  // 4 partial sums
    
    // Final accumulator (sum of 4 partial results) - combinational
    logic signed [31:0] accumulator;
    
    // Exponent calculation - combinational
    logic signed [7:0] exp_sum;
    
    // Output registers (1-cycle latency)
    logic signed [31:0] result_mantissa_reg;
    logic signed [7:0]  result_exponent_reg;
    
    // ===================================================================
    // MLP72 Hardware-Accelerated Dot Product Computation
    // ===================================================================
    
    // Generate 4 instances of ACX_INT_MULT_ADD (8 multiplications each)
    genvar inst;
    generate
        for (inst = 0; inst < 4; inst++) begin : gen_mult_add
            // Each instance handles 8 consecutive elements
            // Instance 0: elements 0-7, Instance 1: elements 8-15, etc.
            localparam int ELEM_START = inst * 8;
            localparam int ELEM_END = ELEM_START + 7;
            
            // ACX_INT_MULT_ADD primitive (hardware-accelerated)
            ACX_INT_MULT_ADD #(
                .int_size(8),               // 8-bit signed integers
                .num_mult(8),               // 8 parallel multiplications per instance
                .int_unsigned_a(0),         // Signed input A
                .int_unsigned_b(0),         // Signed input B
                .accumulate(0),             // No multi-cycle accumulation
                .in_reg_enable(0),          // No input registers (already registered externally)
                .pipeline_regs(0),          // Match current 1-cycle latency
                .dout_size(32)              // 32-bit output for sum
            ) i_mult_add_inst (
                .i_clk(i_clk),
                .i_din_a(i_man_left[(ELEM_END*8)+7:ELEM_START*8]),   // 64-bit slice (8x8-bit)
                .i_din_b(i_man_right[(ELEM_END*8)+7:ELEM_START*8]),  // 64-bit slice (8x8-bit)
                .i_in_reg_a_ce(1'b0),      // Not used (in_reg_enable=0)
                .i_in_reg_b_ce(1'b0),      // Not used (in_reg_enable=0)
                .i_in_reg_rstn(1'b1),      // Not used (in_reg_enable=0)
                .i_pipeline_ce(1'b0),      // Not used (pipeline_regs=0)
                .i_pipeline_rstn(1'b1),    // Not used (pipeline_regs=0)
                .i_load(1'b0),             // Not used (accumulate=0)
                .o_dout(mult_add_result[inst])                       // 32-bit partial sum
            );
        end
    endgenerate
    
    // ===================================================================
    // Final Accumulation and Exponent Calculation
    // ===================================================================
    always_comb begin
        // Sum all 4 partial results from MLP primitives
        accumulator = mult_add_result[0] + mult_add_result[1] + 
                     mult_add_result[2] + mult_add_result[3];
        
        // Calculate result exponent: exp_left + exp_right - 2*bias
        // With bias=15: exp_sum = exp_left + exp_right - 30
        // Note: Result can be negative when both exponents are small
        // Note: exp=0 is a valid GFP8 exponent (represents 2^(-15)), not zero!
        exp_sum = $signed(i_exp_left + i_exp_right) - 8'sd30;
        
        // `ifdef SIMULATION
        // $display("[GROUP_DOT_MLP_G%0d] @%0t exp_left=%0d, exp_right=%0d -> exp_sum=%0d (formula: %0d+%0d-30)",
        //          GROUP_ID, $time, i_exp_left, i_exp_right, exp_sum, i_exp_left, i_exp_right);
        // $display("[GROUP_DOT_MLP_G%0d] @%0t Partial sums: [0]=%0d, [1]=%0d, [2]=%0d, [3]=%0d, total=%0d",
        //          GROUP_ID, $time, mult_add_result[0], mult_add_result[1], mult_add_result[2], mult_add_result[3], accumulator);
        // `endif
    end
    
    // ===================================================================
    // Output Registers (1-cycle latency)
    // ===================================================================
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            result_mantissa_reg <= 32'sd0;
            result_exponent_reg <= 8'sd0;
        end else begin
            result_mantissa_reg <= accumulator;
            result_exponent_reg <= exp_sum;
        end
    end
    
    // ===================================================================
    // Output Assignment
    // ===================================================================
    assign o_result_mantissa = result_mantissa_reg;
    assign o_result_exponent = result_exponent_reg;

endmodule


