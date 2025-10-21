// ------------------------------------------------------------------
// GFP8 Group Dot Product Module (Registered)
//
// Purpose: Compute dot product of 32-pair GFP8 vectors (one group)
// Algorithm: Integer-only multiply-accumulate with exponent calculation
//
// Input Format:
//  - Two 5-bit exponents (bias=15, shared across 32 elements)
//  - Two 256-bit mantissa vectors (32 × 8-bit signed integers)
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
//     product[i] = man_left[i] × man_right[i]  (8×8 = 16-bit signed)
//  2. Accumulate: acc = Σ(product[i])          (32-bit signed)
//  3. Exponent: exp_result = exp_left + exp_right - 30
//  4. Return: {mantissa: acc, exponent: exp_result}
//
// Performance: 1-cycle latency (registered outputs)
//
// Author: Refactoring from compute_engine.sv
// Date: Thu Oct 9 2025
// ------------------------------------------------------------------

module gfp8_group_dot #(
    parameter int GROUP_ID = 0  // For debug messages
)(
    // Clock and Reset
    input  logic         i_clk,
    input  logic         i_reset_n,
    
    // Group A (left vector)
    input  logic [4:0]   i_exp_left,      // 5-bit exponent (bias=15)
    input  logic [255:0] i_man_left,      // 32 × 8-bit signed mantissas
    
    // Group B (right vector)  
    input  logic [4:0]   i_exp_right,     // 5-bit exponent (bias=15)
    input  logic [255:0] i_man_right,     // 32 × 8-bit signed mantissas
    
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
    
    // Individual mantissa elements (unpacked for readability)
    logic signed [7:0] left_element [0:31];
    logic signed [7:0] right_element [0:31];
    
    // Intermediate products (combinational)
    logic signed [15:0] product [0:31];  // 8×8 = 16-bit signed
    
    // Accumulator (sum of 32 products) - combinational
    // Worst case: 32 × (127 × 127) = 516,096 → needs 20 bits
    // Use 32 bits for safety and sign extension
    logic signed [31:0] accumulator;
    
    // Exponent calculation - combinational
    logic signed [7:0] exp_sum;
    
    // Output registers (1-cycle latency)
    logic signed [31:0] result_mantissa_reg;
    logic signed [7:0]  result_exponent_reg;
    
    // ===================================================================
    // Mantissa Unpacking
    // ===================================================================
    genvar i;
    generate
        for (i = 0; i < GFP_GROUP_SIZE; i++) begin : gen_unpack
            // Extract 8-bit signed elements from packed vectors
            assign left_element[i]  = i_man_left[i*GFP_INT_SIZE +: GFP_INT_SIZE];
            assign right_element[i] = i_man_right[i*GFP_INT_SIZE +: GFP_INT_SIZE];
        end
    endgenerate
    
    // ===================================================================
    // Dot Product Computation (Combinational)
    // ===================================================================
    always_comb begin
        // Initialize accumulator
        accumulator = 32'sd0;
        
        // Handle special case: zero exponents → zero result
        if (i_exp_left == 5'h00 || i_exp_right == 5'h00) begin
            accumulator = 32'sd0;
            exp_sum = 8'sd0;
        end else begin
            // Compute element-wise products and accumulate
            for (int j = 0; j < GFP_GROUP_SIZE; j++) begin
                product[j] = left_element[j] * right_element[j];
                accumulator = accumulator + product[j];
            end
            
            // Calculate result exponent: exp_left + exp_right - 2*bias
            // With bias=15: exp_sum = exp_left + exp_right - 30
            // Note: Result can be negative when both exponents are small
            exp_sum = $signed({3'b0, i_exp_left} + {3'b0, i_exp_right}) - 8'sd30;
            
            `ifdef SIM_VERBOSE
            if (i_exp_left != 0 && i_exp_right != 0) begin
                $display("[GROUP_DOT_G%0d] @%0t exp_left=%0d, exp_right=%0d -> exp_sum=%0d (formula: %0d+%0d-30)",
                         GROUP_ID, $time, i_exp_left, i_exp_right, exp_sum, i_exp_left, i_exp_right);
                $display("[GROUP_DOT_G%0d] @%0t Sample: left[0]=%0d, left[1]=%0d, right[0]=%0d, right[1]=%0d, acc=%0d",
                         GROUP_ID, $time, left_element[0], left_element[1], right_element[0], right_element[1], accumulator);
            end
            `endif
        end
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


