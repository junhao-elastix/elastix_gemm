// ------------------------------------------------------------------
// Floating-Point Adder Pipeline
//
// Purpose: Sum N floating-point values using integer-domain arithmetic
//          to eliminate compounding rounding errors
//
// Architecture:
//   1. fp_to_int: Convert all FP inputs to wide fixed-point integers
//   2. int_adder_tree: Sum integers (exact, no rounding)
//   3. int_to_fp: Convert result to FP with IEEE 754 round-to-nearest-even
//
// Key Insight: Only ONE rounding operation at the final conversion,
//              instead of rounding at each addition stage.
//
// Supported Configurations:
//   - Input:  FP24 (24-bit) or FP16 (16-bit)
//   - Output: FP24 (24-bit) or FP16 (16-bit)
//   - Inputs: 2, 4, 8, or 16 values
//
// Latency: 1 (fp_to_int) + ceil(log2(N)/SEG_LEN) (adder) + 2 (int_to_fp) cycles
//
// Author: Generated for MLP GEMM project
// Date: Dec 2025
// ------------------------------------------------------------------

`timescale 1ps / 1ps
`default_nettype none

module comp_fp_adder_pipeline #(
    parameter int NUM_INPUTS   = 4,      // Power of 2: 2, 4, 8, 16
    parameter int FP_IN_WIDTH  = 24,     // Input: 24 (FP24) or 16 (FP16)
    parameter int FP_OUT_WIDTH = 16,     // Output: 24 (FP24) or 16 (FP16)
    parameter int INT_WIDTH    = 128,    // Internal integer width
    parameter int FRAC_BITS    = 48,     // Fixed-point fractional bits
    parameter int SEG_LEN      = 2       // Adder tree pipeline segment length
) (
    input  logic                                     clk,
    input  logic                                     rst_n,
    input  logic                                     en,
    
    input  logic [NUM_INPUTS-1:0][FP_IN_WIDTH-1:0]   i_fp,
    input  logic                                     i_valid,
    
    output logic [FP_OUT_WIDTH-1:0]                  o_fp,
    output logic                                     o_valid
);

    // =========================================================================
    // Stage 1: FP to Integer Conversion (NUM_INPUTS parallel converters)
    // =========================================================================
    logic [NUM_INPUTS-1:0][INT_WIDTH-1:0] int_values;
    logic [NUM_INPUTS-1:0]                int_valid;
    
    generate
        for (genvar i = 0; i < NUM_INPUTS; i = i + 1) begin : gen_fp_to_int
            fp_to_int #(
                .FP_WIDTH  (FP_IN_WIDTH),
                .INT_WIDTH (INT_WIDTH),
                .FRAC_BITS (FRAC_BITS)
            ) u_fp_to_int (
                .clk     (clk),
                .rst_n   (rst_n),
                .i_fp    (i_fp[i]),
                .i_valid (i_valid),
                .o_int   (int_values[i]),
                .o_valid (int_valid[i])
            );
        end
    endgenerate
    
    // Use valid from first converter (all are synchronized)
    logic stage1_valid;
    assign stage1_valid = int_valid[0];

    // =========================================================================
    // Stage 2: Integer Adder Tree
    // =========================================================================
    logic [INT_WIDTH-1:0] int_sum;
    logic                 adder_valid;
    
    int_adder_tree #(
        .INT_WIDTH (INT_WIDTH),
        .NUM_ELS   (NUM_INPUTS),
        .SEG_LEN   (SEG_LEN)
    ) u_adder_tree (
        .clk     (clk),
        .rst_n   (rst_n),
        .en      (en),
        .i_valid (stage1_valid),
        .i_data  (int_values),
        .o_sum   (int_sum),
        .o_valid (adder_valid)
    );

    // =========================================================================
    // Stage 3: Integer to FP Conversion
    // =========================================================================
    int_to_fp #(
        .INT_WIDTH (INT_WIDTH),
        .FP_WIDTH  (FP_OUT_WIDTH),
        .FRAC_BITS (FRAC_BITS)
    ) u_int_to_fp (
        .clk     (clk),
        .rst_n   (rst_n),
        .i_int   (int_sum),
        .i_valid (adder_valid),
        .o_fp    (o_fp),
        .o_valid (o_valid)
    );

    // =========================================================================
    // Latency Calculation (for documentation)
    // =========================================================================
    // Total latency = 1 (fp_to_int) + ceil(log2(NUM_INPUTS)/SEG_LEN) + 2 (int_to_fp)
    
    function automatic int cdiv(input int x, input int y);
        return (x + y - 1) / y;
    endfunction
    
    localparam int ADDER_STAGES = $clog2(NUM_INPUTS);
    localparam int ADDER_LATENCY = cdiv(ADDER_STAGES, SEG_LEN);
    localparam int TOTAL_LATENCY = 1 + ADDER_LATENCY + 2;

    // =========================================================================
    // Parameter Validation
    // =========================================================================
    initial begin
        assert (NUM_INPUTS >= 2 && NUM_INPUTS <= 16)
            else $error("NUM_INPUTS must be between 2 and 16");
        assert ((NUM_INPUTS & (NUM_INPUTS - 1)) == 0)
            else $error("NUM_INPUTS must be a power of 2");
        assert (FP_IN_WIDTH == 24 || FP_IN_WIDTH == 16)
            else $error("FP_IN_WIDTH must be 24 (FP24) or 16 (FP16)");
        assert (FP_OUT_WIDTH == 24 || FP_OUT_WIDTH == 16)
            else $error("FP_OUT_WIDTH must be 24 (FP24) or 16 (FP16)");
        assert (INT_WIDTH >= 64 && INT_WIDTH <= 256)
            else $error("INT_WIDTH must be between 64 and 256");
        
        $display("fp_adder_pipeline: NUM_INPUTS=%0d, FP_IN=%0d, FP_OUT=%0d, INT=%0d, LATENCY=%0d",
                 NUM_INPUTS, FP_IN_WIDTH, FP_OUT_WIDTH, INT_WIDTH, TOTAL_LATENCY);
    end

endmodule

`default_nettype wire

