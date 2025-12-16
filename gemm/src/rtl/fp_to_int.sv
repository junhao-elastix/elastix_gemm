// ------------------------------------------------------------------
// Parameterized Floating-Point to Fixed-Point Integer Converter
//
// Purpose: Convert FP24 or FP16 to wide signed fixed-point integer
//          for exact integer-domain arithmetic (no rounding errors)
//
// Supported Formats:
//   FP24: sign[23], exp[22:15] (8-bit, bias=127), mant[14:0] (15-bit)
//   FP16: sign[15], exp[14:10] (5-bit, bias=15),  mant[9:0]  (10-bit)
//
// Output: Signed 2's complement fixed-point integer
//         The decimal point is at bit FRAC_BITS from the right
//
// Latency: 1 cycle (registered output)
//
// Author: Generated for MLP GEMM project
// Date: Dec 2025
// ------------------------------------------------------------------

`timescale 1ps / 1ps
`default_nettype none

module fp_to_int #(
    parameter int FP_WIDTH  = 24,     // 24 for FP24, 16 for FP16
    parameter int INT_WIDTH = 128,    // Output width: 64, 128, 192, 256
    parameter int FRAC_BITS = 48      // Fractional bits in fixed-point
) (
    input  logic                  clk,
    input  logic                  rst_n,
    
    input  logic [FP_WIDTH-1:0]   i_fp,
    input  logic                  i_valid,
    
    output logic [INT_WIDTH-1:0]  o_int,    // Signed 2's complement
    output logic                  o_valid
);

    // =========================================================================
    // Derived Parameters based on FP_WIDTH
    // =========================================================================
    localparam int EXP_BITS = (FP_WIDTH == 24) ? 8 : 5;
    localparam int MAN_BITS = (FP_WIDTH == 24) ? 15 : 10;
    localparam int EXP_BIAS = (FP_WIDTH == 24) ? 127 : 15;
    
    // Full mantissa includes implicit leading 1
    localparam int FULL_MAN_BITS = MAN_BITS + 1;
    
    // Maximum shift amount (to prevent overflow)
    localparam int MAX_SHIFT = INT_WIDTH - 1;

    // =========================================================================
    // Field Extraction (combinational)
    // =========================================================================
    logic                  fp_sign;
    logic [EXP_BITS-1:0]   fp_exp;
    logic [MAN_BITS-1:0]   fp_mant;
    logic [FULL_MAN_BITS-1:0] full_mant;
    
    // Extract fields based on format
    generate
        if (FP_WIDTH == 24) begin : gen_fp24
            assign fp_sign = i_fp[23];
            assign fp_exp  = i_fp[22:15];
            assign fp_mant = i_fp[14:0];
        end else begin : gen_fp16
            assign fp_sign = i_fp[15];
            assign fp_exp  = i_fp[14:10];
            assign fp_mant = i_fp[9:0];
        end
    endgenerate
    
    // Add implicit leading 1 (for normal numbers)
    assign full_mant = {1'b1, fp_mant};

    // =========================================================================
    // Zero/Denormal Detection
    // =========================================================================
    logic is_zero;
    assign is_zero = (fp_exp == '0);  // Zero or denormal -> treat as zero

    // =========================================================================
    // Shift Amount Calculation
    // =========================================================================
    // The mantissa represents 1.xxxx * 2^(exp - bias)
    // We want to place it at the correct position in the fixed-point integer
    // 
    // If exp == bias (e.g., 127 for FP24), the value is 1.xxxx
    // This should be placed with the integer part at bit FRAC_BITS
    //
    // shift_amt = exp - EXP_BIAS + FRAC_BITS - MAN_BITS
    //           = exp - EXP_BIAS + FRAC_BITS - MAN_BITS
    //
    // For exp=127, FRAC_BITS=48, MAN_BITS=15: shift = 127-127+48-15 = 33
    // The full_mant (16 bits) starts at bit 33, so MSB is at bit 48
    
    logic signed [15:0] shift_amt_signed;
    logic [7:0] shift_amt;
    logic shift_right;
    
    assign shift_amt_signed = $signed({1'b0, fp_exp}) - $signed(EXP_BIAS) + 
                              $signed(FRAC_BITS) - $signed(MAN_BITS);
    
    assign shift_right = shift_amt_signed[15];  // Negative shift = shift right
    assign shift_amt = shift_right ? (-shift_amt_signed[7:0]) : shift_amt_signed[7:0];

    // =========================================================================
    // Mantissa Positioning (combinational)
    // =========================================================================
    logic [INT_WIDTH-1:0] positioned_mant;
    logic [INT_WIDTH-1:0] extended_mant;
    
    // Zero-extend mantissa to INT_WIDTH
    assign extended_mant = {{(INT_WIDTH-FULL_MAN_BITS){1'b0}}, full_mant};
    
    always_comb begin
        if (is_zero) begin
            positioned_mant = '0;
        end else if (shift_right) begin
            // Right shift (value < 1.0 for large negative exponents)
            if (shift_amt >= INT_WIDTH) begin
                positioned_mant = '0;  // Underflow to zero
            end else begin
                positioned_mant = extended_mant >> shift_amt;
            end
        end else begin
            // Left shift (normal case)
            if (shift_amt >= (INT_WIDTH - FULL_MAN_BITS)) begin
                // Overflow - saturate (shouldn't happen in normal operation)
                positioned_mant = {1'b0, {(INT_WIDTH-1){1'b1}}};  // Max positive
            end else begin
                positioned_mant = extended_mant << shift_amt;
            end
        end
    end

    // =========================================================================
    // Sign Application (2's complement)
    // =========================================================================
    logic [INT_WIDTH-1:0] signed_result;
    
    always_comb begin
        if (fp_sign && !is_zero) begin
            // Negative: apply 2's complement
            signed_result = -positioned_mant;
        end else begin
            signed_result = positioned_mant;
        end
    end

    // =========================================================================
    // Output Register
    // =========================================================================
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            o_int   <= '0;
            o_valid <= 1'b0;
        end else begin
            o_int   <= signed_result;
            o_valid <= i_valid;
        end
    end

    // =========================================================================
    // Parameter Validation
    // =========================================================================
    initial begin
        assert (FP_WIDTH == 24 || FP_WIDTH == 16)
            else $error("FP_WIDTH must be 24 (FP24) or 16 (FP16)");
        assert (INT_WIDTH >= 64 && INT_WIDTH <= 256)
            else $error("INT_WIDTH must be between 64 and 256");
        assert (FRAC_BITS >= 16 && FRAC_BITS < INT_WIDTH)
            else $error("FRAC_BITS must be >= 16 and < INT_WIDTH");
    end

endmodule

`default_nettype wire

