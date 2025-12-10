// ------------------------------------------------------------------
// FP24 to FP16 Converter
//
// Purpose: Convert FP24 (24-bit floating point) to IEEE 754 FP16
//
// FP24 Format:
//   - Sign: bit 23
//   - Exponent: bits 22:15 (8 bits, bias = 127)
//   - Mantissa: bits 14:0 (15 bits, implicit leading 1)
//
// FP16 Format (IEEE 754 half precision):
//   - Sign: bit 15
//   - Exponent: bits 14:10 (5 bits, bias = 15)
//   - Mantissa: bits 9:0 (10 bits, implicit leading 1)
//
// Conversion:
//   1. Sign: direct copy
//   2. Exponent: re-bias (FP24 bias=127 → FP16 bias=15, subtract 112)
//   3. Mantissa: truncate from 15 bits to 10 bits
//
// Special Cases:
//   - Zero: exp=0, mant=0 → FP16 zero
//   - Overflow (exp > 142): saturate to FP16 max (±inf or max normal)
//   - Underflow (exp < 113): flush to zero (no denormals)
//
// Latency: 1 cycle (registered output)
//
// Author: Generated for MLP project
// Date: 2024
// ------------------------------------------------------------------

`timescale 1ns / 1ps
`default_nettype none

module fp24_to_fp16 (
    input  wire        i_clk,
    input  wire        i_reset_n,

    // FP24 input
    input  wire [23:0] i_fp24,
    input  wire        i_valid,

    // FP16 output (registered)
    output logic [15:0] o_fp16,
    output logic        o_valid
);

    // Extract FP24 fields
    wire        fp24_sign = i_fp24[23];
    wire [7:0]  fp24_exp  = i_fp24[22:15];
    wire [14:0] fp24_mant = i_fp24[14:0];

    // Intermediate signals
    logic [15:0] fp16_result;
    logic        fp16_sign;
    logic [4:0]  fp16_exp;
    logic [9:0]  fp16_mant;

    // Exponent conversion
    // FP24 exp range: 0-255 (bias 127) → actual range: -127 to +128
    // FP16 exp range: 0-31 (bias 15) → actual range: -14 to +15 (normal), with 0 and 31 special
    //
    // For normal FP16: exp_fp16 = exp_fp24 - 127 + 15 = exp_fp24 - 112
    // Valid FP16 normal range: exp_fp24 in [113, 142] → exp_fp16 in [1, 30]

    logic [8:0] exp_adjusted;  // Signed to detect underflow

    always_comb begin
        fp16_sign = fp24_sign;

        // Check for zero
        if (fp24_exp == 8'd0 && fp24_mant == 15'd0) begin
            // Zero
            fp16_exp = 5'd0;
            fp16_mant = 10'd0;
        end
        // Check for FP24 infinity/NaN (exp = 255)
        else if (fp24_exp == 8'd255) begin
            // Map to FP16 infinity/NaN
            fp16_exp = 5'd31;
            fp16_mant = (fp24_mant == 15'd0) ? 10'd0 : 10'd1;  // Inf or NaN
        end
        else begin
            // Normal number conversion
            exp_adjusted = {1'b0, fp24_exp} - 9'd112;

            if (exp_adjusted[8] || exp_adjusted == 9'd0) begin
                // Underflow: exp_fp24 < 113 → flush to zero
                fp16_exp = 5'd0;
                fp16_mant = 10'd0;
            end
            else if (exp_adjusted > 9'd30) begin
                // Overflow: exp_fp24 > 142 → saturate to infinity
                fp16_exp = 5'd31;
                fp16_mant = 10'd0;
            end
            else begin
                // Normal conversion
                fp16_exp = exp_adjusted[4:0];
                fp16_mant = fp24_mant[14:5];  // Truncate lower 5 bits
            end
        end

        fp16_result = {fp16_sign, fp16_exp, fp16_mant};
    end

    // Registered output
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            o_fp16 <= 16'd0;
            o_valid <= 1'b0;
        end else begin
            o_fp16 <= fp16_result;
            o_valid <= i_valid;
        end
    end

endmodule

`default_nettype wire
