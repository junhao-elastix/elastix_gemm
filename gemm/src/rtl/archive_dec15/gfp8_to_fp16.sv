// ------------------------------------------------------------------
// GFP8 to FP16 Converter
//
// Purpose: Convert GFP8 accumulated result to IEEE 754 FP16 format
// 
// Algorithm:
//  1. Handle zero case
//  2. Extract sign and absolute value
//  3. Find leading zeros (normalize mantissa)
//  4. Calculate FP16 exponent with bias adjustment
//  5. Handle underflow/overflow
//  6. Extract 10-bit mantissa fraction
//  7. Pack into FP16 format: [sign][exp(5)][mantissa(10)]
//
// FP16 Format (IEEE 754):
//  - Sign: 1 bit
//  - Exponent: 5 bits (bias=15, range: -14 to +15)
//  - Mantissa: 10 bits (implicit leading 1)
//
// GFP8 Format:
//  - Mantissa: 32-bit signed integer
//  - Exponent: 8-bit signed integer (UNBIASED - bias already removed by group_dot)
//
// Latency: 1 cycle (registered outputs)
//
// Author: Junhao Pan
// Date: 10/10/2025
// ------------------------------------------------------------------

module gfp8_to_fp16 (
    // Clock and Reset
    input  logic         i_clk,
    input  logic         i_reset_n,
    
    // GFP8 Input
    input  logic signed [31:0] i_gfp_mantissa,    // Signed 32-bit mantissa
    input  logic signed [7:0]  i_gfp_exponent,    // Signed 8-bit exponent
    input  logic               i_valid,           // Input valid
    
    // FP16 Output (registered)
    output logic [15:0]  o_fp16_result,           // IEEE 754 FP16 format
    output logic         o_valid                  // Output valid
);

    // ===================================================================
    // Combinational Conversion Logic
    // ===================================================================
    logic [15:0] fp16_next;
    logic valid_next;
    
    always_comb begin
        valid_next = i_valid;
        
        // Handle zero case
        if (i_gfp_mantissa == 32'sd0) begin
            fp16_next = 16'h0000;
        end else begin
            // Local variables for conversion
            automatic logic sign;
            automatic logic signed [31:0] abs_mantissa;
            automatic logic signed [7:0] exp_signed;
            automatic logic signed [8:0] fp16_exp_signed;
            automatic logic [4:0] fp16_exp;
            automatic logic [9:0] fp16_mant;
            automatic integer leading_zeros;
            
            // Rounding variables (declared here for scope)
            automatic logic round_bit;
            automatic logic sticky_bit;
            automatic logic [9:0] mant_truncated;
            automatic logic [9:0] mant_rounded;
            
            // Extract sign and absolute value
            sign = i_gfp_mantissa[31];
            abs_mantissa = sign ? -i_gfp_mantissa : i_gfp_mantissa;
            exp_signed = i_gfp_exponent;
            
            // Find leading zeros to normalize mantissa
            // Count leading zeros from MSB (bit 31) down to LSB (bit 0)
            leading_zeros = 0;
            casez (abs_mantissa)
                32'b1???????????????????????????????: leading_zeros = 0;
                32'b01??????????????????????????????: leading_zeros = 1;
                32'b001?????????????????????????????: leading_zeros = 2;
                32'b0001????????????????????????????: leading_zeros = 3;
                32'b00001???????????????????????????: leading_zeros = 4;
                32'b000001??????????????????????????: leading_zeros = 5;
                32'b0000001?????????????????????????: leading_zeros = 6;
                32'b00000001????????????????????????: leading_zeros = 7;
                32'b000000001???????????????????????: leading_zeros = 8;
                32'b0000000001??????????????????????: leading_zeros = 9;
                32'b00000000001?????????????????????: leading_zeros = 10;
                32'b000000000001????????????????????: leading_zeros = 11;
                32'b0000000000001???????????????????: leading_zeros = 12;
                32'b00000000000001??????????????????: leading_zeros = 13;
                32'b000000000000001?????????????????: leading_zeros = 14;
                32'b0000000000000001????????????????: leading_zeros = 15;
                32'b00000000000000001???????????????: leading_zeros = 16;
                32'b000000000000000001??????????????: leading_zeros = 17;
                32'b0000000000000000001?????????????: leading_zeros = 18;
                32'b00000000000000000001????????????: leading_zeros = 19;
                32'b000000000000000000001???????????: leading_zeros = 20;
                32'b0000000000000000000001??????????: leading_zeros = 21;
                32'b00000000000000000000001?????????: leading_zeros = 22;
                32'b000000000000000000000001????????: leading_zeros = 23;
                32'b0000000000000000000000001???????: leading_zeros = 24;
                32'b00000000000000000000000001??????: leading_zeros = 25;
                32'b000000000000000000000000001?????: leading_zeros = 26;
                32'b0000000000000000000000000001????: leading_zeros = 27;
                32'b00000000000000000000000000001???: leading_zeros = 28;
                32'b000000000000000000000000000001??: leading_zeros = 29;
                32'b0000000000000000000000000000001?: leading_zeros = 30;
                32'b00000000000000000000000000000001: leading_zeros = 31;
                default: leading_zeros = 32; // Should not happen (zero already handled)
            endcase
            
            // Normalize mantissa to [1.0, 2.0) by shifting left
            // After shift, bit 31 has the leading 1
            abs_mantissa = abs_mantissa << leading_zeros;
            
            // Calculate FP16 exponent
            // GFP: value = mantissa * 2^(exp_signed)  [exp_signed is UNBIASED]
            // After normalization (shifting left by leading_zeros):
            //   normalized_mantissa is in range [2^31, 2^32)
            //   value = (normalized_mantissa / 2^31) * 2^(exp_signed) / 2^(leading_zeros)
            //         = (normalized_mantissa / 2^31) * 2^(exp_signed - leading_zeros)
            // FP16: value = 1.mantissa_fraction * 2^(exp_unbiased)
            // So: exp_unbiased = exp_signed - leading_zeros + 31
            //     (The +31 accounts for normalized mantissa being in [2^31, 2^32) range)
            //     (The /2^31 is handled by extracting mantissa bits [30:21])
            // FP16 biased exponent (bias=15): fp16_exp = exp_unbiased + 15
            fp16_exp_signed = exp_signed + 31 - leading_zeros + 15;
            
            // Handle exponent range
            // FP16 exponent field: 0 = denormal/zero, 1-30 = normal, 31 = inf/NaN
            //
            // DENORMAL SUPPORT:
            // When fp16_exp_signed < 1, the value is in the denormal range.
            // FP16 denormals: exp_field=0, value = 0.mantissa × 2^(-14)
            // Minimum denormal: 2^(-24) (mantissa=1)
            //
            // For denormals, we need to denormalize by right-shifting the mantissa
            // by (1 - fp16_exp_signed) positions.
            if (fp16_exp_signed < -10) begin
                // Below minimum FP16 denormal (mantissa would be shifted out completely)
                // Minimum denormal needs at least 1 bit in 10-bit mantissa
                // With fp16_exp_signed = 0, we shift by 1, so limit is -10
                fp16_next = 16'h0000;
            end else if (fp16_exp_signed < 1) begin
                // DENORMAL RANGE: 0 >= fp16_exp_signed >= -10
                // Denormalize mantissa by right-shifting
                automatic integer denorm_shift;
                automatic logic [31:0] denorm_mantissa;
                automatic logic [9:0] mant_truncated_denorm;
                automatic logic round_bit_denorm;
                automatic logic sticky_bit_denorm;
                automatic logic [9:0] mant_rounded_denorm;

                denorm_shift = 1 - fp16_exp_signed;  // Shift amount (1 to 11)
                denorm_mantissa = abs_mantissa >> denorm_shift;

                // Extract mantissa and rounding bits from denormalized value
                mant_truncated_denorm = denorm_mantissa[30:21];
                round_bit_denorm = denorm_mantissa[20];
                sticky_bit_denorm = |denorm_mantissa[19:0];

                // IEEE 754 round-to-nearest-even for denormals
                if (round_bit_denorm && (sticky_bit_denorm || mant_truncated_denorm[0])) begin
                    mant_rounded_denorm = mant_truncated_denorm + 10'd1;
                    fp16_mant = mant_rounded_denorm[9:0];  // Denormals don't carry into exponent
                end else begin
                    fp16_mant = mant_truncated_denorm;
                end

                fp16_next = {sign, 5'b00000, fp16_mant};  // exp_field = 0 for denormals
            end else if (fp16_exp_signed > 30) begin
                // Overflow to infinity
                fp16_next = {sign, 5'b11111, 10'b0000000000};
            end else begin
                // Normal case with IEEE 754 round-to-nearest-even
                fp16_exp = fp16_exp_signed[4:0];
                
                // Extract mantissa and rounding bits
                mant_truncated = abs_mantissa[30:21];  // 10-bit mantissa
                round_bit = abs_mantissa[20];           // First discarded bit (0.5 ULP)
                sticky_bit = |abs_mantissa[19:0];      // OR of remaining 20 bits
                
                // IEEE 754 round-to-nearest-even:
                // Round up if: (round_bit=1) AND (sticky_bit=1 OR LSB=1)
                // This implements: round up if > 0.5 ULP, or if exactly 0.5 ULP and LSB is odd
                if (round_bit && (sticky_bit || mant_truncated[0])) begin
                    mant_rounded = mant_truncated + 10'd1;
                    
                    // Check for mantissa overflow (1023 + 1 = 1024 = overflow)
                    if (mant_rounded[10]) begin
                        // Mantissa overflow: increment exponent, mantissa becomes 0
                        // This represents a carry into the exponent
                        fp16_exp = fp16_exp + 5'd1;
                        fp16_mant = 10'b0000000000;
                    end else begin
                        fp16_mant = mant_rounded[9:0];
                    end
                end else begin
                    // Round down (truncate)
                    fp16_mant = mant_truncated;
                end
                
                fp16_next = {sign, fp16_exp, fp16_mant};
            end
        end
    end
    
    // ===================================================================
    // Output Registers (1-cycle latency)
    // ===================================================================
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            o_fp16_result <= 16'h0000;
            o_valid <= 1'b0;
        end else begin
            o_fp16_result <= fp16_next;
            o_valid <= valid_next;
        end
    end

endmodule


