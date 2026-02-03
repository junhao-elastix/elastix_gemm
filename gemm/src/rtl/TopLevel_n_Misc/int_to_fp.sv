// ------------------------------------------------------------------
// Parameterized Fixed-Point Integer to Floating-Point Converter
//
// Purpose: Convert wide signed fixed-point integer to FP24 or FP16
//          with IEEE 754 round-to-nearest-even (RNE)
//
// Supported Output Formats:
//   FP24: sign[23], exp[22:15] (8-bit, bias=127), mant[14:0] (15-bit)
//   FP16: sign[15], exp[14:10] (5-bit, bias=15),  mant[9:0]  (10-bit)
//
// Rounding: IEEE 754 Round-to-Nearest-Even
//   - Uses Guard, Round, Sticky bits (GRS)
//   - GRS > 100: round up
//   - GRS < 100: round down (truncate)
//   - GRS == 100: round to even (check LSB of mantissa)
//
// Latency: 2 cycles (pipelined)
//
// Author: Generated for MLP GEMM project
// Date: Dec 2025
// ------------------------------------------------------------------

`timescale 1ps / 1ps
`default_nettype none

module int_to_fp #(
    parameter int INT_WIDTH = 128,    // Input width: 64, 128, 192, 256
    parameter int FP_WIDTH  = 16,     // 24 for FP24, 16 for FP16
    parameter int FRAC_BITS = 48      // Where decimal point is in the integer
) (
    input  logic                  clk,
    input  logic                  rst_n,
    
    input  logic [INT_WIDTH-1:0]  i_int,    // Signed 2's complement
    input  logic                  i_valid,
    
    output logic [FP_WIDTH-1:0]   o_fp,
    output logic                  o_valid
);

    // =========================================================================
    // Derived Parameters based on FP_WIDTH
    // =========================================================================
    localparam int EXP_BITS = (FP_WIDTH == 24) ? 8 : 5;
    localparam int MAN_BITS = (FP_WIDTH == 24) ? 15 : 10;
    localparam int EXP_BIAS = (FP_WIDTH == 24) ? 127 : 15;
    localparam int EXP_MAX  = (FP_WIDTH == 24) ? 254 : 30;  // Max normal exponent
    localparam int EXP_MIN  = 1;                             // Min normal exponent

    // =========================================================================
    // Stage 1: Sign handling, absolute value, leading zero count
    // =========================================================================
    logic                   s1_valid;
    logic                   s1_sign;
    logic [INT_WIDTH-1:0]   s1_abs;
    logic [$clog2(INT_WIDTH)-1:0] s1_lzc;  // Leading zero count
    logic                   s1_is_zero;
    
    // Sign detection and absolute value
    logic                   is_negative;
    logic [INT_WIDTH-1:0]   abs_value;
    
    assign is_negative = i_int[INT_WIDTH-1];
    assign abs_value = is_negative ? (-i_int) : i_int;
    
    // Count leading zeros - priority encoder
    function automatic [$clog2(INT_WIDTH)-1:0] count_leading_zeros(input logic [INT_WIDTH-1:0] val);
        automatic logic [$clog2(INT_WIDTH)-1:0] count;
        automatic logic found;
        count = INT_WIDTH;  // Default: all zeros
        found = 1'b0;
        for (int i = INT_WIDTH-1; i >= 0; i--) begin
            if (val[i] && !found) begin
                count = INT_WIDTH - 1 - i;
                found = 1'b1;
            end
        end
        return count;
    endfunction
    
    // Stage 1 pipeline register
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            s1_valid   <= 1'b0;
            s1_sign    <= 1'b0;
            s1_abs     <= '0;
            s1_lzc     <= '0;
            s1_is_zero <= 1'b1;
        end else begin
            s1_valid   <= i_valid;
            s1_sign    <= is_negative;
            s1_abs     <= abs_value;
            s1_lzc     <= count_leading_zeros(abs_value);
            s1_is_zero <= (abs_value == '0);
        end
    end

    // =========================================================================
    // Stage 2: Normalization, rounding, and assembly
    // =========================================================================
    
    // Calculate MSB position (position of highest 1)
    // MSB_pos = INT_WIDTH - 1 - LZC
    logic signed [15:0] msb_pos;
    assign msb_pos = INT_WIDTH - 1 - s1_lzc;
    
    // Calculate exponent
    // The value is: abs_value = M * 2^(MSB_pos - FRAC_BITS)
    // In FP format: 1.xxxx * 2^(exp - bias)
    // So: exp = MSB_pos - FRAC_BITS + bias
    logic signed [15:0] exp_unbiased;
    logic signed [15:0] exp_biased;
    
    assign exp_unbiased = msb_pos - FRAC_BITS;
    assign exp_biased = exp_unbiased + EXP_BIAS;
    
    // Normalize: shift to align mantissa bits
    // We want: [MSB_pos : MSB_pos - MAN_BITS] for mantissa
    //          [MSB_pos - MAN_BITS - 1] = Guard bit
    //          [MSB_pos - MAN_BITS - 2] = Round bit
    //          [MSB_pos - MAN_BITS - 3 : 0] = Sticky bits (OR of all lower bits)
    //
    // Shift amount to put MSB at bit (MAN_BITS + 3) for GRS extraction
    // We need (MAN_BITS + 3 + 1) bits = (MAN_BITS + 4) bits for rounding
    
    localparam int NORM_WIDTH = MAN_BITS + 4;  // mantissa + GRS + 1 for implied
    
    logic [INT_WIDTH-1:0] shifted_abs;
    logic [$clog2(INT_WIDTH)-1:0] shift_amt;
    logic shift_left;
    
    // Shift to normalize (put MSB at fixed position)
    // Target: MSB at bit (NORM_WIDTH - 1)
    always_comb begin
        if (s1_lzc < (INT_WIDTH - NORM_WIDTH)) begin
            // Shift right (normal case for large values)
            shift_left = 1'b0;
            shift_amt = s1_lzc - (INT_WIDTH - NORM_WIDTH - s1_lzc);
        end else begin
            // Shift left (for small values)
            shift_left = 1'b1;
            shift_amt = INT_WIDTH - NORM_WIDTH - s1_lzc;
        end
    end
    
    // Compute normalized value with sticky bit
    logic [NORM_WIDTH-1:0] norm_mant;
    logic [MAN_BITS-1:0]   raw_mant;
    logic                  guard_bit;
    logic                  round_bit;
    logic                  sticky_bit;
    
    always_comb begin
        // Direct extraction based on MSB position
        if (s1_is_zero) begin
            norm_mant = '0;
        end else if (msb_pos >= NORM_WIDTH - 1) begin
            // Need to shift right
            automatic logic [$clog2(INT_WIDTH)-1:0] rshift = msb_pos - (NORM_WIDTH - 1);
            if (rshift >= INT_WIDTH) begin
                norm_mant = '0;
            end else begin
                norm_mant = s1_abs[msb_pos -: NORM_WIDTH];
                // Calculate sticky from bits below
            end
        end else begin
            // Need to shift left (small value)
            automatic logic [$clog2(INT_WIDTH)-1:0] lshift = (NORM_WIDTH - 1) - msb_pos;
            norm_mant = s1_abs << lshift;
        end
    end
    
    // Extract mantissa and rounding bits
    // norm_mant format: [NORM_WIDTH-1] = implied 1
    //                   [NORM_WIDTH-2 : NORM_WIDTH-1-MAN_BITS] = mantissa
    //                   [NORM_WIDTH-2-MAN_BITS] = Guard
    //                   [NORM_WIDTH-3-MAN_BITS] = Round
    //                   [NORM_WIDTH-4-MAN_BITS : 0] = Sticky candidates
    
    // Extract mantissa and rounding bits using shift-based approach
    // Simplified: shift to get mantissa+GRS, compute sticky from lower bits
    logic [INT_WIDTH-1:0] shifted_val;
    logic [INT_WIDTH-1:0] sticky_mask;
    logic [MAN_BITS+3:0] extracted_bits;
    
    always_comb begin
        if (s1_is_zero) begin
            raw_mant   = '0;
            guard_bit  = 1'b0;
            round_bit  = 1'b0;
            sticky_bit = 1'b0;
        end else begin
            // Shift value right to align MSB (implied 1) at position (MAN_BITS + 3)
            // After shift: bit[MAN_BITS+3] = implied 1
            //             bits[MAN_BITS+2:3] = mantissa (MAN_BITS bits)
            //             bit[2] = guard, bit[1] = round, bit[0] = part of sticky
            if (msb_pos >= (MAN_BITS + 3)) begin
                automatic int shift_right = msb_pos - (MAN_BITS + 3);
                shifted_val = s1_abs >> shift_right;
                
                // Extract mantissa and GRS from shifted value
                extracted_bits = shifted_val[MAN_BITS+3:0];
                raw_mant = extracted_bits[MAN_BITS+2:3];  // Mantissa bits (skip implied 1 at bit MAN_BITS+3)
                guard_bit = extracted_bits[2];
                round_bit = extracted_bits[1];
                
                // Sticky: check if any bits were lost in the shift + LSB of extracted bits
                sticky_mask = ({{(INT_WIDTH-1){1'b0}}, 1'b1} << shift_right) - 1'b1;
                sticky_bit = (|(s1_abs & sticky_mask)) | extracted_bits[0];
            end else begin
                // Small value: shift left to fill mantissa
                automatic int shift_left = (MAN_BITS + 3) - msb_pos;
                shifted_val = s1_abs << shift_left;
                extracted_bits = shifted_val[MAN_BITS+3:0];
                raw_mant = extracted_bits[MAN_BITS+2:3];  // Mantissa bits (skip implied 1)
                guard_bit = extracted_bits[2];
                round_bit = extracted_bits[1];
                sticky_bit = extracted_bits[0];
            end
        end
    end
    
    // =========================================================================
    // IEEE 754 Round-to-Nearest-Even
    // =========================================================================
    logic [2:0] grs;
    logic       round_up;
    logic [MAN_BITS-1:0] rounded_mant;
    logic       mant_overflow;
    
    assign grs = {guard_bit, round_bit, sticky_bit};
    
    always_comb begin
        // Round-to-nearest-even logic
        if (grs > 3'b100) begin
            // GRS > 0.5: round up
            round_up = 1'b1;
        end else if (grs < 3'b100) begin
            // GRS < 0.5: round down (truncate)
            round_up = 1'b0;
        end else begin
            // GRS == 0.5: round to even (check LSB)
            round_up = raw_mant[0];
        end
    end
    
    // Apply rounding
    logic [MAN_BITS:0] mant_plus_one;
    assign mant_plus_one = raw_mant + 1'b1;
    assign mant_overflow = mant_plus_one[MAN_BITS];
    
    always_comb begin
        if (round_up) begin
            rounded_mant = mant_plus_one[MAN_BITS-1:0];
        end else begin
            rounded_mant = raw_mant;
        end
    end
    
    // =========================================================================
    // Exponent Adjustment and Overflow/Underflow Handling
    // =========================================================================
    logic [EXP_BITS-1:0] final_exp;
    logic [MAN_BITS-1:0] final_mant;
    logic                is_overflow;
    logic                is_underflow;
    
    // Adjust exponent if mantissa overflowed during rounding
    logic signed [15:0] adjusted_exp;
    assign adjusted_exp = exp_biased + (round_up && mant_overflow ? 1 : 0);
    
    // Subnormal calculation signals
    logic signed [15:0] subnormal_shift;
    logic [MAN_BITS-1:0] shifted_subnormal_mant;
    logic [MAN_BITS:0] full_normalized_mant;  // Includes implicit 1 for subnormal conversion
    
    always_comb begin
        is_overflow = 1'b0;
        is_underflow = 1'b0;
        subnormal_shift = 1 - adjusted_exp;
        shifted_subnormal_mant = '0;
        full_normalized_mant = '0;
        
        if (s1_is_zero) begin
            // Zero
            final_exp = '0;
            final_mant = '0;
        end else if (adjusted_exp > EXP_MAX) begin
            // Overflow: saturate to infinity
            is_overflow = 1'b1;
            final_exp = {EXP_BITS{1'b1}};  // All 1s = infinity
            final_mant = '0;
        end else if (adjusted_exp < EXP_MIN) begin
            // Subnormal/Denormal range: exp < 1
            // For FP16: value = 2^-14 × (mantissa/2^MAN_BITS), NO implicit 1!
            // For FP24: value = 2^-126 × (mantissa/2^MAN_BITS)
            // 
            // The mantissa extraction assumed normal format (removed implicit 1),
            // but subnormals need all bits explicit. We need to add back the
            // implicit 1 and then shift for the subnormal exponent.
            
            is_underflow = 1'b1;  // Flag for debug
            final_exp = '0;  // Subnormal has exp=0
            
            // Reconstruct full normalized mantissa (with implicit 1)
            // For normal: value would be 1.mantissa
            // For subnormal: we represent as 0.mantissa shifted
            
            if (round_up && mant_overflow) begin
                // Rounded to 1.0, so full value is 10...0
                full_normalized_mant = {1'b1, {MAN_BITS{1'b0}}};
            end else begin
                // Add implicit 1 back to rounded_mant
                full_normalized_mant = {1'b1, rounded_mant};
            end
            
            // Shift right to convert from "1.xxx * 2^(exp_biased-15)" to "0.yyy * 2^-14"
            // subnormal_shift = 1 - adjusted_exp (already calculated)
            
            if (subnormal_shift >= (MAN_BITS + 1)) begin
                // Value too small - true underflow to zero
                final_mant = '0;
            end else begin
                // Shift the full normalized value
                shifted_subnormal_mant = full_normalized_mant >> subnormal_shift;
                final_mant = shifted_subnormal_mant[MAN_BITS-1:0];  // Take lower MAN_BITS bits
            end
        end else begin
            // Normal number
            final_exp = adjusted_exp[EXP_BITS-1:0];
            if (round_up && mant_overflow) begin
                // Mantissa overflowed to 1.0, so mantissa field is 0
                final_mant = '0;
            end else begin
                final_mant = rounded_mant;
            end
        end
    end
    
    // =========================================================================
    // Output Assembly and Register
    // =========================================================================
    logic [FP_WIDTH-1:0] fp_result;
    
    generate
        if (FP_WIDTH == 24) begin : gen_fp24_out
            assign fp_result = {s1_sign, final_exp, final_mant};
        end else begin : gen_fp16_out
            assign fp_result = {s1_sign, final_exp, final_mant};
        end
    endgenerate
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            o_fp    <= '0;
            o_valid <= 1'b0;
        end else begin
            o_fp    <= fp_result;
            o_valid <= s1_valid;
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

