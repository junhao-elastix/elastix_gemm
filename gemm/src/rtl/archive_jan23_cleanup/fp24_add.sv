`timescale 1ps / 1ps

// 2-Stage Pipelined FP24 Adder
//
// FP24 Format (ACX MLP native):
//  - Sign: 1 bit [23]
//  - Exponent: 8 bits [22:15] (bias=127)
//  - Mantissa: 15 bits [14:0] (implicit leading 1)
//
// Pipeline stages:
//  - Stage 1: Field extraction, exponent comparison, mantissa alignment
//  - Stage 2: Addition, normalization, result assembly
//
// Latency: 2 cycles (i_valid → o_valid)

`default_nettype none

module fp24_add (
    input  logic        clk,
    input  logic        rstn,
    input  logic [23:0] a,
    input  logic [23:0] b,
    input  logic        i_valid,
    output logic [23:0] sum,
    output logic        o_valid
);

    // =========================================================================
    // Stage 1: Field Extraction and Alignment (Combinational)
    // =========================================================================
    
    // Field Extraction
    logic        a_sign, b_sign;
    logic [7:0]  a_exp, b_exp;
    logic [14:0] a_mant, b_mant;

    assign a_sign = a[23];
    assign a_exp  = a[22:15];
    assign a_mant = a[14:0];

    assign b_sign = b[23];
    assign b_exp  = b[22:15];
    assign b_mant = b[14:0];

    // Special Case Detection
    logic a_is_zero, b_is_zero;
    logic a_is_inf_nan, b_is_inf_nan;

    assign a_is_zero    = (a_exp == 8'd0);
    assign b_is_zero    = (b_exp == 8'd0);
    assign a_is_inf_nan = (a_exp == 8'd255);
    assign b_is_inf_nan = (b_exp == 8'd255);

    // Add Implicit Leading 1
    logic [15:0] a_mant_full, b_mant_full;

    assign a_mant_full = a_is_zero ? 16'd0 : {1'b1, a_mant};
    assign b_mant_full = b_is_zero ? 16'd0 : {1'b1, b_mant};

    // Exponent Comparison and Alignment
    logic        a_exp_larger;
    logic [7:0]  exp_diff;
    logic [7:0]  larger_exp;

    assign a_exp_larger = (a_exp >= b_exp);
    assign exp_diff     = a_exp_larger ? (a_exp - b_exp) : (b_exp - a_exp);
    assign larger_exp   = a_exp_larger ? a_exp : b_exp;

    // Extended precision: {mantissa_16bit, 3 guard bits} = 19 bits
    logic [18:0] a_mant_ext, b_mant_ext;
    assign a_mant_ext = {a_mant_full, 3'b000};
    assign b_mant_ext = {b_mant_full, 3'b000};

    // Shift amount capped at 19
    logic [4:0] shift_amt;
    assign shift_amt = (exp_diff > 8'd19) ? 5'd19 : exp_diff[4:0];

    // Aligned mantissas
    logic [18:0] a_mant_aligned, b_mant_aligned;
    assign a_mant_aligned = a_exp_larger ? a_mant_ext : (a_mant_ext >> shift_amt);
    assign b_mant_aligned = a_exp_larger ? (b_mant_ext >> shift_amt) : b_mant_ext;

    // Effective subtract
    logic eff_subtract;
    assign eff_subtract = (a_sign != b_sign);

    // =========================================================================
    // Stage 1 Pipeline Registers
    // =========================================================================
    logic        s1_valid;
    logic [23:0] s1_a, s1_b;
    logic        s1_a_sign, s1_b_sign;
    logic        s1_a_is_zero, s1_b_is_zero;
    logic        s1_a_is_inf_nan, s1_b_is_inf_nan;
    logic [7:0]  s1_larger_exp;
    logic [18:0] s1_a_mant_aligned, s1_b_mant_aligned;
    logic        s1_eff_subtract;

    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            s1_valid           <= 1'b0;
            s1_a               <= 24'd0;
            s1_b               <= 24'd0;
            s1_a_sign          <= 1'b0;
            s1_b_sign          <= 1'b0;
            s1_a_is_zero       <= 1'b0;
            s1_b_is_zero       <= 1'b0;
            s1_a_is_inf_nan    <= 1'b0;
            s1_b_is_inf_nan    <= 1'b0;
            s1_larger_exp      <= 8'd0;
            s1_a_mant_aligned  <= 19'd0;
            s1_b_mant_aligned  <= 19'd0;
            s1_eff_subtract    <= 1'b0;
        end else begin
            s1_valid           <= i_valid;
            s1_a               <= a;
            s1_b               <= b;
            s1_a_sign          <= a_sign;
            s1_b_sign          <= b_sign;
            s1_a_is_zero       <= a_is_zero;
            s1_b_is_zero       <= b_is_zero;
            s1_a_is_inf_nan    <= a_is_inf_nan;
            s1_b_is_inf_nan    <= b_is_inf_nan;
            s1_larger_exp      <= larger_exp;
            s1_a_mant_aligned  <= a_mant_aligned;
            s1_b_mant_aligned  <= b_mant_aligned;
            s1_eff_subtract    <= eff_subtract;
        end
    end

    // =========================================================================
    // Stage 2: Addition, Normalization, Result (Combinational from S1 regs)
    // =========================================================================

    // Mantissa comparison (from registered values)
    logic s1_a_mant_larger;
    assign s1_a_mant_larger = (s1_a_mant_aligned >= s1_b_mant_aligned);

    // Addition/Subtraction
    logic [19:0] add_result, sub_result, mant_sum;

    assign add_result = {1'b0, s1_a_mant_aligned} + {1'b0, s1_b_mant_aligned};
    assign sub_result = s1_a_mant_larger ?
                        ({1'b0, s1_a_mant_aligned} - {1'b0, s1_b_mant_aligned}) :
                        ({1'b0, s1_b_mant_aligned} - {1'b0, s1_a_mant_aligned});
    assign mant_sum   = s1_eff_subtract ? sub_result : add_result;

    // Result sign
    logic result_sign;
    assign result_sign = s1_eff_subtract ? (s1_a_mant_larger ? s1_a_sign : s1_b_sign) : s1_a_sign;

    // Overflow and Zero Detection
    logic overflow;
    logic is_zero_result;

    assign overflow       = mant_sum[19];
    assign is_zero_result = (mant_sum == 20'd0);

    // Leading Zero Count
    function automatic logic [4:0] count_leading_zeros(input logic [19:0] val);
        logic [4:0] clz;
        clz = 5'd20;
        for (int i = 19; i >= 0; i--) begin
            if (val[i] && clz == 5'd20)
                clz = 5'd19 - i[4:0];
        end
        return clz;
    endfunction

    logic [4:0] leading_zeros;
    assign leading_zeros = count_leading_zeros(mant_sum);

    // Normalization
    logic [4:0]  norm_left_shift;
    logic [19:0] mant_after_norm;

    assign norm_left_shift = (leading_zeros > 5'd1) ? (leading_zeros - 5'd1) : 5'd0;

    always_comb begin
        if (is_zero_result)
            mant_after_norm = 20'd0;
        else if (overflow)
            mant_after_norm = mant_sum >> 1;
        else if (leading_zeros == 5'd1)
            mant_after_norm = mant_sum;
        else if (leading_zeros > 5'd1 && leading_zeros <= 5'd19)
            mant_after_norm = mant_sum << norm_left_shift;
        else
            mant_after_norm = 20'd0;
    end

    // Exponent Adjustment
    logic signed [9:0] exp_adjust;
    logic signed [9:0] new_exp_signed;

    always_comb begin
        if (is_zero_result)
            exp_adjust = -10'sd127;
        else if (overflow)
            exp_adjust = 10'sd1;
        else if (leading_zeros == 5'd1)
            exp_adjust = 10'sd0;
        else if (leading_zeros > 5'd1)
            exp_adjust = 10'sd1 - $signed({5'd0, leading_zeros});
        else
            exp_adjust = 10'sd0;
    end

    assign new_exp_signed = $signed({2'b0, s1_larger_exp}) + exp_adjust;

    // Exponent Clamping
    logic        exp_overflow_flag;
    logic        exp_underflow_flag;
    logic [7:0]  final_exp;
    logic [14:0] final_mant;

    assign exp_overflow_flag  = (new_exp_signed >= 10'sd255);
    assign exp_underflow_flag = (new_exp_signed <= 10'sd0);

    assign final_exp = exp_overflow_flag  ? 8'd255 :
                       exp_underflow_flag ? 8'd0 :
                       new_exp_signed[7:0];

    assign final_mant = (exp_underflow_flag || is_zero_result) ? 15'd0 :
                        exp_overflow_flag ? 15'd0 :
                        mant_after_norm[17:3];

    // Result Assembly (combinational)
    logic [23:0] result_normal;
    logic [23:0] sum_comb;
    
    assign result_normal = {result_sign, final_exp, final_mant};

    always_comb begin
        if (s1_a_is_zero && s1_b_is_zero)
            sum_comb = 24'd0;
        else if (s1_a_is_zero)
            sum_comb = s1_b;
        else if (s1_b_is_zero)
            sum_comb = s1_a;
        else if (s1_a_is_inf_nan)
            sum_comb = s1_a;
        else if (s1_b_is_inf_nan)
            sum_comb = s1_b;
        else if (is_zero_result)
            sum_comb = {result_sign, 23'd0};
        else
            sum_comb = result_normal;
    end

    // =========================================================================
    // Stage 2 Output Registers
    // =========================================================================
    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            sum     <= 24'd0;
            o_valid <= 1'b0;
        end else begin
            sum     <= sum_comb;
            o_valid <= s1_valid;
        end
    end

endmodule

`default_nettype wire
