module fp_add #(
    parameter mwidth_p,
    parameter ewidth_p
) (
    input logic clk_i,
    input logic reset_i,

    input logic v_i,
    input logic [mwidth_p-1:0] mant_a_i,
    input logic [ewidth_p-1:0] exp_a_i,
    input logic [mwidth_p-1:0] mant_b_i,
    input logic [ewidth_p-1:0] exp_b_i,
    
    output logic v_o,
    output logic [mwidth_p-1:0] mant_o,
    output logic [ewidth_p-1:0] exp_o
);

    // STAGE 0
    // find maximum exponent
    logic shift_a_not_b;
    logic [ewidth_p-1:0] max_exp, mant_shift;
    assign shift_b_not_a = (exp_a_i > exp_b_i);
    assign max_exp = shift_b_not_a ? exp_a_i : exp_b_i;
    assign mant_shift = max_exp - (shift_b_not_a ? exp_b_i : exp_a_i);

    // stage registers
    logic v_r;
    logic shift_b_not_a_r;
    logic [mwidth_p-1:0] mant_a_r, mant_b_r;
    logic [ewidth_p-1:0] max_exp_r, mant_shift_r;
    always_ff @(posedge clk_i) begin
        max_exp_r <= max_exp;
        shift_b_not_a_r <= shift_b_not_a;
        mant_shift_r <= mant_shift;
        mant_a_r <= mant_a_i;
        mant_b_r <= mant_b_i;
    end

    // STAGE 1
    // shift mantissas
    logic [mwidth_p-1:0] mant_shifted, mant_a_shifted, mant_b_shifted;
    assign mant_shifted = $signed(shift_b_not_a_r ? mant_b_r : mant_a_r) >>> mant_shift_r;
    assign mant_a_shifted = shift_b_not_a_r ? mant_a_r: mant_shifted;
    assign mant_b_shifted = shift_b_not_a_r ? mant_shifted: mant_b_r;

    // stage registers
    logic v_r2;
    logic [ewidth_p-1:0] max_exp_r2;
    logic [mwidth_p-1:0] mant_a_shifted_r2, mant_b_shifted_r2;
    always_ff @(posedge clk_i) begin
        max_exp_r2 <= max_exp_r;
        mant_a_shifted_r2 <= mant_a_shifted;
        mant_b_shifted_r2 <= mant_b_shifted;
    end

    // STAGE 2
    // perform addition
    logic [mwidth_p:0] mant_sum;
    assign mant_sum = {mant_a_shifted_r2[mwidth_p-1], mant_a_shifted_r2} + {mant_b_shifted_r2[mwidth_p-1], mant_b_shifted_r2};

    // only used for normalization when there is no mantissa overflow
    logic [$clog2(mwidth_p+1)-1:0] leading_signs;
    clz #(
        .width_p(mwidth_p)
    ) i_clz (
        .data_i(mant_sum[mwidth_p-1] ? ~mant_sum[0 +: mwidth_p] : mant_sum[0 +: mwidth_p]),
        .clz_o(leading_signs)
    );

    // stage registers
    logic v_r3;
    logic [mwidth_p:0] mant_sum_r3;
    logic [ewidth_p-1:0] max_exp_r3;
    logic [$clog2(mwidth_p+1)-1:0] leading_signs_r3;
    always_ff @(posedge clk_i) begin
        mant_sum_r3 <= mant_sum;
        max_exp_r3 <= max_exp_r2;
        leading_signs_r3 <= leading_signs;
    end

    // STAGE 3
    // normalize result
    logic [ewidth_p-1:0] norm_shift;
    logic [mwidth_p-1:0] mant_r3;
    logic [ewidth_p-1:0] exp_r3;
    assign norm_shift = (leading_signs_r3 <= max_exp_r3) ? (leading_signs_r3 - 1) : max_exp_r3;
    always_comb begin
        // check for mantissa overflow
        if (mant_sum_r3[mwidth_p] != mant_sum_r3[mwidth_p-1]) begin
            if (max_exp_r3 == {ewidth_p{1'b1}}) begin
                // exponent overflow, saturate to max value
                mant_r3 = mant_sum_r3[mwidth_p] ? {1'b1, {mwidth_p-1{1'b0}}} : {1'b0, {mwidth_p-1{1'b1}}};
                exp_r3 = max_exp_r3;
            end else begin
                mant_r3 = mant_sum_r3 >> 1;
                exp_r3 = max_exp_r3 + 1;
            end
        end else begin
            mant_r3 = mant_sum_r3 << norm_shift;
            exp_r3 = max_exp_r3 - norm_shift;
        end
    end

    // stage registers
    logic v_r4;
    logic [mwidth_p-1:0] mant_r4;
    logic [ewidth_p-1:0] exp_r4;
    always_ff @(posedge clk_i) begin
        mant_r4 <= mant_r3;
        exp_r4 <= exp_r3;
    end

    // STAGE 4
    // output stage
    assign v_o = v_r4;
    assign mant_o = mant_r4;
    assign exp_o = exp_r4;

    // propagate valid signals
    always_ff @(posedge clk_i) begin
        if (reset_i) begin
            v_r <= 1'b0;
            v_r2 <= 1'b0;
            v_r3 <= 1'b0;
            v_r4 <= 1'b0;
        end else begin
            v_r <= v_i;
            v_r2 <= v_r;
            v_r3 <= v_r2;
            v_r4 <= v_r3;
        end
    end

endmodule