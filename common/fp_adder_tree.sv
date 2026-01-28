module fp_adder_tree #(
    parameter mwidth_p,
    parameter ewidth_p,
    parameter els_p,
    parameter seg_len_p,

    localparam stages_lp = $clog2(els_p)
) (
    input logic clk_i,
    input logic reset_i,

    input logic v_i,
    input logic [els_p-1:0][mwidth_p-1:0] mant_i,
    input logic [els_p-1:0][ewidth_p-1:0] exp_i,

    output logic v_o,
    output logic [mwidth_p-1:0] mant_o,
    output logic [ewidth_p-1:0] exp_o
);

    // Intermediate signals
    logic [stages_lp:0][els_p-1:0][mwidth_p-1:0] mant_stage_add, mant_stage_r, mant_stage_data;
    logic [stages_lp:0][els_p-1:0][ewidth_p-1:0] exp_stage_add, exp_stage_r, exp_stage_data;
    logic [stages_lp:0] v_add, v_r, v_stage;

    // Assign input to stage 0
    assign v_stage[0] = v_i;
    assign mant_stage_data[0] = mant_i;
    assign exp_stage_data[0] = exp_i;

    // Output assignment
    assign v_o = v_stage[stages_lp];
    assign mant_o = mant_stage_data[stages_lp][0];
    assign exp_o = exp_stage_data[stages_lp][0];

    // Generate adder tree
    genvar s, i;
    generate
        for (s = 0; s < stages_lp; s++) begin : stage_gen
            localparam stage_els_lp = els_p >> s;
            // FP adders
            for (i = 0; i < stage_els_lp/2; i++) begin : rof_add
                // pick valid from first adder only
                logic add_v_lo;
                if (i == 0) begin: gen_valid
                    assign v_add[s+1] = add_v_lo;
                end

                fp_add #(
                    .mwidth_p(mwidth_p),
                    .ewidth_p(ewidth_p)
                ) i_fp_add (
                    .clk_i(clk_i),
                    .reset_i(reset_i),

                    .v_i(v_stage[s]),
                    .mant_a_i(mant_stage_data[s][2*i]),
                    .exp_a_i(exp_stage_data[s][2*i]),
                    .mant_b_i(mant_stage_data[s][2*i+1]),
                    .exp_b_i(exp_stage_data[s][2*i+1]),

                    .v_o(add_v_lo),
                    .mant_o(mant_stage_add[s+1][i]),
                    .exp_o(exp_stage_add[s+1][i])
                );
            end

            // If odd number of elements, pass last element through adder to match latency
            if (stage_els_lp % 2) begin: gen_odd
                fp_add #(
                    .mwidth_p(mwidth_p),
                    .ewidth_p(ewidth_p)
                ) i_fp_add (
                    .clk_i(clk_i),
                    .reset_i(reset_i),

                    .v_i(v_stage[s]),
                    .mant_a_i(mant_stage_data[s][stage_els_lp-1]),
                    .exp_a_i(exp_stage_data[s][stage_els_lp-1]),
                    .mant_b_i('0),
                    .exp_b_i('0),

                    .v_o(/* unused */),
                    .mant_o(mant_stage_add[s+1][stage_els_lp/2]),
                    .exp_o(exp_stage_add[s+1][stage_els_lp/2])
                );
            end

            // conditionaly create a stage register based on seg_len_p
            if(s % seg_len_p == seg_len_p-1 || s == stages_lp-1) begin : gen_reg
                assign v_stage[s+1] = v_r[s+1];
                assign mant_stage_data[s+1] = mant_stage_r[s+1];
                assign exp_stage_data[s+1] = exp_stage_r[s+1];
                always_ff @(posedge clk_i) begin
                    if (reset_i) begin
                        v_r[s+1] <= 1'b0;
                        mant_stage_r[s+1] <= '0;
                        exp_stage_r[s+1] <= '0;
                    end else begin
                        v_r[s+1] <= v_add[s+1];
                        for (int i = 0; i < (stage_els_lp+1)/2; i++) begin
                            mant_stage_r[s+1][i] <= mant_stage_add[s+1][i];
                            exp_stage_r[s+1][i] <= exp_stage_add[s+1][i];
                        end
                    end
                end
            end else begin : gen_noreg
                assign v_stage[s+1] = v_add[s+1];
                assign mant_stage_data[s+1] = mant_stage_add[s+1];
                assign exp_stage_data[s+1] = exp_stage_add[s+1];
            end
        end
    endgenerate

    initial begin
        assert (els_p >= 2) else $error("els_p must be >= 2");
        assert ((seg_len_p >= 1) && (seg_len_p <= stages_lp)) else $error("seg_len_p must be in the range [1, $clog2(els_p)]");
    end

endmodule