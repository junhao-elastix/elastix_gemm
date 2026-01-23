module fp_adder_tree_tb();

    // Parameters
    localparam tests_p = 100000;
    localparam mwidth_p = 11;
    localparam ewidth_p = 5;
    localparam bias_p = 2**(ewidth_p-1) - 1;
    localparam els_p = 8;
    localparam seg_len_p = 1;

    localparam stages_lp = $clog2(els_p);

    localparam real max_val_lp = ((1 << (mwidth_p - 1)) - 1) * (2.0 ** (2**ewidth_p - 1 - bias_p));
    localparam real min_val_lp = -1 * (1 << (mwidth_p - 1)) * (2.0 ** (2**ewidth_p - 1 - bias_p));

    // Clock and reset
    logic clk_i;
    logic reset_i;

    // DUT signals
    logic v_i;
    logic [els_p-1:0][mwidth_p-1:0] mant_i;
    logic [els_p-1:0][ewidth_p-1:0] exp_i;
    logic v_o;
    logic [mwidth_p-1:0] mant_o;
    logic [ewidth_p-1:0] exp_o;

    // Reference queue for checking
    logic [tests_p-1:0][els_p-1:0][mwidth_p-1:0] input_mants;
    logic [tests_p-1:0][els_p-1:0][ewidth_p-1:0] input_exps;
    real expected_out [0:tests_p-1];

    // DUT instantiation
    fp_adder_tree #(
        .mwidth_p(mwidth_p),
        .ewidth_p(ewidth_p),
        .els_p(els_p),
        .seg_len_p(seg_len_p)
    ) dut (
        .clk_i(clk_i),
        .reset_i(reset_i),
        .v_i(v_i),
        .mant_i(mant_i),
        .exp_i(exp_i),
        .v_o(v_o),
        .mant_o(mant_o),
        .exp_o(exp_o)
    );

    // Clock generation
    initial begin
        clk_i = 0;
        forever #5 clk_i = ~clk_i;
    end

    // input output generation
    initial begin
        for (int i = 0; i < tests_p; i++) begin
            for (int j = 0; j < els_p; j++) begin
                do begin
                    input_mants[i][j] = $urandom;
                    input_exps[i][j] = ($urandom % (2**(ewidth_p) - 2));
                end while (input_mants[i][j][mwidth_p-1] == input_mants[i][j][mwidth_p-2]);
            end

            expected_out[i] = 0.0;
            for (int j = 0; j < els_p; j++) begin
                expected_out[i] += $itor($signed(input_mants[i][j])) * (2.0 ** $signed(input_exps[i][j] - bias_p));
            end
            expected_out[i] = (expected_out[i] > max_val_lp) ? max_val_lp : expected_out[i];
            expected_out[i] = (expected_out[i] < min_val_lp) ? min_val_lp : expected_out[i];
        end
    end

    // apply inputs
    initial begin
        reset_i = 1;
        v_i = 0;
        mant_i = '0;
        exp_i = '0;

        repeat(5) @(negedge clk_i);
        reset_i = 0;

        for (int t = 0; t < tests_p; t++) begin
            v_i = 1;
            mant_i = input_mants[t];
            exp_i = input_exps[t];
            @(negedge clk_i);
        end
        v_i = 0;
    end

    // check outputs
    real real_out, real_in, real_in_abs, max_in_abs;
    real err, max_err, max_idx;
    initial begin
        wait (v_o);
        @(negedge clk_i);
        max_err = 0.0;
        max_idx = 0;
        for (int t = 0; t < tests_p; t++) begin
            max_in_abs = 0.0;
            for (int j = 0; j < els_p; j++) begin
                real_in = $itor($signed(input_mants[t][j])) * (2.0 ** $signed(input_exps[t][j] - bias_p));
                real_in_abs = (real_in < 0) ? -real_in : real_in;
                max_in_abs = (max_in_abs < real_in_abs) ? real_in_abs : max_in_abs;
                //$display("Input %0d: Mantissa: %0d, Exponent: %0d, Value: %f", j, $signed(input_mants[t][j]), $unsigned(input_exps[t][j]), real_in);
            end

            real_out = $itor($signed(mant_o)) * (2.0 ** $signed(exp_o - bias_p));
            err = (expected_out[t] - real_out) / max_in_abs;
            err = (err < 0) ? -err : err;
            max_idx = (err > max_err) ? t : max_idx;
            max_err = (err > max_err) ? err : max_err;

            $display("Mantissa: %0d, Exponent: %0d", $signed(mant_o), $unsigned(exp_o));
            $display("Test %0d: Expected %f, Got %f, Error: %f", t, expected_out[t], real_out, err);
            @(negedge clk_i);
        end
        $display("Max relative error over %0d tests: %f (at test %0d)", tests_p, max_err, max_idx);
        $display("max val: %f, min val: %f", max_val_lp, min_val_lp);
        $finish;
    end

endmodule