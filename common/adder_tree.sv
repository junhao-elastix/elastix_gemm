// Signed Fixed-Point Adder Tree
module adder_tree
    import common_pkg::*;
#(
    parameter width_p,
    parameter els_p,
    parameter seg_len_p,

    localparam stages_lp = $clog2(els_p),
    localparam latency_lp = cdiv(stages_lp, seg_len_p)
) (
    input  logic clk_i,
    input  logic reset_i,
    input  logic en_i,

    input  logic v_i,
    input  logic [els_p-1:0][width_p-1:0] data_i,

    output logic v_o,
    output logic [width_p-1:0] data_o
);

    // Intermediate signals
    logic [stages_lp:0][els_p-1:0][width_p-1:0] stage_add, stage_r, stage_data;
    logic [latency_lp-1:0] v_r;

    // Assign input to stage 0
    assign stage_data[0] = data_i;

    // Output assignment
    assign v_o = v_r[latency_lp-1];
    assign data_o = stage_data[stages_lp][0];

    // Output valid signal generation
    always_ff @(posedge clk_i) begin
        if (reset_i) begin
            v_r <= '0;
        end else if (en_i) begin
            v_r <= (latency_lp > 1) ? {v_r[latency_lp-2:0], v_i} : v_i;
        end
    end

    // Generate adder tree
    genvar s, i;
    generate
        for (s = 0; s < stages_lp; s++) begin : stage_gen
            localparam stage_els_lp = els_p >> s;
            for (i = 0; i < stage_els_lp/2; i++) begin : add_gen
                assign stage_add[s+1][i] = stage_data[s][2*i] + stage_data[s][2*i+1];
            end

            // If odd number of elements, pass through last element
            if (stage_els_lp % 2) begin
                assign stage_add[s+1][stage_els_lp/2] = stage_data[s][stage_els_lp-1];
            end

            if(s % seg_len_p == seg_len_p-1 || s == stages_lp-1) begin : reg_gen
                assign stage_data[s+1] = stage_r[s+1];
                for (i = 0; i < (stage_els_lp+1)/2; i++) begin : reg_rof
                    always_ff @(posedge clk_i) begin
                        if (reset_i) begin
                            stage_r[s+1][i] <= '0;
                        end else if (en_i) begin
                            stage_r[s+1][i] <= stage_add[s+1][i];
                        end
                    end
                end
            end else begin : noreg_gen
                assign stage_data[s+1] = stage_add[s+1];
            end
        end
    endgenerate

    // Parameter sanity checks
    initial begin
        assert (width_p > 0)
            else $error("width_p must be > 0");
        assert (els_p >= 2)
            else $error("els_p must be >= 2");
        assert ((seg_len_p >= 1) && (seg_len_p <= stages_lp))
            else $error("seg_len_p must be in the range [1, $clog2(els_p)]");
    end

endmodule