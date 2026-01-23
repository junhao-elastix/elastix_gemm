// Count Leading Zeros Module
module clz #(
    parameter width_p,
    localparam out_width_lp = $clog2(width_p+1)
) (
    input logic [width_p-1:0] data_i,
    output logic [out_width_lp-1:0] clz_o
);

    if (width_p == 1) begin: gen_one
        assign clz_o = data_i[0] ? 1'b0 : 1'b1;
    end else if (width_p == 2) begin: gen_two
        assign clz_o = data_i[1] ? 2'b0 : (data_i[0] ? 2'b1 : 2'b10);
    end else begin: gen_rec
        localparam padded_width_lp = 1 << $clog2(width_p);
        localparam half_width_lp = (padded_width_lp / 2);

        logic [$clog2(padded_width_lp+1)-1:0] padded_clz_lo;
        logic [$clog2(padded_width_lp+1)-2:0] half_clz_lo;
        wire [padded_width_lp-1:0] padded = (width_p == padded_width_lp) ? data_i : {data_i, {(padded_width_lp - width_p){1'b1}}};

        wire [half_width_lp-1:0] lower = padded[0 +: half_width_lp];
        wire [half_width_lp-1:0] upper = padded[half_width_lp +: half_width_lp];
        wire upper_zero = ~|upper;

        clz #(
            .width_p(half_width_lp)
        ) i_half_clz (
            .data_i(upper_zero ? lower : upper),
            .clz_o(half_clz_lo)
        );

        assign padded_clz_lo = half_clz_lo + (upper_zero ? half_width_lp : '0);
        assign clz_o = padded_clz_lo[0 +: out_width_lp];
    end

    initial begin
        assert(width_p >= 1) else $error("Width must be at least 1");
    end

endmodule