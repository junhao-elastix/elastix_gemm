// Data Picker Module based on Variable Sizes and Indexes
module pick #(
    parameter width_p,
    parameter unit_width_p,
    parameter sign_ext_p,

    localparam sel_width_lp = (width_p == unit_width_p) ? 1 : $clog2(width_p/unit_width_p),
    localparam size_width_lp = $clog2(sel_width_lp+1),
    localparam lg_unit_width_lp = $clog2(unit_width_p)
) (
    input logic [width_p-1:0] data_i,
    input logic [sel_width_lp-1:0] sel_i,
    input logic [size_width_lp-1:0] size_i,

    output logic [width_p-1:0] data_o
);

    if (width_p == unit_width_p) begin: gen_noop
        assign data_o = data_i;
    end else begin: gen_pick
        logic [width_p-1:0] data_rot_lo;
        assign data_rot_lo = {2{data_i}} >> {sel_i, {lg_unit_width_lp{1'b0}}};

        logic [sel_width_lp:0][width_p-1:0] picks_lo;
        for (genvar i = 0; i <= sel_width_lp; i++) begin : rof_slice
            localparam slice_width_lp = (unit_width_p*(2**i));
            localparam pad_width_lp = width_p - slice_width_lp;
            wire ext = sign_ext_p ? data_rot_lo[slice_width_lp-1] : 1'b0;
            assign picks_lo[i] = {{pad_width_lp{ext}}, data_rot_lo[0+:slice_width_lp]};
        end

        assign data_o = picks_lo[size_i];
    end

    initial begin
        assert($onehot(width_p) == 1) else $error("width_p (%0d) must be a power of 2", width_p);
        assert($onehot(unit_width_p) == 1) else $error("unit_width_p (%0d) must be a power of 2", unit_width_p);
        assert(width_p % unit_width_p == 0) else $error("width_p (%0d) must be a multiple of unit_width_p (%0d)", width_p, unit_width_p);
        assert(width_p >= unit_width_p) else $error("width_p (%0d) must be >= unit_width_p (%0d)", width_p, unit_width_p);
    end

endmodule

