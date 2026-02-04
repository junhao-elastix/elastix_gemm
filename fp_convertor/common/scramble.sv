// Data Scrambler Module for Interleaving with Variable Sizes
module scramble #(
    parameter els_p,
    parameter width_p,
    parameter unit_width_p,

    localparam sel_width_lp = (width_p == unit_width_p) ? 1 : $clog2(width_p/unit_width_p),
    localparam size_width_lp = $clog2(sel_width_lp+1),

    localparam max_size_lp = (1 << size_width_lp) - 1,
    localparam unit_els_lp = width_p / unit_width_p
) (
    input logic [els_p-1:0][width_p-1:0] data_i,
    input logic [size_width_lp-1:0] size_i,

    output logic [els_p-1:0][width_p-1:0] data_o
);

    if (width_p == unit_width_p) begin : gen_noop
        assign data_o = data_i;
    end else begin : gen_scramble
        // flattening input data
        logic [els_p*width_p-1:0] data_flat_li;
        for (genvar i = 0; i < els_p; i++) begin
            assign data_flat_li[i*width_p +: width_p] = data_i[i];
        end

        // generating scrambled data for all sizes
        logic [max_size_lp:0][els_p*width_p-1:0] data_scrambled_lo;
        for (genvar s = 0; s <= max_size_lp; s++) begin : rof_size
            localparam slice_els_lp = unit_els_lp / (1 << s);
            localparam slice_width_lp = width_p / slice_els_lp;

            // breaking up data slices
            logic [slice_els_lp-1:0][(els_p/slice_els_lp)*width_p-1:0] slice_data_lo;
            for (genvar i = 0; i < slice_els_lp; i++) begin : rof_slice
                assign slice_data_lo[i] = data_flat_li[(i*(els_p/slice_els_lp)*width_p) +: (els_p/slice_els_lp)*width_p];
            end

            // reassembling scrambled data from slices
            for (genvar i = 0; i < (els_p * slice_els_lp); i++) begin : rof_scramble
                localparam slice_idx_lp = (i % slice_els_lp);
                localparam slice_offset_lp = (i / slice_els_lp) * slice_width_lp;
                assign data_scrambled_lo[s][i*slice_width_lp +: slice_width_lp] = slice_data_lo[slice_idx_lp][slice_offset_lp +: slice_width_lp];
            end
        end

        // picking data based on input size
        for (genvar i = 0; i < els_p; i++) begin: rof_out
            assign data_o[i] = data_scrambled_lo[size_i][i*width_p +: width_p];
        end
    end


    initial begin
        assert($onehot(els_p) == 1) else $error("els_p (%0d) must be a power of 2", els_p);
        assert($onehot(width_p) == 1) else $error("width_p (%0d) must be a power of 2", width_p);
        assert($onehot(unit_width_p) == 1) else $error("unit_width_p (%0d) must be a power of 2", unit_width_p);
    end

endmodule