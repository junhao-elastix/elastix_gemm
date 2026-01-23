// Adapter Module for Width Conversion
module adapter #(
    parameter in_width_p,
    parameter out_width_p,

    localparam els_lp = (in_width_p > out_width_p) ? (in_width_p / out_width_p) : (out_width_p / in_width_p)
) (
    input logic clk_i,
    input logic reset_i,

    output logic ready_o,
    input logic v_i,
    input logic [in_width_p-1:0] data_i,

    input logic ready_i,
    output logic v_o,
    output logic [out_width_p-1:0] data_o
);

    if(in_width_p == out_width_p) begin : gen_pass
        assign ready_o = ready_i;
        assign v_o = v_i;
        assign data_o = data_i;
    end else if (in_width_p > out_width_p) begin : gen_piso
        piso #(
            .width_p(out_width_p),
            .els_p(els_lp)
        ) i_piso (
            .clk_i(clk_i),
            .reset_i(reset_i),

            .ready_o(ready_o),
            .v_i(v_i),
            .data_i(data_i),

            .ready_i(ready_i),
            .v_o(v_o),
            .data_o(data_o)
        );
    end else begin : gen_sipo
        sipo #(
            .width_p(in_width_p),
            .els_p(els_lp)
        ) i_sipo (
            .clk_i(clk_i),
            .reset_i(reset_i),

            .ready_o(ready_o),
            .v_i(v_i),
            .data_i(data_i),

            .ready_i(ready_i),
            .v_o(v_o),
            .data_o(data_o)
        );
    end

    initial begin
        assert((in_width_p % out_width_p == 0) || (out_width_p % in_width_p == 0)) else $error("in_width_p and out_width_p must be divisible");
    end

endmodule