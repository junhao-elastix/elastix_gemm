// A Chain of Two-Entry FIFOs
module two_fifo_chain #(
    parameter els_p,
    parameter width_p
) (
    input logic clk_i,
    input logic reset_i,

    output logic ready_o,
    input logic v_i,
    input logic [width_p-1:0] data_i,

    input logic ready_i,
    output logic v_o,
    output logic [width_p-1:0] data_o
);

    logic [els_p:0] v, ready;
    logic [els_p:0][width_p-1:0] data;

    assign ready_o = ready[0];
    assign v[0] = v_i;
    assign data[0] = data_i;

    assign ready[els_p] = ready_i;
    assign v_o = v[els_p];
    assign data_o = data[els_p];

    for (genvar i = 0; i < els_p; i++) begin: rof_fifos
        two_fifo #(
            .width_p(width_p)
        ) i_two_fifo (
            .clk_i(clk_i),
            .reset_i(reset_i),

            .ready_o(ready[i]),
            .v_i(v[i]),
            .data_i(data[i]),

            .ready_i(ready[i+1]),
            .v_o(v[i+1]),
            .data_o(data[i+1])
        );
    end

endmodule