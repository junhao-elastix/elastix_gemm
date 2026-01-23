// Simple One-Entry FIFO
module one_fifo #(
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

    logic [width_p-1:0] data_r;
    logic v_r;

    assign ready_o = ~reset_i & (~v_r | ready_i);
    assign v_o = v_r;
    assign data_o = data_r;

    always_ff @(posedge clk_i) begin
        if (reset_i) begin
            v_r <= 1'b0;
            data_r <= '0;
        end else begin
            v_r <= (v_i & ready_o) ? 1'b1 : (v_o & ready_i) ? 1'b0 : v_r;
            data_r <= (v_i & ready_o) ? data_i : data_r;
        end
    end

endmodule