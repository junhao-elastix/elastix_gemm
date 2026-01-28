// Parallel-In Serial-Out (PISO) Module
module piso #(
    parameter width_p,
    parameter els_p
) (
    input logic clk_i,
    input logic reset_i,

    output logic ready_o,
    input logic v_i,
    input logic [els_p-1:0][width_p-1:0] data_i,

    input logic ready_i,
    output logic v_o,
    output logic [width_p-1:0] data_o
);

    logic v_lo;
    logic top_ready_lo, bot_ready_lo;
    logic top_ready_li, bot_ready_li;
    logic [els_p-1:0][width_p-1:0] data_lo;
    logic [$clog2(els_p)-1:0] cnt_r;

    assign v_o = v_lo;
    assign data_o = data_lo[cnt_r];
    assign ready_o = top_ready_lo & bot_ready_lo;

    assign top_ready_li = ready_i & (cnt_r == els_p - 1);
    assign bot_ready_li = ready_i & (cnt_r == els_p - 2);

    always_ff @(posedge clk_i) begin
        if (reset_i) begin
            cnt_r <= '0;
        end else if (v_o & ready_i) begin
            if (cnt_r == els_p - 1) begin
                cnt_r <= '0;
            end else begin
                cnt_r <= cnt_r + 1'b1;
            end
        end
    end

    two_fifo #(
        .width_p(width_p)
    ) i_top_fifo (
        .clk_i(clk_i),
        .reset_i(reset_i),

        .ready_o(top_ready_lo),
        .v_i(v_i & ready_o),
        .data_i(data_i[els_p-1]),

        .ready_i(top_ready_li),
        .v_o(v_lo),
        .data_o(data_lo[els_p-1])
    );

    one_fifo #(
        .width_p((els_p -1) * width_p)
    ) i_bot_fifo (
        .clk_i(clk_i),
        .reset_i(reset_i),

        .ready_o(bot_ready_lo),
        .v_i(v_i & ready_o),
        .data_i(data_i[els_p-2:0]),

        .ready_i(bot_ready_li),
        .v_o(),
        .data_o(data_lo[els_p-2:0])
    );

    initial begin
        assert(els_p > 1) else $error("PISO requires els_p > 1");
    end

endmodule