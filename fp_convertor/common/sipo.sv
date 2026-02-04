// Serial-In Parallel-Out (SIPO) Module
module sipo #(
    parameter width_p,
    parameter els_p
) (
    input logic clk_i,
    input logic reset_i,

    output logic ready_o,
    input logic v_i,
    input logic [width_p-1:0] data_i,

    input logic ready_i,
    output logic v_o,
    output logic [els_p-1:0][width_p-1:0] data_o
);

    logic [els_p-1:0][width_p-1:0] data_lo;
    logic [$clog2(els_p+1)-1:0] cnt_r;

    logic wr, rd;
    assign wr = v_i & ready_o;
    assign rd = v_o & ready_i;

    assign v_o = (cnt_r == els_p);
    assign data_o = data_lo;
    assign ready_o = ~(v_o & ~ready_i);

    always_ff @(posedge clk_i) begin
        if (reset_i) begin
            cnt_r <= '0;
        end else begin
            if(rd) begin
                cnt_r <= wr;
            end else if (wr) begin
                cnt_r <= cnt_r + 1'b1;
            end
        end
    end

    always_ff @(posedge clk_i) begin
        if (reset_i) begin
            data_lo <= '0;
        end else if (wr) begin
            data_lo <= {data_i, data_lo[els_p-1:1]};
        end
    end

endmodule