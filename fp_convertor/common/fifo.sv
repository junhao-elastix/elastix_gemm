// FIFO module
module fifo #(
    parameter width_p,
    parameter els_p,

    localparam ptr_width_lp = $clog2(els_p)
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

    logic [width_p-1:0] fifo_mem [0:els_p-1];
    logic [ptr_width_lp-1:0] wr_ptr, rd_ptr;
    logic [ptr_width_lp:0] count;

    wire wr = v_i & ready_o;
    wire rd = v_o & ready_i;

    logic v_r;
    logic [width_p-1:0] data_r;

    assign ready_o = (count < els_p) & ~reset_i;
    assign v_o = v_r & ~reset_i;
    assign data_o = data_r;

    wire mem_has_data = v_r ? (count > 1) : (count > 0);
    wire mem_rd = mem_has_data & (rd | ~v_r);
    wire mem_wr = wr;

    always_ff @(posedge clk_i) begin
        if (reset_i) begin
            wr_ptr <= '0;
        end else if (mem_wr) begin
            wr_ptr <= wr_ptr + 1;
            fifo_mem[wr_ptr] <= data_i;
        end
    end

    always_ff @(posedge clk_i) begin
        if (reset_i) begin
            rd_ptr <= '0;
            v_r <= 1'b0;
            data_r <= '0;
        end else begin
            rd_ptr <= mem_rd ? (rd_ptr + 1) : rd_ptr;
            v_r <= mem_rd ? 1'b1 : (rd ? 1'b0 : v_r);
            data_r <= mem_rd ? fifo_mem[rd_ptr] : data_r;
        end
    end

    always_ff @(posedge clk_i) begin
        if (reset_i) begin
            count <= '0;
        end else begin
            count <= count + wr - rd;
        end
    end

endmodule