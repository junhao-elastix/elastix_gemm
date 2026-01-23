// Simple Two-Entry FIFO
module two_fifo #(
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

    logic [1:0][width_p-1:0] mem;
    logic [1:0] valid;
    logic wr_ptr, rd_ptr;
    logic wr, rd;

    assign wr = v_i & ready_o;
    assign rd = v_o & ready_i;

    // Write logic
    always_ff @(posedge clk_i) begin
        if (reset_i) begin
            valid <= '0;
            wr_ptr <= 1'b0;
            rd_ptr <= 1'b0;
        end else begin
            if (rd) begin
                valid[rd_ptr] <= 1'b0;
                rd_ptr <= rd_ptr + 1'b1;
            end

            if (wr) begin
                valid[wr_ptr] <= 1'b1;
                mem[wr_ptr] <= data_i;
                wr_ptr <= wr_ptr + 1'b1;
            end

            //valid <= (valid & ~({1'b0, rd} << rd_ptr)) | ({1'b0, wr} << wr_ptr);
        end
    end

    // Output assignments
    assign ready_o = ~valid[wr_ptr];
    assign v_o = valid[rd_ptr];
    assign data_o = mem[rd_ptr];

endmodule