// Synchronous 1-Read 1-Write Inferred BRAM Module
module mem_1r1w #(
    parameter els_p,
    parameter width_p,

    localparam addr_width_lp = $clog2(els_p)
) (
    input clk_i,
    input reset_i,

    input logic w_v_i,
    input logic [addr_width_lp-1:0] w_addr_i,
    input logic [width_p-1:0] w_data_i,
    input logic [width_p/8-1:0] w_en_i,

    input logic r_v_i,
    input logic [addr_width_lp-1:0] r_addr_i,

    output logic r_v_o,
    output logic [width_p-1:0] r_data_o
);

    logic [width_p-1:0] mem [0:els_p-1];
    logic [width_p-1:0] r_data_r;
    logic r_v_r;

    assign r_v_o = r_v_r;
    assign r_data_o = r_data_r;

    always_ff @(posedge clk_i) begin
        if (reset_i) begin
            r_v_r <= 1'b0;
            r_data_r <= '0;
        end else begin
            r_v_r <= r_v_i;
            r_data_r <= mem[r_addr_i];

            if (w_v_i) begin
                for (int i = 0; i < width_p/8; i++) begin
                    if (w_en_i[i]) begin
                        mem[w_addr_i][i*8 +: 8] <= w_data_i[i*8 +: 8];
                    end
                end
            end
        end
    end

    initial begin
        assert(width_p % 8 == 0) else $error("width_p (%0d) must be a multiple of 8", width_p);
    end

endmodule