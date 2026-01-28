// Virtualized Time-Multiplexed BRAM with N Read Ports and 1 Write Port
module vbram_nr1w #(
    parameter virt_factor_p,
    parameter addr_width_p,
    parameter data_width_p,
    parameter reg_out_p,
    parameter bram_type_p,
    parameter metadata_width_p,

    localparam bram_latency_lp = 1 + reg_out_p
) (
    input logic r_clk_i,
    input logic r_reset_i,

    input logic w_clk_i,
    input logic w_reset_i,

    input logic r_v_i,
    input logic r_last_i,
    input logic [addr_width_p-1:0] r_addr_i,

    input logic w_v_i,
    input logic [addr_width_p-1:0] w_addr_i,
    input logic [data_width_p-1:0] w_data_i,
    input logic [data_width_p/8-1:0] w_en_i,

    output logic r_v_o,
    output logic [virt_factor_p-1:0][data_width_p-1:0] r_data_o,

    input logic [metadata_width_p-1:0] metadata_i,
    output logic [virt_factor_p-1:0][metadata_width_p-1:0] metadata_o
);

    // read data shift register
    logic [virt_factor_p-2:0][data_width_p-1:0] r_data_pipe_r;
    // last signal shift register to match BRAM latency
    logic [bram_latency_lp-1:0] last_r;
    // metadata shift register to match BRAM latency plus virtualization factor
    logic [bram_latency_lp+virt_factor_p-2:0][metadata_width_p-1:0] metadata_r;
    // BRAM read ports
    logic r_v_lo;
    logic [data_width_p-1:0] r_data_lo;

    assign r_v_o = r_v_lo & last_r[bram_latency_lp-1];
    for (genvar i = 0; i < virt_factor_p; i++) begin
        assign r_data_o[i] = (i == 0) ? r_data_lo : r_data_pipe_r[i - 1];
        assign metadata_o[i] = metadata_r[bram_latency_lp + i - 1];
    end

    always_ff @(posedge r_clk_i) begin
        if (r_reset_i) begin
            r_data_pipe_r <= '0;
            last_r <= '0;
            metadata_r <= '0;
        end else begin
            last_r <= (bram_latency_lp > 1) ? {last_r[bram_latency_lp-2:0], r_last_i} : r_last_i;
            r_data_pipe_r <= (virt_factor_p > 2) ? {r_data_pipe_r[virt_factor_p-3:0], r_data_lo} : r_data_lo;
            metadata_r <= {metadata_r[bram_latency_lp+virt_factor_p-3:0], metadata_i};
        end
    end

    case (bram_type_p)
        "BRAM18": begin
            bram18_1r1w #(
                .addr_width_p(addr_width_p),
                .data_width_p(data_width_p),
                .reg_out_p(1)
            ) bram (
                .r_clk_i(r_clk_i),
                .r_reset_i(r_reset_i),
                .r_v_i(r_v_i),
                .r_addr_i(r_addr_i),

                .r_v_o(r_v_lo),
                .r_data_o(r_data_lo),

                .w_clk_i(w_clk_i),
                .w_reset_i(w_reset_i),
                .w_v_i(w_v_i),
                .w_addr_i(w_addr_i),
                .w_data_i(w_data_i),
                .w_en_i(w_en_i)
            );
        end
        "BRAM36": begin
            bram36_1r1w #(
                .addr_width_p(addr_width_p),
                .data_width_p(data_width_p),
                .reg_out_p(1)
            ) bram (
                .r_clk_i(r_clk_i),
                .r_reset_i(r_reset_i),
                .r_v_i(r_v_i),
                .r_addr_i(r_addr_i),

                .r_v_o(r_v_lo),
                .r_data_o(r_data_lo),

                .w_clk_i(w_clk_i),
                .w_reset_i(w_reset_i),
                .w_v_i(w_v_i),
                .w_addr_i(w_addr_i),
                .w_data_i(w_data_i),
                .w_en_i(w_en_i)
            );
        end
        default: begin
            initial begin
                $error("Invalid bram_type_p: %s (valid options are 'BRAM18' and 'BRAM36')", bram_type_p);
            end
        end
    endcase

    initial begin
        assert(virt_factor_p >= 2) else $error("virt_factor_p must be >= 2");
    end

endmodule