// ------------------------------------------------------------------
// Result to DMA BRAM Adapter Module (Simple Registered)
//
// Purpose: Converts ready-valid stream from result_collector_2d to
//          BRAM write interface for DMA readback.
//
// Design: Simple registered adapter - no FIFO
//  - Always ready to accept data
//  - On valid input, register data and generate BRAM write next cycle
//  - Sequential address generation
//  - 16-bit keep mask expanded to 32-bit byte strobe
//
// Author: Junhao Pan
// Date: Jan 23, 2026
// ------------------------------------------------------------------

module result_to_dma #(
    parameter DATA_WIDTH = 256,
    parameter ADDR_WIDTH = 9
) (
    input  logic                    i_clk,
    input  logic                    i_reset_n,

    // Ready-Valid Input (from result_collector_2d)
    input  logic [DATA_WIDTH-1:0]   i_data,
    input  logic [15:0]             i_keep,      // 16 FP16 value mask
    input  logic                    i_last,
    input  logic                    i_valid,
    output logic                    o_ready,

    // BRAM Write Output (to dma_bram_bridge)
    output logic                    o_bram_wr_en,
    output logic [ADDR_WIDTH-1:0]   o_bram_wr_addr,
    output logic [DATA_WIDTH-1:0]   o_bram_wr_data,
    output logic [31:0]             o_bram_wr_strobe
);

    // ===================================================================
    // Keep-to-Strobe Expansion Function
    // ===================================================================
    // Expand 16-bit keep mask to 32-bit byte strobe (each FP16 = 2 bytes)
    function automatic [31:0] expand_keep_to_strobe(input [15:0] keep);
        logic [31:0] strobe;
        for (int i = 0; i < 16; i++) begin
            strobe[i*2 +: 2] = {2{keep[i]}};
        end
        return strobe;
    endfunction

    // ===================================================================
    // Registered Output with Address Counter
    // ===================================================================
    logic [ADDR_WIDTH-1:0]  addr_counter;
    logic                   wr_en_reg;
    logic [ADDR_WIDTH-1:0]  wr_addr_reg;
    logic [DATA_WIDTH-1:0]  wr_data_reg;
    logic [31:0]            wr_strobe_reg;

    // Always ready - simple passthrough with 1-cycle latency
    assign o_ready = 1'b1;

    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            addr_counter  <= {ADDR_WIDTH{1'b0}};
            wr_en_reg     <= 1'b0;
            wr_addr_reg   <= {ADDR_WIDTH{1'b0}};
            wr_data_reg   <= {DATA_WIDTH{1'b0}};
            wr_strobe_reg <= 32'd0;
        end else begin
            // Default: no write
            wr_en_reg <= 1'b0;

            // On valid input, register for BRAM write
            if (i_valid) begin
                wr_en_reg     <= 1'b1;
                wr_addr_reg   <= addr_counter;
                wr_data_reg   <= i_data;
                wr_strobe_reg <= expand_keep_to_strobe(i_keep);
                addr_counter  <= addr_counter + {{(ADDR_WIDTH-1){1'b0}}, 1'b1};
            end
        end
    end

    // ===================================================================
    // Output Assignments
    // ===================================================================
    assign o_bram_wr_en     = wr_en_reg;
    assign o_bram_wr_addr   = wr_addr_reg;
    assign o_bram_wr_data   = wr_data_reg;
    assign o_bram_wr_strobe = wr_strobe_reg;

endmodule : result_to_dma
