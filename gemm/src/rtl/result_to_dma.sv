// ------------------------------------------------------------------
// Result to DMA BRAM Adapter Module (Circular Buffer, Always-Drain)
//
// Purpose: Converts ready-valid stream from result_collector_2d to
//          BRAM write interface with circular buffer semantics.
//
// Design: Circular buffer adapter WITHOUT backpressure (always drain)
//  - wr_ptr managed by hardware, rd_ptr from host register
//  - ALWAYS accepts data from result_collector (o_ready = 1)
//  - Host must consume data fast enough or risk overwrite
//  - almost_full signal kept for monitoring only, not flow control
//  - Used entries calculated for host polling
//  - 16-bit keep mask expanded to 32-bit byte strobe
//
// Author: Junhao Pan
// Date: Jan 28, 2026 (Updated Jan 29: always-drain mode)
// ------------------------------------------------------------------

module result_to_dma #(
    parameter DATA_WIDTH = 256,
    parameter ADDR_WIDTH = 9,
    parameter ALMOST_FULL_MARGIN = 16  // Backpressure margin
) (
    input  logic                    i_clk,
    input  logic                    i_reset_n,

    // Ready-Valid Input (from result_collector_2d)
    input  logic [DATA_WIDTH-1:0]   i_data,
    input  logic [15:0]             i_keep,      // 16 FP16 value mask
    input  logic                    i_last,
    input  logic                    i_valid,
    output logic                    o_ready,

    // Circular Buffer Control (from host register)
    input  logic [ADDR_WIDTH-1:0]   i_rd_ptr,

    // Circular Buffer Status (to host registers)
    output logic [ADDR_WIDTH-1:0]   o_wr_ptr,
    output logic [ADDR_WIDTH:0]     o_used_entries,  // 10 bits for 0-512
    output logic                    o_almost_full,
    output logic                    o_empty,

    // BRAM Write Output (to dma_bram_bridge)
    output logic                    o_bram_wr_en,
    output logic [ADDR_WIDTH-1:0]   o_bram_wr_addr,
    output logic [DATA_WIDTH-1:0]   o_bram_wr_data,
    output logic [31:0]             o_bram_wr_strobe
);

    // ===================================================================
    // Local Parameters
    // ===================================================================
    localparam BUFFER_DEPTH = (1 << ADDR_WIDTH);  // 512 lines
    localparam ALMOST_FULL_THRESHOLD = BUFFER_DEPTH - ALMOST_FULL_MARGIN;  // 496

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
    // Circular Buffer Pointers
    // ===================================================================
    logic [ADDR_WIDTH-1:0] wr_ptr_reg;
    logic [ADDR_WIDTH:0]   used_entries_comb;
    logic                  almost_full_comb;
    logic                  empty_comb;

    // Used entries calculation (combinational)
    // Handles wrap-around: if wr_ptr < rd_ptr, buffer has wrapped
    always_comb begin
        if (wr_ptr_reg >= i_rd_ptr)
            used_entries_comb = {1'b0, wr_ptr_reg} - {1'b0, i_rd_ptr};
        else
            used_entries_comb = BUFFER_DEPTH[ADDR_WIDTH:0] - {1'b0, i_rd_ptr} + {1'b0, wr_ptr_reg};
    end

    // Backpressure and empty flags
    assign almost_full_comb = (used_entries_comb >= ALMOST_FULL_THRESHOLD);
    assign empty_comb = (wr_ptr_reg == i_rd_ptr);

    // Ready signal: ALWAYS ready to drain result_collector's output FIFO
    // Host must consume data fast enough or risk overwrite
    assign o_ready = 1'b1;

    // ===================================================================
    // Registered Outputs
    // ===================================================================
    logic                   wr_en_reg;
    logic [ADDR_WIDTH-1:0]  wr_addr_reg;
    logic [DATA_WIDTH-1:0]  wr_data_reg;
    logic [31:0]            wr_strobe_reg;

    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            wr_ptr_reg    <= {ADDR_WIDTH{1'b0}};
            wr_en_reg     <= 1'b0;
            wr_addr_reg   <= {ADDR_WIDTH{1'b0}};
            wr_data_reg   <= {DATA_WIDTH{1'b0}};
            wr_strobe_reg <= 32'd0;
        end else begin
            // Default: no write
            wr_en_reg <= 1'b0;

            // On valid input AND ready, register for BRAM write
            if (i_valid && o_ready) begin
                wr_en_reg     <= 1'b1;
                wr_addr_reg   <= wr_ptr_reg;
                wr_data_reg   <= i_data;
                wr_strobe_reg <= expand_keep_to_strobe(i_keep);

                // Increment write pointer with wrap-around
                if (wr_ptr_reg == BUFFER_DEPTH - 1)
                    wr_ptr_reg <= {ADDR_WIDTH{1'b0}};
                else
                    wr_ptr_reg <= wr_ptr_reg + {{(ADDR_WIDTH-1){1'b0}}, 1'b1};
            end
        end
    end

    // ===================================================================
    // Output Assignments
    // ===================================================================
    // BRAM interface
    assign o_bram_wr_en     = wr_en_reg;
    assign o_bram_wr_addr   = wr_addr_reg;
    assign o_bram_wr_data   = wr_data_reg;
    assign o_bram_wr_strobe = wr_strobe_reg;

    // Circular buffer status
    assign o_wr_ptr       = wr_ptr_reg;
    assign o_used_entries = used_entries_comb;
    assign o_almost_full  = almost_full_comb;
    assign o_empty        = empty_comb;

endmodule : result_to_dma
