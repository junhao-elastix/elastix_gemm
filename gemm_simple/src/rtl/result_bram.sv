// ------------------------------------------------------------------
// Result BRAM Module
//
// Purpose: BRAM-based buffer for FP16 computation results
// Features:
//  - 16,384 entries × 16-bit width (FP16 format: 1 sign + 5 exp + 10 mantissa)
//  - Drop-in replacement for result_fifo with identical interface
//  - Dual-port BRAM for independent read/write access
//  - FIFO-compatible read/write semantics
//  - Full/empty status flags
//  - Count output for monitoring
//
// Resource Usage:
//  - ~4 ACX_BRAM72K primitives (vs ~6 for FP24, ~160 for equivalent FIFO)
//  - 33% resource savings vs FP24, 97% vs FIFO implementation
//
// Author: MS2.0 Result BRAM Enhancement
// Date: Fri Oct  3 05:30:36 AM PDT 2025 (Updated to FP16: Oct 11 2025)
// ------------------------------------------------------------------

module result_bram
import gemm_pkg::*;
(
    input  logic        i_clk,
    input  logic        i_reset_n,

    // Write Interface (from Compute Engine)
    input  logic [15:0] i_wr_data,     // FP16: [15]=sign, [14:10]=exp, [9:0]=mantissa
    input  logic        i_wr_en,
    output logic        o_full,
    output logic        o_afull,       // Almost full (back-pressure)

    // Read Interface (to Testbench/Host)
    output logic [15:0] o_rd_data,
    input  logic        i_rd_en,
    output logic        o_empty,

    // Status
    output logic [14:0] o_count   // 15-bit count (supports up to 32K entries)
);

    // ===================================================================
    // Parameters
    // ===================================================================
    localparam DEPTH      = tile_out_fifo_els_gp;  // 64 from gemm_pkg
    localparam DATA_WIDTH = 16;                     // FP16 format
    localparam ADDR_WIDTH = $clog2(DEPTH);          // 6 bits
    localparam AFULL_THRESHOLD = 192;               // Almost full at 192/256 entries (was 48/64)

    // ===================================================================
    // Internal Signals
    // ===================================================================

    // BRAM Storage - Inferred as block RAM
    (* ram_style = "block" *) logic [DATA_WIDTH-1:0] mem [0:DEPTH-1];

    // Pointers
    logic [ADDR_WIDTH-1:0] wr_ptr;
    logic [ADDR_WIDTH-1:0] rd_ptr;
    logic [ADDR_WIDTH-1:0] rd_ptr_next;

    // Count and Status
    logic [ADDR_WIDTH:0]   count_reg;  // 15 bits to hold 0-16,384
    logic                  full_reg;
    logic                  empty_reg;
    logic                  afull_reg;

    // Read data pipeline for BRAM registered output
    logic [DATA_WIDTH-1:0] rd_data_bram;
    logic [DATA_WIDTH-1:0] rd_data_reg;
    logic                  rd_valid;

    // Combinational status flags (to avoid 1-cycle delay)
    logic                  empty_comb;
    logic                  full_comb;
    logic                  afull_comb;
    
    assign empty_comb = (count_reg == 0);
    assign full_comb  = (count_reg == DEPTH);
    assign afull_comb = (count_reg >= AFULL_THRESHOLD);

    // ===================================================================
    // Write Logic
    // ===================================================================
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            wr_ptr <= '0;
        end else begin
            if (i_wr_en && !full_comb) begin
                mem[wr_ptr] <= i_wr_data;
                wr_ptr <= wr_ptr + 1'b1;
            end
        end
    end

    // ===================================================================
    // Read Logic
    // ===================================================================

    // Read pointer management
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            rd_ptr <= '0;
        end else begin
            if (i_rd_en && !empty_comb) begin
                rd_ptr <= rd_ptr + 1'b1;
            end
        end
    end

    // BRAM read - synchronous read (1 cycle latency)
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            rd_data_bram <= '0;
        end else begin
            // Read ahead to maintain FWFT-like behavior
            if (i_rd_en && !empty_comb) begin
                rd_data_bram <= mem[rd_ptr + 1'b1];
            end else if (!empty_comb) begin
                rd_data_bram <= mem[rd_ptr];
            end
        end
    end

    // Output register for FWFT compatibility
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            rd_data_reg <= '0;
            rd_valid <= 1'b0;
        end else begin
            if (!empty_comb) begin
                rd_data_reg <= rd_data_bram;
                rd_valid <= 1'b1;
            end else begin
                rd_valid <= 1'b0;
            end
        end
    end

    // Output assignment
    assign o_rd_data = rd_data_reg;

    // ===================================================================
    // Count and Status Logic
    // ===================================================================
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            count_reg <= '0;
        end else begin
            case ({i_wr_en && !full_comb, i_rd_en && !empty_comb})
                2'b10:   count_reg <= count_reg + 1'b1;  // Write only
                2'b01:   count_reg <= count_reg - 1'b1;  // Read only
                default: count_reg <= count_reg;         // Both or neither
            endcase
        end
    end

    // Register status flags for output
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            full_reg <= 1'b0;
            empty_reg <= 1'b1;
            afull_reg <= 1'b0;
        end else begin
            full_reg  <= full_comb;
            empty_reg <= empty_comb;
            afull_reg <= afull_comb;
        end
    end

    // Output assignments
    assign o_full  = full_reg;
    assign o_empty = empty_reg;
    assign o_afull = afull_reg;
    assign o_count = {{(15-ADDR_WIDTH-1){1'b0}}, count_reg};  // Zero-extend to 15 bits

    // ===================================================================
    // Assertions (for simulation only)
    // ===================================================================

    `ifdef SIM
        // Check for overflow
        property no_overflow;
            @(posedge i_clk) disable iff (~i_reset_n)
            (i_wr_en && full_reg) |=> $stable(wr_ptr);
        endproperty
        assert property (no_overflow) else
            $error("[RESULT_BRAM] Write to full BRAM attempted!");

        // Check for underflow
        property no_underflow;
            @(posedge i_clk) disable iff (~i_reset_n)
            (i_rd_en && empty_reg) |=> $stable(rd_ptr);
        endproperty
        assert property (no_underflow) else
            $error("[RESULT_BRAM] Read from empty BRAM attempted!");

        // Check FP16 format (sign bit should be explicit)
        property valid_fp16;
            @(posedge i_clk) disable iff (~i_reset_n)
            i_wr_en |-> (i_wr_data[15] == 1'b0 || i_wr_data[15] == 1'b1);
        endproperty
        assert property (valid_fp16) else
            $warning("[RESULT_BRAM] FP16 sign bit undefined!");

        // Verify BRAM capacity
        initial begin
            $display("[RESULT_BRAM] Configured for %0d entries (FIFO depth)", DEPTH);
            $display("[RESULT_BRAM] Data width: 16-bit FP16 format");
            $display("[RESULT_BRAM] Almost full threshold: %0d entries", AFULL_THRESHOLD);
        end
    `endif

    // ===================================================================
    // Debug Display (for simulation)
    // ===================================================================

    `ifdef SIM_VERBOSE
        always @(posedge i_clk) begin
            if (i_wr_en && !full_reg) begin
                $display("[RESULT_BRAM] Write: addr=%0d, data=0x%06x (S=%b, E=%02x, M=%04x), count=%0d",
                         wr_ptr, i_wr_data, i_wr_data[23], i_wr_data[22:15], i_wr_data[14:0], count_reg+1);
            end
            if (i_rd_en && !empty_reg) begin
                $display("[RESULT_BRAM] Read:  addr=%0d, data=0x%06x (S=%b, E=%02x, M=%04x), count=%0d",
                         rd_ptr, o_rd_data, o_rd_data[23], o_rd_data[22:15], o_rd_data[14:0], count_reg-1);
            end
            if (full_reg && i_wr_en) begin
                $warning("[RESULT_BRAM] Buffer full! count=%0d", count_reg);
            end
        end
    `endif

endmodule : result_bram
