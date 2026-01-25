// =============================================================================
// result_fifo_to_simple_bram.sv - 256-bit Direct Write (MLP Mode)
// =============================================================================
// Direct adapter: 256-bit results (16×FP16) -> BRAM with circular buffer tracking
//
// Description:
//   - Receives 16 FP16 results per cycle from MLP compute engine
//   - Writes full 256-bit lines directly to BRAM
//   - Implements circular FIFO with 13-bit wr_ptr counter (8192 FP16 results)
//   - Increments wr_ptr by 16 for each 256-bit write
//   - Provides backpressure when 8128 results are written
//
// MLP Mode Changes (Dec 2025):
//   - Changed input from 16-bit FIFO to 256-bit direct (i_data_256, i_data_valid)
//   - wr_ptr increments by 16 per write (16 FP16 values per 256-bit line)
//   - Removed FIFO read latency handling (direct write on valid)
//   - Simplified flow: valid -> immediate BRAM write
//
// Architecture:
//   - 256-bit writes at line granularity (no byte-granular positioning needed)
//   - 13-bit FP16 addressing: ptr/16 = line address, ptr%16 = position in line
//   - Circular buffer wraps at 8192 (512 lines × 16 FP16/line)
//
// Author: Junhao Pan
// Date: December 2025
// =============================================================================

module result_fifo_to_simple_bram (
    input  logic        i_clk,
    input  logic        i_reset_n,

    // 256-bit result interface (from MLP compute engine)
    input  logic [255:0] i_data_256,        // 16×FP16 results
    input  logic         i_data_valid,      // Valid pulse
    input  logic [8:0]   i_wr_addr,         // Write address from engine (for verification)

    // Legacy FIFO interface (directly connected for backward compat, unused)
    input  logic [15:0] i_fifo_rdata,
    output logic        o_fifo_ren,
    input  logic        i_fifo_empty,

    // BRAM interface (256-bit per line, full-line writes)
    output logic [8:0]   o_bram_wr_addr,   // Line address (0-511)
    output logic [255:0] o_bram_wr_data,   // Full 256-bit data
    output logic         o_bram_wr_en,
    output logic [31:0]  o_bram_wr_strobe, // All bytes valid for 256-bit write

    // First 4 results exposed to registers (for quick host access)
    output logic [15:0] o_result_0,
    output logic [15:0] o_result_1,
    output logic [15:0] o_result_2,
    output logic [15:0] o_result_3,

    // Circular buffer interface
    input  logic [12:0] i_rd_ptr,         // Read pointer from host (0-8191, FP16 granularity)
    output logic [12:0] o_wr_ptr,         // Write pointer (0-8191, FP16 granularity)
    output logic [13:0] o_used_entries,   // Number of valid FP16 results (0-8192)
    output logic        o_empty,          // Buffer empty flag
    output logic        o_almost_full     // Backpressure signal
);

    // =========================================================================
    // Parameters
    // =========================================================================
    localparam TOTAL_CAPACITY = 8192;           // Total FP16 results
    localparam ALMOST_FULL_THRESHOLD = 8128;    // Trigger when < 64 FP16s free (4 lines)
    localparam FP16_PER_LINE = 16;              // 16 FP16 values per 256-bit line

    // =========================================================================
    // Internal State
    // =========================================================================
    logic [12:0]  rd_ptr;                    // FP16 read position (0-8191) from host
    logic [12:0]  wr_ptr;                    // FP16 write position (0-8191)
    logic         first_write_captured;       // Flag for first write capture

    // =========================================================================
    // Legacy FIFO interface - tie off (not used in MLP mode)
    // =========================================================================
    assign o_fifo_ren = 1'b0;  // Never read from legacy FIFO

    // =========================================================================
    // Circular Buffer Management
    // =========================================================================
    logic [13:0] used_entries;               // 14-bit to hold 0-8192

    // Calculate used entries (circular buffer arithmetic)
    always_comb begin
        if (wr_ptr >= rd_ptr) begin
            used_entries = {1'b0, wr_ptr} - {1'b0, rd_ptr};  // Normal case
        end else begin
            used_entries = 14'd8192 - {1'b0, rd_ptr} + {1'b0, wr_ptr};  // Wrapped case
        end
    end

    // =========================================================================
    // Write Pointer Management
    // =========================================================================
    // Circular counter with automatic wrap, increments by 16 per 256-bit write
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            wr_ptr <= 13'd0;
            rd_ptr <= 13'd0;
        end else begin
            // Update rd_ptr from host CSR
            if (i_rd_ptr != rd_ptr) begin
                rd_ptr <= i_rd_ptr;
            end

            // Increment wr_ptr by 16 on each valid 256-bit write
            if (i_data_valid) begin
                if (wr_ptr >= TOTAL_CAPACITY - FP16_PER_LINE) begin
                    wr_ptr <= 13'd0;  // Wrap around
                end else begin
                    wr_ptr <= wr_ptr + 13'd16;  // Increment by 16 FP16 values
                end
            end
        end
    end

    // =========================================================================
    // Threshold Detection for Backpressure
    // =========================================================================
    always_comb begin
        o_almost_full = (used_entries >= ALMOST_FULL_THRESHOLD);
        o_empty = (wr_ptr == rd_ptr);
    end

    // =========================================================================
    // BRAM Write Logic (Direct 256-bit Write)
    // =========================================================================
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            o_bram_wr_en     <= 1'b0;
            o_bram_wr_addr   <= 9'd0;
            o_bram_wr_data   <= 256'd0;
            o_bram_wr_strobe <= 32'd0;
            o_result_0       <= 16'd0;
            o_result_1       <= 16'd0;
            o_result_2       <= 16'd0;
            o_result_3       <= 16'd0;
            first_write_captured <= 1'b0;
        end else begin
            // Default: no write
            o_bram_wr_en <= 1'b0;

            // Write 256-bit line directly to BRAM when valid
            if (i_data_valid) begin
                // BRAM line address from wr_ptr (divide by 16)
                o_bram_wr_addr   <= wr_ptr[12:4];
                o_bram_wr_data   <= i_data_256;
                o_bram_wr_en     <= 1'b1;
                o_bram_wr_strobe <= 32'hFFFFFFFF;  // All 32 bytes valid

                // Capture first 4 results on first write only
                if (!first_write_captured) begin
                    o_result_0 <= i_data_256[15:0];
                    o_result_1 <= i_data_256[31:16];
                    o_result_2 <= i_data_256[47:32];
                    o_result_3 <= i_data_256[63:48];
                    first_write_captured <= 1'b1;
                end
            end
        end
    end

    // =========================================================================
    // Output Assignments
    // =========================================================================
    assign o_wr_ptr = wr_ptr;
    assign o_used_entries = used_entries;

endmodule : result_fifo_to_simple_bram
