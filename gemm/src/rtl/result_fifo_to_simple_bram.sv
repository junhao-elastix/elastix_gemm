// =============================================================================
// result_fifo_to_simple_bram.sv - Direct Write (No Packer)
// =============================================================================
// Direct adapter: Result FIFO (16-bit FP16) -> BRAM (byte-granular writes)
//
// Description:
//   - Reads FP16 results from compute engine's result FIFO (1-cycle latency)
//   - Writes each FP16 DIRECTLY to BRAM using byte enables
//   - No buffering/packing - immediate write on each result
//   - Implements circular FIFO with 13-bit wr_ptr counter (8192 results)
//   - Provides backpressure when 7/8 full (7936 results)
//
// Key Changes from Packed Version:
//   - Removed pack_buffer and pack_position (no accumulation)
//   - Removed flush logic (no longer needed)
//   - Added o_bram_wr_strobe for byte-granular writes
//   - wr_ptr always reflects actual BRAM state
//   - Simplified to 1-cycle FIFO read latency (was 2-cycle)
//
// Architecture:
//   - Standard synchronous FIFO: rd_en on cycle N, data valid on cycle N+1
//   - Continuous draining with immediate byte-granular writes
//   - 13-bit FP16 addressing: {addr[12:0], 1'b0} for 2-byte alignment
//   - BRAM line = addr[12:4], byte position = addr[3:0] * 2
//   - Circular buffer wraps at 8192
// =============================================================================

module result_fifo_to_simple_bram (
    input  logic        i_clk,
    input  logic        i_reset_n,

    // Result FIFO interface (from compute engine)
    input  logic [15:0] i_fifo_rdata,
    output logic        o_fifo_ren,
    input  logic        i_fifo_empty,

    // BRAM interface (256-bit per line, byte-granular writes)
    output logic [8:0]   o_bram_wr_addr,   // Line address (0-511)
    output logic [255:0] o_bram_wr_data,   // Data (FP16 positioned by strobe)
    output logic         o_bram_wr_en,
    output logic [31:0]  o_bram_wr_strobe, // Byte enables (2 bits set per FP16)

    // First 4 results exposed to registers (for quick host access)
    output logic [15:0] o_result_0,
    output logic [15:0] o_result_1,
    output logic [15:0] o_result_2,
    output logic [15:0] o_result_3,

    // Circular buffer interface
    input  logic [12:0] i_rd_ptr,         // Read pointer from host (0-8191)
    output logic [12:0] o_wr_ptr,         // Write pointer (0-8191)
    output logic [13:0] o_used_entries,   // Number of valid FP16 results (0-8192)
    output logic        o_empty,          // Buffer empty flag
    input  logic        i_write_top_reset, // Host reset signal (resets wr_ptr)
    output logic        o_almost_full     // Backpressure signal
);

    // =========================================================================
    // Parameters
    // =========================================================================
    localparam TOTAL_CAPACITY = 8192;           // Total FP16 results
    localparam ALMOST_FULL_THRESHOLD = 7936;    // Trigger when < 256 FP16s free

    // =========================================================================
    // Internal State
    // =========================================================================
    logic         fifo_rd_valid;             // 1-cycle pipeline for FIFO read latency
    logic [12:0]  wr_ptr;                    // FP16 write position (0-8191)
    logic [12:0]  first_four_count;          // Counter for first 4 results capture

    // Direct write calculation signals (unused, kept for potential debug)
    logic [8:0]   line_addr;                 // BRAM line address
    logic [3:0]   fp16_position;             // FP16 position within line (0-15)
    logic [4:0]   byte_position;             // Byte position within 256-bit line
    logic [31:0]  byte_strobe;               // Byte enable mask

    // =========================================================================
    // Circular Buffer Management
    // =========================================================================
    logic [13:0] used_entries;               // 14-bit to hold 0-8192

    // Calculate used entries (circular buffer arithmetic)
    always_comb begin
        if (wr_ptr >= i_rd_ptr) begin
            used_entries = {1'b0, wr_ptr} - {1'b0, i_rd_ptr};  // Normal case
        end else begin
            used_entries = 14'd8192 - {1'b0, i_rd_ptr} + {1'b0, wr_ptr};  // Wrapped case
        end
    end

    // =========================================================================
    // Write Pointer Management
    // =========================================================================
    // Circular counter with host reset capability (hardware auto-wraps)
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            wr_ptr <= 13'd0;
        end else if (i_write_top_reset) begin
            wr_ptr <= 13'd0;  // Host reset
        end else if (fifo_rd_valid) begin
            // Increment on each valid result (wraps at 8192)
            if (wr_ptr == TOTAL_CAPACITY - 1) begin
                wr_ptr <= 13'd0;  // Wrap around
            end else begin
                wr_ptr <= wr_ptr + 13'd1;
            end
        end
    end

    // =========================================================================
    // Threshold Detection for Backpressure
    // =========================================================================
    always_comb begin
        o_almost_full = (used_entries >= ALMOST_FULL_THRESHOLD);
        o_empty = (wr_ptr == i_rd_ptr);
    end

    // =========================================================================
    // FIFO Read and BRAM Write Logic (Direct Write - No Packing!)
    // =========================================================================
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            o_fifo_ren       <= 1'b0;
            fifo_rd_valid    <= 1'b0;
            o_bram_wr_en     <= 1'b0;
            o_bram_wr_addr   <= 9'd0;
            o_bram_wr_data   <= 256'd0;
            o_bram_wr_strobe <= 32'd0;
            o_result_0       <= 16'd0;
            o_result_1       <= 16'd0;
            o_result_2       <= 16'd0;
            o_result_3       <= 16'd0;
            first_four_count <= 13'd0;
        end else begin
            // Default: no write
            o_bram_wr_en <= 1'b0;

            // Pipeline FIFO read (1 cycle for data to arrive)
            // Standard synchronous FIFO: Assert rd_en on cycle N, data valid on cycle N+1
            fifo_rd_valid <= o_fifo_ren;

            // Issue FIFO read pulse (ONE cycle only!) if not empty and not already reading
            // CRITICAL: o_fifo_ren must be a pulse, not level-sensitive!
            if (!i_fifo_empty && !o_almost_full && !o_fifo_ren && !fifo_rd_valid) begin
                o_fifo_ren <= 1'b1;
            end else begin
                o_fifo_ren <= 1'b0;
            end

            // Write directly to BRAM 1 cycle after read (when fifo_rd_valid is high)
            if (fifo_rd_valid) begin
                // Capture first 4 results to dedicated registers
                if (first_four_count < 4) begin
                    case (first_four_count)
                        13'd0: o_result_0 <= i_fifo_rdata;
                        13'd1: o_result_1 <= i_fifo_rdata;
                        13'd2: o_result_2 <= i_fifo_rdata;
                        13'd3: o_result_3 <= i_fifo_rdata;
                        default: ;
                    endcase
                    first_four_count <= first_four_count + 13'd1;
                end

                // Write FP16 immediately to BRAM
                // Use direct expressions to avoid blocking assignment timing issues
                o_bram_wr_addr   <= wr_ptr[12:4];  // Line address
                o_bram_wr_data   <= {240'd0, i_fifo_rdata} << ({wr_ptr[3:0], 1'b0} * 8);  // Position FP16
                o_bram_wr_en     <= 1'b1;
                o_bram_wr_strobe <= 32'd3 << {wr_ptr[3:0], 1'b0};  // Byte strobe
            end

            // Handle write_top_reset
            if (i_write_top_reset) begin
                first_four_count <= 13'd0;
                // Note: wr_ptr reset handled in separate always_ff block
            end
        end
    end

    // =========================================================================
    // Output Assignments
    // =========================================================================
    assign o_wr_ptr = wr_ptr;
    assign o_used_entries = used_entries;

endmodule : result_fifo_to_simple_bram
