// ------------------------------------------------------------------
// Result FIFO to BRAM Adapter
//
// Purpose: Convert streaming FIFO output (FP16 results) to BRAM writes
// This allows engine_top's FIFO interface to work with the existing
// BRAM DMA infrastructure in elastix_gemm_top.
//
// Functionality:
//  - Reads FP16 results from engine_top result FIFO
//  - Packs 16 FP16 values into 256-bit BRAM line
//  - Writes packed data to result BRAM for host DMA access
//  - Auto-increments BRAM address
//
// Packing Format (256-bit line):
//  [255:240] = result[15] (FP16)
//  [239:224] = result[14] (FP16)
//  ...
//  [15:0]    = result[0]  (FP16)
//
// Author: Integration for MS2.0 GEMM Engine
// Date: Sun Oct 12 19:05 PDT 2025
// ------------------------------------------------------------------

module result_fifo_to_bram
(
    // Clock and Reset
    input  logic        i_clk,
    input  logic        i_reset_n,

    // FIFO Read Interface (from engine_top)
    input  logic [15:0] i_fifo_rdata,   // FP16 result data
    output logic        o_fifo_ren,     // Read enable
    input  logic        i_fifo_empty,   // FIFO empty flag

    // BRAM Write Interface (to axi_bram_responder)
    output logic [8:0]   o_bram_wr_addr,   // BRAM address (512 lines)
    output logic [255:0] o_bram_wr_data,   // 256-bit BRAM data (16xFP16)
    output logic         o_bram_wr_en,     // BRAM write enable
    
    // First 4 Results to Registers (for testing without BRAM DMA)
    output logic [15:0]  o_result_0,       // First FP16 result
    output logic [15:0]  o_result_1,       // Second FP16 result
    output logic [15:0]  o_result_2,       // Third FP16 result
    output logic [15:0]  o_result_3        // Fourth FP16 result
);

    // ===================================================================
    // Packing State Machine with 1-Cycle FIFO Read Latency
    // ===================================================================
    logic [3:0]   pack_count;        // Count FP16 values (0-15)
    logic [255:0] pack_buffer;       // Accumulate 16 FP16 values
    logic [8:0]   bram_addr;         // Auto-incrementing BRAM address
    logic         fifo_rd_pending;   // Track pending FIFO read (1-cycle latency)

    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            pack_count        <= 4'd0;
            pack_buffer       <= 256'd0;
            bram_addr         <= 9'd0;
            o_bram_wr_en      <= 1'b0;
            o_bram_wr_addr    <= 9'd0;
            o_bram_wr_data    <= 256'd0;
            o_fifo_ren        <= 1'b0;
            fifo_rd_pending   <= 1'b0;
            o_result_0        <= 16'd0;
            o_result_1        <= 16'd0;
            o_result_2        <= 16'd0;
            o_result_3        <= 16'd0;
        end else begin
            // Default: no BRAM write
            o_bram_wr_en <= 1'b0;

            // Issue FIFO read if not empty and no pending read
            if (!i_fifo_empty && !fifo_rd_pending) begin
                o_fifo_ren      <= 1'b1;
                fifo_rd_pending <= 1'b1;
            end else begin
                o_fifo_ren <= 1'b0;
            end

            // Process FIFO data on next cycle after read
            if (fifo_rd_pending) begin
                fifo_rd_pending <= 1'b0;
                
                // Capture first 4 results to dedicated registers
                case (pack_count)
                    4'd0: o_result_0 <= i_fifo_rdata;
                    4'd1: o_result_1 <= i_fifo_rdata;
                    4'd2: o_result_2 <= i_fifo_rdata;
                    4'd3: o_result_3 <= i_fifo_rdata;
                    default: ;  // No register capture after first 4
                endcase
                
                // Pack FP16 value into buffer
                case (pack_count)
                    4'd0:  pack_buffer[15:0]     <= i_fifo_rdata;
                    4'd1:  pack_buffer[31:16]    <= i_fifo_rdata;
                    4'd2:  pack_buffer[47:32]    <= i_fifo_rdata;
                    4'd3:  pack_buffer[63:48]    <= i_fifo_rdata;
                    4'd4:  pack_buffer[79:64]    <= i_fifo_rdata;
                    4'd5:  pack_buffer[95:80]    <= i_fifo_rdata;
                    4'd6:  pack_buffer[111:96]   <= i_fifo_rdata;
                    4'd7:  pack_buffer[127:112]  <= i_fifo_rdata;
                    4'd8:  pack_buffer[143:128]  <= i_fifo_rdata;
                    4'd9:  pack_buffer[159:144]  <= i_fifo_rdata;
                    4'd10: pack_buffer[175:160]  <= i_fifo_rdata;
                    4'd11: pack_buffer[191:176]  <= i_fifo_rdata;
                    4'd12: pack_buffer[207:192]  <= i_fifo_rdata;
                    4'd13: pack_buffer[223:208]  <= i_fifo_rdata;
                    4'd14: pack_buffer[239:224]  <= i_fifo_rdata;
                    4'd15: pack_buffer[255:240]  <= i_fifo_rdata;
                endcase

                // Increment pack count
                pack_count <= pack_count + 4'd1;

                // When buffer is full (16 FP16 values), write to BRAM
                if (pack_count == 4'd15) begin
                    o_bram_wr_data <= {i_fifo_rdata, pack_buffer[239:0]};  // Complete the 256-bit line
                    o_bram_wr_addr <= bram_addr;
                    o_bram_wr_en   <= 1'b1;
                    bram_addr      <= bram_addr + 9'd1;
                    pack_count     <= 4'd0;  // Reset pack count
                end
            end
        end
    end

endmodule : result_fifo_to_bram


