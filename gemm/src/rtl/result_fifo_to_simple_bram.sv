// =============================================================================
// result_fifo_to_simple_bram.sv
// =============================================================================
// Simple adapter: Result FIFO (16-bit FP16) -> BRAM (one result per line)
//
// Description:
//   - Reads FP16 results from compute engine's result FIFO
//   - Writes each result to a separate BRAM line (no packing)
//   - BRAM line format: {240'h0, fp16_result[15:0]} (zero-padded to 256 bits)
//   - Exposes first 4 results to dedicated output registers for quick access
//
// Architecture:
//   - Continuous FIFO draining (reads whenever !empty)
//   - Simple address increment (one result = one BRAM line)
//   - Clean 1:1 mapping for easy host readback
// =============================================================================

module result_fifo_to_simple_bram (
    input  logic        i_clk,
    input  logic        i_reset_n,
    
    // Result FIFO interface (from compute engine)
    input  logic [15:0] i_fifo_rdata,
    output logic        o_fifo_ren,
    input  logic        i_fifo_empty,
    
    // BRAM interface (256-bit per line, one result per line)
    output logic [8:0]  o_bram_wr_addr,
    output logic [255:0] o_bram_wr_data,
    output logic        o_bram_wr_en,
    
    // First 4 results exposed to registers (for quick host access)
    output logic [15:0] o_result_0,
    output logic [15:0] o_result_1,
    output logic [15:0] o_result_2,
    output logic [15:0] o_result_3
);

    // =========================================================================
    // Internal State
    // =========================================================================
    logic [1:0]  fifo_rd_pipeline;   // 2-bit pipeline for FIFO read latency
    logic [8:0]  result_count;       // Number of results written to BRAM
    
    // =========================================================================
    // FIFO Read State Machine
    // =========================================================================
    // Continuous draining with proper 2-cycle latency:
    // Cycle N:   Issue read (o_fifo_ren = 1), pipeline[0] = 1
    // Cycle N+1: Keep ren low, pipeline[1] = pipeline[0]
    // Cycle N+2: Data valid, capture and write to BRAM
    
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            o_fifo_ren        <= 1'b0;
            o_bram_wr_en      <= 1'b0;
            o_bram_wr_addr    <= 9'd0;
            o_bram_wr_data    <= 256'd0;
            fifo_rd_pipeline  <= 2'b00;
            result_count      <= 9'd0;
            o_result_0        <= 16'd0;
            o_result_1        <= 16'd0;
            o_result_2        <= 16'd0;
            o_result_3        <= 16'd0;
        end else begin
            // Default: no BRAM write
            o_bram_wr_en <= 1'b0;
            
            // Shift pipeline register
            fifo_rd_pipeline <= {fifo_rd_pipeline[0], 1'b0};
            
            // Continuous FIFO draining: issue read whenever FIFO has data
            // and no read is in progress (pipeline is empty)
            if (!i_fifo_empty && fifo_rd_pipeline == 2'b00) begin
                o_fifo_ren           <= 1'b1;
                fifo_rd_pipeline[0]  <= 1'b1;
            end else begin
                o_fifo_ren <= 1'b0;
            end

            // Capture and write FIFO data 2 cycles after read
            // (when pipeline[1] == 1)
            if (fifo_rd_pipeline[1]) begin
                // Capture first 4 results to dedicated registers
                case (result_count)
                    9'd0: o_result_0 <= i_fifo_rdata;
                    9'd1: o_result_1 <= i_fifo_rdata;
                    9'd2: o_result_2 <= i_fifo_rdata;
                    9'd3: o_result_3 <= i_fifo_rdata;
                    default: ;  // No register capture after first 4
                endcase
                
                // Write to BRAM: one result per line (zero-padded to 256 bits)
                o_bram_wr_data <= {240'h0, i_fifo_rdata};  // FP16 result in LSBs
                o_bram_wr_addr <= result_count;
                o_bram_wr_en   <= 1'b1;
                
                // Increment result count
                result_count <= result_count + 9'd1;
            end
        end
    end

endmodule : result_fifo_to_simple_bram

