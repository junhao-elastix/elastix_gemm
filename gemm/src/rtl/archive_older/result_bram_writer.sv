// ------------------------------------------------------------------
// Result BRAM Writer Module
//
// Purpose: Convert FP24 stream to packed FP16 BRAM writes
// Features:
//  - FP24 to FP16 conversion: {sign[1], exp[5], mant[10]}
//  - Pack 16 FP16 values into 256-bit BRAM lines
//  - Auto-increment BRAM addresses
//  - Handles 128x128 matrix output (1024 FP16 values = 64 BRAM lines)
//
// FP Conversion:
//  FP24 (1+8+15): sign | exp[7:0] | mant[14:0]
//  FP16 (1+5+10): sign | exp[4:0] | mant[9:0]
//  Conversion: {s, e[4:0], m[14:5]} with saturation
//
// Author: Integration for MS2.0 GEMM Engine
// Date: Mon Oct  7 08:50:00 AM PDT 2024
// ------------------------------------------------------------------

module result_bram_writer
#(
    parameter BRAM_ADDR_WIDTH = 9,     // 512 addresses
    parameter BRAM_DATA_WIDTH = 256,   // 256-bit lines
    parameter FP16_PER_LINE = 16       // 16 FP16 values per line
)
(
    input  logic                         i_clk,
    input  logic                         i_reset_n,

    // FP24 Result Stream Interface
    input  logic [23:0]                  i_fp24_result,
    input  logic                         i_result_valid,
    output logic                         o_result_ready,

    // BRAM Write Interface
    output logic [BRAM_ADDR_WIDTH-1:0]  o_bram_wr_addr,
    output logic [BRAM_DATA_WIDTH-1:0]  o_bram_wr_data,
    output logic                         o_bram_wr_en,

    // Control
    input  logic                         i_clear,       // Clear address and buffer
    output logic [31:0]                  o_result_count // Total FP16 values written
);

    // ===================================================================
    // Internal Signals
    // ===================================================================

    // FP16 accumulation buffer
    logic [15:0] fp16_buffer [0:FP16_PER_LINE-1];
    logic [3:0]  buffer_count;  // 0-15 values in buffer

    // BRAM address
    logic [BRAM_ADDR_WIDTH-1:0] bram_addr_reg;

    // Result counter
    logic [31:0] result_count_reg;

    // FP24 to FP16 conversion
    logic [15:0] fp16_converted;

    // ===================================================================
    // FP24 to FP16 Conversion
    // ===================================================================
    // FP24: sign[23] | exp[22:15] | mant[14:0]
    // FP16: sign[15] | exp[14:10] | mant[9:0]

    always_comb begin
        logic        sign;
        logic [7:0]  exp24;
        logic [14:0] mant24;
        logic [4:0]  exp16;
        logic [9:0]  mant16;

        // Extract FP24 fields
        sign   = i_fp24_result[23];
        exp24  = i_fp24_result[22:15];
        mant24 = i_fp24_result[14:0];

        // Convert exponent (with saturation)
        // FP24 bias: 127, FP16 bias: 15
        // exp16 = exp24 - 127 + 15 = exp24 - 112
        if (exp24 == 8'h00) begin
            // Zero/denormal
            exp16 = 5'h00;
            mant16 = 10'h000;
        end else if (exp24 == 8'hFF) begin
            // Inf/NaN
            exp16 = 5'h1F;
            mant16 = mant24[14:5];  // Preserve NaN payload
        end else if (exp24 < 8'd113) begin
            // Underflow to zero
            exp16 = 5'h00;
            mant16 = 10'h000;
        end else if (exp24 > 8'd142) begin
            // Overflow to infinity
            exp16 = 5'h1F;
            mant16 = 10'h000;
        end else begin
            // Normal conversion: FP24 bias=127, FP16 bias=15, net adjustment = -112
            exp16 = exp24 - 8'd112;  // Unbias FP24 (-127) and rebias FP16 (+15)
            mant16 = mant24[14:5];  // Take upper 10 bits of mantissa
        end

        // Pack FP16
        fp16_converted = {sign, exp16, mant16};
    end

    // ===================================================================
    // Buffer Management
    // ===================================================================
    always_ff @(posedge i_clk) begin
        if (~i_reset_n || i_clear) begin
            buffer_count <= 4'd0;
            fp16_buffer <= '{default: 16'h0000};  // SystemVerilog array assignment (synthesis-friendly)
        end else if (i_result_valid && o_result_ready) begin
            // Store converted FP16 in buffer
            fp16_buffer[buffer_count] <= fp16_converted;

            // Update count or reset after write
            if (buffer_count == FP16_PER_LINE - 1) begin
                buffer_count <= 4'd0;
            end else begin
                buffer_count <= buffer_count + 4'd1;
            end
        end
    end

    // ===================================================================
    // BRAM Write Control
    // ===================================================================
    always_ff @(posedge i_clk) begin
        if (~i_reset_n || i_clear) begin
            bram_addr_reg <= '0;
            o_bram_wr_en <= 1'b0;
            o_bram_wr_data <= '0;
        end else begin
            // Default: no write
            o_bram_wr_en <= 1'b0;

            // Write when buffer is full
            if (i_result_valid && o_result_ready && buffer_count == FP16_PER_LINE - 1) begin
                // Pack all FP16 values into 256-bit line (synthesis-optimized)
                // Pack buffered values (0-14) and current value (15) in single assignment
                o_bram_wr_data <= {fp16_converted, fp16_buffer[14], fp16_buffer[13], fp16_buffer[12],
                                  fp16_buffer[11], fp16_buffer[10], fp16_buffer[9],  fp16_buffer[8],
                                  fp16_buffer[7],  fp16_buffer[6],  fp16_buffer[5],  fp16_buffer[4],
                                  fp16_buffer[3],  fp16_buffer[2],  fp16_buffer[1],  fp16_buffer[0]};

                o_bram_wr_en <= 1'b1;
                // Address is assigned combinationally from bram_addr_reg (see line 180)

                // Increment address for next write
                bram_addr_reg <= bram_addr_reg + 1'b1;
            end
        end
    end

    // ===================================================================
    // Result Counter
    // ===================================================================
    always_ff @(posedge i_clk) begin
        if (~i_reset_n || i_clear) begin
            result_count_reg <= 32'd0;
        end else if (i_result_valid && o_result_ready) begin
            result_count_reg <= result_count_reg + 32'd1;
        end
    end

    // ===================================================================
    // Output Assignments
    // ===================================================================
    assign o_result_ready = 1'b1;  // Always ready to accept results (simple design)
    assign o_bram_wr_addr = bram_addr_reg;
    assign o_result_count = result_count_reg;

    // ===================================================================
    // Debug Display (for simulation)
    // ===================================================================
    `ifdef SIMULATION
        always @(posedge i_clk) begin
            if (i_result_valid && o_result_ready) begin
                $display("[RESULT_WRITER] @%0t FP24=0x%06x -> FP16=0x%04x (buffer[%0d])",
                         $time, i_fp24_result, fp16_converted, buffer_count);
            end
            if (o_bram_wr_en) begin
                $display("[RESULT_WRITER] @%0t Writing BRAM[%0d]: %064x",
                         $time, o_bram_wr_addr, o_bram_wr_data);
            end
        end
    `endif

endmodule : result_bram_writer