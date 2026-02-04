// =============================================================================
// GFP8 Quantizer Module
// =============================================================================
// Quantizes aligned signed mantissas from GFP16 (11-bit) to GFP8 (8-bit).
// Pure combinational module - no clock or state.
//
// For each element:
//   1. Add rounding constant (0.5 ULP at target precision)
//   2. Right shift to reduce bits
//   3. Saturate to [-128, 127] range (8-bit signed)
//
// Key features:
//   - Preserves 2's complement sign throughout
//   - Round-to-nearest via rounding constant
//   - Saturation clamps on overflow (no wrap-around)
// =============================================================================

module gfp8_quantizer #(
    parameter int IN_MAN_BITS  = 11,       // Source: GFP16 mantissa (signed)
    parameter int OUT_MAN_BITS = 8,        // Target: GFP8 mantissa (signed)
    parameter int IN_ELEMENTS  = 16        // Elements per word
) (
    // Input: Aligned signed mantissas
    input  logic signed [IN_ELEMENTS-1:0][IN_MAN_BITS-1:0]   i_aligned_mans,
    input  logic [IN_ELEMENTS-1:0]                            i_round_bits,
    input  logic [IN_ELEMENTS-1:0]                            i_is_zero,

    // Output: Quantized GFP8 mantissas
    output logic signed [IN_ELEMENTS-1:0][OUT_MAN_BITS-1:0]  o_gfp8_mans
);

    // Derived parameters
    localparam int QUANT_SHIFT = IN_MAN_BITS - OUT_MAN_BITS;  // 11 - 8 = 3

    // Saturation limits for 8-bit signed
    localparam logic signed [OUT_MAN_BITS-1:0] MAX_POS = (1 << (OUT_MAN_BITS-1)) - 1;  // +127
    localparam logic signed [OUT_MAN_BITS-1:0] MAX_NEG = -(1 << (OUT_MAN_BITS-1));     // -128

    // =========================================================================
    // Internal signals for combinational logic
    // =========================================================================
    logic signed [IN_MAN_BITS:0] rounded [IN_ELEMENTS];   // Extra bit for overflow
    logic signed [IN_MAN_BITS:0] shifted [IN_ELEMENTS];

    // =========================================================================
    // Combinational Quantization Logic
    // =========================================================================
    always_comb begin
        for (int i = 0; i < IN_ELEMENTS; i++) begin
            if (i_is_zero[i]) begin
                // Zero element
                rounded[i] = '0;
                shifted[i] = '0;
                o_gfp8_mans[i] = '0;
            end else begin
                // Step 1: Add rounding (round-to-nearest)
                // Add rounding constant: round_bit << (QUANT_SHIFT - 1)
                if (QUANT_SHIFT > 0) begin
                    rounded[i] = $signed(i_aligned_mans[i]) +
                                 $signed({{(IN_MAN_BITS-QUANT_SHIFT+1){1'b0}}, i_round_bits[i], {(QUANT_SHIFT-1){1'b0}}});
                end else begin
                    rounded[i] = {i_aligned_mans[i][IN_MAN_BITS-1], i_aligned_mans[i]};
                end

                // Step 2: Arithmetic right shift to quantize
                shifted[i] = rounded[i] >>> QUANT_SHIFT;

                // Step 3: Saturate to output range
                if (shifted[i] > $signed(MAX_POS)) begin
                    o_gfp8_mans[i] = MAX_POS;
                end else if (shifted[i] < $signed(MAX_NEG)) begin
                    o_gfp8_mans[i] = MAX_NEG;
                end else begin
                    o_gfp8_mans[i] = shifted[i][OUT_MAN_BITS-1:0];
                end
            end
        end
    end

endmodule
