// =============================================================================
// GFP16 Field Extraction Module
// =============================================================================
// Extracts exponent and signed mantissa fields from GFP16 format.
// Pure combinational module - no clock or state.
//
// GFP16 Format (per element):
//   [15:11] = exp[4:0]   - 5-bit exponent
//   [10:0]  = man[10:0]  - 11-bit SIGNED mantissa (2's complement)
//
// Key differences from IEEE FP:
//   - No separate sign bit (sign is in mantissa MSB)
//   - No implicit 1 (mantissa is explicit)
//   - Mantissa is 2's complement, not sign-magnitude
// =============================================================================

module gfp16_extract #(
    parameter int GFP16_TOTAL_BITS = 16,      // Total bits per element
    parameter int GFP16_EXP_BITS   = 5,       // Exponent field width
    parameter int GFP16_MAN_BITS   = 11,      // Signed mantissa bits
    parameter int IN_ELEMENTS      = 16       // Elements per word
) (
    // Input: Packed GFP16 data
    input  logic [IN_ELEMENTS-1:0][GFP16_TOTAL_BITS-1:0]   i_gfp16_data,

    // Output: Extracted fields
    output logic [IN_ELEMENTS-1:0][GFP16_EXP_BITS-1:0]     o_exps,
    output logic signed [IN_ELEMENTS-1:0][GFP16_MAN_BITS-1:0] o_mans,
    output logic [IN_ELEMENTS-1:0]                          o_is_zero
);

    // =========================================================================
    // Combinational Extraction Logic
    // =========================================================================
    always_comb begin
        for (int i = 0; i < IN_ELEMENTS; i++) begin
            // Extract exponent (upper bits)
            o_exps[i] = i_gfp16_data[i][GFP16_TOTAL_BITS-1 -: GFP16_EXP_BITS];

            // Extract signed mantissa (lower bits)
            o_mans[i] = i_gfp16_data[i][GFP16_MAN_BITS-1:0];

            // Zero detection: exp=0 AND man=0
            o_is_zero[i] = (o_exps[i] == '0) && (o_mans[i] == '0);
        end
    end

endmodule
