// =============================================================================
// Signed Mantissa Aligner Module
// =============================================================================
// Aligns signed mantissas to the group's maximum exponent using arithmetic
// right shift (preserves sign via sign extension).
//
// For each element:
//   shift_amount = max_exp - elem_exp
//   aligned_man = man >>> shift_amount  (arithmetic shift)
//
// Key features:
//   - Arithmetic right shift preserves 2's complement sign
//   - Captures round bit (first discarded bit) for rounding
//   - Zero elements pass through unchanged
// =============================================================================

module signed_aligner #(
    parameter int EXP_BITS    = 5,         // Exponent bit width
    parameter int MAN_BITS    = 11,        // Signed mantissa bits
    parameter int IN_ELEMENTS = 16         // Elements per word
) (
    // Input: Extracted GFP16 fields
    input  logic [IN_ELEMENTS-1:0][EXP_BITS-1:0]              i_exps,
    input  logic signed [IN_ELEMENTS-1:0][MAN_BITS-1:0]       i_mans,
    input  logic [IN_ELEMENTS-1:0]                            i_is_zero,
    input  logic [EXP_BITS-1:0]                               i_max_exp,

    // Output: Aligned mantissas
    output logic signed [IN_ELEMENTS-1:0][MAN_BITS-1:0]       o_aligned_mans,
    output logic [IN_ELEMENTS-1:0]                            o_round_bits
);

    // =========================================================================
    // Internal signals for combinational logic
    // =========================================================================
    logic [EXP_BITS-1:0] shift_amt [IN_ELEMENTS];
    logic signed [MAN_BITS-1:0] man_signed [IN_ELEMENTS];

    // =========================================================================
    // Combinational Alignment Logic
    // =========================================================================
    always_comb begin
        for (int i = 0; i < IN_ELEMENTS; i++) begin
            // Compute shift amount
            shift_amt[i] = i_max_exp - i_exps[i];

            // Explicitly interpret as signed for arithmetic shift
            man_signed[i] = $signed(i_mans[i]);

            if (i_is_zero[i]) begin
                // Zero element: pass through as zero
                o_aligned_mans[i] = '0;
                o_round_bits[i]   = 1'b0;
            end else if (shift_amt[i] == '0) begin
                // No shift needed
                o_aligned_mans[i] = man_signed[i];
                o_round_bits[i]   = 1'b0;
            end else if (shift_amt[i] >= MAN_BITS[EXP_BITS-1:0]) begin
                // Complete underflow - result is 0 or -1 based on sign
                // For 2's complement, shifting by >= width gives all sign bits
                o_aligned_mans[i] = man_signed[i][MAN_BITS-1] ? '1 : '0;
                o_round_bits[i]   = 1'b0;  // No meaningful rounding
            end else begin
                // Arithmetic right shift (sign-extending)
                o_aligned_mans[i] = man_signed[i] >>> shift_amt[i];

                // Round bit is the first discarded bit (bit at position shift_amt-1)
                o_round_bits[i] = man_signed[i][shift_amt[i]-1];
            end
        end
    end

endmodule
