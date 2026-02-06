module gfp_align_quant #(
    parameter int EXP_BITS     = 5,         // Exponent bit width
    parameter int IN_MAN_BITS  = 11,        // Input mantissa bits (signed)
    parameter int OUT_MAN_BITS = 8,         // Output mantissa bits (signed)
    parameter int IN_ELEMENTS  = 16         // Elements per word
) (
    // Input: Extracted GFP fields
    input  logic [IN_ELEMENTS-1:0][EXP_BITS-1:0]               i_exps,
    input  logic signed [IN_ELEMENTS-1:0][IN_MAN_BITS-1:0]     i_mans,
    input  logic [IN_ELEMENTS-1:0]                              i_is_zero,
    input  logic [EXP_BITS-1:0]                                 i_max_exp,

    // Output: Aligned and quantized mantissas
    output logic signed [IN_ELEMENTS-1:0][OUT_MAN_BITS-1:0]    o_mans
);

    localparam int QUANT_SHIFT = IN_MAN_BITS - OUT_MAN_BITS;  // 11 - 8 = 3

    logic [EXP_BITS-1:0]                 shift_amt    [IN_ELEMENTS];
    logic signed [IN_MAN_BITS-1:0]       aligned      [IN_ELEMENTS];
    logic                                quant_round_bit [IN_ELEMENTS];
    logic                                at_max_pos   [IN_ELEMENTS];

    always_comb begin
        for (int i = 0; i < IN_ELEMENTS; i++) begin
            shift_amt[i] = i_max_exp - i_exps[i];

            // Step 1: Alignment to max exponent
            if (i_is_zero[i]) begin
                // Zero element: bypass
                aligned[i] = '0;
            end else if (shift_amt[i] == '0) begin
                // No shift needed
                aligned[i] = i_mans[i];
            end else if (shift_amt[i] >= IN_MAN_BITS[EXP_BITS-1:0]) begin
                // Underflow: sign-extend
                aligned[i] = i_mans[i][IN_MAN_BITS-1] ? '1 : '0;
            end else begin
                // Arithmetic right shift - $signed required for packed array indexing
                aligned[i] = $signed(i_mans[i]) >>> shift_amt[i];
            end

            // Step 2: Quantization round bit (MSB of bits being discarded)
            // This is bit [QUANT_SHIFT-1] of the aligned value
            quant_round_bit[i] = i_is_zero[i] ? 1'b0 : aligned[i][QUANT_SHIFT-1];

            // Overflow prevention: check if result would be max positive (127)
            // Condition: positive AND upper bits (that become output) are all 1s
            at_max_pos[i] = ~aligned[i][IN_MAN_BITS-1] &
                            (&aligned[i][IN_MAN_BITS-2:QUANT_SHIFT]);

            // Step 3: Quantization with rounding
            if (i_is_zero[i]) begin
                // Zero element
                o_mans[i] = '0;
            end else if (at_max_pos[i]) begin
                // At max positive: skip rounding to prevent overflow
                o_mans[i] = aligned[i][IN_MAN_BITS-1:QUANT_SHIFT];
            end else begin
                // Normal case: add quantization rounding and shift
                // Round bit adds 0.5 LSB (bit position QUANT_SHIFT-1 = 2)
                o_mans[i] = $signed(aligned[i] + $signed({{(IN_MAN_BITS-QUANT_SHIFT){1'b0}}, quant_round_bit[i], {(QUANT_SHIFT-1){1'b0}}}))
                            >>> QUANT_SHIFT;
            end
        end
    end

endmodule
