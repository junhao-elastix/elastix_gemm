// =============================================================================
// Group Max Exponent Finder Module (Simplified)
// =============================================================================
// Combinational module that finds maximum exponent in current word.
// For GFP format - no has_frac logic needed since mantissas are explicit.
//
// Features:
//   - Pure combinational max finding
//   - Excludes zero and padded elements
//   - Single-cycle latency with ready/valid passthrough
// =============================================================================

module group_max_exp_finder #(
    parameter int EXP_WIDTH    = 5,        // GFP16 exponent width
    parameter int IN_ELEMENTS  = 16,       // Elements per input word
    parameter int GROUP_WORDS  = 2,        // Unused - kept for interface compatibility
    parameter int MAN_BITS     = 11,       // Signed mantissa bits (unused)

    // Derived parameters
    localparam int ELEM_EN_WIDTH = $clog2(IN_ELEMENTS + 1)
) (
    input  logic                                        clk_i,
    input  logic                                        reset_i,

    // Input interface
    output logic                                        ready_o,
    input  logic                                        v_i,
    input  logic [IN_ELEMENTS-1:0][EXP_WIDTH-1:0]       exps_i,
    input  logic signed [IN_ELEMENTS-1:0][MAN_BITS-1:0] mans_i,      // Unused
    input  logic [IN_ELEMENTS-1:0]                      is_zero_i,
    input  logic [ELEM_EN_WIDTH-1:0]                    pad_i,
    input  logic                                        last_i,

    // Output interface
    input  logic                                        ready_i,
    output logic                                        v_o,
    output logic [EXP_WIDTH-1:0]                        max_exp_o,
    output logic                                        group_last_o
);

    // =========================================================================
    // Combinational Max Exponent Logic
    // =========================================================================
    logic [EXP_WIDTH-1:0] word_max_exp;

    always_comb begin
        word_max_exp = '0;

        for (int i = 0; i < IN_ELEMENTS; i++) begin
            // Only consider non-zero elements within valid range (not padded)
            if (!is_zero_i[i] && (i < (IN_ELEMENTS - pad_i))) begin
                if (exps_i[i] > word_max_exp) begin
                    word_max_exp = exps_i[i];
                end
            end
        end
    end

    // =========================================================================
    // Simple Passthrough with Single Register Stage
    // =========================================================================
    // Ready when downstream is ready or output not valid
    assign ready_o = ready_i | ~v_o;

    always_ff @(posedge clk_i) begin
        if (reset_i) begin
            v_o          <= 1'b0;
            max_exp_o    <= '0;
            group_last_o <= 1'b0;
        end else begin
            // Clear output valid when consumed
            if (ready_i) begin
                v_o <= 1'b0;
            end

            // Register new input when valid and ready
            if (v_i && ready_o) begin
                v_o          <= 1'b1;
                max_exp_o    <= word_max_exp;
                group_last_o <= last_i;
            end
        end
    end

endmodule
