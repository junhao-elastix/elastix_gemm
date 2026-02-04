// =============================================================================
// GFP Normalize and Quantize Module
// =============================================================================
// Top-level module for GFP16 → GFP8 conversion.
// Normalizes mantissas to shared exponent, then quantizes to 8-bit.
//
// Architecture:
//   Input -> Ingress FIFO -> gfp16_extract -> Data Staging FIFO
//                                          -> group_max_exp_finder -> Exp FIFO
//   Data Staging + Exp FIFO -> signed_aligner -> gfp8_quantizer -> Egress FIFO -> Output
//
// Features:
//   - Backpressure support via ready/valid
//   - Configurable FIFO depths
//   - Signed mantissa alignment (arithmetic shift)
//   - Round-to-nearest quantization with saturation
// =============================================================================

module gfp_norm_quant #(
    // GFP16 input parameters
    parameter int GFP16_TOTAL_BITS = 16,
    parameter int GFP16_EXP_BITS   = 5,
    parameter int GFP16_MAN_BITS   = 11,

    // GFP8 output parameters
    parameter int GFP8_MAN_BITS    = 8,
    parameter int GFP8_EXP_BITS    = 5,    // Same as GFP16 exponent width

    // Streaming parameters
    parameter int IN_ELEMENTS      = 16,       // Elements per input word

    // FIFO depths
    parameter int INGRESS_FIFO_ELS = 8,
    parameter int DATA_FIFO_ELS    = 4,
    parameter int EGRESS_FIFO_ELS  = 2,

    // Derived parameters - do not modify
    localparam int ELEM_EN_WIDTH   = $clog2(IN_ELEMENTS + 1)
) (
    input  logic                                              clk_i,
    input  logic                                              reset_i,

    // Input streaming interface (GFP16 format)
    output logic                                              ready_o,
    input  logic                                              v_i,
    input  logic [IN_ELEMENTS-1:0][GFP16_TOTAL_BITS-1:0]      data_i,
    input  logic [ELEM_EN_WIDTH-1:0]                          pad_i,
    input  logic                                              last_i,

    // Output streaming interface (GFP8 format)
    input  logic                                              ready_i,
    output logic                                              v_o,
    output logic [IN_ELEMENTS-1:0][GFP8_MAN_BITS-1:0]         mantissa_o,
    output logic [GFP8_EXP_BITS-1:0]                          exponent_o,
    output logic [ELEM_EN_WIDTH-1:0]                          pad_o,
    output logic                                              last_o
);

    // =========================================================================
    // Ingress FIFO Data Type
    // =========================================================================
    typedef struct packed {
        logic                                              last;
        logic [ELEM_EN_WIDTH-1:0]                          pad;
        logic [IN_ELEMENTS-1:0][GFP16_TOTAL_BITS-1:0]      data;
    } ingress_data_t;

    localparam int INGRESS_WIDTH = $bits(ingress_data_t);

    // =========================================================================
    // Ingress FIFO
    // =========================================================================
    logic                  ingress_ready;
    logic                  ingress_v;
    ingress_data_t         ingress_data_in;
    ingress_data_t         ingress_data_out;

    assign ingress_data_in.last = last_i;
    assign ingress_data_in.pad  = pad_i;
    assign ingress_data_in.data = data_i;
    assign ready_o = ingress_ready;

    fifo #(
        .width_p (INGRESS_WIDTH),
        .els_p   (INGRESS_FIFO_ELS)
    ) ingress_fifo (
        .clk_i   (clk_i),
        .reset_i (reset_i),
        .ready_o (ingress_ready),
        .v_i     (v_i),
        .data_i  (ingress_data_in),
        .ready_i (extract_ready),
        .v_o     (ingress_v),
        .data_o  (ingress_data_out)
    );

    // =========================================================================
    // GFP16 Field Extraction (Combinational)
    // =========================================================================
    logic [IN_ELEMENTS-1:0][GFP16_EXP_BITS-1:0]              extract_exps;
    logic signed [IN_ELEMENTS-1:0][GFP16_MAN_BITS-1:0]       extract_mans;
    logic [IN_ELEMENTS-1:0]                                   extract_is_zero;

    gfp16_extract #(
        .GFP16_TOTAL_BITS (GFP16_TOTAL_BITS),
        .GFP16_EXP_BITS   (GFP16_EXP_BITS),
        .GFP16_MAN_BITS   (GFP16_MAN_BITS),
        .IN_ELEMENTS      (IN_ELEMENTS)
    ) extract_inst (
        .i_gfp16_data (ingress_data_out.data),
        .o_exps       (extract_exps),
        .o_mans       (extract_mans),
        .o_is_zero    (extract_is_zero)
    );

    // =========================================================================
    // Data Staging FIFO
    // =========================================================================
    typedef struct packed {
        logic                                              last;
        logic [ELEM_EN_WIDTH-1:0]                          pad;
        logic [IN_ELEMENTS-1:0][GFP16_EXP_BITS-1:0]        exps;
        logic signed [IN_ELEMENTS-1:0][GFP16_MAN_BITS-1:0] mans;
        logic [IN_ELEMENTS-1:0]                            is_zero;
    } staging_data_t;

    localparam int STAGING_WIDTH = $bits(staging_data_t);

    staging_data_t staging_data_in;
    staging_data_t staging_data_out;
    logic          staging_ready;
    logic          staging_v;

    assign staging_data_in.last    = ingress_data_out.last;
    assign staging_data_in.pad     = ingress_data_out.pad;
    assign staging_data_in.exps    = extract_exps;
    assign staging_data_in.mans    = extract_mans;
    assign staging_data_in.is_zero = extract_is_zero;

    // Ready to consume from ingress when both staging and max_exp_finder are ready
    logic extract_ready;
    assign extract_ready = staging_ready & max_exp_ready;

    fifo #(
        .width_p (STAGING_WIDTH),
        .els_p   (DATA_FIFO_ELS)
    ) staging_fifo (
        .clk_i   (clk_i),
        .reset_i (reset_i),
        .ready_o (staging_ready),
        .v_i     (ingress_v & extract_ready),
        .data_i  (staging_data_in),
        .ready_i (process_ready),
        .v_o     (staging_v),
        .data_o  (staging_data_out)
    );

    // =========================================================================
    // Max Exponent Finder (Combinational + Single Register)
    // =========================================================================
    logic                        max_exp_ready;
    logic                        max_exp_v;
    logic [GFP16_EXP_BITS-1:0]   max_exp_out;
    logic                        max_exp_group_last;

    group_max_exp_finder #(
        .EXP_WIDTH   (GFP16_EXP_BITS),
        .IN_ELEMENTS (IN_ELEMENTS),
        .MAN_BITS    (GFP16_MAN_BITS)
    ) max_exp_finder (
        .clk_i       (clk_i),
        .reset_i     (reset_i),
        .ready_o     (max_exp_ready),
        .v_i         (ingress_v & extract_ready),
        .exps_i      (extract_exps),
        .mans_i      (extract_mans),
        .is_zero_i   (extract_is_zero),
        .pad_i       (ingress_data_out.pad),
        .last_i      (ingress_data_out.last),
        .ready_i     (exp_fifo_ready),
        .v_o         (max_exp_v),
        .max_exp_o   (max_exp_out),
        .group_last_o(max_exp_group_last)
    );

    // =========================================================================
    // Exponent FIFO (one_fifo for minimal latency)
    // =========================================================================
    logic [GFP16_EXP_BITS-1:0] exp_data_out;
    logic                      exp_fifo_ready;
    logic                      exp_fifo_v;

    one_fifo #(
        .width_p (GFP16_EXP_BITS)
    ) exp_fifo (
        .clk_i   (clk_i),
        .reset_i (reset_i),
        .ready_o (exp_fifo_ready),
        .v_i     (max_exp_v),
        .data_i  (max_exp_out),
        .ready_i (process_ready & staging_v),
        .v_o     (exp_fifo_v),
        .data_o  (exp_data_out)
    );

    // =========================================================================
    // Processing Stage (Combinational)
    // =========================================================================
    // Wait until both staging data and exp are available
    logic process_ready;
    logic process_valid;

    assign process_valid = staging_v & exp_fifo_v;
    assign process_ready = egress_ready;

    // Signed Mantissa Alignment
    logic signed [IN_ELEMENTS-1:0][GFP16_MAN_BITS-1:0] aligned_mans;
    logic [IN_ELEMENTS-1:0]                            round_bits;

    signed_aligner #(
        .EXP_BITS    (GFP16_EXP_BITS),
        .MAN_BITS    (GFP16_MAN_BITS),
        .IN_ELEMENTS (IN_ELEMENTS)
    ) aligner_inst (
        .i_exps         (staging_data_out.exps),
        .i_mans         (staging_data_out.mans),
        .i_is_zero      (staging_data_out.is_zero),
        .i_max_exp      (exp_data_out),
        .o_aligned_mans (aligned_mans),
        .o_round_bits   (round_bits)
    );

    // GFP8 Quantization
    logic signed [IN_ELEMENTS-1:0][GFP8_MAN_BITS-1:0] gfp8_mans;

    gfp8_quantizer #(
        .IN_MAN_BITS  (GFP16_MAN_BITS),
        .OUT_MAN_BITS (GFP8_MAN_BITS),
        .IN_ELEMENTS  (IN_ELEMENTS)
    ) quantizer_inst (
        .i_aligned_mans (aligned_mans),
        .i_round_bits   (round_bits),
        .i_is_zero      (staging_data_out.is_zero),
        .o_gfp8_mans    (gfp8_mans)
    );

    // GFP8 Exponent (same width as GFP16, just pass through)
    logic [GFP8_EXP_BITS-1:0] gfp8_exp;
    assign gfp8_exp = exp_data_out;

    // =========================================================================
    // Egress FIFO
    // =========================================================================
    typedef struct packed {
        logic                                         last;
        logic [ELEM_EN_WIDTH-1:0]                     pad;
        logic [GFP8_EXP_BITS-1:0]                     exponent;
        logic signed [IN_ELEMENTS-1:0][GFP8_MAN_BITS-1:0] mantissas;
    } egress_data_t;

    localparam int EGRESS_WIDTH = $bits(egress_data_t);

    egress_data_t egress_data_in;
    egress_data_t egress_data_out;
    logic         egress_ready;

    assign egress_data_in.last      = staging_data_out.last;
    assign egress_data_in.pad       = staging_data_out.pad;
    assign egress_data_in.exponent  = gfp8_exp;
    assign egress_data_in.mantissas = gfp8_mans;

    two_fifo #(
        .width_p (EGRESS_WIDTH)
    ) egress_fifo (
        .clk_i   (clk_i),
        .reset_i (reset_i),
        .ready_o (egress_ready),
        .v_i     (process_valid & process_ready),
        .data_i  (egress_data_in),
        .ready_i (ready_i),
        .v_o     (v_o),
        .data_o  (egress_data_out)
    );

    // =========================================================================
    // Output Assignment
    // =========================================================================
    assign mantissa_o = egress_data_out.mantissas;
    assign exponent_o = egress_data_out.exponent;
    assign pad_o      = egress_data_out.pad;
    assign last_o     = egress_data_out.last;

endmodule
