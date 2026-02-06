module gfp_norm_quant #(
    // GFP11E5 input parameters (11-bit mantissa + 5-bit exponent = 16 bits total)
    parameter int GFP11E5_EXP_BITS   = 5,
    parameter int GFP11E5_MAN_BITS   = 11,

    // GFP8E5 output parameters (8-bit mantissa + 5-bit exponent = 13 bits total)
    parameter int GFP8E5_MAN_BITS    = 8,
    parameter int GFP8E5_EXP_BITS    = 5,    // Same as GFP11E5 exponent width

    // Streaming parameters
    parameter int IN_ELEMENTS      = 16,       // Elements per input word

    // FIFO depths
    parameter int INGRESS_FIFO_ELS = 8,
    parameter int DATA_FIFO_ELS    = 8,
    parameter int EGRESS_FIFO_ELS  = 8,

    // Derived parameters - do not modify
    parameter int GFP11E5_TOTAL_BITS = GFP11E5_EXP_BITS + GFP11E5_MAN_BITS,
    parameter int ELEM_EN_WIDTH   = $clog2(IN_ELEMENTS + 1)
) (
    input  logic                                              clk_i,
    input  logic                                              reset_i,

    // Input streaming interface (GFP11E5 format) - ready/valid with ack
    output logic                                              ready_o,
    input  logic                                              valid_i,
    input  logic [IN_ELEMENTS-1:0][GFP11E5_TOTAL_BITS-1:0]      data_i,
    input  logic [ELEM_EN_WIDTH-1:0]                          pad_i,
    input  logic                                              last_i,
    output logic                                              ack_o,       // Input acknowledged

    // Output streaming interface (GFP8E5 format) - ready/valid with ack
    input  logic                                              ready_i,
    output logic                                              valid_o,
    output logic [IN_ELEMENTS-1:0][GFP8E5_MAN_BITS-1:0]         mantissa_o,
    output logic [GFP8E5_EXP_BITS-1:0]                          exponent_o,
    output logic [ELEM_EN_WIDTH-1:0]                          pad_o,
    output logic                                              last_o,
    input  logic                                              ack_i        // Output acknowledged
);

    // =========================================================================
    // Ingress FIFO Data Type
    // =========================================================================
    typedef struct packed {
        logic                                              last;
        logic [ELEM_EN_WIDTH-1:0]                          pad;
        logic [IN_ELEMENTS-1:0][GFP11E5_TOTAL_BITS-1:0]      data;
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

    assign ack_o = valid_i & ready_o;

    fifo #(
        .width_p (INGRESS_WIDTH),
        .els_p   (INGRESS_FIFO_ELS)
    ) ingress_fifo (
        .clk_i   (clk_i),
        .reset_i (reset_i),
        .ready_o (ingress_ready),
        .v_i     (valid_i),
        .data_i  (ingress_data_in),
        .ready_i (extract_ready),
        .v_o     (ingress_v),
        .data_o  (ingress_data_out)
    );

    // =========================================================================
    // Data Staging FIFO
    // =========================================================================
    typedef struct packed {
        logic                                              last;
        logic [ELEM_EN_WIDTH-1:0]                          pad;
        logic [IN_ELEMENTS-1:0][GFP11E5_EXP_BITS-1:0]        exps;
        logic signed [IN_ELEMENTS-1:0][GFP11E5_MAN_BITS-1:0] mans;
        logic [IN_ELEMENTS-1:0]                            is_zero;
    } staging_data_t;

    localparam int STAGING_WIDTH = $bits(staging_data_t);

    staging_data_t staging_data_in;
    staging_data_t staging_data_out;
    logic          staging_ready;
    logic          staging_v;

    // Extract GFP11E5 fields into staging struct
    always_comb begin
        staging_data_in.last = ingress_data_out.last;
        staging_data_in.pad  = ingress_data_out.pad;
        for (int i = 0; i < IN_ELEMENTS; i++) begin
            staging_data_in.exps[i]    = ingress_data_out.data[i][GFP11E5_TOTAL_BITS-1 -: GFP11E5_EXP_BITS];
            staging_data_in.mans[i]    = ingress_data_out.data[i][GFP11E5_MAN_BITS-1:0];
            staging_data_in.is_zero[i] = (ingress_data_out.data[i] == '0);
        end
    end

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
    // Max Exponent Finder (has internal register - match with staging fifo)
    // =========================================================================
    logic                        max_exp_ready;
    logic                        max_exp_v;
    logic [GFP11E5_EXP_BITS-1:0]   max_exp_out;
    logic                        max_exp_group_last;

    gfp_find_max_exp #(
        .EXP_WIDTH   (GFP11E5_EXP_BITS),
        .IN_ELEMENTS (IN_ELEMENTS),
        .MAN_BITS    (GFP11E5_MAN_BITS)
    ) max_exp_finder (
        .clk_i       (clk_i),
        .reset_i     (reset_i),
        .ready_o     (max_exp_ready),
        .v_i         (ingress_v & extract_ready),
        .exps_i      (staging_data_in.exps),
        .mans_i      (staging_data_in.mans),
        .is_zero_i   (staging_data_in.is_zero),
        .pad_i       (staging_data_in.pad),
        .last_i      (staging_data_in.last),
        .ready_i     (process_ready & staging_v),
        .v_o         (max_exp_v),
        .max_exp_o   (max_exp_out),
        .group_last_o(max_exp_group_last)
    );

    // =========================================================================
    // Processing Stage (Combinational)
    // =========================================================================
    // Wait until both staging data and max_exp are available
    logic process_ready;
    logic process_valid;

    assign process_valid = staging_v & max_exp_v;
    assign process_ready = egress_ready;

    // Combined Alignment + Quantization (merged module)
    logic signed [IN_ELEMENTS-1:0][GFP8E5_MAN_BITS-1:0] gfp8_mans;

    gfp_align_quant #(
        .EXP_BITS     (GFP11E5_EXP_BITS),
        .IN_MAN_BITS  (GFP11E5_MAN_BITS),
        .OUT_MAN_BITS (GFP8E5_MAN_BITS),
        .IN_ELEMENTS  (IN_ELEMENTS)
    ) align_quant_inst (
        .i_exps    (staging_data_out.exps),
        .i_mans    (staging_data_out.mans),
        .i_is_zero (staging_data_out.is_zero),
        .i_max_exp (max_exp_out),
        .o_mans    (gfp8_mans)
    );

    // GFP8E5 Exponent (same width as GFP11E5, just pass through)
    logic [GFP8E5_EXP_BITS-1:0] gfp8_exp;
    assign gfp8_exp = max_exp_out;

    // =========================================================================
    // Egress FIFO
    // =========================================================================
    typedef struct packed {
        logic                                         last;
        logic [ELEM_EN_WIDTH-1:0]                     pad;
        logic [GFP8E5_EXP_BITS-1:0]                     exponent;
        logic signed [IN_ELEMENTS-1:0][GFP8E5_MAN_BITS-1:0] mantissas;
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
        .ready_i (ready_i | ack_i),  // Accept on ready or explicit ack
        .v_o     (valid_o),
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
