// -----------------------------------------------------------------------------
// Wrapper for Achronix ACX_BRAM72K_FIFO primitive.
//
// Reference: Speedster7t Component Library User Guide UG086-1, ACX_BRAM72K_FIFO
//   (doc/Component_Library/Speedster7t_Component_Library_User_Guide_UG086-1.html,
//    part340-part355: Memories -> ACX_BRAM72K_FIFO, Parameters, Ports,
//    Instantiation Template).
// Usage reference: gddr_ref_design/src/rtl/axi_bw_monitor.sv (lines 374-402).
//
// The primitive is not inferrable; this wrapper provides a parameterized
// interface and right-justified data alignment per UG086-1 (din/dout
// for write_width/read_width < 128 start at index 0, upper bits zero).
// -----------------------------------------------------------------------------

module acx_fifo #(
    parameter int DATA_WIDTH       = 288,   // 4, 8, 9, 16, 18, 32, 36, 64, 72, 128, 144
    parameter int AEMPTY_THRESHOLD = 14'h10,
    parameter int AFULL_THRESHOLD  = 14'h10,
    parameter int SYNC_MODE        = 1,    // 1 = single clock (wrclk=rdclk), 0 = async
    parameter int OUTREG_ENABLE    = 1,    // 1 = 2-cycle read latency, 0 = 1-cycle
    parameter int FWFT_MODE        = 0,    // 0 = standard, 1 = first-word fall-through
    parameter int ECC_DECODER_ENABLE = 0,
    parameter int ECC_ENCODER_ENABLE = 0
) (
    input  logic                  rstn,
    input  logic                  wrclk,
    input  logic                  rdclk,
    input  logic                  wren,
    input  logic [DATA_WIDTH-1:0] din,
    input  logic                  rden,
    output logic [DATA_WIDTH-1:0] dout,
    output logic                  full,
    output logic                  almost_full,
    output logic                  write_error,
    output logic                  empty,
    output logic                  almost_empty,
    output logic                  read_error,
    output logic [1:0]            sbit_error,
    output logic [1:0]            dbit_error
);

    localparam int PRIM_WIDTH = 144;

    logic [PRIM_WIDTH-1:0] din_prim;
    logic [PRIM_WIDTH-1:0] dout_prim;

    // Right-justified alignment per UG086-1: data from index 0, upper bits zero
    assign din_prim = {{(PRIM_WIDTH - DATA_WIDTH){1'b0}}, din};
    assign dout     = dout_prim[DATA_WIDTH-1:0];

    ACX_BRAM72K_FIFO #(
        .aempty_threshold   (14'(AEMPTY_THRESHOLD)),
        .afull_threshold    (14'(AFULL_THRESHOLD)),
        .ecc_decoder_enable (ECC_DECODER_ENABLE),
        .ecc_encoder_enable (ECC_ENCODER_ENABLE),
        .fwft_mode          (FWFT_MODE),
        .outreg_enable      (OUTREG_ENABLE),
        .rdclk_polarity     ("rise"),
        .read_width         (DATA_WIDTH),
        .sync_mode          (SYNC_MODE),
        .wrclk_polarity     ("rise"),
        .write_width        (DATA_WIDTH)
    ) u_fifo (
        .din         (din_prim),
        .wrclk       (wrclk),
        .rdclk       (rdclk),
        .wren        (wren),
        .rden        (rden),
        .rstn        (rstn),
        .dout        (dout_prim),
        .sbit_error  (sbit_error),
        .dbit_error  (dbit_error),
        .almost_full (almost_full),
        .full        (full),
        .almost_empty(almost_empty),
        .empty       (empty),
        .write_error (write_error),
        .read_error  (read_error)
    );

endmodule
