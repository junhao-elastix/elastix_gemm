
// Combined MLP and BRAM module configured for dual 8x8 dot products
//
// CONFIGURATION OVERVIEW:
// ======================
// This module performs two simultaneous 8x8 dot products:
// - Input: 8 values from DIN (duplicated to both MLP banks)
// - Parameters: 16 values from BRAM (8 per bank, stored as 144-bit words)
// - Output: Two dot product results (one per bank)

`timescale 1ps / 1ps
`default_nettype none
// Achronix primitive simulation enables
`ifdef SPEEDSTER7T_SIMULATION
`define ACX_ENABLE_PRIMITIVE_SIM
`endif


module mlp_bram #(
    // Only difference between base and upper MLPs is muxsel
    parameter logic [1:0] mux_sel_multa_l = 2'b00,  // Mux select for forward cascade A, lower block
    parameter logic [2:0]  mux_sel_multa_h = 3'b000, // Mux select for forward cascade A, higher block
    parameter logic del_multa_l = 1'b1,
    parameter logic del_multa_h = 1'b1
) (
    // Clock and Reset
    input wire clk,
    input wire rstn,
    input wire ce,

    // MLP Data Input
    input wire [71:0] din,

    input wire load,          // Reset accumulator w/ value in DOUT
    input wire accumulate_ce, // Add current DOUT to accumulator

    // BRAM Interface
    input wire [71:0] bram_din,  // BRAM data input
    input wire [ 9:0] wraddr,    // BRAM write address
    input wire        wren,      // BRAM write enable
    input wire [ 8:0] rdaddr,    // BRAM read address

    // LRAM Interface
    input wire [5:0] lram_wraddr,  // LRAM write address
    input wire       lram_wren,    // LRAM write enable
    input wire [5:0] lram_rdaddr,  // LRAM read address
    input wire       lram_rden,    // LRAM read enable
    input wire       lram_rstregn, // LRAM output register reset

    // Cascade Chain Interface
    input wire [71:0] fwdi_multa_h,  // Forward cascade path inputs for multiplier A inputs, higher multiplier block.
    input wire [71:0] fwdi_multb_h,  // Forward cascade path inputs for multiplier B inputs, higher multiplier block.
    input wire [71:0] fwdi_multa_l,  // Forward cascade path inputs for multiplier A inputs, lower multiplier block.
    input wire [71:0] fwdi_multb_l,  // Forward cascade path inputs for multiplier B inputs, lower multiplier block.
    input wire [47:0] fwdi_dout,     // Cascade input from MLP below

    // Forward Cascade Outputs
    output wire [71:0] fwdo_multa_h,  // Forward cascade A, higher block
    output wire [71:0] fwdo_multb_h,  // Forward cascade B, higher block
    output wire [71:0] fwdo_multa_l,  // Forward cascade A, lower block
    output wire [71:0] fwdo_multb_l,  // Forward cascade B, lower block

    // MLP Outputs
    output wire [47:0] fwdo_dout,  // Cascade output to MLP above
    output wire [71:0] dout        // Primary MAC result output
);

  // Internal signals for BRAM-MLP connections
  wire [143:0] bram_dout;  // BRAM DOUT to MLP connection

  // NOTE: LRAM has 'virtual' ports (in MODE 1 - RAM [lram_fifo_enable = 0]):
  // lram_wraddr[5:0] = expb[7:2]
  // lram_wren = ce[7]
  // lram_rdaddr[5:0] = {expb[1:0], ce[11:8]}
  // lram_rstregn = rstn[0]
  // Wire up accordingly:
  wire [ 11:0] mlp_ce = {lram_rdaddr[3:0], lram_wren, lram_rden, 3'b000, ce, ce, accumulate_ce};
  wire [  3:0] mlp_rstn = {2'b00, rstn, lram_rstregn};
  wire [  7:0] expb = {lram_wraddr[5:0], lram_rdaddr[5:4]};

  // In 144-bit mode, address bits [13:5] select the (read) word
  // In 72-bit mode address bits [13:4] select the (write) word
  weight_bram #() u_weight_bram (
      .wrclk(clk),
      .din(bram_din),
      .wraddr(wraddr),
      .wren(wren),
      .rdclk(clk),
      .rdaddr(rdaddr),
      .rden(1'b1),  // TODO (ce advanced by bram latency)?
      .dout(bram_dout)
  );

  mlp_dot16_bfp8 #(
      .mux_sel_multa_h(mux_sel_multa_h),
      .mux_sel_multa_l(mux_sel_multa_l),
      .del_multa_l(del_multa_l),
      .del_multa_h(del_multa_h)
  ) u_mlp_dot16_bfp8 (
      .clk(clk),
      .ce(mlp_ce),
      .rstn(mlp_rstn),
      .mlp_din(din),
      .bram_to_mlp(bram_dout),

      // Cascade paths (internal to column)
      .fwdi_multa_h(fwdi_multa_h),
      .fwdi_multa_l(fwdi_multa_l),
      .fwdi_multb_h(fwdi_multb_h),
      .fwdi_multb_l(fwdi_multb_l),
      .fwdi_dout(fwdi_dout),
      .fwdo_multa_h(fwdo_multa_h),
      .fwdo_multa_l(fwdo_multa_l),
      .fwdo_multb_h(fwdo_multb_h),
      .fwdo_multb_l(fwdo_multb_l),
      .fwdo_dout(fwdo_dout),

      .expb(expb),
      .load(load),
      .load_ab(load),
      // Output stage
      .mlp_dout(dout),
      .mlpram_mlp_dout(  /* NC */)
  );
endmodule : mlp_bram
