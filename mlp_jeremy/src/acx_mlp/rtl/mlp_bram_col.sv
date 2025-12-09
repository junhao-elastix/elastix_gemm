
// Combined MLP and BRAM module configured for dual 8x8 dot products
//
// CONFIGURATION OVERVIEW:
// ======================
// This module performs two simultaneous 8x8 dot products:
// - Input: 8 values from DIN (duplicated to both MLP banks)
// - Parameters: 16 values from BRAM (8 per bank, stored as 144-bit words)
// - Output: Two dot product results (one per bank)

`timescale 1ns / 1ps

`default_nettype none
// Achronix primitive simulation enables
`ifdef SPEEDSTER7T_SIMULATION
    `define ACX_ENABLE_PRIMITIVE_SIM
    `define ACX_ENABLE_MLP_SIM
    `define ACX_ENABLE_BRAM_SIM
`endif


module mlp_bram_col #(
    // How many MLPs to stack in this column
    parameter integer NUM_MLPS = 8,
    parameter logic dump_waves = 0
) (
    // Clock and Reset
    input  wire        clk,              // System clock
    input  wire        rstn,
    input  wire        ce,

    // MLP Data Input & Control
    input  wire [71:0] din,
    input  wire        load,            // Reset accumulator w/ value in DOUT
    input  wire accumulate,             // Add current DOUT to accumulator

    // BRAM Interface - shared across all MLPs in column, with separate write enables
    input  wire [71:0]         bram_din,
    input  wire [9:0]          wraddr,
    input  wire [NUM_MLPS-1:0] wren,
    input  wire [8:0]          rdaddr,

    // MLP Outputs
    output wire [71:0] dout [NUM_MLPS-1:0]
);


// Use internal accumulators instead of LRAM (for now)
logic [5:0] lram_wraddr = 6'd0;         // LRAM write address
logic       lram_wren = 1'b0;           // LRAM write enable
logic [5:0] lram_rdaddr = 6'd0;         // LRAM read address
logic       lram_rden = 1'b0;           // LRAM read enable
logic       lram_rstregn = 1'b0;        // LRAM output register reset

// Cascade Chain Interface(s)
wire [71:0] multa_h[NUM_MLPS-1:0];        // Forward cascade A, higher
wire [71:0] multb_h[NUM_MLPS-1:0];        // Forward cascade B, higher
wire [71:0] multa_l[NUM_MLPS-1:0];        // Forward cascade A, lower
wire [71:0] multb_l[NUM_MLPS-1:0];        // Forward cascade B, lower

 mlp_bram #(
    // Select DIN_A[71:0] for both A ports at column base
    .mux_sel_multa_l(2'b00),
    .mux_sel_multa_h(3'b000),
    .del_multa_h(1'b1),
    .del_multa_l(1'b1)
 ) mlp_col_base (
    .clk(clk),
    .rstn(rstn),
    .ce(ce),
    .din(din),
    .bram_din(bram_din),
    .wraddr(wraddr),
    .wren(wren[0]),
    .rdaddr(rdaddr),

    .lram_wraddr(lram_wraddr),         // LRAM write address
    .lram_wren(lram_wren),             // LRAM write enable
    .lram_rdaddr(lram_rdaddr),         // LRAM read address
    .lram_rden(lram_wren),             // LRAM read enable
    .lram_rstregn(lram_rstregn),       // LRAM output register reset

    .load(load),                  // Loads DOUT -> accumulator
    .accumulate_ce(accumulate),    // Accumulate enable for dot product accumulation

    // Cascade Chain Interface (only using A port cascade, B port from local BRAM)
    .fwdi_multa_h(/* NC */),        // Forward cascade A, higher block
    .fwdi_multb_h(/* NC */),        // Forward cascade B, higher block
    .fwdi_multa_l(/* NC */),        // Forward cascade A, lower block
    .fwdi_multb_l(/* NC */),        // Forward cascade B, lower block
    .fwdi_dout(/* NC */),           // Cascade input from MLP below

    // Forward Cascade Outputs
    .fwdo_multa_h(multa_h[0]),      // Forward cascade A, higher block
    .fwdo_multb_h(multb_h[0]),      // Forward cascade B, higher block
    .fwdo_multa_l(multa_l[0]),      // Forward cascade A, lower block
    .fwdo_multb_l(multb_l[0]),      // Forward cascade B, lower block

    // MLP Outputs
    .fwdo_dout(/* NC */),           // Cascade output to MLP above
    .dout(dout[0])                  // Primary MAC result output

);

  for (genvar i = 1; i < NUM_MLPS; i = i + 1) begin : mlp_gen

    mlp_bram #(
        // Select cascade input for A ports
        .mux_sel_multa_l(2'b11),
        .mux_sel_multa_h(3'b111),
        .del_multa_h(1'b0),
        .del_multa_l(1'b0)
    ) mlp_col_stack (
        .clk(clk),
        .rstn(rstn),
        .ce(ce),
        .din(din),
        .bram_din(bram_din),
        .wraddr(wraddr),
        .wren(wren[i]),
        .rdaddr(rdaddr),

        .lram_wraddr(lram_wraddr),         // LRAM write address
        .lram_wren(lram_wren),             // LRAM write enable
        .lram_rdaddr(lram_rdaddr),         // LRAM read address
        .lram_rden(lram_wren),             // LRAM read enable
        .lram_rstregn(lram_rstregn),       // LRAM output register reset

        .load(load),                  // Loads DOUT -> accumulator
        .accumulate_ce(accumulate),   // Accumulate enable for dot product accumulation

        // Cascade In
        .fwdi_multa_h(multa_h[i-1]),     // Forward cascade A, higher block
        .fwdi_multb_h(multb_h[i-1]),     // Forward cascade B, higher block
        .fwdi_multa_l(multa_l[i-1]),     // Forward cascade A, lower block
        .fwdi_multb_l(multb_l[i-1]),     // Forward cascade B, lower block
        .fwdi_dout(/* NC */),            // Cascade input from MLP below

        // Cascade Out
        .fwdo_multa_h(multa_h[i]),        // Forward cascade A, higher block
        .fwdo_multb_h(multb_h[i]),        // Forward cascade B, higher block
        .fwdo_multa_l(multa_l[i]),        // Forward cascade A, lower block
        .fwdo_multb_l(multb_l[i]),        // Forward cascade B, lower block

        // MLP Outputs
        .fwdo_dout(/* NC */),         // Cascade output to MLP above
        .dout(dout[i])                // Primary MAC result output
    );
  end


initial begin
    if (dump_waves) begin
        $dumpfile("mlp_bram_col.vcd");
        $dumpvars(0, mlp_bram_col);
   end
end

endmodule