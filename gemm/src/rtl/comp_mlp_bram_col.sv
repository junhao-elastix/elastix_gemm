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
    `define ACX_ENABLE_MLP_SIM
    `define ACX_ENABLE_BRAM_SIM
`endif


module comp_mlp_bram_col #(
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

    // Block Floating Point exponent for activation data
    // This drives the MLP's expb port via LRAM virtual port mapping
    input  wire [7:0]  expb,            // Shared exponent for BFP mode

    // BRAM Interface - shared across all MLPs in column, with separate write enables
    input  wire [71:0]         bram_din,
    input  wire [9:0]          wraddr,
    input  wire [NUM_MLPS-1:0] wren,
    input  wire [8:0]          rdaddr,

    // MLP Outputs
    output wire [71:0] dout [NUM_MLPS-1:0]
);


// LRAM virtual port mapping for expb (per comp_mlp_bram.sv comments):
// lram_wraddr[5:0] = expb[7:2]
// lram_rdaddr[5:4] = expb[1:0]
// lram_rdaddr[3:0] = ce[11:8] (not used here, set to 0)
// This mapping allows the activation exponent to reach the MLP's expb input
logic [5:0] lram_wraddr;
logic       lram_wren = 1'b0;           // LRAM write enable (not used)
logic [5:0] lram_rdaddr;
logic       lram_rden = 1'b0;           // LRAM read enable (not used)
logic       lram_rstregn = 1'b0;        // LRAM output register reset (not used)

// Drive LRAM virtual ports to encode expb
assign lram_wraddr = expb[7:2];          // Upper 6 bits of expb
assign lram_rdaddr = {expb[1:0], 4'b0000}; // Lower 2 bits of expb + padding

// Cascade Chain Interface(s)
logic [71:0] multa_h[NUM_MLPS-1:0];        // Forward cascade A, higher
logic [71:0] multb_h[NUM_MLPS-1:0];        // Forward cascade B, higher
logic [71:0] multa_l[NUM_MLPS-1:0];        // Forward cascade A, lower
logic [71:0] multb_l[NUM_MLPS-1:0];        // Forward cascade B, lower

 comp_mlp_bram #(
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

    comp_mlp_bram #(
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
        $dumpfile("comp_mlp_bram_col.vcd");
        $dumpvars(0, comp_mlp_bram_col);
   end
end

// synthesis translate_off
`ifdef SIMULATION
// Debug: Track MLP inputs and outputs for sign debugging
logic [7:0] din_bytes [7:0];  // Unpack din mantissas for debug
logic [15:0] dout_sign_check;  // Check sign bits of FP24 outputs

always_comb begin
    for (int b = 0; b < 8; b++) begin
        din_bytes[b] = din[b*8 +: 8];
    end
    // Check FP24 sign bits: dout[47:24] = bank0, dout[23:0] = bank1
    dout_sign_check[0] = dout[0][23];  // MLP0 bank1 sign
    dout_sign_check[1] = dout[0][47];  // MLP0 bank0 sign
end

// Log when load signal is asserted - shows accumulator reset timing
always @(posedge clk) begin
    if (load && ce) begin
        $display("[MLP_COL_DBG] @%0t LOAD: expb=0x%02x din_man[0:3]=0x%02x,0x%02x,0x%02x,0x%02x",
                 $time, expb, din_bytes[0], din_bytes[1], din_bytes[2], din_bytes[3]);
    end
end

// Log MLP outputs periodically when accumulate is active
integer cycle_cnt = 0;
always @(posedge clk) begin
    if (ce && accumulate && !load) begin
        cycle_cnt <= cycle_cnt + 1;
        // Log every 128 cycles and at specific points
        if (cycle_cnt % 128 == 0 || cycle_cnt == 1 || cycle_cnt == 4 || cycle_cnt == 16) begin
            // dout[0] format: bits[47:24]=FP24_bank0, bits[23:0]=FP24_bank1
            $display("[MLP_COL_OUT] @%0t cycle=%0d MLP0: bank0=0x%06x(s=%b) bank1=0x%06x(s=%b) expb=0x%02x",
                     $time, cycle_cnt,
                     dout[0][47:24], dout[0][47],  // bank0 and its sign
                     dout[0][23:0], dout[0][23],   // bank1 and its sign
                     expb);
        end
    end
end
`endif
// synthesis translate_on

endmodule