
// MLP configured for dual 8x8 int8 dot products, to simplify instantiation
//
// CONFIGURATION OVERVIEW:
// ======================
// This module performs two simultaneous 8x8 dot products:
// - Input: One BFP8 block (1 exponent + 8 mantissas), duplicated to both MLP banks
// - Parameters: Two BFP8 blocks from BRAM
// - Output: Two fp24 (or fp16) dot product results (one per bank)
//
// DATA FLOW:
// ==========
// Bank 0 (Lower): DIN[8 values] × BRAM_DOUT[71:0][8 parameters] → DOT_PRODUCT_0
// Bank 1 (Upper): DIN[8 values] × BRAM_DOUT[143:72][8 parameters] → DOT_PRODUCT_1

`timescale 1ps / 1ps

// Achronix primitive simulation enables
`ifdef SPEEDSTER7T_SIMULATION
    `define ACX_ENABLE_PRIMITIVE_SIM
`endif


module comp_mlp_dot16_bfp8 #(
    // MLP Parameters
    parameter string       mlp_location                  = "",
    parameter string       mlp_clk_polarity              = "rise", // "rise", "fall"

    // MLP Input busses data selection - Configured for dual 8x8 dot products
    parameter logic [1:0]  mux_sel_multa_l               = 2'b00,  // Lower bank A: MLP_DIN[71:0] (8 input values duplicated)
                                                                   // 2'b00 - MLP_DIN[71:0]
                                                                   // 2'b01 - LRAM_DOUT[71:0] - internal connection
                                                                   // 2'b10 - BRAM_DOUT[71:0] - virtual port name
                                                                   // 2'b11 - FWDI_MULTA_L
    parameter logic [2:0]  mux_sel_multa_h               = 3'b000, // Upper bank A: MLP_DIN[71:0] (8 input values duplicated)
                                                                   // 3'b000 - MLP_DIN[71:0]
                                                                   // 3'b001 - BRAM_DIN[71:0]
                                                                   // 3'b010 - LRAM_DOUT[71:0] - internal connection
                                                                   // 3'b011 - LRAM_DOUT[143:72] - internal connection
                                                                   // 3'b100 - BRAM_DOUT[71:0] - virtual port name
                                                                   // 3'b101 - BRAM_DOUT[143:72] - virtual port name
                                                                   // 3'b110 - FWDI_MULTA_L[71:0]
                                                                   // 3'b111 - FWDI_MULTA_H[71:0]
    parameter logic [1:0]  mux_sel_multb_l               = 2'b10,  // Lower bank B: BRAM_DOUT[71:0] (8 parameters)
                                                                   // 2'b00 - MLP_DIN[71:0]
                                                                   // 2'b01 - LRAM_DOUT[71:0] - internal connection
                                                                   // 2'b10 - BRAM_DOUT[71:0] - virtual port name
                                                                   // 2'b11 - FWDI_MULTB_L
    parameter logic [2:0]  mux_sel_multb_h               = 3'b101, // Upper bank B: BRAM_DOUT[143:72] (8 parameters)
                                                                   // 3'b000 - MLP_DIN[71:0]
                                                                   // 3'b001 - BRAM_DIN[71:0]
                                                                   // 3'b010 - LRAM_DOUT[71:0] - internal connection
                                                                   // 3'b011 - LRAM_DOUT[143:72] - internal connection
                                                                   // 3'b100 - BRAM_DOUT[71:0] - internal connection
                                                                   // 3'b101 - BRAM_DOUT[143:72] - internal connection
                                                                   // 3'b110 - FWDI_MULTB_L[71:0]
                                                                   // 3'b111 - FWDI_MULTB_H[71:0]
    parameter logic        del_multa_l                   = 1'b1,   // Enable stage0 register for input timing
                                                                   // Selects if each delay stage register is enabled or bypassed:
                                                                   // 1'b0 – delay stage register is bypassed
                                                                   // 1'b1 – delay stage register is enabled ★ ENABLED for timing
                                                                   // do not forget to configure also "cesel_... and rstsel_...
    parameter logic        del_multa_h                   = 1'b1,   // Enable stage0 register for input timing
    parameter logic        del_multb_l                   = 1'b1,   // Enable stage0 register for BRAM timing
    parameter logic        del_multb_h                   = 1'b1,   // Enable stage0 register for BRAM timing
    parameter logic        del_expb_din_reg              = 1'b0,   // enable for expb register
    parameter logic [3:0]  cesel_multa_l                 = 4'h2,   // Set to always enabled (1'bD) for continuous operation
                                                                   // 4'h0 – 1'b0
                                                                   // 4'h1 – ce[0]
                                                                   // 4'h2 – ce[1]
                                                                   // 4'h3 – ce[2]
                                                                   // 4'h4 – ce[3]
                                                                   // 4'h5 – ce[4]
                                                                   // 4'h6 – ce[5]
                                                                   // 4'h7 – ce[6]  - used for lram_rden
                                                                   // 4'h8 – ce[7]  - used for lram_wren
                                                                   // 4'h9 – ce[8]  - used for lram_rdaddr[0]
                                                                   // 4'hA – ce[9]  - used for lram_rdaddr[1]
                                                                   // 4'hB – ce[10] - used for lram_rdaddr[2]
                                                                   // 4'hC – ce[11] - used for lram_rdaddr[3]
                                                                   // 4'hD – 1'b1 ★ SELECTED (always enabled)
    // TODO: remap and use these CE's to lower power consumption?
    parameter logic [3:0]  cesel_multa_h                 = 4'h2,   // Always enabled for continuous operation
    parameter logic [3:0]  cesel_multb_l                 = 4'h2,   // Always enabled for continuous operation
    parameter logic [3:0]  cesel_multb_h                 = 4'h2,   // Always enabled for continuous operation
    parameter logic [3:0]  cesel_expb_din_reg            = 4'h0,   // Selects the ce inputs
    parameter logic [2:0]  rstsel_multa_l                = 3'h2,   // Use rstn[1] for proper reset control
                                                                   // 3'h0 - 1'b0
                                                                   // 3'h1 - rstn[0] - used for lram_rstregn
                                                                   // 3'h2 - rstn[1] ★ SELECTED
                                                                   // 3'h3 - rstn[2]
                                                                   // 3'h4 - rstn[3]
                                                                   // 3'h5 - 1'b1
    parameter logic [2:0]  rstsel_multa_h                = 3'h2,   // Use rstn[1] for proper reset control
    parameter logic [2:0]  rstsel_multb_l                = 3'h2,   // Use rstn[1] for proper reset control
    parameter logic [2:0]  rstsel_multb_h                = 3'h2,   // Use rstn[1] for proper reset control
    parameter logic [2:0]  rstsel_expb_din_reg           = 3'h0,   // Selects the rstn input for each delay stage register

    parameter logic        lram_out2multb_l              = 1'b0,   // Routes LRAM_DOUT[71:0] direct to the multb_l bus, bypassing mux_sel_multb_l:
                                                                   // 1'b0 – 'b' input to the multipliers is the bus selected by mux_sel_multb_l.
                                                                   // 1'b1 – 'b' input to the low bank of multipliers is LRAM_DOUT[71:0]
                                                                   // LRAM_DOUT[143:0] is an internal connection only from the coupled LRAM.
                                                                   // This is not available as an input port on the MLP.
    parameter logic        lram_out2multb_h              = 1'b0,   // Routes LRAM_DOUT[143:72] direct to the multb_h bus, bypassing mux_sel_multbh:
                                                                   // 1'b0 – 'b' input to the multipliers is the bus selected by mux_sel_multbh.
                                                                   // 1'b1 – 'b' input to the high bank of multipliers is LRAM_DOUT[143:2]
                                                                   // LRAM_DOUT[143:0] is an internal connection only from the coupled LRA.
                                                                   // This is not available as an input port on tte MLP.

    // multiplier data selecton
// Table 107: Sixteen Multipliers (×4 Mode – bytesel_00_07 = 'h01; bytesel_08_15 = 'h21)
    parameter logic [4:0]  bytesel_00_07                 = 5'h05,  // Lower bank: BFP Int8 ×2/×4 mode (8 multiplications)
                                                                   // 5'h00 - Int8 ×1 and ×2 split mode
                                                                   // 5'h01 - Int8 ×2 and ×4 mode
                                                                   // 5'h02 -
                                                                   // 5'h03 - block floating point (BFP) Int8. 3 or 6 multiplications
                                                                   // 5'h04 - BFP Int8 separate expb. 4 or 8 multiplications
                                                                   // 5'h05 - BFP Int8 ×2/×4 mode. 8 or 16 multiplications ★ SELECTED
                                                                   // 5'h06 -
                                                                   // 5'h07 - Int7 ×1 and ×2 mode
                                                                   // 5'h08 - Int7 ×2 and ×4 mode
                                                                   // 5'h09 - BFP Int7 x1/×2 mode 4 or 8 multiplications
                                                                   // 5'h0A - Int6 ×1 and ×2 split mode
                                                                   // 5'h0B - Int6 ×2 and ×4 mode
                                                                   // 5'h0C -
                                                                   // 5'h0D - BFP Int6
                                                                   // 5'h0E - BFP Int6 separate expb
                                                                   // 5'h0F - BFP Int6 ×2 mode
                                                                   // 5'h10 - BFP Int6 ×4 mode
                                                                   // 5'h11 - Int16 ×1 mode
                                                                   // 5'h12 - Int16 ×2 mode
                                                                   // 5'h13 - BFLOAT16. 1 or 2 multiplications
                                                                   // 5'h14 - BFLOAT16. 2 multiplications
                                                                   // 5'h15 - BFLOAT16. 2 multiplications
                                                                   // 5'h16 - FP16. 1 or 2 multiplications
                                                                   // 5'h17 - FP16. 2 multiplications
                                                                   // 5'h18 - FP16. 2 multiplications
                                                                   // 5'h19 - FP24. 1 or 2 multiplications
                                                                   // 5'h1A - FP24. 2 multiplications
                                                                   // 5'h1B - BFP Int7 ×2 mode. 9 multiplications
                                                                   // 5'h1C - BFP Int7 ×4 mode. 16 multiplications
                                                                   // 5'h1D -
                                                                   // 5'h1E -
                                                                   // 5'h1F - Int32 mode
    parameter logic [5:0]  bytesel_08_15                 = 6'h25,  // Upper bank: BFP Int8 ×2 mode (8 multiplications)
                                                                   // 6'h00 - Int8 ×1 mode
                                                                   // 6'h01 - Int8 ×2 mode
                                                                   // 6'h02 -
                                                                   // 5'h03 - BFP Int8 3 multiplications
                                                                   // 6'h04 - BFP Int8 separate expb. 4 multiplications
                                                                   // 6'h05 - BFP Int8 ×2 mode. 8 multiplications
                                                                   // 6'h06 -
                                                                   // 5'h07 - Int7 ×1 mode
                                                                   // 6'h08 - Int7 ×2 mode
                                                                   // 6'h09 - BFP Int7 ×1 mode. 4 multiplications
                                                                   // 6'h0A - Int6 ×1 mode
                                                                   // 6'h0B - Int6 ×2 mode
                                                                   // 6'h0C -
                                                                   // 5'h0D - BFP Int6
                                                                   // 6'h0E - BFP Int6 separate expb
                                                                   // 6'h0F - BFP Int6 ×2 mode
                                                                   // 6'h10 - BFP Int6 ×4 mode
                                                                   // 6'h11 - Int16 ×1 mode
                                                                   // 6'h12 - Int16 ×2 mode
                                                                   // 6'h13 - BFLOAT16. ×1 mode. 1 multiplication
                                                                   // 6'h14 - BFLOAT16. ×2 mode. 2 multiplications
                                                                   // 6'h15 - BFLOAT16. ×2 alternate mode. 2 multiplications
                                                                   // 6'h16 - FP16. ×1 mode. 1 multiplications
                                                                   // 6'h17 - FP16. ×2 mode. 2 multiplications
                                                                   // 6'h18 - FP16. ×2 alternate mode. 2 multiplications
                                                                   // 6'h19 - FP24. ×1 mode. 1 multiplication
                                                                   // 6'h1A - FP24. ×2 mode. 2 multiplications
                                                                   // 6'h1B - BFP Int7 ×2 mode. 9 multiplications
                                                                   // 6'h1C - BFP Int7 ×4 mode. 16 multiplications
                                                                   // 6'h1D -
                                                                   // 6'h1E -
                                                                   // 6'h1F - Int32 mode
                                                                   // 6'h20 - Int8 ×2 split mode
                                                                   // 6'h21 - Int8 ×4 mode.
                                                                   // 6'h22 -
                                                                   // 5'h23 - BFP Int8 6 multiplications
                                                                   // 6'h24 - BFP Int8 separate expb. 8 multiplications.
                                                                   // 6'h25 - BFP Int8 ×4 mode. 16 multiplications
                                                                   // 6'h26 -
                                                                   // 5'h27 - Int7 ×2 split mode
                                                                   // 6'h28 - Int7 ×4
                                                                   // 6'h29 - BFP Int7 ×2 mode. 8 multiplications
                                                                   // 6'h2A - Int6 ×2 split mode
                                                                   // 6'h2B - Int6 ×4 mode
                                                                   // 6'h2C -
                                                                   // 5'h2D -
                                                                   // 6'h2E -
                                                                   // 6'h2F -
                                                                   // 6'h30 -
                                                                   // 6'h31 - Int16 ×2 split mode
                                                                   // 6'h32 - Int16 ×2 compact mode
                                                                   // 6'h33 - BFLOAT16. ×2 split mode. 2 multiplications
                                                                   // 6'h34 -
                                                                   // 6'h35 - BFLOAT16. ×2 compact mode. 2 multiplications
                                                                   // 6'h36 - FP16. ×2 split mode. 2 multiplications
                                                                   // 6'h37 -
                                                                   // 6'h38 - FP16. ×2 compact mode. 2 multiplications
                                                                   // 6'h39 - FP24. ×2 split mode. 2 multiplications
                                                                   // 6'h3A - FP24. ×2 split mode. 2 multiplications
                                                                   // 6'h3B -
                                                                   // 6'h3C -
                                                                   // 6'h3D -
                                                                   // 6'h3E -
                                                                   // 6'h3F -
    parameter logic        del_mult00a                   = 1'b0,   // enable for stage1 register
    parameter logic        del_mult00b                   = 1'b0,   //
    parameter logic        del_mult01a                   = 1'b0,   //
    parameter logic        del_mult01b                   = 1'b0,   //
    parameter logic        del_mult02a                   = 1'b0,   //
    parameter logic        del_mult02b                   = 1'b0,   //
    parameter logic        del_mult03a                   = 1'b0,   //
    parameter logic        del_mult03b                   = 1'b0,   //
    parameter logic        del_mult04_07a                = 1'b0,   //
    parameter logic        del_mult04_07b                = 1'b0,   //
    parameter logic        del_mult08_11a                = 1'b0,   //
    parameter logic        del_mult08_11b                = 1'b0,   //
    parameter logic        del_mult12_15a                = 1'b0,   //
    parameter logic        del_mult12_15b                = 1'b0,   //
    parameter logic [3:0]  cesel_mult00a                 = 4'h0,   // Selects the ce inputs for each delay stage register
    parameter logic [3:0]  cesel_mult00b                 = 4'h0,   //
    parameter logic [3:0]  cesel_mult01a                 = 4'h0,   //
    parameter logic [3:0]  cesel_mult01b                 = 4'h0,   //
    parameter logic [3:0]  cesel_mult02a                 = 4'h0,   //
    parameter logic [3:0]  cesel_mult02b                 = 4'h0,   //
    parameter logic [3:0]  cesel_mult03a                 = 4'h0,   //
    parameter logic [3:0]  cesel_mult03b                 = 4'h0,   //
    parameter logic [3:0]  cesel_mult04_07a              = 4'h0,   //
    parameter logic [3:0]  cesel_mult04_07b              = 4'h0,   //
    parameter logic [3:0]  cesel_mult08_11a              = 4'h0,   //
    parameter logic [3:0]  cesel_mult08_11b              = 4'h0,   //
    parameter logic [3:0]  cesel_mult12_15a              = 4'h0,   //
    parameter logic [3:0]  cesel_mult12_15b              = 4'h0,   //
    parameter logic [2:0]  rstsel_mult00a                = 3'h0,   // Selects the rstn input for each delay stage register
    parameter logic [2:0]  rstsel_mult00b                = 3'h0,   //
    parameter logic [2:0]  rstsel_mult01a                = 3'h0,   //
    parameter logic [2:0]  rstsel_mult01b                = 3'h0,   //
    parameter logic [2:0]  rstsel_mult02a                = 3'h0,   //
    parameter logic [2:0]  rstsel_mult02b                = 3'h0,   //
    parameter logic [2:0]  rstsel_mult03a                = 3'h0,   //
    parameter logic [2:0]  rstsel_mult03b                = 3'h0,   //
    parameter logic [2:0]  rstsel_mult04_07a             = 3'h0,   //
    parameter logic [2:0]  rstsel_mult04_07b             = 3'h0,   //
    parameter logic [2:0]  rstsel_mult08_11a             = 3'h0,   //
    parameter logic [2:0]  rstsel_mult08_11b             = 3'h0,   //
    parameter logic [2:0]  rstsel_mult12_15a             = 3'h0,   //
    parameter logic [2:0]  rstsel_mult12_15b             = 3'h0,   //
    parameter logic        rst_mode_mult00a              = 1'b0,   // Selects the reset mode (clocked vs. unclocked) for
                                                                   // each delay stage register:
                                                                   // 1'b0 – synchronous reset mode.
                                                                   // 1'b1 – asynchronous reset mode1'b0 - synchronous, 1'b1 - asynchronous
    parameter logic        rst_mode_mult00b              = 1'b0,   //
    parameter logic        rst_mode_mult01a              = 1'b0,   //
    parameter logic        rst_mode_mult01b              = 1'b0,   //
    parameter logic        rst_mode_mult02a              = 1'b0,   //
    parameter logic        rst_mode_mult02b              = 1'b0,   //
    parameter logic        rst_mode_mult03a              = 1'b0,   //
    parameter logic        rst_mode_mult03b              = 1'b0,   //

    // multiplier operation
    parameter logic [4:0]  multmode_00_07                = 5'h00,  // operation of the lower half
                                                                   // 5'h00 - SIGNED 8×8
                                                                   // 5'h01 - UNSIGNED 8×8
                                                                   // 5'h02 - SMAG 8×8 (SignMAGnitude)
                                                                   // 5'h03 - SIGNED 7×7
                                                                   // 5'h04 - SMAG 7×7 (SignMAGnitude)
                                                                   // 5'h05 - SIGNED 6×6
                                                                   // 5'h06 - SMAG 6×6 (SignMAGnitude)
                                                                   // 5'h07 - SIGNED 4×4
                                                                   // 5'h08 - SMAG 4×4 (SignMAGnitude)
                                                                   // 5'h09 - SNOADD 4×4 (Sign-NOADDer)
                                                                   // 5'h0A - SIGNED 3×3
                                                                   // 5'h0B - SMAG 3×3 (SignMAGnitude)
                                                                   // 5'h0C - SNOADD 3×3 (Sign-NOADDer)
                                                                   // 5'h0D - SIGNED 16×16
                                                                   // 5'h0E - SA_UB 16×16 (SignedA_UnsignedB)
                                                                   // 5'h0F - UA_SB 16×16 (UnsignedA_SignedB)
                                                                   // 5'h10 - UNSIGNED 16×16
                                                                   // 5'h11 - NO OP (NO OPeration)
                                                                   // 5'h12 - A SIGNED, B UNSIGNED 8×8
                                                                   // 5'h13 - A UNSIGNED, B SIGNED 8×8
                                                                   // 5'h14 - SA_SB 32×32 (SignedA_SignedB)
                                                                   // 5'h15 - SA_UB 32×32 (SignedA_UnSignedB)
                                                                   // 5'h16 - UA_SB 32×32 (UnSignedA_SignedB)
                                                                   // 5'h17 - UA_UB 32×32 (UnSignedA_UnSignedB)
                                                                   // 5'h18 -
    parameter logic [4:0]  multmode_08_15                = 5'h00,  // operation of the upper half
                                                                   // 5'h00 - SIGNED 8×8
                                                                   // 5'h01 - UNSIGNED 8×8
                                                                   // 5'h02 - SMAG 8×8 (SignMAGnitude)
                                                                   // 5'h03 - SIGNED 7×7
                                                                   // 5'h04 - SMAG 7×7 (SignMAGnitude)
                                                                   // 5'h05 - SIGNED 6×6
                                                                   // 5'h06 - SMAG 6×6 (SignMAGnitude)
                                                                   // 5'h07 - SIGNED 4×4
                                                                   // 5'h08 - SMAG 4×4 (SignMAGnitude)
                                                                   // 5'h09 - SNOADD 4×4 (Sign-NOADDer)
                                                                   // 5'h0A - SIGNED 3×3
                                                                   // 5'h0B - SMAG 3×3 (SignMAGnitude)
                                                                   // 5'h0C - SNOADD 3×3 (Sign-NOADDer)
                                                                   // 5'h0D - SIGNED 16×16
                                                                   // 5'h0E - SA_UB 16×16 (SignedA_UnsignedB)
                                                                   // 5'h0F - UA_SB 16×16 (UnsignedA_SignedB)
                                                                   // 5'h10 - UNSIGNED 16×16
                                                                   // 5'h11 - NO OP (NO OPeration)
                                                                   // 5'h12 - A SIGNED, B UNSIGNED 8×8
                                                                   // 5'h13 - A UNSIGNED, B SIGNED 8×8
                                                                   // 5'h14 - SA_SB 32×32 (SignedA_SignedB)
                                                                   // 5'h15 - SA_UB 32×32 (SignedA_UnSignedB)
                                                                   // 5'h16 - UA_SB 32×32 (UnSignedA_SignedB)
                                                                   // 5'h17 - UA_UB 32×32 (UnSignedA_UnSignedB)
                                                                   // 5'h18 -
    // Use the adders for the two 8x8 products
    parameter logic        add_00_07_bypass              = 1'b0,   // Adder tree : ADD07 = ADD03 + ADD47
                                                                   // 1'b0 – selects ADD07 output
                                                                   // 1'b1 – selects ADD03 output
    parameter logic        add_00_07_sub                 = 1'b0,   // controls if ADD07 is in subtract mode
                                                                   // 1'b0 – ADD_SUB07 performs ADD{7:4] + ADD[3:0]
                                                                   // 1'b1 – ADD0_SUB7 performs ADD{7:4] - ADD[3:0]
    parameter logic        add_08_15_bypass              = 1'b0,   // Adder tree : ADD815 = ADD811 + ADD1215
                                                                   // 1'b0 – selects ADD815 output
                                                                   // 1'b1 – selects ADD811 output
    parameter logic        add_08_15_sub                 = 1'b0,   // controls if ADD815 is in subtract mode
                                                                   // 1'b0 – ADD815 performs ADD[15:12] + ADD[11:8]
                                                                   // 1'b1 – ADD815 performs ADD[15:12] - ADD[11:8]

    parameter logic        del_add_00_07_reg             = 1'b1,   // Enable stage2 register for adder timing
    parameter logic        del_add_08_15_reg             = 1'b1,   // Enable stage2 register for adder timing
    parameter logic [3:0]  cesel_add_00_07_reg           = 4'hD,   // Always enabled (1'b1) for continuous operation
    parameter logic [3:0]  cesel_add_08_15_reg           = 4'hD,   // Always enabled (1'b1) for continuous operation
    parameter logic [2:0]  rstsel_add_00_07_reg          = 3'h2,   // Use rstn[1] for proper reset control
    parameter logic [2:0]  rstsel_add_08_15_reg          = 3'h2,   // Use rstn[1] for proper reset control


    // Floating Point (do exoponents need a delay to match del_add_.._reg?)
    // input pipeline registers for FP and Block FP
    parameter logic del_expa_reg                         = 2'h1,   // Number of delay stages applied to floating point A input sign and
                                                                   // exponent from byte selection to FP_MULT_AB.
                                                                   // 2 or 3 stages supported?
    parameter logic [1:0]  del_expb_reg                  = 2'h1,   // Number of delay stages applied to floating point B input sign and
                                                                   // exponent from byte selection to FP_MULT_AB.
    parameter logic [1:0]  del_expc_reg                  = 2'h1,   // Number of delay stages applied to floating point C input sign and
                                                                   // exponent from byte selection to FP_MULT_CD.
    parameter logic [1:0]  del_expd_reg                  = 2'h1,   // Number of delay stages applied to floating point D input sign and
                                                                   // exponent from byte selection to FP_MULT_CD.
    parameter logic [3:0]  cesel_expta_reg               = 4'hD,   // Selects the ce inputs for each delay stage register:
    parameter logic [3:0]  cesel_exptb_reg               = 4'hD,   //
    parameter logic [3:0]  cesel_exptc_reg               = 4'hD,   //
    parameter logic [3:0]  cesel_exptd_reg               = 4'hD,   //
    parameter logic [2:0]  rstsel_expta_reg              = 3'h2,   // Selects the rstn input for each delay stage register
    parameter logic [2:0]  rstsel_exptb_reg              = 3'h2,   //
    parameter logic [2:0]  rstsel_exptc_reg              = 3'h2,   //
    parameter logic [2:0]  rstsel_exptd_reg              = 3'h2,   //

    // FP Configuration
    parameter logic        fpmult_ab_blockfp             = 1'b1,   // Select (A×B) regular floating point or block floating point:
                                                                   // 1'b0 – ReguIar floating point (input – floating-point numbers)
                                                                   // 1'b1 – Block floating point (input – integer mantissas and shared exponent)
    parameter logic        fpmult_ab_exp_size            = 1'b0,   // Exponents ea and eb are represented by biased unsigned integers ea and eb:
                                                                   // 1'b0 – Bits ea/eb are 8 bits
                                                                   // 1'b1 – Bits ea/eb are 5 bits
    parameter logic [2:0]  fpmult_ab_blockfp_mode        = 3'b000, // Select size of integer multipliers for (A*B) block floating point
                                                                   // 3'b000: 8*8
                                                                   // 3'b001: 16*16
                                                                   // 3'b011: 3*3
                                                                   // 3'b100: 4*4
                                                                   // 3'b110: 6*6
                                                                   // 3'b111: 7*7
    parameter logic        fpmult_cd_blockfp             = 1'b1,   // Select (C×D) regular floating point or block floating point:
                                                                   // 1'b0 – ReguIar floating point (input – floating-point numbers)
                                                                   // 1'b1 – Block floating point (input – integer mantissas and shared exponent)
    parameter logic        fpmult_cd_exp_size            = 1'b0,   // Exponents ea and eb are represented by biased unsigned integers ea and eb:
                                                                   // 1'b0 – Bits ec/ed are 8 bits
                                                                   // 1'b1 – Bits ec/ed are 5 bits
    parameter logic [2:0]  fpmult_cd_blockfp_mode        = 3'b000, // Select size of integer multipliers for (C*D) block floating point
                                                                   // 3'b000: 8*8
                                                                   // 3'b001: 16*16
                                                                   // 3'b011: 3*3
                                                                   // 3'b100: 4*4
                                                                   // 3'b110: 6*6
                                                                   // 3'b111: 7*7
    parameter logic        del_fpmult_ab_pipe_reg        = 1'b0,   // pipeline register enable
    parameter logic        del_fpmult_cd_pipe_reg        = 1'b0,   //
    parameter logic [3:0]  cesel_fpmult_ab_pipe_reg      = 4'h1,   // select ce
    parameter logic [3:0]  cesel_fpmult_cd_pipe_reg      = 4'h1,   //
    parameter logic [2:0]  rstsel_fpmult_ab_pipe_reg     = 3'h2,   // select rstn
    parameter logic [2:0]  rstsel_fpmult_cd_pipe_reg     = 3'h2,   //

    // output stage

    parameter logic        fpadd_abcd_sel                = 1'b0,   // FPADD_ABCD select
                                                                   // 1'b0: FPMULT_AB output routed towards FPMULT_AB_REG
                                                                   // 1'b1: FPADD_ABCD output routed to FPMULT_AB_REG
    parameter logic        add_00_15_sel                 = 1'b0,   // Selects if the output of ADD015 is used
                                                                   // 1'b0: ADD0_7_REG output is routed toward FPMULT_AB_REG
                                                                   // 1'b1: ADD015 output is routed toward FPMULT_AB_REG
    parameter logic        fpmult_ab_bypass              = 1'b0,   // multiplication mode selection
                                                                   // 1'b0 - floating-Point Multiplier are enabled
                                                                   // 1'b1 - floating-Point Multiplier is bypassed; integer multiplier are selected
                                                                   // ***********************************************************
                                                                   //             use ADD07            |            use ADD015
                                                                   //     fpmult_ab_bypass     = 1'b1    |    fpmult_ab_bypass     = 1'b1
                                                                   //     add_00_15_sel         = 1'b0    |    add_00_15_sel         = 1'b1
                                                                   //     fpadd_abcd_sel         = 1'bx    |    fpadd_abcd_sel         = 1'bx
                                                                   //
                                                                   //             use FPMULT_AB        |    use FPMULT_AB + FPMULT_CD
                                                                   //     fpmult_ab_bypass     = 1'b0    |    fpmult_ab_bypass     = 1'b0
                                                                   //     add_00_15_sel         = 1'bx    |    add_00_15_sel         = 1'bx
                                                                   //     fpadd_abcd_sel         = 1'b0    |    fpadd_abcd_sel         = 1'b1
                                                                   // ***********************************************************
    parameter logic        del_fpmult_ab_reg             = 1'b0,   // Selects if delay stage register is enabled or bypassed:
    parameter logic [3:0]  cesel_fpmult_ab_reg           = 4'h1,   // select ce
    parameter logic [2:0]  rstsel_fpmult_ab_reg          = 3'h2,   // select rstn
    parameter logic        fpmult_cd_bypass              = 1'b0,   // multiplication mode selection
                                                                   // 1'b0 - floating-Point Multiplier is enabled
                                                                   // 1'b1 - floating-Point Multiplier is bypassed; integer multiplier is selected

    // lower half output pre-selection
    // fpadd_ab_dina is always connected to pipeline register
    // AB is the only accum that can select LRAM_DOUT[119:72] as input
    parameter logic [2:0]  fpadd_ab_dinb_sel             = 3'b000, // Select the addend, or subtrahend for the AB Accumulator
                                                                   // 3'b000 - 48-bit ACCUM_AB_REG input (always registered)
                                                                   // 3'b001 - 48-bit MLP Forward Cascaded input FWDI_DOUT[47:0]
                                                                   // 3'b010 - 48-bit LRAM_DOUT[47:0]
                                                                   // 3'b011 - 24-bit LRAM_DOUT[59:36] (top 24 bits tied to zero)
                                                                   // 3'b100 - 24-bit MLP Forward Cascade input FWDI_DOUT[47:24] (top 24 bits tied to zero)
                                                                   // 3'b101 - 48-bit LRAM_DOUT[119:72]
                                                                   // 3'b110 -
                                                                   // 3'b111 -
    parameter logic [2:0]  fpadd_cd_dinb_sel             = 3'b000, // Select the addend, or subtrahend for the CD accumulator
                                                                   // 3'b000 – 48-bit ACCUM_CD_REG input (registered)
                                                                   // 3'b001 – 48-bit MLP forward cascaded input FWDI_DOUT[47:0]
                                                                   // 3'b010 – 48-bit LRAM_DOUT[47:0]
                                                                   // 3'b011 – Reserved
                                                                   // 3'b100 – 48-bit AB Accumulator data output
                                                                   // 3'b101 -
                                                                   // 3'b110 -
                                                                   // 3'b111 -
    parameter logic        fpadd_ab_nornd                = 1'b0,   // Disable FPADD_AB rounding
                                                                   // 1'b0: FPADD_AB round to even mode
                                                                   // 1'b1: FPADD_AB rounding disabled (truncation)
    parameter logic [1:0]  fpadd_ab_output_format        = 2'b00,  // Selection of floating-point output format of AB Floating-Point Multiplier
                                                                   // 2'b00: Output format will be FP24 based
                                                                   // 2'b01: Output format will be BF16 based
                                                                   // 2'b10: Output format will be FP16 based Disable FPADD_AB rounding
    parameter logic        add_accum_ab_bypass           = 1'b0,   // USE AB accumulator (not bypass) for BFP accumulation
                                                                   // 1'b0 – integer AB accumulator value is used ★ ENABLED
                                                                   // 1'b1 – bypass integer AB accumulator or FPADD_AB accumulator
    parameter logic        accum_ab_reg_din_sel          = 1'b1,   // Select between integer (or bypass) and floating-point AB result
                                                                   // 1'b0 – Value from integer AB accumulator block (or bypass)
                                                                   // 1'b1 – Value from floating-point AB accumulator block
    parameter logic        del_accum_ab_reg              = 1'b0,   // Selects if each delay stage register is enabled or bypassed
    parameter logic [3:0]  cesel_accum_ab_reg            = 4'h1,   // select ce
    parameter logic [2:0]  rstsel_accum_ab_reg           = 3'h2,   // select rstn

    parameter logic        fpadd_cd_dina_sel             = 1'b0,   // Select the value between (C×D) floating-point multiplier and (A×B) accumulator
                                                                   // 1'b0 – Select the output from the (C×D) floating-point multiplier or ADD815
                                                                   // 1'b1 – 48-bit AB Accumulator data output

    parameter logic        fpadd_cd_nornd                = 1'b0,   // Disable FPADD_CD rounding
                                                                   // 1'b0: FPADD_CD round to even mode
                                                                   // 1'b1: FPADD_CD rounding disabled (truncation)
    parameter logic [1:0]  fpadd_cd_output_format        = 2'b00,  // Selection of floating-point output format of CD Floating-Point Multiplier
                                                                   // 2'b00: Output format will be FP24 based
                                                                   // 2'b01: Output format will be BF16 based
                                                                   // 2'b10: Output format will be FP16 based Disable FPADD_CD rounding
    parameter logic        add_accum_cd_bypass           = 1'b0,   // USE CD accumulator (not bypass) for BFP accumulation
                                                                   // 1'b0 – CD accumulator value is used ★ ENABLED
                                                                   // 1'b1 – Bypass CD accumulator and use signal selected with  fpadd_cd_dina_sel
  // Each half-MLP computes its own dot-product and produces half of the LRAM value
//   localparam logic   fpadd_ab_bypass   = 1'b0;   // Use AB accumulator
//   localparam logic   fpadd_cd_bypass   = 1'b0;   // Use CD accumulator

// out_reg_din_sel(fpadd_cd_bypass? 3'b011 : 3'b010),
    parameter logic [2:0]  out_reg_din_sel               = 3'b010, // Select out_reg input - bypass floating-point value and accumulator value
                                                                   // 3'b000 – Value is from Mult8×4
														    	   // 3'b001 - I32xI32, (ADD_ACCUM_CD[47:0],ADD0_7_REG[15:0])
                                                                   // 3'b010 – FP_ADD_CD floating-point value
                                                                   // 3'b011 – output or bypass of integer CD accumulator, as set by add_accum_cd_bypass
                                                                   // 3'b100 – 8-wide A +/– B output
                                                                   // 3'b110 – Value is Mult16×2
    parameter logic        del_out_reg_00_15             = 1'b0,   // Selects if each delay stage register is enabled or bypassed
    parameter logic        del_out_reg_16_31             = 1'b0,   //
    parameter logic        del_out_reg_32_47             = 1'b0,   //
    parameter logic        del_out_reg_48_63             = 1'b0,   //
    parameter logic [3:0]  cesel_out_reg_00_15           = 4'h1,   // select ce
    parameter logic [3:0]  cesel_out_reg_16_31           = 4'h1,   //
    parameter logic [3:0]  cesel_out_reg_32_47           = 4'h1,   //
    parameter logic [3:0]  cesel_out_reg_48_63           = 4'h1,   //
    parameter logic [2:0]  rstsel_out_reg_00_15          = 3'h2,   // select rstn
    parameter logic [2:0]  rstsel_out_reg_16_31          = 3'h2,   //
    parameter logic [2:0]  rstsel_out_reg_32_47          = 3'h2,   //
    parameter logic [2:0]  rstsel_out_reg_48_63          = 3'h2,   //
    parameter logic        rst_mode_out_reg_00_15        = 1'b0,   // Selects the reset mode (clocked vs. unclocked) for each delay stage register:
    parameter logic        rst_mode_out_reg_16_31        = 1'b0,   // 1'b0 - synchronous, 1'b1 - asynchronous
    parameter logic        rst_mode_out_reg_32_47        = 1'b0,   //
    parameter logic        rst_mode_out_reg_48_63        = 1'b0,   //

    parameter logic        del_fp_format_ab_reg          = 1'b0,   // Selects if each delay stage register is enabled or bypassed
    parameter logic        del_fp_format_cd_reg          = 1'b0,   //
    parameter logic [3:0]  cesel_fp_format_ab_reg        = 4'h1,   // select ce
    parameter logic [3:0]  cesel_fp_format_cd_reg        = 4'h1,   //
    parameter logic [2:0]  rstsel_fp_format_ab_reg       = 3'h2,   // select rstn
    parameter logic [2:0]  rstsel_fp_format_cd_reg       = 3'h2,   //

    parameter logic [1:0]  dout_mlp_sel                  = 2'b01,  // Select values for the forward DOUT cascade path:
                                                                   // 2'b00 – value from optionally registered output OUT_REG[63:0]
                                                                   // 2'b01 – concatenated outputs of upper and lower MLP outputs {24'h0,ACCUM_AB_REG[23:0],OUT_REG[23:0]}, used to pass floating point values via fwdo_dout.
                                                                   // 2'b10 – value from optionally registered output ACCUM_AB_REG[47:0].
                                                                   // 2'b11 – concatenated lower 36 bits from upper and lower MLP outputs {ACCUM_AB_REG[35:0],OUT_REG[35:0]}

    parameter logic [1:0]  outmode_sel                   = 2'b11,  // Select final DOUT value:
                                                                   // 2'b00 – 72-bit output of value selected by parameter dout_mlp_sel[1:0].
                                                                   // 2'b01 – LRAM_DOUT[71:0].(1)
                                                                   // 2'b10 – BRAM_DOUT[143:72].
                                                                   // 2'b11 – optionally registered concatenated outputs of floating point format conversion
                                                                   // registers with status {20'h0,fp_ab_status, fp_cd_status, accum_ab_reg,out_reg}.

    parameter logic        rndsubload_share              = 1'b0,   // use common pin or separate lower and upper half
    parameter logic [2:0]  del_rndsubload_reg            = 3'h0,   // enable reg - delay match for load etc (0 - 4 delays)
    parameter logic [2:0]  del_rndsubload_ab_reg         = 3'h0,   // enable reg - delay match for load etc (0 - 3 delays)
    parameter logic [3:0]  cesel_rndsubload_reg          = 4'h0,   // permanent enable
    parameter logic [3:0]  cesel_rndsubload_ab_reg       = 4'h0,   // permanent enable
    parameter logic [2:0]  rstsel_rndsubload_reg         = 3'h0,   // no rstn
    parameter logic [2:0]  rstsel_rndsubload_ab_reg      = 3'h0,   // permanent reset

    // LRAM - configured for 144-bit {accum_ab & accum_cd} storage

    parameter string       mem_init_file                 = "",
    parameter logic [71:0] initd_0                       = 72'h0,
    parameter logic [71:0] initd_1                       = 72'hx,
    parameter logic [71:0] initd_2                       = 72'hx,
    parameter logic [71:0] initd_3                       = 72'hx,
    parameter logic [71:0] initd_4                       = 72'hx,
    parameter logic [71:0] initd_5                       = 72'hx,
    parameter logic [71:0] initd_6                       = 72'hx,
    parameter logic [71:0] initd_7                       = 72'hx,
    parameter logic [71:0] initd_8                       = 72'hx,
    parameter logic [71:0] initd_9                       = 72'hx,
    parameter logic [71:0] initd_10                      = 72'hx,
    parameter logic [71:0] initd_11                      = 72'hx,
    parameter logic [71:0] initd_12                      = 72'hx,
    parameter logic [71:0] initd_13                      = 72'hx,
    parameter logic [71:0] initd_14                      = 72'hx,
    parameter logic [71:0] initd_15                      = 72'hx,
    parameter logic [71:0] initd_16                      = 72'hx,
    parameter logic [71:0] initd_17                      = 72'hx,
    parameter logic [71:0] initd_18                      = 72'hx,
    parameter logic [71:0] initd_19                      = 72'hx,
    parameter logic [71:0] initd_20                      = 72'hx,
    parameter logic [71:0] initd_21                      = 72'hx,
    parameter logic [71:0] initd_22                      = 72'hx,
    parameter logic [71:0] initd_23                      = 72'hx,
    parameter logic [71:0] initd_24                      = 72'hx,
    parameter logic [71:0] initd_25                      = 72'hx,
    parameter logic [71:0] initd_26                      = 72'hx,
    parameter logic [71:0] initd_27                      = 72'hx,
    parameter logic [71:0] initd_28                      = 72'hx,
    parameter logic [71:0] initd_29                      = 72'hx,
    parameter logic [71:0] initd_30                      = 72'hx,
    parameter logic [71:0] initd_31                      = 72'hx,
    parameter logic        lram_clk_sel_rd               = 1'b0,   // Select MLP clk for LRAM write clock
                                                                   // 1'b0: LRAM write clock driven by lram_wrclk
                                                                   // 1'b1: LRAM write clock driven by clk
    parameter string       lram_rdclk_polarity           = "rise", // Specifies whether registers are clocked by the rising or falling edge of the clock
                                                                   // supported values; "rise", "fall"
    parameter logic        lram_clk_sel_wr               = 1'b0,   // Select MLP clk for LRAM write clock
                                                                   // 1'b0: LRAM write clock driven by lram_wrclk
                                                                   // 1'b1: LRAM write clock driven by clk
    parameter string       lram_wrclk_polarity           = "rise", // Specifies whether registers are clocked by the rising or falling edge of the clock
                                                                   // supported values; "rise", "fall"
    parameter logic        lram_sr_assertion             = 1'b0,   // Selects the LRAM reset mode
                                                                   // 1'b0: Synchronous Reset-Mode
                                                                   // 1'b1: Asynchronous Reset-Mode

    parameter logic        lram_clear_enable             = 1'b0,   // Enable LRAM block memory clear:
                                                                   // 1'b0 – LRAM block memory clear is disabled.
                                                                   // 1'b1 – when the virtual port lram_regrstn is asserted (1'b0), the contents of the LRAM memory are reset to 0.
                                                                   // The LRAM output register is always reset when lram_regrstn is asserted low, independent of the state of lram_clear_enable
    parameter logic        lram_sync_mode                = 1'b1,   // Controls Write-Clock and Read-Clock are in synchronous mode
                                                                   // 1'b0: Write-Clock and Read-Clock are in asynchronous
                                                                   // 1'b1: Write-Clock and Read-Clock are the same clock (synchronous)
    // TODO: ACX notes this enabled operation > 500MHz
    parameter logic        lram_reg_dout                 = 1'b0,   // Enable optional LRAM_DOUT[143:0] register:
                                                                   // 1'b0 – LRAM read data is asynchronous read, no register.
                                                                   // 1'b1 – LRAM read data is synchronous read, register enabled.
    parameter logic [1:0]  lram_input_control_mode       = 2'b01,  // Select LRAM Input control mode:
                                                                   // 2'b00 – BRAM controls LRAM write control. -> mode 0
                                                                   // 2'b01 – LRAM uses MLP inputs. -> mode 1
                                                                   // 2'b10 – LRAM uses MLP inputs with additional FIFO controller FSM inputs. -> mode 2
                                                                   // 2'b11 – LRAM is off/disabled.
                                                                   // This controls the source of wraddr and wren.
    parameter logic [1:0]  lram_output_control_mode      = 2'b01,  // Select LRAM output control mode:
                                                                   // 2'b00 – BRAM controls LRAM read control. -> mode 0
                                                                   // 2'b01 – LRAM uses MLP inputs. -> mode 1
                                                                   // 2'b10 – LRAM uses MLP inputs with additional FIFO controller FSM inputs. -> mode 2
                                                                   // 2'b11 – LRAM is off/disabled.
                                                                   // This controls the source of rdaddr, rden and regrstn:
    parameter logic [1:0]  lram_read_width               = 2'b10,  // Select LRAM read data width and depth value:
                                                                   // 2'b00 – data is 72-bit wide and 32 deep
                                                                   // 2'b01 – data is 36-bit wide and 64 deep
                                                                   // 2'b10 – data is 144-bit wide and 16 deep
    parameter logic [1:0]  lram_write_width              = 2'b10,  // Select LRAM write data width and depth value:
                                                                   // 2'b00 – data is 72-bit wide and 32 deep
                                                                   // 2'b01 – data is 36-bit wide and 64 deep
                                                                   // 2'b10 – data is 144-bit wide and 16 deep
    parameter logic        lram_accum_data_input_sel     = 1'b0,   // Select Accumulated data for LRAM_DIN[143:0]:
                                                                   // 1'b0 – aggregation of {24'h0, ADD_ACCUM_AB[47:0], 24'h0, ADD_ACCUM_CD[47:0]}. ×144-bit mode.
                                                                   // 1'b1 – aggregation of {72'h0, 12'h0, ADD_ACCUM_AB[23:0], 12'h0, ADD_ACCUM_CD[23:0]}. ×72-bit mode.
    parameter logic [1:0]  lram_write_data_mode          = 2'b10,  // LRAM_DIN[143:0] source:
                                                                   // 2'b00 – mlpram_din2mlpdout[143:0]. BRAM internal ×144-bit write data.
                                                                   // 2'b01 – aggregation of {mlpram_din2mlpdout[71:0], MLP_DIN[71:0]}. BRAM internal ×72-bit input and MLP ×72-bit data in.
                                                                   // 2'b10 – input selected by lram_accum_data_input_sel.
                                                                   // 2'b11 – aggregation of mutliplier "b" input buses, {multb_h[71:0], multb_l[71:0]}.

    parameter logic        lram_fifo_enable              = 1'b0,   // Enable LRAM FIFO mode (optional in mode 1, required in mode 2):
                                                                   // 1'b0 – LRAM is not in FIFO mode.
                                                                   // 1'b1 – LRAM is in FIFO mode.
    parameter logic        lram_fifo_sync_mode           = 1'b0,   // 1'b0 – LRAM FIFO is in asynchronous mode.
                                                                   // 1'b1 – LRAM FIFO is in synchronous mode.
    parameter logic        lram_fifo_ignore_flags        = 1'b0,   // Enable LRAM FIFO address pointers to ignore empty/full status
                                                                   // 1'b0 – LRAM FIFO does not write when the FIFO is full (asserting write_error) and
                                                                   //        does not read when the FIFO is empty (asserting read_error). This is normal FIFO behavior.
                                                                   // 1'b1 – a write always writes to memory and increments the write pointer,
                                                                   //        regardless of full status. A read always reads from memory and increments the read pointer,
                                                                   //        regardless of empty status. In this mode, the read and write pointers act as regular
                                                                   //        address counters without operating as a FIFO. Ignore the full, empty, almost_full,
                                                                   //        almost_empty, write_error, and read_error flags.
    parameter logic        lram_fifo_fwft_mode           = 1'b0,   // Enable LRAM FIFO in first-word-fall-through (FWFT) mode:
                                                                   // 1'b1 – FWFT support is enabled.
                                                                   // 1'b0 – FWFT is not enabled.
    parameter logic [6:0]  lram_fifo_aempty_threshold    = 7'h0,   // Set LRAM FIFO almost empty threshold. User-defined configuration bit. Recommended
                                                                   // values are not less than 7'h01.
    parameter logic [6:0]  lram_fifo_afull_threshold     = 7'h0,   // Set LRAM FIFO almost full threshold. User-defined configuration bit. Recommended values
                                                                   // are less than 7'h3F.
    parameter logic [6:0]  lram_fifo_rdptr_maxval        = 7'h0,   // LRAM FIFO read pointer maximum value (must be 'h7F for normal FIFO operation)
    parameter logic [6:0]  lram_fifo_wrptr_maxval        = 7'h0,   // LRAM FIFO write pointer maximum value (must be 'h7F for normal FIFO operation)

    parameter logic [3:0]  lram_clk_pulse_sel            = 4'h3,   // use default value
    parameter logic [2:0]  lram_enable_write_via_bram    = 2'h0,   // use default value
    parameter logic        lram_fifo_fast_ef             = 1'h0,   // use default value
    parameter logic        lram_fifo_num_sync_stages_r2w = 1'h0,   // use default value
    parameter logic        lram_fifo_num_sync_stages_w2r = 1'h0,   // use default value
    parameter logic [1:0]  lram_fifo_out_modeb           = 2'h0,   // use default value
    parameter logic [6:0]  lram_fifo_rdptr_rstval        = 7'h0,   // use default value
    parameter logic [6:0]  lram_fifo_wrptr_rstval        = 7'h0    // use default value
) (
    input wire              clk,                                // MLP clock
    input wire [11:0]       ce,                                 // 12 clock enable
    input wire [3:0]        rstn,                               // 4 resets

    // input stage
    input wire [71:0]       mlp_din,                                // MLP_DIN[71:0] data inputs.
    input wire [143:0]      bram_to_mlp,                // Dedicated path from co-sited ACX_BRAM72K.
                                                                // Connects BRAM_DOUT[143:0] to MLP.
    input wire [71:0]       fwdi_multa_h,                       // Forward cascade path inputs for multiplier A inputs, higher multiplier block.
    input wire [71:0]       fwdi_multb_h,                       // Forward cascade path inputs for multiplier B inputs, higher multiplier block.
    input wire [71:0]       fwdi_multa_l,                       // Forward cascade path inputs for multiplier A inputs, lower multiplier block.
    input wire [71:0]       fwdi_multb_l,                       // Forward cascade path inputs for multiplier B inputs, lower multiplier block.
    input wire [7:0]        expb,


    output wire [71:0]      fwdo_multa_h,                       // Forward cascade path output for multiplier A inputs, higher multiplier block.
    output wire [71:0]      fwdo_multb_h,                       // Forward cascade path output for multiplier B inputs, higher multiplier block.
                                                                // This bus is the selection from mult_sel_multb_h and is not affected by the
                                                                // value of lram_out2multb_h.
    output wire [71:0]      fwdo_multa_l,                       // Forward cascade path output for multiplier A inputs, lower multiplier block
    output wire [71:0]      fwdo_multb_l,                       // Forward cascade path output for multiplier B inputs, lower multiplier block.
                                                                // This bus is the selection from mult_sel_multb_l and is not affected by the
                                                                // value of lram_out2multb_l.

    // output stage
    input wire              load,                               // rndsubshare = 1'b0 – when the upper half cd_add_accum accumulator is enabled,
                                                                //                         load the accumulator with the add[15:8] sum.
                                                                // rndsubshare = 1'b1 – load both ab_add_accum and cd_add_accum with their respective sum inputs.
    input wire              load_ab,                            // rndsubshare = 1'b0 – when the lower half ab_add_accum accumulator is enabled,
                                                                //                         load the accumulator with the output of the add_00_15_sel multiplexer.
                                                                // rndsubshare = 1'b1 – unused.
    input  wire [47:0]      fwdi_dout,                          // MLP72 internally calculated result, cascaded from ACX_MLP72 below.
    output wire [47:0]      fwdo_dout,                          // MLP72 internally calculated results, cascaded up to ACX_MLP72 above.
    output wire [71:0]      mlp_dout,                               // The result of the multiply-accumulate operation.
// (jj) - confusing - is this available outside the tile?? (NO)
    output wire [95:0]      mlpram_mlp_dout                    // Bits[47:0] ACX_MLP72 internally calculated result truncated to 48 bits.
                                                                // Bits[95:48] result of the ab sum path.
                                                                // The intended operation of mlpram_mlp_dout is when dout_mlp_sel selects the result of
                                                                // the cd sum path. Then mlpram_mlp_dout is a concatenation of the cd and ab sums,
                                                                // each truncated to 48 bits.

);

// Connect to 'Open' to force a pin to remain unconnected rather than tied off
wire Open;
ACX_FLOAT undriven(Open);

ACX_MLP72
# (
        .location                           (mlp_location),
        .clk_polarity                       (mlp_clk_polarity),
        .mux_sel_multa_l                    (mux_sel_multa_l),
        .mux_sel_multa_h                    (mux_sel_multa_h),
        .mux_sel_multb_l                    (mux_sel_multb_l),
        .mux_sel_multb_h                    (mux_sel_multb_h),
        .del_multa_l                        (del_multa_l),
        .del_multa_h                        (del_multa_h),
        .del_multb_l                        (del_multb_l),
        .del_multb_h                        (del_multb_h),
        .del_expb_din_reg                   (del_expb_din_reg),
        .cesel_multa_l                      (cesel_multa_l),
        .cesel_multa_h                      (cesel_multa_h),
        .cesel_multb_l                      (cesel_multb_l),
        .cesel_multb_h                      (cesel_multb_h),
        .cesel_expb_din_reg                 (cesel_expb_din_reg),
        .rstsel_multa_l                     (rstsel_multa_l),
        .rstsel_multa_h                     (rstsel_multa_h),
        .rstsel_multb_l                     (rstsel_multb_l),
        .rstsel_multb_h                     (rstsel_multb_h),
        .rstsel_expb_din_reg                (rstsel_expb_din_reg),
        .lram_out2multb_l                   (lram_out2multb_l),
        .lram_out2multb_h                   (lram_out2multb_h),
        .bytesel_00_07                      (bytesel_00_07),
        .bytesel_08_15                      (bytesel_08_15),
        .del_mult00a                        (del_mult00a),
        .del_mult00b                        (del_mult00b),
        .del_mult01a                        (del_mult01a),
        .del_mult01b                        (del_mult01b),
        .del_mult02a                        (del_mult02a),
        .del_mult02b                        (del_mult02b),
        .del_mult03a                        (del_mult03a),
        .del_mult03b                        (del_mult03b),
        .del_mult04_07a                     (del_mult04_07a),
        .del_mult04_07b                     (del_mult04_07b),
        .del_mult08_11a                     (del_mult08_11a),
        .del_mult08_11b                     (del_mult08_11b),
        .del_mult12_15a                     (del_mult12_15a),
        .del_mult12_15b                     (del_mult12_15b),
        .cesel_mult00a                      (cesel_mult00a),
        .cesel_mult00b                      (cesel_mult00b),
        .cesel_mult01a                      (cesel_mult01a),
        .cesel_mult01b                      (cesel_mult01b),
        .cesel_mult02a                      (cesel_mult02a),
        .cesel_mult02b                      (cesel_mult02b),
        .cesel_mult03a                      (cesel_mult03a),
        .cesel_mult03b                      (cesel_mult03b),
        .cesel_mult04_07a                   (cesel_mult04_07a),
        .cesel_mult04_07b                   (cesel_mult04_07b),
        .cesel_mult08_11a                   (cesel_mult08_11a),
        .cesel_mult08_11b                   (cesel_mult08_11b),
        .cesel_mult12_15a                   (cesel_mult12_15a),
        .cesel_mult12_15b                   (cesel_mult12_15b),
        .rstsel_mult00a                     (rstsel_mult00a),
        .rstsel_mult00b                     (rstsel_mult00b),
        .rstsel_mult01a                     (rstsel_mult01a),
        .rstsel_mult01b                     (rstsel_mult01b),
        .rstsel_mult02a                     (rstsel_mult02a),
        .rstsel_mult02b                     (rstsel_mult02b),
        .rstsel_mult03a                     (rstsel_mult03a),
        .rstsel_mult03b                     (rstsel_mult03b),
        .rstsel_mult04_07a                  (rstsel_mult04_07a),
        .rstsel_mult04_07b                  (rstsel_mult04_07b),
        .rstsel_mult08_11a                  (rstsel_mult08_11a),
        .rstsel_mult08_11b                  (rstsel_mult08_11b),
        .rstsel_mult12_15a                  (rstsel_mult12_15a),
        .rstsel_mult12_15b                  (rstsel_mult12_15b),
        .rst_mode_mult00a                   (rst_mode_mult00a),
        .rst_mode_mult00b                   (rst_mode_mult00b),
        .rst_mode_mult01a                   (rst_mode_mult01a),
        .rst_mode_mult01b                   (rst_mode_mult01b),
        .rst_mode_mult02a                   (rst_mode_mult02a),
        .rst_mode_mult02b                   (rst_mode_mult02b),
        .rst_mode_mult03a                   (rst_mode_mult03a),
        .rst_mode_mult03b                   (rst_mode_mult03b),
        .multmode_00_07                     (multmode_00_07),
        .multmode_08_15                     (multmode_08_15),
        .add_00_07_bypass                   (add_00_07_bypass),
        .add_00_07_sub                      (add_00_07_sub),
        .add_08_15_bypass                   (add_08_15_bypass),
        .add_08_15_sub                      (add_08_15_sub),
        .del_add_00_07_reg                  (del_add_00_07_reg),
        .del_add_08_15_reg                  (del_add_08_15_reg),
        .cesel_add_00_07_reg                (cesel_add_00_07_reg),
        .cesel_add_08_15_reg                (cesel_add_08_15_reg),
        .rstsel_add_00_07_reg               (rstsel_add_00_07_reg),
        .rstsel_add_08_15_reg               (rstsel_add_08_15_reg),
        .del_expa_reg                       (del_expa_reg),
        .del_expb_reg                       (del_expb_reg),
        .del_expc_reg                       (del_expc_reg),
        .del_expd_reg                       (del_expd_reg),
        .cesel_expta_reg                    (cesel_expta_reg),
        .cesel_exptb_reg                    (cesel_exptb_reg),
        .cesel_exptc_reg                    (cesel_exptc_reg),
        .cesel_exptd_reg                    (cesel_exptd_reg),
        .rstsel_expta_reg                   (rstsel_expta_reg),
        .rstsel_exptb_reg                   (rstsel_exptb_reg),
        .rstsel_exptc_reg                   (rstsel_exptc_reg),
        .rstsel_exptd_reg                   (rstsel_exptd_reg),
        .fpmult_ab_blockfp                  (fpmult_ab_blockfp),
        .fpmult_ab_exp_size                 (fpmult_ab_exp_size),
        .fpmult_ab_blockfp_mode             (fpmult_ab_blockfp_mode),
        .fpmult_cd_blockfp                  (fpmult_cd_blockfp),
        .fpmult_cd_exp_size                 (fpmult_cd_exp_size),
        .fpmult_cd_blockfp_mode             (fpmult_cd_blockfp_mode),
        .del_fpmult_ab_pipe_reg             (del_fpmult_ab_pipe_reg),
        .del_fpmult_cd_pipe_reg             (del_fpmult_cd_pipe_reg),
        .cesel_fpmult_ab_pipe_reg           (cesel_fpmult_ab_pipe_reg),
        .cesel_fpmult_cd_pipe_reg           (cesel_fpmult_cd_pipe_reg),
        .rstsel_fpmult_ab_pipe_reg          (rstsel_fpmult_ab_pipe_reg),
        .rstsel_fpmult_cd_pipe_reg          (rstsel_fpmult_cd_pipe_reg),
        .fpadd_abcd_sel                     (fpadd_abcd_sel),
        .add_00_15_sel                      (add_00_15_sel),
        .fpmult_ab_bypass                   (fpmult_ab_bypass),
        .del_fpmult_ab_reg                  (del_fpmult_ab_reg),
        .cesel_fpmult_ab_reg                (cesel_fpmult_ab_reg),
        .rstsel_fpmult_ab_reg               (rstsel_fpmult_ab_reg),
        .fpmult_cd_bypass                   (fpmult_cd_bypass),
        .fpadd_ab_dinb_sel                  (fpadd_ab_dinb_sel),
        .fpadd_ab_nornd                     (fpadd_ab_nornd),
        .fpadd_ab_output_format             (fpadd_ab_output_format),
        .add_accum_ab_bypass                (add_accum_ab_bypass),
        .accum_ab_reg_din_sel               (accum_ab_reg_din_sel),
        .del_accum_ab_reg                   (del_accum_ab_reg),
        .cesel_accum_ab_reg                 (cesel_accum_ab_reg),
        .rstsel_accum_ab_reg                (rstsel_accum_ab_reg),
        .fpadd_cd_dina_sel                  (fpadd_cd_dina_sel),
        .fpadd_cd_dinb_sel                  (fpadd_cd_dinb_sel),
        .fpadd_cd_nornd                     (fpadd_cd_nornd),
        .fpadd_cd_output_format             (fpadd_cd_output_format),
        .add_accum_cd_bypass                (add_accum_cd_bypass),
        .out_reg_din_sel                    (out_reg_din_sel),
        .del_out_reg_00_15                  (del_out_reg_00_15),
        .del_out_reg_16_31                  (del_out_reg_16_31),
        .del_out_reg_32_47                  (del_out_reg_32_47),
        .del_out_reg_48_63                  (del_out_reg_48_63),
        .cesel_out_reg_00_15                (cesel_out_reg_00_15),
        .cesel_out_reg_16_31                (cesel_out_reg_16_31),
        .cesel_out_reg_32_47                (cesel_out_reg_32_47),
        .cesel_out_reg_48_63                (cesel_out_reg_48_63),
        .rstsel_out_reg_00_15               (rstsel_out_reg_00_15),
        .rstsel_out_reg_16_31               (rstsel_out_reg_16_31),
        .rstsel_out_reg_32_47               (rstsel_out_reg_32_47),
        .rstsel_out_reg_48_63               (rstsel_out_reg_48_63),
        .rst_mode_out_reg_00_15             (rst_mode_out_reg_00_15),
        .rst_mode_out_reg_16_31             (rst_mode_out_reg_16_31),
        .rst_mode_out_reg_32_47             (rst_mode_out_reg_32_47),
        .rst_mode_out_reg_48_63             (rst_mode_out_reg_48_63),
        .del_fp_format_ab_reg               (del_fp_format_ab_reg),
        .del_fp_format_cd_reg               (del_fp_format_cd_reg),
        .cesel_fp_format_ab_reg             (cesel_fp_format_ab_reg),
        .cesel_fp_format_cd_reg             (cesel_fp_format_cd_reg),
        .rstsel_fp_format_ab_reg            (rstsel_fp_format_ab_reg),
        .rstsel_fp_format_cd_reg            (rstsel_fp_format_cd_reg),
        .dout_mlp_sel                       (dout_mlp_sel),
        .outmode_sel                        (outmode_sel),
        .rndsubload_share                   (rndsubload_share),
        .del_rndsubload_reg                 (del_rndsubload_reg),
        .del_rndsubload_ab_reg              (del_rndsubload_ab_reg),
        .cesel_rndsubload_reg               (cesel_rndsubload_reg),
        .cesel_rndsubload_ab_reg            (cesel_rndsubload_ab_reg),
        .rstsel_rndsubload_reg              (rstsel_rndsubload_reg),
        .rstsel_rndsubload_ab_reg           (rstsel_rndsubload_ab_reg),
        .mem_init_file                      (mem_init_file),
        .initd_0                            (initd_0),
        .initd_1                            (initd_1),
        .initd_2                            (initd_2),
        .initd_3                            (initd_3),
        .initd_4                            (initd_4),
        .initd_5                            (initd_5),
        .initd_6                            (initd_6),
        .initd_7                            (initd_7),
        .initd_8                            (initd_8),
        .initd_9                            (initd_9),
        .initd_10                           (initd_10),
        .initd_11                           (initd_11),
        .initd_12                           (initd_12),
        .initd_13                           (initd_13),
        .initd_14                           (initd_14),
        .initd_15                           (initd_15),
        .initd_16                           (initd_16),
        .initd_17                           (initd_17),
        .initd_18                           (initd_18),
        .initd_19                           (initd_19),
        .initd_20                           (initd_20),
        .initd_21                           (initd_21),
        .initd_22                           (initd_22),
        .initd_23                           (initd_23),
        .initd_24                           (initd_24),
        .initd_25                           (initd_25),
        .initd_26                           (initd_26),
        .initd_27                           (initd_27),
        .initd_28                           (initd_28),
        .initd_29                           (initd_29),
        .initd_30                           (initd_30),
        .initd_31                           (initd_31),
        .lram_clk_sel_rd                    (lram_clk_sel_rd),
        .lram_rdclk_polarity                (lram_rdclk_polarity),
        .lram_clk_sel_wr                    (lram_clk_sel_wr),
        .lram_wrclk_polarity                (lram_wrclk_polarity),
        .lram_sr_assertion                  (lram_sr_assertion),
        .lram_clear_enable                  (lram_clear_enable),
        .lram_clk_pulse_sel                 (lram_clk_pulse_sel),
        .lram_sync_mode                     (lram_sync_mode),
        .lram_reg_dout                      (lram_reg_dout),
        .lram_input_control_mode            (lram_input_control_mode),
        .lram_output_control_mode           (lram_output_control_mode),
        .lram_read_width                    (lram_read_width),
        .lram_write_width                   (lram_write_width),
        .lram_accum_data_input_sel          (lram_accum_data_input_sel),
        .lram_write_data_mode               (lram_write_data_mode),
        .lram_fifo_enable                   (lram_fifo_enable),
        .lram_fifo_sync_mode                (lram_fifo_sync_mode),
        .lram_fifo_ignore_flags             (lram_fifo_ignore_flags),
        .lram_fifo_fwft_mode                (lram_fifo_fwft_mode),
        .lram_fifo_aempty_threshold         (lram_fifo_aempty_threshold),
        .lram_fifo_afull_threshold          (lram_fifo_afull_threshold),
        .lram_fifo_rdptr_maxval             (lram_fifo_rdptr_maxval),
        .lram_fifo_wrptr_maxval             (lram_fifo_wrptr_maxval),
        .lram_enable_write_via_bram         (lram_enable_write_via_bram),
        .lram_fifo_fast_ef                  (lram_fifo_fast_ef),
        .lram_fifo_num_sync_stages_r2w      (lram_fifo_num_sync_stages_r2w),
        .lram_fifo_num_sync_stages_w2r      (lram_fifo_num_sync_stages_w2r),
        .lram_fifo_out_modeb                (lram_fifo_out_modeb),
        .lram_fifo_rdptr_rstval             (lram_fifo_rdptr_rstval),
        .lram_fifo_wrptr_rstval             (lram_fifo_wrptr_rstval)


) i_MLP (
      // MLP:
      .clk(clk),
      .din(mlp_din),
      .load_ab(load_ab),
      .load(load),
      .sub_ab(1'b0),
      .sub(1'b0),
      .ce(ce),
      .rstn(rstn),
      .expb(expb),
      .dout(mlp_dout),

      // direct connections from/to ACX_BRAM72K:
      .mlpram_din(/*72*/),                // connect to ACX_BRAM72K:mlpram_din
      .mlpram_we(/*9*/),                  // connect to ACX_BRAM72K:mlpram_we
      .mlpram_dout(/*144*/),              // connect to ACX_BRAM72K:mlpram_dout
      .mlpram_mlp_dout(/*96*/),           // connect to ACX_BRAM72K:mlpram_mlp_dout (MLP result)
      .mlpram_bramdin2mlpdin({72{Open}}), // connect to ACX_BRAM72K:mlpram_din2mlpdin (BRAM din)
      .mlpram_bramdout2mlp(bram_to_mlp),  // connect to ACX_BRAM72K:mlpram_dout2mlp (BRAM dout)
      .mlpram_din2mlpdout({144{Open}}),   // connect to ACX_BRAM72K:mlpram_din2mlpdout (LRAM din)
      .mlpram_wraddr({6{Open}}),          // connect to ACX_BRAM72K:mlpram_wraddr
      .mlpram_wren(Open),                 // connect to ACX_BRAM72K:mlpram_wren
      .mlpram_rdaddr({6{Open}}),          // connect to ACX_BRAM72K:mlpram_rdaddr
      .mlpram_rden(Open),                 // connect to ACX_BRAM72K:mlpram_rden
      .mlpram_sbit_error(Open),           // connect to ACX_BRAM72K:mlpram_sbit_error
      .mlpram_dbit_error(Open),           // connect to ACX_BRAM72K:mlpram_dbit_error
      // ECC (pass-through from wide ACX_BRAM72K):
      .sbit_error(),
      .dbit_error(),

      // MLP cascade (going up):
      .fwdi_multa_h(fwdi_multa_h),
      .fwdi_multa_l(fwdi_multa_l),
      .fwdi_multb_h(fwdi_multb_h),
      .fwdi_multb_l(fwdi_multb_l),
      .fwdi_dout({48{Open}}),
      .fwdo_multa_h(fwdo_multa_h),
      .fwdo_multa_l(fwdo_multa_l),
      .fwdo_multb_h(fwdo_multb_h),
      .fwdo_multb_l(fwdo_multb_l),
      .fwdo_dout(/*48*/),

      // LRAM:
      .lram_wrclk(clk),
      .lram_rdclk(clk),
      .empty(),
      .full(),
      .almost_empty(),
      .almost_full(),
      .write_error(),
      .read_error()
);

endmodule