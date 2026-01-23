// ----------------------------------------------------------------------
//  Description: Weight BRAM Module - Dual-Port Memory for Weight Storage
//
//  This module implements a dual-port BRAM using Achronix ACX_BRAM72K primitive
//  for storing BFP8 weight blocks. The BRAM is configured for asymmetric access:
//  - Write: 72-bit words (1 BFP8 block = 8 elements × 8 bits + 8-bit exponent)
//  - Read:  144-bit words (2 BFP8 blocks)
//  - Read data connects directly to MLP weight inputs via mlpram_dout2mlp
//
//  SIMULATION NOTE: When USE_BEHAVIORAL_BRAM is defined, uses a simple behavioral
//  model because the ACX_BRAM72K mlpram_dout2mlp path doesn't work standalone
//  without a connected MLP primitive in simulation.
// ----------------------------------------------------------------------
`default_nettype none

module weight_bram #(
    parameter string mem_init_file = ""  // Memory initialization file
) (
    input wire        wrclk,   // Write clock
    input wire [71:0] din,     // Write data (72-bit BFP8 block)
    input wire [ 9:0] wraddr,  // Write address
    input wire        wren,    // Write enable

    input  wire       rdclk,   // Read clock
    input  wire [8:0] rdaddr,  // Read address
    input  wire       rden,    // Read enable
    output wire [143:0] dout   // Read data (144-bit: 2 BFP8 blocks)
);

  // BRAM72K native configuration
  localparam integer native_data_width = 72;        // Native BRAM data width
  localparam integer native_addrhi_width = 10;      // Native BRAM address width

// =============================================================================
// BEHAVIORAL MODEL FOR SIMULATION
// =============================================================================
// The ACX_BRAM72K simulation model's mlpram_dout2mlp output doesn't work
// correctly in standalone simulation (without connected MLP primitive).
// Use a simple behavioral model for functional verification.
// =============================================================================
`ifdef USE_BEHAVIORAL_BRAM

  // Simple behavioral dual-port asymmetric RAM
  // Write: 72-bit at 10-bit address (1024 locations)
  // Read: 144-bit at 9-bit address (512 locations, combining two 72-bit words)

  reg [71:0] mem [0:1023];
  reg [143:0] dout_reg;

  // Write port
  always @(posedge wrclk) begin
    if (wren) begin
      mem[wraddr] <= din;
      `ifdef DEBUG_WEIGHT_BRAM
      $display("[WT_BRAM_WR] @%0t wraddr=%0d din[71:64]=0x%02x din[63:0]=0x%016x",
               $time, wraddr, din[71:64], din[63:0]);
      `endif
    end
  end

  // Read port - combinatorial read with registered output
  // Read address N maps to: {mem[2*N+1], mem[2*N]}
  wire [9:0] rd_addr_even = {rdaddr, 1'b0};  // 2*rdaddr
  wire [9:0] rd_addr_odd  = {rdaddr, 1'b1};  // 2*rdaddr + 1

  always @(posedge rdclk) begin
    if (rden) begin
      dout_reg <= {mem[rd_addr_odd], mem[rd_addr_even]};
      `ifdef DEBUG_WEIGHT_BRAM
      $display("[WT_BRAM_RD] @%0t rdaddr=%0d dout[143:72]=0x%018x dout[71:0]=0x%018x",
               $time, rdaddr, mem[rd_addr_odd], mem[rd_addr_even]);
      `endif
    end
  end

  assign dout = dout_reg;

`else // !USE_BEHAVIORAL_BRAM - Use ACX primitive
// =============================================================================
// ACX_BRAM72K PRIMITIVE FOR SYNTHESIS
// =============================================================================

  // BRAM output to MLP connection
  wire [2*native_data_width-1 : 0] bram_to_mlp_dout;

  // Reorder BRAM output to match expected format (jjf - ?? just change muxsel??)
  // BRAM outputs [143:72] and [71:0], we need [143:72] first, then [71:0]
  // assign dout = { bram_to_mlp_dout[native_data_width +: native_data_width],  // Upper block
  //                 bram_to_mlp_dout[0 +: native_data_width] };                // Lower block


  // Unconnected signal handling - use wire assign to avoid floating signals
  (* keep = "true" *) wire Open = 1'b0;

  // synthesis translate_off
  `ifdef DEBUG_WEIGHT_BRAM
  always @(posedge wrclk) begin
      if (wren) begin
          $display("[WT_BRAM_WR] @%0t wraddr=%0d din[71:64]=0x%02x din[63:0]=0x%016x",
                   $time, wraddr, din[71:64], din[63:0]);
      end
  end
  `endif
  // synthesis translate_on

  // Achronix BRAM72K primitive instantiation
  ACX_BRAM72K #(
      // Clock configuration
      .rdclk_polarity("rise"),           // Rising edge read clock
      .wrclk_polarity("rise"),           // Rising edge write clock
      .clk_sel_wr(2'b00),                // Write clock selection
      .clk_sel_rd(2'b00),                // Read clock selection

      // Asymmetric read/write configuration
      .write_width(4'b0001),             // Write: 9 bytes = 72 bits
      .read_width(4'b0011),               // Read: 18 bytes = 144 bits
      .wrmem_input_sel(4'h0),            // Single BRAM write
      .rdmem_input_sel(4'h0),            // Single BRAM read
      .outreg_enable(1'b0),              // No output register

      // Input register configuration (disabled for maximum performance)
      .del_fwdi_ram_wr_addr(1'b0),       // No write address register
      .del_fwdi_ram_wr_data(1'b0),       // No write data register
      .del_fwdi_ram_rd_addr(1'b0),       // No read address register
      .ce_fwdi_ram_wr_addr(1'b0),        // No write address clock enable
      .ce_fwdi_ram_rd_addr(1'b0),        // No read address clock enable

      // BRAM cascade configuration (disabled)
      .blk_addr_enable(1'b0),            // No block addressing
      .blk_addr_value(7'h0),             // Block address value
      .blk_wraddr_mask(7'h0),            // Write address mask
      .blk_rdaddr_mask(7'h0),            // Read address mask
      .enable_revi_rd_data(1'b0),        // No reverse read data
      .dout_sel(1'b0),                   // Direct output selection

      // LRAM access configuration (disabled)
      .mlpram_din2mlpdout_sel(1'b0),     // No LRAM data selection
      .wide_lram_enable(1'b0),           // No wide LRAM

      // FIFO mode configuration (disabled)
      .fifo_enable(1'b0),                // No FIFO mode
      .fifo_ignore_flags(1'b0),          // No flag ignoring
      .fifo_wrptr_rstval(15'h0),         // Write pointer reset value
      .fifo_rdptr_rstval(15'h0),         // Read pointer reset value
      .fifo_wrptr_maxval(15'h7FFF),      // Write pointer max value
      .fifo_rdptr_maxval(15'h7FFF),      // Read pointer max value
      .fifo_sync_mode(1'b0),             // No sync mode
      .fifo_num_sync_stages_w2r(1'b0),   // No write-to-read sync stages
      .fifo_num_sync_stages_r2w(1'b0),   // No read-to-write sync stages
      .fifo_afull_threshold(15'h4),      // Almost full threshold
      .fifo_aempty_threshold(15'h4),     // Almost empty threshold
      .fifo_fwft_mode(1'b0),             // No first-word-fall-through
      .fast_ef(1'b0),                    // No fast empty/full

      // ECC configuration (bypassed for performance)
      .ecc_bypass_encode(1'b1),         // Bypass ECC encoding
      .ecc_bypass_decode(1'b1),          // Bypass ECC decoding

      // Memory initialization
      .mem_init_file(mem_init_file)      // Memory initialization file
  ) u_acx_bram72k (
      // Write port
      .wrclk(wrclk),                     // Write clock
      .din(din),                    // Write data (72-bit)
      .wren(wren),                       // Write enable
      .wraddrhi(wraddr), // Write address
      .wrmsel(1'b0),                     // Write memory select
      .we(9'h1FF),                       // Write enable mask (all 9 bytes)

      // Read port
      .rdclk(rdclk),                     // Read clock
      .rden(rden),                       // Read enable
      .rdaddrhi({ rdaddr, 1'b0 }), // Read address
      .rdmsel(1'b0),                     // Read memory select
      .outreg_rstn(1'b0),                // Output register reset (disabled)
      .outlatch_rstn(1'b1),              // Output latch reset (cannot be bypassed)
      .outreg_ce(1'b0),                  // Output register clock enable (disabled)
      .dout(/*72*/),                     // Direct BRAM output (unused)

      // Direct MLP connections for high-performance weight access
      .mlpclk(rdclk),                    // MLP clock (same as read clock)
      .mlpram_din({72{Open}}),           // MLP write data (unused)
      .mlpram_we({9{Open}}),             // MLP write enable (unused)
      .mlpram_dout({144{Open}}),         // MLP LRAM output (unused)
      .mlpram_mlp_dout({96{Open}}),      // MLP result output (unused)
      .mlpram_din2mlpdin(/*72*/),        // MLP input from BRAM (unused)
      //.mlpram_dout2mlp(bram_to_mlp_dout), // BRAM output to MLP (144-bit)
      .mlpram_dout2mlp(dout), // BRAM output to MLP (144-bit)
      .mlpram_din2mlpdout(/*144*/),      // MLP input to LRAM (unused)
      .mlpram_wraddr(/*6*/),             // MLP write address (unused)
      .mlpram_wren(),                    // MLP write enable (unused)
      .mlpram_rdaddr(/*6*/),             // MLP read address (unused)
      .mlpram_rden(),                    // MLP read enable (unused)
      .mlpram_sbit_error(),              // MLP single-bit error (unused)
      .mlpram_dbit_error(),              // MLP double-bit error (unused)

      // Block address configuration (unused)
      .revi_wblk_addr({7{Open}}),        // Reverse write block address
      .revi_rblk_addr({7{Open}}),        // Reverse read block address
      .revo_wblk_addr(/*7*/),            // Reverse write block address output
      .revo_rblk_addr(/*7*/),            // Reverse read block address output

      // BRAM cascade connections (unused)
      .fwdi_ram_wr_addr({14{Open}}),     // Forward write address input
      .fwdi_ram_wblk_addr({7{Open}}),    // Forward write block address input
      .fwdi_ram_wren(Open),              // Forward write enable input
      .fwdi_ram_we({18{Open}}),          // Forward write enable mask input
      .fwdi_ram_wrmsel(Open),            // Forward write memory select input
      .fwdi_ram_wr_data({144{Open}}),    // Forward write data input
      .fwdi_ram_rd_addr({14{Open}}),     // Forward read address input
      .fwdi_ram_rblk_addr({7{Open}}),    // Forward read block address input
      .fwdi_ram_rden(Open),              // Forward read enable input
      .fwdi_ram_rdmsel(Open),            // Forward read memory select input
      .fwdo_ram_wr_addr(/*14*/),         // Forward write address output
      .fwdo_ram_wblk_addr(/*7*/),        // Forward write block address output
      .fwdo_ram_wren(),                  // Forward write enable output
      .fwdo_ram_we(/*18*/),              // Forward write enable mask output
      .fwdo_ram_wrmsel(),                // Forward write memory select output
      .fwdo_ram_wr_data(/*144*/),        // Forward write data output
      .fwdo_ram_rd_addr(/*14*/),         // Forward read address output
      .fwdo_ram_rblk_addr(/*7*/),        // Forward read block address output
      .fwdo_ram_rden(),                  // Forward read enable output
      .fwdo_ram_rdmsel(),                // Forward read memory select output

      // BRAM reverse cascade connections (unused)
      .revi_ram_rd_addr({14{Open}}),     // Reverse read address input
      .revi_ram_rblk_addr({7{Open}}),    // Reverse read block address input
      .revi_ram_rden(Open),              // Reverse read enable input
      .revi_ram_rd_data({144{Open}}),    // Reverse read data input
      .revi_ram_rdval(Open),             // Reverse read valid input
      .revi_ram_rdmsel(Open),            // Reverse read memory select input
      .revo_ram_rd_addr(/*14*/),         // Reverse read address output
      .revo_ram_rblk_addr(/*7*/),        // Reverse read block address output
      .revo_ram_rden(),                  // Reverse read enable output
      .revo_ram_rd_data(/*144*/),        // Reverse read data output
      .revo_ram_rdval(),                 // Reverse read valid output
      .revo_ram_rdmsel(),                // Reverse read memory select output

      // BRAM FIFO status signals (unused)
      .full(),                           // FIFO full flag
      .almost_full(),                    // FIFO almost full flag
      .empty(),                          // FIFO empty flag
      .almost_empty(),                   // FIFO almost empty flag
      .write_error(),                    // FIFO write error
      .read_error(),                     // FIFO read error

      // ECC error signals (unused)
      .sbit_error(),                     // Single-bit error
      .dbit_error()                      // Double-bit error
  );

`endif // USE_BEHAVIORAL_BRAM

// NOTE (jjf): eneing-placement uses simpler module:

  // ACX_BRAM72K_SDP #(
  //     .write_width(72),
  //     .read_width(72),
  //     .byte_width(8),
  //     .outreg_enable(a_delayed)
  // ) a0_bram (
  //     .wrclk(i_b_wrclk),
  //     .rdclk(i_clk),
  //     .din({ {native_bram_width-arg_block_size {1'b0}}, i_wr_a }),
  //     .we({9'h0, 9'h1FF}),
  //     .wren(i_a_wren),
  //     .wraddr({i_a_wraddr, 4'b0}),
  //     .rden(1'b1),
  //     .rdaddr({i_a_rdaddr, 3'b0}),
  //     .outreg_rstn(1'b1),
  //     .outlatch_rstn(1'b1),
  //     .outreg_ce(1'b1),
  //     .dout(a0_dout)
  // );


endmodule  // weight_bram

//////////////////////////////////////
// End Speedster7t BRAM72K Wrapper User Model
//////////////////////////////////////
