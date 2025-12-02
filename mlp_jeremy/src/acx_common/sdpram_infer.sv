//---------------------------------------------------------------------------------
//
// Copyright (c) 2021 Achronix Semiconductor Corp.
// All Rights Reserved.
//
// This Software constitutes an unpublished work and contains
// valuable proprietary information and trade secrets belonging
// to Achronix Semiconductor Corp.
//
// Permission is hereby granted to use this Software including
// without limitation the right to copy, modify, merge or distribute
// copies of the software subject to the following condition:
//
// The above copyright notice and this permission notice shall
// be included in in all copies of the Software.
//
// The Software is provided “as is” without warranty of any kind
// expressed or implied, including but not limited to the warranties
// of merchantability fitness for a particular purpose and non-infringement,
// in no event shall the copyright holder be liable for any claim,
// damages, or other liability for any damages or other liability,
// whether an action of contract, tort or otherwise, arising from,
// out of or in connection with the Software
//
//
//---------------------------------------------------------------------------------
// Design: SDP memory inference
// Decides between BRAM and LRAM based on the requested size
// Restriction that read and write ports must be of the same dimensions
// Copied from https://www.achronix.com/sites/default/files/docs/Speedster7t_Component_Library_User_Guide_UG086.pdf
//---------------------------------------------------------------------------------
`timescale 1ps / 1ps
module sdpram_infer #(
    parameter ADDR_WIDTH = 0,
    parameter DATA_WIDTH = 0,
    parameter OUT_REG_EN = 0,
    parameter INIT_FILE_NAME = ""
) (
    // Clocks and resets
    input wire wr_clk,
    input wire rd_clk,
    // Enables
    input wire we,
    input wire rd_en,
    input wire rstreg,
    // Address and data
    input wire [ADDR_WIDTH-1:0] wr_addr,
    input wire [ADDR_WIDTH-1:0] rd_addr,
    input wire [DATA_WIDTH-1:0] wr_data,
    // Output
    output reg [DATA_WIDTH-1:0] rd_data
);
  // Determine if size is small enough for an LRAM
  localparam MEM_LRAM = ( ((DATA_WIDTH <= 36) && (ADDR_WIDTH <= 6)) ||
                        ((DATA_WIDTH <= 72) && (ADDR_WIDTH <= 5)) ||
                        ((DATA_WIDTH <= 144) && (ADDR_WIDTH <= 4))) ? 1 : 0;
  localparam WIDE_BRAM = (DATA_WIDTH > 72) ? 1 : 0;
  // Define combinatorial and registered outputs from memory array
  logic [DATA_WIDTH-1:0] rd_data_int;
  logic [DATA_WIDTH-1:0] rd_data_reg;
  logic read_collision;
  always @(posedge rd_clk)
    if (~rstreg) rd_data_reg <= {DATA_WIDTH{1'b0}};
    else rd_data_reg <= rd_data_int;
  // Need a generate block to apply the appropriate syn_ramstyle to the memory array
  // Rest of the the code has to be within the generate block to access that variable
  generate
    if (MEM_LRAM == 1) begin : gb_lram
      logic [DATA_WIDTH-1:0] mem[(2**ADDR_WIDTH)-1:0]  /* synthesis syn_ramstyle = "logic" */;
      // If an initialisation file exists, then initialise the memory
      if (INIT_FILE_NAME != "") begin : gb_init
        initial $readmemh(INIT_FILE_NAME, mem);
      end
      // Writing. Inference does not currently support byte enables
      // Also generate the signals to detect if there is a memory collision
      logic [ADDR_WIDTH-1:0] wr_addr_d;
      always @(posedge wr_clk)
        if (we) begin
          mem[wr_addr] <= wr_data;
          wr_addr_d <= wr_addr;
        end
      // LRAM only supports the WRITE_FIRST mode. So if rd_addr = wr_addr then
      // write takes priority and read value is invalid
      // The value from the array is combinatorial, (this is different than for BRAM)
      // Write address is effective on the cycle it is writing to the memory, (i.e. it is registered)
      assign read_collision = (wr_addr_d == rd_addr);
      assign rd_data_int = (read_collision) ? {DATA_WIDTH{1'bx}} : mem[rd_addr];
    end else if (WIDE_BRAM == 1) begin : gb_wide_bram
      logic [DATA_WIDTH-1:0] mem[(2**ADDR_WIDTH)-1:0]  /* synthesis syn_ramstyle = "large_ram" */;
      // If an initialisation file exists, then initialise the memory
      if (INIT_FILE_NAME != "") begin : gb_init
        initial $readmemh(INIT_FILE_NAME, mem);
      end
      // Writing. Inference does not currently support byte enables
      always @(posedge wr_clk)
        if (we) begin
          mem[wr_addr] <= wr_data;
        end
      // BRAM supports WRITE_FIRST mode only, (write takes precedence over read)
      // Calculate if there will be a collision
      // write takes priority and read value is invalid
      // Both wr_addr and rd_addr have registered operations on the memory array
      assign read_collision = (wr_addr == rd_addr) && we;
      always @(posedge rd_clk)
        if (rd_en) begin
          // Read collisions cannot be modelled in synthesis, so use solely in simulation
          // synthesis synthesis_off
          if (read_collision) rd_data_int <= {ADDR_WIDTH{1'bx}};
          else
            // synthesis synthesis_on
            rd_data_int <= mem[rd_addr];
        end
    end else begin : gb_bram
      logic [DATA_WIDTH-1:0] mem[(2**ADDR_WIDTH)-1:0]  /* synthesis syn_ramstyle = "block_ram"*/;
      // If an initialisation file exists, then initialise the memory
      if (INIT_FILE_NAME != "") begin : gb_init
        initial $readmemh(INIT_FILE_NAME, mem);
      end
      // Writing. Inference does not currently support byte enables
      always @(posedge wr_clk)
        if (we) begin
          mem[wr_addr] <= wr_data;
        end
      // BRAM supports WRITE_FIRST mode only, (write takes precedence over read)
      // Calculate if there will be a collision
      // write takes priority and read value is invalid
      // Both wr_addr and rd_addr have registered operations on the memory array
      assign read_collision = (wr_addr == rd_addr) && we;
      always @(posedge rd_clk)
        if (rd_en) begin
          // Read collisions cannot be modelled in synthesis, so use solely in simulation
          // synthesis synthesis_off
          if (read_collision) rd_data_int <= {ADDR_WIDTH{1'bx}};
          else
            // synthesis synthesis_on
            rd_data_int <= mem[rd_addr];
        end
    end
  endgenerate
  // Select output based on whether output register is enabled
  assign rd_data = (OUT_REG_EN) ? rd_data_reg : rd_data_int;
endmodule : sdpram_infer
