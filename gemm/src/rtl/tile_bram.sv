// ------------------------------------------------------------------
// Tile BRAM Module with Separate Left/Right Architecture
//
// Purpose: L1 memory layer for compute engine
// Architecture (matches dispatcher_bram.sv structure):
//  - FOUR separate BRAMs:
//    man_left:   256-bit × 512 lines (left matrix mantissas)
//    man_right:  256-bit × 512 lines (right matrix mantissas)
//    exp_left:   8-bit × 512 entries (left exponents)
//    exp_right:  8-bit × 512 entries (right exponents)
//
// Write Interface:
//  - FOUR PARALLEL WRITE PORTS (per SINGLE_ROW_REFERENCE.md)
//  - All four can write in SAME cycle with counter [0-511]
//  - man_left, man_right, exp_left, exp_right all driven simultaneously
//
// Read Interface (to compute_engine):
//  - Dual-read mantissas: Parallel left/right access
//  - Dual-read exponents: Separate left/right ports
//
// Author: MS2.0 Architecture - Separate BRAM Fix
// Date: Sun Oct 27, 2025
// ------------------------------------------------------------------

module tile_bram #(
    parameter MAN_WIDTH = 256,          // Mantissa line width
    parameter EXP_WIDTH = 8,            // Exponent width
    parameter BRAM_DEPTH = 512,         // 512 lines per side
    parameter ADDR_WIDTH = $clog2(BRAM_DEPTH) // 9-bit address width
)
(
    input  logic                     i_clk,
    input  logic                     i_reset_n,

    // ====================================================================
    // Write Ports 
    // FOUR PARALLEL WRITE PORTS - All can write in same cycle
    // ====================================================================
    // Left mantissa write port
    input  logic [ADDR_WIDTH-1:0]       i_man_left_wr_addr,
    input  logic                        i_man_left_wr_en,
    input  logic [MAN_WIDTH-1:0]        i_man_left_wr_data,

    // Right mantissa write port
    input  logic [ADDR_WIDTH-1:0]       i_man_right_wr_addr,
    input  logic                        i_man_right_wr_en,
    input  logic [MAN_WIDTH-1:0]        i_man_right_wr_data,

    // Left exponent write port
    input  logic [ADDR_WIDTH-1:0]       i_exp_left_wr_addr,
    input  logic                        i_exp_left_wr_en,
    input  logic [EXP_WIDTH-1:0]        i_exp_left_wr_data,

    // Right exponent write port
    input  logic [ADDR_WIDTH-1:0]       i_exp_right_wr_addr,
    input  logic                        i_exp_right_wr_en,
    input  logic [EXP_WIDTH-1:0]        i_exp_right_wr_data,

    // ====================================================================
    // Dual Read Ports (for compute_engine)
    // All four BRAMs have identical structure: 9-bit address + enable
    // ====================================================================
    // Left matrix mantissa read
    input  logic [ADDR_WIDTH-1:0]       i_man_left_rd_addr,
    input  logic                        i_man_left_rd_en,
    output logic [MAN_WIDTH-1:0]        o_man_left_rd_data,

    // Right matrix mantissa read
    input  logic [ADDR_WIDTH-1:0]       i_man_right_rd_addr,
    input  logic                        i_man_right_rd_en,
    output logic [MAN_WIDTH-1:0]        o_man_right_rd_data,

    // Left exponent read
    input  logic [ADDR_WIDTH-1:0]       i_exp_left_rd_addr,
    input  logic                        i_exp_left_rd_en,
    output logic [EXP_WIDTH-1:0]        o_exp_left_rd_data,

    // Right exponent read
    input  logic [ADDR_WIDTH-1:0]       i_exp_right_rd_addr,
    input  logic                        i_exp_right_rd_en,
    output logic [EXP_WIDTH-1:0]        o_exp_right_rd_data
);

    // ===================================================================
    // LEFT SIDE BUFFERS
    // ===================================================================
    (* ram_style = "block" *) logic [MAN_WIDTH-1:0] man_left [0:BRAM_DEPTH-1];   // 512 lines
    (* ram_style = "block" *) logic [EXP_WIDTH-1:0] exp_left [0:BRAM_DEPTH-1];   // 512 exponents

    // ===================================================================
    // RIGHT SIDE BUFFERS
    // ===================================================================
    (* ram_style = "block" *) logic [MAN_WIDTH-1:0] man_right [0:BRAM_DEPTH-1];  // 512 lines
    (* ram_style = "block" *) logic [EXP_WIDTH-1:0] exp_right [0:BRAM_DEPTH-1];  // 512 exponents

    // ===================================================================
    // SIMULATION NOTE: Memory initialization via DISPATCH operation
    // ===================================================================
    // No initial block needed - testbench writes data via tile_bram write ports
    // (simulating DISPATCH operation)

    // ===================================================================
    // WRITE LOGIC - MANTISSAS (PARALLEL - All can write in same cycle)
    // ===================================================================
    // Left mantissa write
    always_ff @(posedge i_clk) begin
        if (i_man_left_wr_en) begin
            man_left[i_man_left_wr_addr] <= i_man_left_wr_data;
            `ifdef SIMULATION
            $display("[TILE_WR] @%0t man_left[%0d] = 0x%064x",
                     $time, i_man_left_wr_addr, i_man_left_wr_data);
            `endif
        end
    end

    // Right mantissa write (can execute in SAME cycle as left)
    always_ff @(posedge i_clk) begin
        if (i_man_right_wr_en) begin
            man_right[i_man_right_wr_addr] <= i_man_right_wr_data;
            `ifdef SIMULATION
            $display("[TILE_WR] @%0t man_right[%0d] = 0x%064x",
                     $time, i_man_right_wr_addr, i_man_right_wr_data);
            `endif
        end
    end

    // ===================================================================
    // WRITE LOGIC - EXPONENTS
    // ===================================================================
    always_ff @(posedge i_clk) begin
        if (i_exp_left_wr_en) begin
            exp_left[i_exp_left_wr_addr] <= i_exp_left_wr_data;
            `ifdef SIMULATION
            $display("[TILE_WR] @%0t exp_left[%0d] = 0x%02x",
                     $time, i_exp_left_wr_addr, i_exp_left_wr_data);
            `endif
        end
        if (i_exp_right_wr_en) begin
            exp_right[i_exp_right_wr_addr] <= i_exp_right_wr_data;
            `ifdef SIMULATION
            $display("[TILE_WR] @%0t exp_right[%0d] = 0x%02x",
                     $time, i_exp_right_wr_addr, i_exp_right_wr_data);
            `endif
        end
    end

    // ===================================================================
    // READ LOGIC - MANTISSAS (Dual-Port)
    // ===================================================================
    logic [MAN_WIDTH-1:0] man_left_rd_data_reg;
    logic [MAN_WIDTH-1:0] man_right_rd_data_reg;

    // Left mantissa read (registered)
    always_ff @(posedge i_clk) begin
        if (i_man_left_rd_en) begin
            man_left_rd_data_reg <= man_left[i_man_left_rd_addr];
            `ifdef SIMULATION
            $display("[TILE_RD] @%0t man_left[%0d] → 0x%064x",
                     $time, i_man_left_rd_addr, man_left[i_man_left_rd_addr]);
            `endif
        end
    end
    assign o_man_left_rd_data = man_left_rd_data_reg;

    // Right mantissa read (registered)
    always_ff @(posedge i_clk) begin
        if (i_man_right_rd_en) begin
            man_right_rd_data_reg <= man_right[i_man_right_rd_addr];
            `ifdef SIMULATION
            $display("[TILE_RD] @%0t man_right[%0d] → 0x%064x",
                     $time, i_man_right_rd_addr, man_right[i_man_right_rd_addr]);
            `endif
        end
    end
    assign o_man_right_rd_data = man_right_rd_data_reg;

    // ===================================================================
    // READ LOGIC - EXPONENTS (with enable signals)
    // ===================================================================
    logic [EXP_WIDTH-1:0] exp_left_rd_data_reg;
    logic [EXP_WIDTH-1:0] exp_right_rd_data_reg;

    // Left exponent read (registered)
    always_ff @(posedge i_clk) begin
        if (i_exp_left_rd_en) begin
            exp_left_rd_data_reg <= exp_left[i_exp_left_rd_addr];
            `ifdef SIMULATION
            $display("[TILE_RD] @%0t exp_left[%0d] → 0x%02x",
                     $time, i_exp_left_rd_addr, exp_left[i_exp_left_rd_addr]);
            `endif
        end
    end
    assign o_exp_left_rd_data = exp_left_rd_data_reg;

    // Right exponent read (registered)
    always_ff @(posedge i_clk) begin
        if (i_exp_right_rd_en) begin
            exp_right_rd_data_reg <= exp_right[i_exp_right_rd_addr];
            `ifdef SIMULATION
            $display("[TILE_RD] @%0t exp_right[%0d] → 0x%02x",
                     $time, i_exp_right_rd_addr, exp_right[i_exp_right_rd_addr]);
            `endif
        end
    end
    assign o_exp_right_rd_data = exp_right_rd_data_reg;

endmodule
