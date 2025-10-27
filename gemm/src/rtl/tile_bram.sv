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
    parameter DATA_WIDTH = 256,       // Mantissa line width
    parameter MANTISSA_DEPTH = 512,   // 512 lines per side
    parameter EXP_DEPTH = 512         // 512 exponents per side
)
(
    input  logic                     i_clk,
    input  logic                     i_reset_n,

    // ====================================================================
    // Write Ports 
    // FOUR PARALLEL WRITE PORTS - All can write in same cycle
    // ====================================================================
    // Left mantissa write port
    input  logic [8:0]               i_man_left_wr_addr,      // 9-bit: [0:511]
    input  logic [DATA_WIDTH-1:0]    i_man_left_wr_data,
    input  logic                     i_man_left_wr_en,

    // Right mantissa write port
    input  logic [8:0]               i_man_right_wr_addr,     // 9-bit: [0:511]
    input  logic [DATA_WIDTH-1:0]    i_man_right_wr_data,
    input  logic                     i_man_right_wr_en,

    // Left exponent write port
    input  logic [8:0]               i_left_exp_wr_addr,
    input  logic [7:0]               i_left_exp_wr_data,
    input  logic                     i_left_exp_wr_en,

    // Right exponent write port
    input  logic [8:0]               i_right_exp_wr_addr,
    input  logic [7:0]               i_right_exp_wr_data,
    input  logic                     i_right_exp_wr_en,

    // ====================================================================
    // Dual Read Ports (for compute_engine)
    // ====================================================================
    // Left matrix mantissa read
    input  logic [10:0]              i_left_man_rd_addr,  // 11-bit for compute engine
    output logic [DATA_WIDTH-1:0]    o_left_man_rd_data,
    input  logic                     i_left_man_rd_en,

    // Right matrix mantissa read
    input  logic [10:0]              i_right_man_rd_addr, // 11-bit for compute engine
    output logic [DATA_WIDTH-1:0]    o_right_man_rd_data,
    input  logic                     i_right_man_rd_en,

    // Left exponent read
    input  logic [8:0]               i_left_exp_rd_addr,
    output logic [7:0]               o_left_exp_rd_data,

    // Right exponent read
    input  logic [8:0]               i_right_exp_rd_addr,
    output logic [7:0]               o_right_exp_rd_data
);

    // ===================================================================
    // LEFT SIDE BUFFERS
    // ===================================================================
    logic [DATA_WIDTH-1:0] man_left [0:MANTISSA_DEPTH-1];   // 512 lines
    logic [7:0] exp_left [0:EXP_DEPTH-1];                   // 512 entries

    // ===================================================================
    // RIGHT SIDE BUFFERS
    // ===================================================================
    logic [DATA_WIDTH-1:0] man_right [0:MANTISSA_DEPTH-1];  // 512 lines
    logic [7:0] exp_right [0:EXP_DEPTH-1];                  // 512 entries

    // ===================================================================
    // SIMULATION INITIALIZATION (prevent X-states)
    // ===================================================================
    `ifdef SIMULATION
    integer init_i;
    initial begin
        for (init_i = 0; init_i < MANTISSA_DEPTH; init_i = init_i + 1) begin
            man_left[init_i] = '0;
            man_right[init_i] = '0;
        end
        for (init_i = 0; init_i < EXP_DEPTH; init_i = init_i + 1) begin
            exp_left[init_i] = '0;
            exp_right[init_i] = '0;
        end
    end
    `endif

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
        if (i_left_exp_wr_en) begin
            exp_left[i_left_exp_wr_addr] <= i_left_exp_wr_data;
        end
        if (i_right_exp_wr_en) begin
            exp_right[i_right_exp_wr_addr] <= i_right_exp_wr_data;
        end
    end

    // ===================================================================
    // READ LOGIC - MANTISSAS (Dual-Port)
    // ===================================================================
    logic [DATA_WIDTH-1:0] left_man_rd_data_reg;
    logic [DATA_WIDTH-1:0] right_man_rd_data_reg;

    // Left mantissa read (registered)
    always_ff @(posedge i_clk) begin
        if (i_left_man_rd_en) begin
            left_man_rd_data_reg <= man_left[i_left_man_rd_addr[8:0]];  // Use lower 9 bits
            `ifdef SIMULATION
            $display("[TILE_RD] @%0t man_left[%0d] → 0x%064x",
                     $time, i_left_man_rd_addr[8:0], man_left[i_left_man_rd_addr[8:0]]);
            `endif
        end
    end
    assign o_left_man_rd_data = left_man_rd_data_reg;

    // Right mantissa read (registered)
    always_ff @(posedge i_clk) begin
        if (i_right_man_rd_en) begin
            right_man_rd_data_reg <= man_right[i_right_man_rd_addr[8:0]];  // Use lower 9 bits
            `ifdef SIMULATION
            $display("[TILE_RD] @%0t man_right[%0d] → 0x%064x",
                     $time, i_right_man_rd_addr[8:0], man_right[i_right_man_rd_addr[8:0]]);
            `endif
        end
    end
    assign o_right_man_rd_data = right_man_rd_data_reg;

    // ===================================================================
    // READ LOGIC - EXPONENTS
    // ===================================================================
    logic [7:0] left_exp_rd_data_reg;
    logic [7:0] right_exp_rd_data_reg;

    // Left exponent read (registered)
    always_ff @(posedge i_clk) begin
        left_exp_rd_data_reg <= exp_left[i_left_exp_rd_addr];
    end
    assign o_left_exp_rd_data = left_exp_rd_data_reg;

    // Right exponent read (registered)
    always_ff @(posedge i_clk) begin
        right_exp_rd_data_reg <= exp_right[i_right_exp_rd_addr];
    end
    assign o_right_exp_rd_data = right_exp_rd_data_reg;

endmodule
