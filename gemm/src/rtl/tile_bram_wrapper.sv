// ------------------------------------------------------------------
// Tile BRAM Wrapper - Private L1 Cache for Each Compute Tile
//
// Purpose: Dual-port BRAM for per-tile matrix storage (single_row architecture)
// Features:
//  - Mantissa BRAM: Port A (Write) / Port B (Read)
//  - Exponent BRAM: Separate 512×8-bit storage for per-group exponents
//  - Depth: 512 lines/entries (128 Native Vectors × 4 lines/NV)
//  - Mantissa Width: 256 bits/line (32 bytes)
//  - Exponent Width: 8 bits/entry
//
// Memory Organization:
//  - Each Native Vector (NV) = 4 groups × 32 GFP8 values = 128 values
//  - Each NV occupies 4 consecutive mantissa lines + 4 exponent entries
//  - Mantissas: line[N], line[N+1], line[N+2], line[N+3]
//  - Exponents: exp[N×4+0], exp[N×4+1], exp[N×4+2], exp[N×4+3]
//  - Total capacity: 128 NVs = 512 mantissa lines + 512 exponent entries
//
// Usage:
//  tile_bram_left:  Holds activations (broadcast from dispatcher)
//  tile_bram_right: Holds weights (distributed from dispatcher)
//
// Author: Single_Row Multi-Tile Architecture Migration
// Date: Mon Oct 20 2025
// ------------------------------------------------------------------

module tile_bram_wrapper #(
    parameter DEPTH = 512,          // 512 lines/entries (128 NVs × 4 lines/NV)
    parameter WIDTH = 256,          // 256 bits per mantissa line
    parameter ADDR_WIDTH = $clog2(DEPTH)  // 9 bits for 512 depth
) (
    input  logic                    i_clk,
    input  logic                    i_reset_n,

    // ====================================================================
    // Mantissa Port A: Write Interface (from dispatcher_control)
    // ====================================================================
    input  logic [ADDR_WIDTH-1:0]   i_man_wr_addr,      // Write address [8:0]
    input  logic [WIDTH-1:0]        i_man_wr_data,      // Write data [255:0]
    input  logic                    i_man_wr_en,        // Write enable

    // ====================================================================
    // Mantissa Port B: Read Interface (to compute_engine_modular)
    // ====================================================================
    input  logic [ADDR_WIDTH-1:0]   i_man_rd_addr,      // Read address [8:0]
    output logic [WIDTH-1:0]        o_man_rd_data,      // Read data [255:0]
    input  logic                    i_man_rd_en,        // Read enable

    // ====================================================================
    // Exponent Write Interface (from dispatcher_control during DISPATCH)
    // ====================================================================
    input  logic [ADDR_WIDTH-1:0]   i_exp_wr_addr,      // Write address [8:0]
    input  logic [7:0]              i_exp_wr_data,      // Write data [7:0]
    input  logic                    i_exp_wr_en,        // Write enable

    // ====================================================================
    // Exponent Read Interface (to compute_engine_modular)
    // ====================================================================
    input  logic [ADDR_WIDTH-1:0]   i_exp_rd_addr,      // Read address [8:0]
    output logic [7:0]              o_exp_rd_data       // Read data [7:0]
);

    // ===================================================================
    // Mantissa BRAM (Dual-Port)
    // ===================================================================
    // Port A: 256-bit write (32 bytes)
    // Port B: 256-bit read (32 bytes)
    // Total capacity: 512 × 256 bits = 16 KB

    logic [WIDTH-1:0] mantissa_mem [0:DEPTH-1];

    // Mantissa Port A: Write
    always_ff @(posedge i_clk) begin
        if (i_man_wr_en) begin
            mantissa_mem[i_man_wr_addr] <= i_man_wr_data;
        end
    end

    // Mantissa Port B: Read (registered output for better timing)
    always_ff @(posedge i_clk) begin
        if (!i_reset_n) begin
            o_man_rd_data <= '0;
        end else if (i_man_rd_en) begin
            o_man_rd_data <= mantissa_mem[i_man_rd_addr];
        end
    end

    // ===================================================================
    // Exponent BRAM (Dual-Port)
    // ===================================================================
    // Port A: 8-bit write
    // Port B: 8-bit read
    // Total capacity: 512 × 8 bits = 512 bytes

    logic [7:0] exponent_mem [0:DEPTH-1];

    // Exponent Port A: Write
    always_ff @(posedge i_clk) begin
        if (i_exp_wr_en) begin
            exponent_mem[i_exp_wr_addr] <= i_exp_wr_data;
        end
    end

    // Exponent Port B: Read (registered output)
    always_ff @(posedge i_clk) begin
        if (!i_reset_n) begin
            o_exp_rd_data <= '0;
        end else begin
            o_exp_rd_data <= exponent_mem[i_exp_rd_addr];
        end
    end

    `ifdef SIMULATION
    // Debug: Monitor BRAM accesses
    always_ff @(posedge i_clk) begin
        if (i_man_wr_en) begin
            $display("[TILE_BRAM_MAN_WR] @%0t addr=0x%03x data=0x%064x",
                     $time, i_man_wr_addr, i_man_wr_data);
        end
        if (i_man_rd_en) begin
            $display("[TILE_BRAM_MAN_RD] @%0t addr=0x%03x data=0x%064x",
                     $time, i_man_rd_addr, mantissa_mem[i_man_rd_addr]);
        end
        if (i_exp_wr_en) begin
            $display("[TILE_BRAM_EXP_WR] @%0t addr=0x%03x data=0x%02x",
                     $time, i_exp_wr_addr, i_exp_wr_data);
        end
    end
    `endif

endmodule
