// ------------------------------------------------------------------
// Row BRAM Module with Native Vector Packing
//
// Purpose: L1 memory layer for ACTIVATIONS (left matrix) ONLY
//          Weights are stored directly in mlp_bram_col (external writes)
//
// Architecture:
//  - Storage: 128 Native Vectors (NVs) for activations
//  - Each NV contains:
//    - 4 mantissa groups (256-bit each)
//    - 1 packed exponent (32-bit with 4 bytes)
//
// Write Interface:
//  - Line-based writes with automatic NV packing
//  - TWO PARALLEL WRITE PORTS (left mantissa + left exponent)
//  - Writes are automatically packed into NV format internally
//
// Read Interface:
//  - Native Vector interface for single-cycle NV reads
//  - Combinational (0-latency) access to complete NVs
//
// REFACTORED: Jan 2026 - Removed right (weight) write/read ports
//             Weights now written directly to mlp_bram_col
//
// Original Author: Junhao Pan
// Date: 10/31/2024
// ------------------------------------------------------------------

`timescale 1ps / 1ps
`default_nettype none

module comp_row_bram #(
    parameter MAN_WIDTH = 256,          // Mantissa line width
    parameter EXP_WIDTH = 8,            // Exponent width
    parameter BRAM_DEPTH = 512,
    parameter ADDR_WIDTH = $clog2(BRAM_DEPTH)
)
(
    input  wire                      i_clk,
    input  wire                      i_reset_n,

    // ====================================================================
    // Write Ports (Activations ONLY - Left Side)
    // TWO PARALLEL WRITE PORTS - mantissa + exponent
    // ====================================================================
    // Left mantissa write port
    input  wire [ADDR_WIDTH-1:0]       i_man_left_wr_addr,
    input  wire                        i_man_left_wr_en,
    input  wire [MAN_WIDTH-1:0]        i_man_left_wr_data,

    // Left exponent write port
    input  wire [ADDR_WIDTH-1:0]       i_exp_left_wr_addr,
    input  wire                        i_exp_left_wr_en,
    input  wire [EXP_WIDTH-1:0]        i_exp_left_wr_data,

    // ====================================================================
    // Native Vector Read Interface (Activations ONLY - Left Side)
    // Combinational reads - complete NV in single cycle
    // ====================================================================
    input  wire [6:0]                  i_nv_left_rd_idx,
    output wire [31:0]                 o_nv_left_exp,         // Packed exponents
    output wire [MAN_WIDTH-1:0]        o_nv_left_man [0:3]    // 4 mantissa groups
);

    // ===================================================================
    // NV-PACKED STORAGE (128 Native Vectors for activations)
    // ===================================================================
    (* ram_style = "block" *) reg [MAN_WIDTH-1:0] nv_man_left [0:127][0:3];
    (* ram_style = "block" *) reg [31:0]          nv_exp_left [0:127];       // 128 NVs x packed exp

    // ===================================================================
    // SIMULATION NOTE: Memory initialization
    // ===================================================================
    // Zero-initialize for simulation (prevents X/Z values)
    integer i, j;
    initial begin
        for (i = 0; i < 128; i = i + 1) begin
            for (j = 0; j < 4; j = j + 1) begin
                nv_man_left[i][j] = {MAN_WIDTH{1'b0}};
            end
            nv_exp_left[i] = 32'b0;
        end
    end

    // ===================================================================
    // WRITE LOGIC - Pack line-based writes into NV format
    // ===================================================================
    // Left mantissa write - pack into NV format
    always @(posedge i_clk) begin
        if (i_man_left_wr_en) begin
            // Calculate NV index and group within NV
            // NV index (addr/4), Group within NV [0-3]
            nv_man_left[i_man_left_wr_addr[8:2]][i_man_left_wr_addr[1:0]] <= i_man_left_wr_data;
        end
    end

    // ===================================================================
    // WRITE LOGIC - EXPONENTS (packed into 32-bit words)
    // ===================================================================
    always @(posedge i_clk) begin
        if (i_exp_left_wr_en) begin
            // Pack exponent into correct byte position in 32-bit word
            case (i_exp_left_wr_addr[1:0])
                2'd0: nv_exp_left[i_exp_left_wr_addr[8:2]][7:0]   <= i_exp_left_wr_data;
                2'd1: nv_exp_left[i_exp_left_wr_addr[8:2]][15:8]  <= i_exp_left_wr_data;
                2'd2: nv_exp_left[i_exp_left_wr_addr[8:2]][23:16] <= i_exp_left_wr_data;
                2'd3: nv_exp_left[i_exp_left_wr_addr[8:2]][31:24] <= i_exp_left_wr_data;
            endcase
        end
    end

    // ===================================================================
    // NV READ LOGIC - Combinational (0-latency)
    // ===================================================================
    // Left NV read - output complete Native Vector
    assign o_nv_left_exp = nv_exp_left[i_nv_left_rd_idx];
    assign o_nv_left_man[0] = nv_man_left[i_nv_left_rd_idx][0];
    assign o_nv_left_man[1] = nv_man_left[i_nv_left_rd_idx][1];
    assign o_nv_left_man[2] = nv_man_left[i_nv_left_rd_idx][2];
    assign o_nv_left_man[3] = nv_man_left[i_nv_left_rd_idx][3];

endmodule

`default_nettype wire
