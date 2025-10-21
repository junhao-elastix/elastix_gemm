// Minimal simulation models for Achronix primitives
// This file provides simulation models for ACX_INT_MULT_ADD and its dependencies

`timescale 1ps/1ps

// ACX_INT_MULT_ADD - Behavioral simulation model
// This is a simplified simulation model for the ACX_INT_MULT_ADD primitive
module ACX_INT_MULT_ADD #(
    parameter  integer int_size = 8,        // number of bits (3..8, 16)
    parameter  integer num_mult = 1,        // number of multipliers
    parameter  logic   int_unsigned_a = 0,  // i_din_a is unsigned
    parameter  logic   int_unsigned_b = 0,  // i_din_b is unsigned
    parameter  logic   accumulate = 0,      // accumulator mode (uses i_load)
    parameter  logic   in_reg_enable = 0,   // enable input reg (uses i_in_reg_*_ce)
    parameter  integer pipeline_regs = 0,   // 0, 1, 2 pipeline stages
    parameter  integer dout_size = 48,      // output bits (<= 48)
    parameter  string  location = ""        // for manual placement
) (
    input  wire                           i_clk,
    input  wire [num_mult*int_size-1 : 0] i_din_a,
    input  wire [num_mult*int_size-1 : 0] i_din_b,
    input  wire                           i_in_reg_a_ce,
    input  wire                           i_in_reg_b_ce,
    input  wire                           i_in_reg_rstn,
    input  wire                           i_pipeline_ce,
    input  wire                           i_pipeline_rstn,
    input  wire                           i_load,
    output wire [dout_size-1 : 0]        o_dout
);

    // Simple behavioral model for simulation
    // Compute sum of products: SUM(a[i] * b[i])
    logic signed [dout_size-1:0] sum;
    
    always_comb begin
        sum = '0;
        for (int i = 0; i < num_mult; i++) begin
            logic signed [int_size-1:0] a, b;
            logic signed [2*int_size-1:0] product;
            
            // Extract elements
            a = int_unsigned_a ? $unsigned(i_din_a[i*int_size +: int_size]) : 
                                 $signed(i_din_a[i*int_size +: int_size]);
            b = int_unsigned_b ? $unsigned(i_din_b[i*int_size +: int_size]) : 
                                 $signed(i_din_b[i*int_size +: int_size]);
            
            // Compute product and accumulate
            product = a * b;
            sum = sum + product;
        end
    end
    
    assign o_dout = sum;

endmodule
