// Wrapper module to select between different BCV controller implementations
// Use +define+USE_FLAT_BCV or +define+USE_PINGPONG_BCV at compile time

module gfp8_bcv_controller #(
    parameter NV_WIDTH = 128
)(
    input  logic        i_clk,
    input  logic        i_reset_n,
    
    // TILE Command Interface
    input  logic        i_tile_en,
    input  logic [7:0]  i_dim_b,
    input  logic [7:0]  i_dim_c,
    input  logic [7:0]  i_dim_v,
    input  logic [8:0]  i_left_base_addr,
    input  logic [8:0]  i_right_base_addr,
    output logic        o_tile_done,

    // BRAM Mantissa Read Interface
    output logic [8:0]   o_man_left_rd_addr,
    output logic         o_man_left_rd_en,
    input  logic [255:0] i_man_left_rd_data,
    output logic [8:0]   o_man_right_rd_addr,
    output logic         o_man_right_rd_en,
    input  logic [255:0] i_man_right_rd_data,

    // Exponent Read Interface
    output logic [8:0]   o_exp_left_rd_addr,
    output logic         o_exp_left_rd_en,
    input  logic [7:0]   i_exp_left_rd_data,
    output logic [8:0]   o_exp_right_rd_addr,
    output logic         o_exp_right_rd_en,
    input  logic [7:0]   i_exp_right_rd_data,

    // Output Result Interface
    output logic signed [31:0] o_result_mantissa,
    output logic signed [7:0]  o_result_exponent,
    output logic               o_result_valid
);

`ifdef USE_FLAT_BCV
    // Use flattened loop implementation
    gfp8_bcv_controller_pingpong_flat #(.NV_WIDTH(NV_WIDTH)) u_controller (.*);
`elsif USE_PINGPONG_BCV
    // Use ping-pong v2 implementation
    gfp8_bcv_controller_pingpong_v2 #(.NV_WIDTH(NV_WIDTH)) u_controller (.*);
`else
    // Default: use original single-FSM implementation
    gfp8_bcv_controller_single_fsm_backup #(.NV_WIDTH(NV_WIDTH)) u_controller (.*);
`endif

endmodule


























