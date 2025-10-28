// Simple working compute_engine stub for CSR bridge testing
module compute_engine
import gemm_pkg::*;
(
    // Clock and Reset
    input  logic        i_clk,
    input  logic        i_reset_n,

    // Master Control Interface (TILE command)
    input  logic                          i_tile_en,
    input  logic [tile_mem_addr_width_gp-1:0] i_left_addr,
    input  logic [tile_mem_addr_width_gp-1:0] i_right_addr,
    input  logic [tile_mem_addr_width_gp-1:0] i_left_ugd_len,
    input  logic [tile_mem_addr_width_gp-1:0] i_right_ugd_len,
    input  logic [tile_mem_addr_width_gp-1:0] i_vec_len,
    input  logic [7:0]                    i_dim_b,
    input  logic [7:0]                    i_dim_c,
    input  logic [7:0]                    i_dim_v,
    input  logic                          i_left_man_4b,
    input  logic                          i_right_man_4b,
    input  logic                          i_main_loop_over_left,
    output logic                          o_tile_done,

    // BRAM Read Interface
    output logic [10:0]                   o_bram_rd_addr,
    output logic                          o_bram_rd_en,
    input  logic [255:0]                  i_bram_rd_data,

    // Result FIFO Write Interface
    output logic [23:0]                   o_result_data,
    output logic                          o_result_valid,
    input  logic                          i_result_full,
    input  logic                          i_result_afull,

    // Debug Interface  
    output logic [3:0]                    o_ce_state
);

    // Simple FSM for testing
    typedef enum logic [3:0] {
        ST_IDLE = 4'd0,
        ST_ACTIVE = 4'd1,
        ST_DONE = 4'd2
    } ce_state_t;
    
    ce_state_t state_reg, state_next;
    
    // State machine - minimal implementation
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            state_reg <= ST_IDLE;
        end else begin
            state_reg <= state_next;
        end
    end
    
    always_comb begin
        state_next = state_reg;
        case (state_reg)
            ST_IDLE: begin
                if (i_tile_en) state_next = ST_ACTIVE;
            end
            ST_ACTIVE: begin
                state_next = ST_DONE;  // Complete immediately for testing
            end
            ST_DONE: begin
                state_next = ST_IDLE;
            end
        endcase
    end
    
    // Output assignments
    assign o_tile_done = (state_reg == ST_DONE);
    assign o_bram_rd_addr = 11'd0;
    assign o_bram_rd_en = 1'b0;
    assign o_result_data = 24'h0;
    assign o_result_valid = 1'b0;
    assign o_ce_state = state_reg;

endmodule