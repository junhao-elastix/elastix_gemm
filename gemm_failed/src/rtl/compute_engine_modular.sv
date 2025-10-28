// ------------------------------------------------------------------
// Modular Compute Engine with Dual BRAM Interface (MS2.0)
//
// Purpose: Refactored GEMM compute engine using hierarchical modules
// Architecture:
//  - gfp8_bcv_controller: BCV loop orchestration with dual BRAM reads
//  - gfp8_nv_dot: 128-element Native Vector dot product
//  - gfp8_group_dot: 32-element group dot product (4 instances)
//  - gfp8_to_fp16: GFP8 to IEEE 754 FP16 conversion
//
// Key Features:
//  - **Dual BRAM read interface**: Parallel reads from left/right BRAMs
//  - V-loop accumulation with exponent alignment
//  - Runtime configurable dimensions (B, C, V)
//  - FP16 output (converted to FP24 for compatibility)
//
// Performance:
//  - Per V iteration: 15 cycles (11 fill + 3 compute + 1 accum)
//  - Total per output: 15×V + 1 cycles
//  - ~42% faster than single BRAM due to parallel reads
//
// Author: Modular refactoring
// Date: Thu Oct 9 23:20 PDT 2025
// ------------------------------------------------------------------

module compute_engine_modular
import gemm_pkg::*;
(
    // Clock and Reset
    input  logic        i_clk,
    input  logic        i_reset_n,

    // ====================================================================
    // Master Control Interface (TILE command)
    // ====================================================================
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

    // ====================================================================
    // Dual BRAM Mantissa Read Interface (from tile_bram - 512 entries, 9-bit addr)
    // ====================================================================
    output logic [8:0]                    o_bram_left_rd_addr,
    input  logic [255:0]                  i_bram_left_rd_data,
    output logic                          o_bram_left_rd_en,

    output logic [8:0]                    o_bram_right_rd_addr,
    input  logic [255:0]                  i_bram_right_rd_data,
    output logic                          o_bram_right_rd_en,
    
    // ====================================================================
    // NEW: Exponent Read Interface (from dispatcher_bram exp ports)
    // ====================================================================
    output logic [8:0]                    o_left_exp_rd_addr,
    input  logic [7:0]                    i_left_exp_rd_data,
    
    output logic [8:0]                    o_right_exp_rd_addr,
    input  logic [7:0]                    i_right_exp_rd_data,

    // ====================================================================
    // Result FIFO Write Interface
    // ====================================================================
    output logic [15:0]                   o_result_data,     // FP16 format
    output logic                          o_result_valid,
    input  logic                          i_result_full,
    input  logic                          i_result_afull,

    // ====================================================================
    // Debug Interface
    // ====================================================================
    output logic [3:0]                    o_ce_state,
    output logic [15:0]                   o_result_count
);

    // ===================================================================
    // BCV Controller Signals
    // ===================================================================
    logic signed [31:0] bcv_result_mantissa;
    logic signed [7:0]  bcv_result_exponent;
    logic               bcv_result_valid;
    logic               bcv_tile_done;
    
    // ===================================================================
    // FP16 Converter Signals
    // ===================================================================
    logic [15:0] fp16_result;
    logic        fp16_valid;
    
    // ===================================================================
    // Result Counter
    // ===================================================================
    logic [15:0] result_count;
    
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            result_count <= 16'd0;
        end else if (i_tile_en) begin
            result_count <= 16'd0;
        end else if (o_result_valid && !i_result_afull) begin
            result_count <= result_count + 1;
        end
    end
    
    assign o_result_count = result_count;
    
    // ===================================================================
    // State Machine for Debug
    // ===================================================================
    typedef enum logic [3:0] {
        ST_IDLE    = 4'd0,
        ST_RUNNING = 4'd1,
        ST_DONE    = 4'd2
    } state_t;
    
    state_t state_reg;
    
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            state_reg <= ST_IDLE;
        end else begin
            case (state_reg)
                ST_IDLE: begin
                    if (i_tile_en) begin
                        state_reg <= ST_RUNNING;
                        $display("[CE_DEBUG] @%t Tile command received: left_addr=%0d, right_addr=%0d, B=%0d, C=%0d, V=%0d",
                                 $time, i_left_addr, i_right_addr, i_dim_b, i_dim_c, i_dim_v);
                    end
                end
                ST_RUNNING: begin
                    if (bcv_tile_done) state_reg <= ST_DONE;
                end
                ST_DONE: begin
                    state_reg <= ST_IDLE;
                end
            endcase
        end
    end
    
    assign o_ce_state = state_reg;
    assign o_tile_done = bcv_tile_done;
    
    // ===================================================================
    // BCV Controller Instance
    // ===================================================================
    gfp8_bcv_controller u_bcv_controller (
        .i_clk              (i_clk),
        .i_reset_n          (i_reset_n),
        
        // TILE command
        .i_tile_en          (i_tile_en),
        .i_dim_b            (i_dim_b),
        .i_dim_c            (i_dim_c),
        .i_dim_v            (i_dim_v),
        .i_left_base_addr   (i_left_addr),
        .i_right_base_addr  (i_right_addr),
        .o_tile_done        (bcv_tile_done),
        
        // Dual BRAM mantissa interface - parallel reads
        .o_mem_left_rd_addr (o_bram_left_rd_addr),
        .o_mem_left_rd_en   (o_bram_left_rd_en),
        .i_mem_left_rd_data (i_bram_left_rd_data),
        
        .o_mem_right_rd_addr(o_bram_right_rd_addr),
        .o_mem_right_rd_en  (o_bram_right_rd_en),
        .i_mem_right_rd_data(i_bram_right_rd_data),
        
        // NEW: Exponent interface - separate read ports
        .o_left_exp_rd_addr (o_left_exp_rd_addr),
        .i_left_exp_rd_data (i_left_exp_rd_data),
        
        .o_right_exp_rd_addr(o_right_exp_rd_addr),
        .i_right_exp_rd_data(i_right_exp_rd_data),
        
        // GFP8 result
        .o_result_mantissa  (bcv_result_mantissa),
        .o_result_exponent  (bcv_result_exponent),
        .o_result_valid     (bcv_result_valid)
    );
    
    // ===================================================================
    // GFP8 to FP16 Converter Instance
    // ===================================================================
    gfp8_to_fp16 u_fp16_converter (
        .i_clk              (i_clk),
        .i_reset_n          (i_reset_n),
        
        // GFP8 input
        .i_gfp_mantissa     (bcv_result_mantissa),
        .i_gfp_exponent     (bcv_result_exponent),
        .i_valid            (bcv_result_valid),
        
        // FP16 output (registered, 1-cycle latency)
        .o_fp16_result      (fp16_result),
        .o_valid            (fp16_valid)
    );
    
    // ===================================================================
    // Output Control - Direct FP16 Output
    // ===================================================================
    // No conversion needed - output FP16 directly
    // FP16 format: [sign(1)][exponent(5)][mantissa(10)]
    
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            o_result_data <= 16'd0;
            o_result_valid <= 1'b0;
        end else begin
            if (fp16_valid && !i_result_afull) begin
                o_result_data <= fp16_result;  // Direct FP16 output
                o_result_valid <= 1'b1;
                $display("[CE_RESULT] @%t Result valid: fp16_result=0x%04x, result_count=%0d", 
                         $time, fp16_result, result_count);
            end else begin
                o_result_valid <= 1'b0;
            end
        end
    end

endmodule


