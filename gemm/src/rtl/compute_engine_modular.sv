// ------------------------------------------------------------------
// Modular Compute Engine with Integrated Tile BRAM (MS2.0)
//
// Purpose: Refactored GEMM compute engine with private L1 cache
// Architecture:
//  - tile_bram: Private L1 memory (4 separate buffers)
//  - gfp8_bcv_controller: BCV loop orchestration with dual BRAM reads
//  - gfp8_nv_dot: 128-element Native Vector dot product
//  - gfp8_group_dot: 32-element group dot product (4 instances)
//  - gfp8_to_fp16: GFP8 to IEEE 754 FP16 conversion
//
// Key Features:
//  - **Integrated tile_bram**: Private L1 cache per compute tile
//  - **DISPATCH write interface**: Exposes tile_bram write ports
//  - **Internal read connections**: tile_bram → bcv_controller
//  - V-loop accumulation with exponent alignment
//  - Runtime configurable dimensions (B, C, V)
//  - FP16 output
//
// Performance:
//  - Per V iteration: 15 cycles (11 fill + 3 compute + 1 accum)
//  - Total per output: 15xV + 1 cycles
//  - ~42% faster than single BRAM due to parallel reads
//
// Author: Modular refactoring + Tile BRAM integration
// Date: Mon Oct 27 2025
// ------------------------------------------------------------------

module compute_engine_modular
import gemm_pkg::*;
(
    // Clock and Reset
    input  logic        i_clk,
    input  logic        i_reset_n,

    // ====================================================================
    // Master Control Interface (TILE command)
    // Per SINGLE_ROW_REFERENCE.md specification
    // ====================================================================
    input  logic        i_tile_en,
    input  logic [15:0] i_tile_left_addr,      // 16 bits: Left matrix start address
    input  logic [15:0] i_tile_right_addr,     // 16 bits: Right matrix start address
    input  logic [7:0]  i_tile_left_ugd_len,   // 8 bits: Left UGD vectors (Batch dimension)
    input  logic [7:0]  i_tile_right_ugd_len,  // 8 bits: Right UGD vectors (Column dimension)
    input  logic [7:0]  i_tile_vec_len,        // 8 bits: UGD vector size (Vector count)
    input  logic        i_tile_left_man_4b,
    input  logic        i_tile_right_man_4b,
    input  logic        i_tile_main_loop_over_left,
    output logic        o_tile_done,

    // ====================================================================
    // Tile BRAM Write Interface (from dispatcher_control via DISPATCH)
    // Four parallel write ports - All can write in same cycle
    // Per SINGLE_ROW_REFERENCE.md: DISPATCH copies dispatcher_bram → tile_bram
    // ====================================================================
    // Left mantissa write port (addr, en, data order per BRAM standard)
    input  logic [8:0]    i_man_left_wr_addr,      // 9-bit: [0:511]
    input  logic          i_man_left_wr_en,
    input  logic [255:0]  i_man_left_wr_data,

    // Right mantissa write port (addr, en, data order per BRAM standard)
    input  logic [8:0]    i_man_right_wr_addr,     // 9-bit: [0:511]
    input  logic          i_man_right_wr_en,
    input  logic [255:0]  i_man_right_wr_data,

    // Left exponent write port (addr, en, data order per BRAM standard)
    input  logic [8:0]    i_left_exp_wr_addr,
    input  logic          i_left_exp_wr_en,
    input  logic [7:0]    i_left_exp_wr_data,

    // Right exponent write port (addr, en, data order per BRAM standard)
    input  logic [8:0]    i_right_exp_wr_addr,
    input  logic          i_right_exp_wr_en,
    input  logic [7:0]    i_right_exp_wr_data,

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
    // Internal Tile BRAM Read Signals (tile_bram → bcv_controller)
    // All four BRAMs have identical structure: 9-bit address + enable
    // ===================================================================
    logic [8:0]    tile_bram_left_rd_addr;
    logic [255:0]  tile_bram_left_rd_data;
    logic          tile_bram_left_rd_en;

    logic [8:0]    tile_bram_right_rd_addr;
    logic [255:0]  tile_bram_right_rd_data;
    logic          tile_bram_right_rd_en;

    logic [8:0]    tile_bram_left_exp_rd_addr;
    logic [7:0]    tile_bram_left_exp_rd_data;
    logic          tile_bram_left_exp_rd_en;

    logic [8:0]    tile_bram_right_exp_rd_addr;
    logic [7:0]    tile_bram_right_exp_rd_data;
    logic          tile_bram_right_exp_rd_en;

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
    // Tile BRAM Instance - Private L1 Cache
    // Per SINGLE_ROW_REFERENCE.md: Each compute tile has private tile_bram
    // ===================================================================
    tile_bram #(
        .MAN_WIDTH       (256),
        .EXP_WIDTH       (8),
        .BRAM_DEPTH      (512)    // 512 lines per side (left/right)
    ) u_tile_bram (
        .i_clk           (i_clk),
        .i_reset_n       (i_reset_n),

        // Write ports (from dispatcher_control via DISPATCH command)
        // Four parallel write paths - all can write in same cycle
        .i_man_left_wr_addr   (i_man_left_wr_addr),
        .i_man_left_wr_en     (i_man_left_wr_en),
        .i_man_left_wr_data   (i_man_left_wr_data),

        .i_man_right_wr_addr  (i_man_right_wr_addr),
        .i_man_right_wr_en    (i_man_right_wr_en),
        .i_man_right_wr_data  (i_man_right_wr_data),

        .i_exp_left_wr_addr   (i_left_exp_wr_addr),
        .i_exp_left_wr_en     (i_left_exp_wr_en),
        .i_exp_left_wr_data   (i_left_exp_wr_data),

        .i_exp_right_wr_addr  (i_right_exp_wr_addr),
        .i_exp_right_wr_en    (i_right_exp_wr_en),
        .i_exp_right_wr_data  (i_right_exp_wr_data),

        // Read ports (internal connection to bcv_controller)
        // Dual-port mantissa reads + exponent reads
        .i_man_left_rd_addr   (tile_bram_left_rd_addr),
        .o_man_left_rd_data   (tile_bram_left_rd_data),
        .i_man_left_rd_en     (tile_bram_left_rd_en),

        .i_man_right_rd_addr  (tile_bram_right_rd_addr),
        .o_man_right_rd_data  (tile_bram_right_rd_data),
        .i_man_right_rd_en    (tile_bram_right_rd_en),

        .i_exp_left_rd_addr   (tile_bram_left_exp_rd_addr),
        .o_exp_left_rd_data   (tile_bram_left_exp_rd_data),
        .i_exp_left_rd_en     (tile_bram_left_exp_rd_en),

        .i_exp_right_rd_addr  (tile_bram_right_exp_rd_addr),
        .o_exp_right_rd_data  (tile_bram_right_exp_rd_data),
        .i_exp_right_rd_en    (tile_bram_right_exp_rd_en)
    );

    // ===================================================================
    // State Machine
    // ===================================================================
    typedef enum logic [3:0] {
        ST_IDLE      = 4'd0,
        ST_COMP_BUSY = 4'd1,  // Compute engine busy (working state)
        ST_COMP_DONE = 4'd2   // Computation complete
    } state_t;

    state_t state_reg;

    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            state_reg <= ST_IDLE;
        end else begin
            case (state_reg)
                ST_IDLE: begin
                    if (i_tile_en) begin
                        state_reg <= ST_COMP_BUSY;
                        $display("[CE_DEBUG] @%t Tile command received: left_addr=%0d, right_addr=%0d, B=%0d, C=%0d, V=%0d",
                                 $time, i_tile_left_addr, i_tile_right_addr, i_tile_left_ugd_len, i_tile_right_ugd_len, i_tile_vec_len);
                    end
                end
                ST_COMP_BUSY: begin
                    if (bcv_tile_done) state_reg <= ST_COMP_DONE;
                end
                ST_COMP_DONE: begin
                    state_reg <= ST_IDLE;
                end
            endcase
        end
    end
    
    assign o_ce_state = state_reg;
    assign o_tile_done = bcv_tile_done;
    
    // ===================================================================
    // BCV Controller Instance - Reads from Internal Tile BRAM
    // ===================================================================
    gfp8_bcv_controller u_bcv_controller (
        .i_clk              (i_clk),
        .i_reset_n          (i_reset_n),

        // TILE command parameters
        .i_tile_en          (i_tile_en),
        .i_dim_b            (i_tile_left_ugd_len),   // Batch dimension (left UGD vectors)
        .i_dim_c            (i_tile_right_ugd_len),  // Column dimension (right UGD vectors)
        .i_dim_v            (i_tile_vec_len),        // Vector count (UGD vector size)
        .i_left_base_addr   (i_tile_left_addr),
        .i_right_base_addr  (i_tile_right_addr),
        .o_tile_done        (bcv_tile_done),

        // Dual BRAM mantissa interface - INTERNAL connection to tile_bram
        .o_man_left_rd_addr (tile_bram_left_rd_addr),
        .o_man_left_rd_en   (tile_bram_left_rd_en),
        .i_man_left_rd_data (tile_bram_left_rd_data),

        .o_man_right_rd_addr(tile_bram_right_rd_addr),
        .o_man_right_rd_en  (tile_bram_right_rd_en),
        .i_man_right_rd_data(tile_bram_right_rd_data),

        // Exponent interface - INTERNAL connection to tile_bram
        .o_exp_left_rd_addr (tile_bram_left_exp_rd_addr),
        .o_exp_left_rd_en   (tile_bram_left_exp_rd_en),
        .i_exp_left_rd_data (tile_bram_left_exp_rd_data),

        .o_exp_right_rd_addr(tile_bram_right_exp_rd_addr),
        .o_exp_right_rd_en  (tile_bram_right_exp_rd_en),
        .i_exp_right_rd_data(tile_bram_right_exp_rd_data),

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


