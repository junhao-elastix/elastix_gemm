// ------------------------------------------------------------------
// GFP8 BCV Loop Controller
//
// Purpose: Orchestrate BxCxV loops with direct tile_bram → MLP path
// Features:
//  - Direct combinational NV indexing
//  - 4-state FSM
//  - Pre-computed exponent operations
//
// State Machine:
//  IDLE      -> Wait for TILE command
//  COMPUTE_NV -> Direct MLP compute with tile_bram data
//  ACCUM     -> Accumulate into V-loop accumulator
//  RETURN    -> Output final result
//
// Author: Junhao Pan
// Date: 10/31/2025
// ------------------------------------------------------------------

module gfp8_bcv_controller (
    // Clock and Reset
    input  logic        i_clk,
    input  logic        i_reset_n,

    // TILE Command Interface
    input  logic        i_tile_en,
    input  logic [7:0]  i_dim_b,              // Output rows (batch)
    input  logic [7:0]  i_dim_c,              // Output columns
    input  logic [7:0]  i_dim_v,              // Inner dimension multiplier (V Native Vectors)
    input  logic [8:0]  i_left_base_addr,
    input  logic [8:0]  i_right_base_addr,
    output logic        o_tile_done,

    // Native Vector Read Interface (to tile_bram) - DIRECT PATH
    output logic [6:0]   o_nv_left_rd_idx,
    input  logic [31:0]  i_nv_left_exp,
    input  logic [255:0] i_nv_left_man [0:3],

    output logic [6:0]   o_nv_right_rd_idx,
    input  logic [31:0]  i_nv_right_exp,
    input  logic [255:0] i_nv_right_man [0:3],

    // Result Interface
    output logic signed [31:0] o_result_mantissa,
    output logic signed [7:0]  o_result_exponent,
    output logic               o_result_valid
);

    // ===================================================================
    // Optimized State Machine Definition (4 states instead of 6)
    // ===================================================================
    typedef enum logic [1:0] {
        ST_IDLE       = 2'd0,
        ST_COMPUTE_NV = 2'd1,  // Direct compute with tile_bram data
        ST_ACCUM      = 2'd2,  // Accumulate into V-loop accumulator
        ST_RETURN     = 2'd3   // Output final result
    } state_t;

    state_t state_reg, state_next;

    // ===================================================================
    // Loop Indices (B, C, V nested loops)
    // ===================================================================
    logic [7:0] b_idx;  // Batch index (0 to B-1)
    logic [7:0] c_idx;  // Column index (0 to C-1)
    logic [7:0] v_idx;  // Vector index (0 to V-1)

    // Dimension registers
    logic [7:0] dim_b_reg, dim_c_reg, dim_v_reg;
    logic [8:0] left_base_reg, right_base_reg;

    // Rising edge detection for i_tile_en
    logic i_tile_en_prev;
    logic i_tile_en_rising;

    assign i_tile_en_rising = i_tile_en && !i_tile_en_prev;

    // ===================================================================
    // OPTIMIZATION: Direct NV Index Generation (COMBINATIONAL)
    // No buffering needed - tile_bram provides stable combinational output
    // ===================================================================
    logic [6:0] left_base_nv, right_base_nv;
    logic [6:0] left_nv_index, right_nv_index;

    // Convert base addresses from line units to NV units (divide by 4)
    assign left_base_nv = left_base_reg[8:2];
    assign right_base_nv = right_base_reg[8:2];

    // Direct index calculation - always active for immediate response
    always_comb begin
        // Calculate NV indices based on current loop counters
        left_nv_index = left_base_nv + (b_idx * dim_v_reg + v_idx);
        right_nv_index = right_base_nv + (c_idx * dim_v_reg + v_idx);

        // Output indices directly to tile_bram (combinational read)
        o_nv_left_rd_idx = left_nv_index;
        o_nv_right_rd_idx = right_nv_index;
    end

    // ===================================================================
    // NV Dot Product Instance - Direct Connection to tile_bram
    // ===================================================================
    logic signed [31:0] nv_dot_mantissa;
    logic signed [7:0]  nv_dot_exponent;

    // Enable signal: pulse high on first cycle IN ST_COMPUTE_NV
    logic nv_dot_input_valid;
    assign nv_dot_input_valid = (state_reg == ST_COMPUTE_NV) && (compute_wait == 3'd0);

    // DIRECT PATH: tile_bram outputs → Ultra-optimized NV dot product (no capture!)
    gfp8_nv_dot u_nv_dot (
        .i_clk              (i_clk),
        .i_reset_n          (i_reset_n),
        .i_input_valid      (nv_dot_input_valid),
        // Direct connection to tile_bram outputs
        .i_exp_left         (i_nv_left_exp),     // Direct from tile_bram
        .i_man_left         (i_nv_left_man),     // Direct from tile_bram
        .i_exp_right        (i_nv_right_exp),    // Direct from tile_bram
        .i_man_right        (i_nv_right_man),    // Direct from tile_bram
        .o_result_mantissa  (nv_dot_mantissa),
        .o_result_exponent  (nv_dot_exponent)
    );

    // ===================================================================
    // V-Loop Accumulator
    // ===================================================================
    logic signed [31:0] accum_mantissa;
    logic signed [7:0]  accum_exponent;

    // Compute pipeline counter (track 4-cycle NV dot latency)
    logic [2:0] compute_wait;

    // ===================================================================
    // State Machine - Next State Logic (OPTIMIZED)
    // ===================================================================
    always_comb begin
        state_next = state_reg;

        case (state_reg)
            ST_IDLE: begin
                if (i_tile_en_rising) begin
                    // Skip FILL_BUFFER, go directly to compute
                    state_next = ST_COMPUTE_NV;
                end
            end

            ST_COMPUTE_NV: begin
                // Wait for 4-cycle gfp8_nv_dot pipeline
                if (compute_wait == 3'd2) begin
                    state_next = ST_ACCUM;
                end
            end

            ST_ACCUM: begin
                // Check if V loop is complete
                if (v_idx >= dim_v_reg - 1) begin
                    state_next = ST_RETURN;
                end else begin
                    // More V iterations - go directly to compute (no fill needed)
                    state_next = ST_COMPUTE_NV;
                end
            end

            ST_RETURN: begin
                // Check if all BxC outputs are complete
                if (c_idx >= dim_c_reg - 1 && b_idx >= dim_b_reg - 1) begin
                    state_next = ST_IDLE;  // All done, return to IDLE
                end else begin
                    // Start next output element - direct to compute
                    state_next = ST_COMPUTE_NV;
                end
            end

            default: state_next = ST_IDLE;
        endcase
    end

    // ===================================================================
    // State Machine - Sequential Logic
    // ===================================================================
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            state_reg <= ST_IDLE;
        end else begin
            state_reg <= state_next;
        end
    end

    // ===================================================================
    // Compute Pipeline Control (4 cycles for NV dot)
    // ===================================================================
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            compute_wait <= 3'd0;
        end else begin
            case (state_reg)
                ST_COMPUTE_NV: begin
                    if (compute_wait < 3'd2) begin
                        compute_wait <= compute_wait + 1;
                    end
                end
                default: begin
                    compute_wait <= 3'd0;
                end
            endcase
        end
    end

    // ===================================================================
    // V-Loop Accumulation (with Exponent Alignment)
    // ===================================================================
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            accum_mantissa <= 32'sd0;
            accum_exponent <= 8'sd0;
        end else begin
            case (state_reg)
                ST_IDLE: begin
                    accum_mantissa <= 32'sd0;
                    accum_exponent <= 8'sd0;
                end

                ST_ACCUM: begin
                    if (v_idx == 8'd0) begin
                        // First V iteration - initialize accumulator
                        accum_mantissa <= nv_dot_mantissa;
                        accum_exponent <= nv_dot_exponent;
                        `ifdef SIMULATION
                        $display("[BCV_OPT] @%0t [B%0d,C%0d] V=%0d INIT: mant=%0d, exp=%0d",
                                 $time, b_idx, c_idx, v_idx, nv_dot_mantissa, nv_dot_exponent);
                        `endif
                    end else begin
                        // Accumulate with exponent alignment
                        automatic logic signed [7:0] max_exp;
                        automatic logic [7:0] exp_diff_accum, exp_diff_dot;
                        automatic logic signed [31:0] aligned_accum, aligned_dot;
                        automatic logic signed [31:0] sum_mantissa;

                        // Find maximum exponent
                        max_exp = ($signed(accum_exponent) > $signed(nv_dot_exponent)) ?
                                  accum_exponent : nv_dot_exponent;

                        // Align mantissas to maximum exponent
                        exp_diff_accum = max_exp - accum_exponent;
                        exp_diff_dot = max_exp - nv_dot_exponent;

                        // Align with underflow check
                        aligned_accum = (exp_diff_accum > 31) ? 32'sd0 :
                                       ($signed(accum_mantissa) >>> exp_diff_accum);
                        aligned_dot = (exp_diff_dot > 31) ? 32'sd0 :
                                     ($signed(nv_dot_mantissa) >>> exp_diff_dot);

                        // Sum aligned mantissas
                        sum_mantissa = aligned_accum + aligned_dot;

                        // Update accumulator
                        accum_mantissa <= sum_mantissa;
                        accum_exponent <= max_exp;

                        `ifdef SIMULATION
                        $display("[BCV_OPT] @%0t [B%0d,C%0d] V=%0d ACCUM: sum=%0d, exp=%0d",
                                 $time, b_idx, c_idx, v_idx, sum_mantissa, max_exp);
                        `endif
                    end
                end

                ST_RETURN: begin
                    // Reset accumulator for next BxC output
                    accum_mantissa <= 32'sd0;
                    accum_exponent <= 8'sd0;
                end
            endcase
        end
    end

    // ===================================================================
    // Loop Index Control (B, C, V nested loops)
    // ===================================================================
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            b_idx <= 8'd0;
            c_idx <= 8'd0;
            v_idx <= 8'd0;
            dim_b_reg <= 8'd0;
            dim_c_reg <= 8'd0;
            dim_v_reg <= 8'd0;
            left_base_reg <= 9'd0;
            right_base_reg <= 9'd0;
            i_tile_en_prev <= 1'b0;
        end else begin
            // Update previous value for edge detection
            i_tile_en_prev <= i_tile_en;

            case (state_reg)
                ST_IDLE: begin
                    if (i_tile_en_rising) begin
                        // Capture dimensions
                        dim_b_reg <= i_dim_b;
                        dim_c_reg <= i_dim_c;
                        dim_v_reg <= i_dim_v;
                        left_base_reg <= i_left_base_addr;
                        right_base_reg <= i_right_base_addr;
                        // Initialize indices
                        b_idx <= 8'd0;
                        c_idx <= 8'd0;
                        v_idx <= 8'd0;
                        `ifdef SIMULATION
                        $display("[BCV_OPT] @%0t NEW TILE: B=%0d, C=%0d, V=%0d",
                                 $time, i_dim_b, i_dim_c, i_dim_v);
                        `endif
                    end
                end

                ST_ACCUM: begin
                    // Advance V index after accumulation
                    if (v_idx < dim_v_reg - 1) begin
                        v_idx <= v_idx + 1;
                        `ifdef SIMULATION
                        $display("[BCV_OPT] V advance: %0d -> %0d", v_idx, v_idx + 1);
                        `endif
                    end
                end

                ST_RETURN: begin
                    // V loop complete, advance C and B indices
                    v_idx <= 8'd0;  // Reset V for next (b,c) pair

                    // Only advance indices if NOT done with all outputs
                    if (!(c_idx >= dim_c_reg - 1 && b_idx >= dim_b_reg - 1)) begin
                        if (c_idx >= dim_c_reg - 1) begin
                            c_idx <= 8'd0;
                            b_idx <= b_idx + 1;
                        end else begin
                            c_idx <= c_idx + 1;
                        end
                    end
                end
            endcase
        end
    end

    // ===================================================================
    // Output Control
    // ===================================================================
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            o_result_mantissa <= 32'sd0;
            o_result_exponent <= 8'sd0;
            o_result_valid <= 1'b0;
            o_tile_done <= 1'b0;
        end else begin
            // Default
            o_result_valid <= 1'b0;
            o_tile_done <= 1'b0;

            case (state_reg)
                ST_RETURN: begin
                    // Output accumulated result for this (b,c) pair
                    o_result_mantissa <= accum_mantissa;
                    o_result_exponent <= accum_exponent;
                    o_result_valid <= 1'b1;

                    // Signal completion when returning to IDLE
                    if (state_next == ST_IDLE) begin
                        o_tile_done <= 1'b1;
                    end

                    `ifdef SIMULATION
                    $display("[BCV_OPT] @%0t [B%0d,C%0d] OUTPUT: mant=%0d, exp=%0d",
                             $time, b_idx, c_idx, accum_mantissa, accum_exponent);
                    `endif
                end
            endcase
        end
    end

endmodule