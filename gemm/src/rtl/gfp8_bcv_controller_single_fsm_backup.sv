// ------------------------------------------------------------------
// GFP8 BCV Loop Controller
//
// Purpose: Orchestrate BxCxV nested loops for matrix multiplication
// Algorithm: For each (b,c): accumulate V Native Vector dot products
//
// Matrix Dimensions:
//  - Matrix A (left): B rows x (128xV) columns -> uses BxV Native Vectors
//  - Matrix B (right): (128xV) rows x C columns -> uses CxV Native Vectors
//  - Output: B x C results (one per (b,c) pair)
//
// State Machine:
//  IDLE         -> Wait for TILE command
//  FILL_BUFFER  -> Load 4 groups (exp+man) for both NV_left and NV_right (5 cycles)
//                  TRUE 1-cycle BRAM latency: Combinational addr → BRAM → registered output
//                  Sets ready flag on cycle 4, transitions on cycle 5
//  COMPUTE_NV   -> Compute NV dot product (4 cycles)  
//  ACCUM        -> Accumulate result into V-loop accumulator (1 cycle)
//  RETURN       -> Output final result after V iterations complete (1 cycle)
//
// Latency per output: 5 (fill) + 4 (compute) + 1 (accum) = 10 cycles per V
//                     Total: 10xV + 1 (return) cycles per BxC result
//
// OPTIMIZATION: Direct combinational connection (no BCV output registers!)
//   Cycle 0 (IDLE→FILL): Issue G0 read → Cycle 1: Capture G0, Issue G1 → ...
//   Cycle 4: Capture G3, set ready flag → Cycle 5: Transition on flag
//
// Author: Refactoring from compute_engine.sv
// Date: Fri Oct 10 2025
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
    input  logic [8:0]  i_left_base_addr,     // Base address for left matrix in tile_bram (9-bit for 512 lines)
    input  logic [8:0]  i_right_base_addr,    // Base address for right matrix in tile_bram (9-bit for 512 lines)
    output logic        o_tile_done,

    // BRAM Mantissa Read Interface (to tile_bram - 512 lines = 9-bit address)
    output logic [8:0]   o_man_left_rd_addr,
    output logic         o_man_left_rd_en,
    input  logic [255:0] i_man_left_rd_data,

    output logic [8:0]   o_man_right_rd_addr,
    output logic         o_man_right_rd_en,
    input  logic [255:0] i_man_right_rd_data,

    // Exponent Read Interface (to dispatcher_bram exp ports)
    output logic [8:0]   o_exp_left_rd_addr,
    output logic         o_exp_left_rd_en,
    input  logic [7:0]   i_exp_left_rd_data,

    output logic [8:0]   o_exp_right_rd_addr,
    output logic         o_exp_right_rd_en,
    input  logic [7:0]   i_exp_right_rd_data,
    
    // Result Interface
    output logic signed [31:0] o_result_mantissa,
    output logic signed [7:0]  o_result_exponent,
    output logic               o_result_valid
);

    // ===================================================================
    // State Machine Definition
    // ===================================================================
    typedef enum logic [2:0] {
        ST_IDLE        = 3'd0,
        ST_FILL_BUFFER = 3'd1,  // Load both NV_left and NV_right (4 cycles)
        ST_COMPUTE_NV  = 3'd2,  // Compute NV dot product (2 cycles)
        ST_ACCUM       = 3'd3,  // Accumulate into V-loop accumulator
        ST_RETURN      = 3'd4,  // Output final result
        ST_DONE        = 3'd5
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
    logic [8:0] left_base_reg, right_base_reg;  // 9-bit for 512-line tile_bram
    
    // Rising edge detection for i_tile_en
    logic i_tile_en_prev;
    logic i_tile_en_rising;
    
    assign i_tile_en_rising = i_tile_en && !i_tile_en_prev;
    
    // Fill buffer ready flag (set when last group captured)
    logic fill_buffer_ready;
    
    // ===================================================================
    // Native Vector Buffers (Local Storage)
    // ===================================================================
    
    // NV_left buffer
    logic [31:0]  nv_left_exp;         // 4 bytes (one per group)
    logic [255:0] nv_left_man [0:3];   // 4 lines x 256 bits
    
    // NV_right buffer
    logic [31:0]  nv_right_exp;        // 4 bytes (one per group)
    logic [255:0] nv_right_man [0:3];  // 4 lines x 256 bits
    
    // Fill cycle counter (0-4: TRUE 1-cycle latency, 4 groups + 1 final cycle)
    logic [2:0] fill_cycle;  // 3 bits to count 0-7
    
    // ===================================================================
    // NV Dot Product Instance
    // ===================================================================
    logic signed [31:0] nv_dot_mantissa;
    logic signed [7:0]  nv_dot_exponent;
    
    // Enable signal: pulse high when entering ST_COMPUTE_NV
    logic nv_dot_input_valid;
    assign nv_dot_input_valid = (state_reg != ST_COMPUTE_NV) && (state_next == ST_COMPUTE_NV);
    
    gfp8_nv_dot u_nv_dot (
        .i_clk              (i_clk),
        .i_reset_n          (i_reset_n),
        .i_input_valid      (nv_dot_input_valid),  // Latch inputs only when entering COMPUTE
        .i_exp_left         (nv_left_exp),
        .i_man_left         (nv_left_man),
        .i_exp_right        (nv_right_exp),
        .i_man_right        (nv_right_man),
        .o_result_mantissa  (nv_dot_mantissa),
        .o_result_exponent  (nv_dot_exponent)
    );
    
    // ===================================================================
    // V-Loop Accumulator
    // ===================================================================
    logic signed [31:0] accum_mantissa;
    logic signed [7:0]  accum_exponent;
    
    // Compute pipeline counter (track 4-cycle latency)
    logic [2:0] compute_wait;
    
    // ===================================================================
    // State Machine - Next State Logic
    // ===================================================================
    always_comb begin
        state_next = state_reg;
        
        case (state_reg)
            ST_IDLE: begin
                if (i_tile_en_rising) begin
                    state_next = ST_FILL_BUFFER;
                end
            end
            
            ST_FILL_BUFFER: begin
                // TRUE 1-cycle BRAM latency (combinational BCV outputs)
                // Cycle 0: Issue G0 | Cycle 1: Capture G0, Issue G1
                // Cycle 2: Capture G1, Issue G2 | Cycle 3: Capture G2, Issue G3
                // Cycle 4: Capture G3, set ready flag
                // Cycle 5: Transition on ready flag
                if (fill_buffer_ready) begin
                    state_next = ST_COMPUTE_NV;
                end
            end
            
            ST_COMPUTE_NV: begin
                // Wait for gfp8_nv_dot 4-cycle pipeline
                if (compute_wait == 3'd3) begin
                    state_next = ST_ACCUM;
                end
            end
            
            ST_ACCUM: begin
                // Check if V loop is complete
                if (v_idx >= dim_v_reg - 1) begin
                    state_next = ST_RETURN;
                end else begin
                    // More V iterations needed
                    state_next = ST_FILL_BUFFER;
                end
            end
            
            ST_RETURN: begin
                // Check if all BxC outputs are complete
                if (c_idx >= dim_c_reg - 1 && b_idx >= dim_b_reg - 1) begin
                    state_next = ST_DONE;
                end else begin
                    // Start next output element (next b,c pair)
                    state_next = ST_FILL_BUFFER;
                end
            end
            
            ST_DONE: begin
                state_next = ST_IDLE;
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
    // BRAM Read Address Generation - DIRECT (COMBINATIONAL) CONNECTION
    // ===================================================================
    // TRUE 1-cycle latency: Address generated combinationally, data back next cycle
    // No registered outputs - direct wire connection to tile_bram
    //
    // Pipeline:
    //   Cycle N:   Generate address (comb) → BRAM input
    //   Cycle N+1: BRAM output ready → Capture data, generate next address
    
    always_comb begin
        // Default: no reads
        o_man_left_rd_addr = 9'd0;
        o_man_right_rd_addr = 9'd0;
        o_exp_left_rd_addr = 9'd0;
        o_exp_right_rd_addr = 9'd0;
        o_man_left_rd_en = 1'b0;
        o_man_right_rd_en = 1'b0;
        o_exp_left_rd_en = 1'b0;
        o_exp_right_rd_en = 1'b0;
        
        if (state_reg == ST_FILL_BUFFER && fill_cycle < 4'd4) begin
            // Calculate NV indices
            automatic logic [15:0] left_nv_index;
            automatic logic [15:0] right_nv_index;
            automatic logic [15:0] left_base_nv;
            automatic logic [15:0] right_base_nv;
            automatic logic [8:0] left_line_addr;
            automatic logic [8:0] right_line_addr;
            
            // Convert base addresses from line units to NV units (divide by 4)
            left_base_nv = {9'd0, left_base_reg[8:2]};
            right_base_nv = {9'd0, right_base_reg[8:2]};
            
            // Calculate NV index based on loop counters
            left_nv_index = left_base_nv + ({8'd0, b_idx} * {8'd0, dim_v_reg} + {8'd0, v_idx});
            right_nv_index = right_base_nv + ({8'd0, c_idx} * {8'd0, dim_v_reg} + {8'd0, v_idx});
            
            // Convert NV index to line address and add group offset
            // fill_cycle 0→G0, 1→G1, 2→G2, 3→G3
            left_line_addr = {left_nv_index[6:0], 2'b00} + {7'd0, fill_cycle[1:0]};
            right_line_addr = {right_nv_index[6:0], 2'b00} + {7'd0, fill_cycle[1:0]};
            
            // Combinational assignment - direct to BRAM (no registers!)
            o_man_left_rd_addr = left_line_addr;
            o_man_right_rd_addr = right_line_addr;
            o_exp_left_rd_addr = left_line_addr;
            o_exp_right_rd_addr = right_line_addr;
            o_man_left_rd_en = 1'b1;
            o_man_right_rd_en = 1'b1;
            o_exp_left_rd_en = 1'b1;
            o_exp_right_rd_en = 1'b1;
        end
    end
    
    // ===================================================================
    // Buffer Filling Logic (5 cycles to grab both NVs + flag for transition)
    // ===================================================================
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            fill_cycle <= 3'd0;
            fill_buffer_ready <= 1'b0;
            nv_left_exp <= 32'd0;
            nv_right_exp <= 32'd0;
            for (int i = 0; i < 4; i++) begin
                nv_left_man[i] <= 256'd0;
                nv_right_man[i] <= 256'd0;
            end
        end else begin
            case (state_reg)
                ST_IDLE: begin
                    fill_cycle <= 3'd0;
                    fill_buffer_ready <= 1'b0;
                end
                
                ST_FILL_BUFFER: begin
                    // TRUE 1-cycle BRAM latency: combinational address → registered BRAM output
                    // Cycle 0: Issue G0 | Cycle 1: Capture G0, Issue G1
                    // Cycle 2: Capture G1, Issue G2 | Cycle 3: Capture G2, Issue G3
                    // Cycle 4: Capture G3, set ready flag → Cycle 5: Transition
                    if (fill_cycle == 3'd1) begin
                        // Cycle 1: Capture G0 (from cycle 0 read)
                        nv_left_exp[7:0] <= i_exp_left_rd_data;
                        nv_right_exp[7:0] <= i_exp_right_rd_data;
                        nv_left_man[0] <= i_man_left_rd_data;
                        nv_right_man[0] <= i_man_right_rd_data;
                        fill_cycle <= fill_cycle + 1;
                    end else if (fill_cycle == 3'd2) begin
                        // Cycle 2: Capture G1
                        nv_left_exp[15:8] <= i_exp_left_rd_data;
                        nv_right_exp[15:8] <= i_exp_right_rd_data;
                        nv_left_man[1] <= i_man_left_rd_data;
                        nv_right_man[1] <= i_man_right_rd_data;
                        fill_cycle <= fill_cycle + 1;
                    end else if (fill_cycle == 3'd3) begin
                        // Cycle 3: Capture G2
                        nv_left_exp[23:16] <= i_exp_left_rd_data;
                        nv_right_exp[23:16] <= i_exp_right_rd_data;
                        nv_left_man[2] <= i_man_left_rd_data;
                        nv_right_man[2] <= i_man_right_rd_data;
                        fill_cycle <= fill_cycle + 1;
                    end else if (fill_cycle == 3'd4) begin
                        // Cycle 4: Capture G3, set ready flag
                        nv_left_exp[31:24] <= i_exp_left_rd_data;
                        nv_right_exp[31:24] <= i_exp_right_rd_data;
                        nv_left_man[3] <= i_man_left_rd_data;
                        nv_right_man[3] <= i_man_right_rd_data;
                        fill_buffer_ready <= 1'b1;  // Signal ready for transition
                        fill_cycle <= 3'd0;  // Reset for next iteration
                    end else begin
                        // Cycle 0: Just increment (issuing first read combinationally)
                        fill_cycle <= fill_cycle + 1;
                    end
                end
                
                ST_COMPUTE_NV: begin
                    // Clear the ready flag once we've transitioned
                    fill_buffer_ready <= 1'b0;
                end
                
                default: begin
                    fill_cycle <= 3'd0;
                end
            endcase
        end
    end
    
    // ===================================================================
    // Compute Pipeline Control
    // ===================================================================
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            compute_wait <= 3'd0;
        end else begin
            case (state_reg)
                ST_COMPUTE_NV: begin
                    if (compute_wait < 3'd3) begin
                        compute_wait <= compute_wait + 1;  // Count: 0→1→2→3
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
                        $display("[BCV_ACCUM] @%0t [B%0d,C%0d] V=%0d INIT: mant=%0d (0x%08x), exp=%0d",
                                 $time, b_idx, c_idx, v_idx, nv_dot_mantissa, nv_dot_mantissa, nv_dot_exponent);
                        `endif
                    end else begin
                        // Accumulate with exponent alignment (FIXED: match original implementation)
                        automatic logic signed [7:0] max_exp;
                        automatic logic [7:0] exp_diff_accum, exp_diff_dot;
                        automatic logic signed [31:0] aligned_accum, aligned_dot;
                        automatic logic signed [31:0] sum_mantissa;
                        
                        // Find maximum exponent (using signed comparison for negative exponents)
                        if ($signed(accum_exponent) > $signed(nv_dot_exponent)) begin
                            max_exp = accum_exponent;
                        end else begin
                            max_exp = nv_dot_exponent;
                        end
                        
                        // Align mantissas to maximum exponent
                        exp_diff_accum = max_exp - accum_exponent;
                        exp_diff_dot = max_exp - nv_dot_exponent;
                        
                        // Align accumulated mantissa with underflow check
                        if (exp_diff_accum > 31) begin
                            aligned_accum = 32'sd0;  // Underflow - set to zero
                        end else begin
                            aligned_accum = $signed(accum_mantissa) >>> exp_diff_accum;
                        end
                        
                        // Align dot product mantissa with underflow check
                        if (exp_diff_dot > 31) begin
                            aligned_dot = 32'sd0;  // Underflow - set to zero
                        end else begin
                            aligned_dot = $signed(nv_dot_mantissa) >>> exp_diff_dot;
                        end
                        
                        // Sum aligned mantissas
                        sum_mantissa = aligned_accum + aligned_dot;
                        
                        // Update accumulator
                        accum_mantissa <= sum_mantissa;
                        accum_exponent <= max_exp;
                        `ifdef SIMULATION
                        $display("[BCV_ACCUM] @%0t [B%0d,C%0d] V=%0d ADD: accum_m=%0d(exp=%0d), dot_m=%0d(exp=%0d) -> aligned_a=%0d, aligned_d=%0d -> sum=%0d(exp=%0d)",
                                 $time, b_idx, c_idx, v_idx, accum_mantissa, accum_exponent, nv_dot_mantissa, nv_dot_exponent,
                                 aligned_accum, aligned_dot, sum_mantissa, max_exp);
                        `endif
                    end
                end
                
                ST_RETURN: begin
                    // Reset accumulator for next BxC output (after outputting result)
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
            left_base_reg <= 11'd0;
            right_base_reg <= 11'd0;
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
                        $display("[BCV_LOOP] @%0t NEW TILE: B=%0d, C=%0d, V=%0d, left_base=%0d, right_base=%0d", 
                                 $time, i_dim_b, i_dim_c, i_dim_v, i_left_base_addr, i_right_base_addr);
                        $display("[BCV_LOOP] @%0t DIM_CAPTURE: dim_b_reg=%0d->%0d, dim_c_reg=%0d->%0d, dim_v_reg=%0d->%0d",
                                 $time, dim_b_reg, i_dim_b, dim_c_reg, i_dim_c, dim_v_reg, i_dim_v);
                    end
                end
                
                ST_ACCUM: begin
                    // Advance V index within current (b,c) pair
                    v_idx <= v_idx + 1;
                    $display("[BCV_LOOP] ACCUM: b=%0d, c=%0d, v=%0d -> v=%0d", 
                             b_idx, c_idx, v_idx, v_idx + 1);
                end
                
                ST_RETURN: begin
                    // V loop complete, advance C and B indices
                    v_idx <= 8'd0;  // Reset V for next (b,c) pair
                    
                    $display("[BCV_LOOP] RETURN: b=%0d, c=%0d completed V loop, advancing indices", 
                             b_idx, c_idx);
                    
                    // Only advance indices if NOT done with all outputs
                    if (!(c_idx >= dim_c_reg - 1 && b_idx >= dim_b_reg - 1)) begin
                        // Advance C index
                        if (c_idx >= dim_c_reg - 1) begin
                            c_idx <= 8'd0;
                            // Advance B index
                            b_idx <= b_idx + 1;
                            $display("[BCV_LOOP]   -> Next: b=%0d, c=0", b_idx + 1);
                        end else begin
                            c_idx <= c_idx + 1;
                            $display("[BCV_LOOP]   -> Next: b=%0d, c=%0d", b_idx, c_idx + 1);
                        end
                    end else begin
                        $display("[BCV_LOOP]   -> DONE (all BxC outputs complete)");
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
                    `ifdef SIMULATION
                    $display("[BCV_ACCUM] @%0t [B%0d,C%0d] RETURN: Final GFP result = mant=%0d (0x%08x), exp=%0d",
                             $time, b_idx, c_idx, accum_mantissa, accum_mantissa, accum_exponent);
                    `endif
                end
                
                ST_DONE: begin
                    o_tile_done <= 1'b1;
                end
            endcase
        end
    end

endmodule

