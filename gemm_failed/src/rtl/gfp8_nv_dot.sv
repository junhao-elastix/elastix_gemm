// ------------------------------------------------------------------
// GFP8 Native Vector Dot Product Module (Registered)
//
// Purpose: Compute dot product of 128-pair GFP8 vectors (one Native Vector)
// Architecture: Instantiates 4× gfp8_group_dot modules and sums results
//
// Input Format:
//  - 32-bit packed exponents per side (4 bytes, one per group, byte-aligned)
//  - Four 256-bit mantissa vectors per side (4 groups × 32 elements = 128 elements)
//
// Exponent Packing (byte-aligned):
//  [31:24] = Group 3 exponent (5-bit value in lower bits, upper 3 bits ignored)
//  [23:16] = Group 2 exponent
//  [15:8]  = Group 1 exponent
//  [7:0]   = Group 0 exponent
//
// Output Format:
//  - Result mantissa: 32-bit signed integer (sum of 4 group results)
//  - Result exponent: 8-bit signed integer (aligned to maximum exponent)
//
// Algorithm:
//  1. Unpack byte-aligned exponents (mask with 0x1F for 5-bit values)
//  2. Compute 4 group dot products in parallel (via gfp8_group_dot)
//  3. Find maximum exponent among 4 groups
//  4. Align mantissas by right-shifting to max exponent
//  5. Sum aligned mantissas
//  6. Register final result
//
// Latency: 3 clock cycles (with input register to prevent corruption)
//  - Cycle 0: Register inputs (CRITICAL: holds inputs stable)
//  - Cycle 1: Group dot products (gfp8_group_dot = 1 cycle)
//  - Cycle 2: Exponent alignment + summation + register
//
// Author: Refactoring from compute_engine.sv
// Date: Thu Oct 9 2025
// ------------------------------------------------------------------

module gfp8_nv_dot (
    // Clock and Reset
    input  logic         i_clk,
    input  logic         i_reset_n,
    
    // Input Enable (register inputs only when high)
    input  logic         i_input_valid,       // Pulse high to latch new inputs
    
    // Left Native Vector (128 elements = 4 groups)
    input  logic [31:0]  i_exp_left,          // 4 bytes: [31:24]=G3, [23:16]=G2, [15:8]=G1, [7:0]=G0
    input  logic [255:0] i_man_left [0:3],    // 4 × 256-bit mantissas
    
    // Right Native Vector (128 elements = 4 groups)
    input  logic [31:0]  i_exp_right,         // 4 bytes: [31:24]=G3, [23:16]=G2, [15:8]=G1, [7:0]=G0
    input  logic [255:0] i_man_right [0:3],   // 4 × 256-bit mantissas
    
    // Result (GFP format) - registered outputs
    output logic signed [31:0] o_result_mantissa,  // Sum of 4 group results
    output logic signed [7:0]  o_result_exponent   // Maximum exponent
);

    // ===================================================================
    // INPUT REGISTERS (TWO stages to prevent same-cycle read issues)
    // ===================================================================
    // Problem 1: BCV controller reuses nv_exp/nv_man registers for next V iteration
    // Problem 2: Combinational logic in gfp8_group_dot reads on same cycle as register write
    // Solution: Two-stage pipeline: capture → stable → compute
    
    // Stage 1: Capture incoming data
    logic [31:0]  exp_left_captured, exp_right_captured;
    logic [255:0] man_left_captured [0:3], man_right_captured [0:3];
    
    // Stage 2: Intermediate propagation
    logic [31:0]  exp_left_prop, exp_right_prop;
    logic [255:0] man_left_prop [0:3], man_right_prop [0:3];
    
    // Stage 3: Stable data for group_dot combinational logic (must be stable for full cycle before GROUP_DOT reads)
    logic [31:0]  exp_left_stable, exp_right_stable;
    logic [255:0] man_left_stable [0:3], man_right_stable [0:3];
    
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            exp_left_captured <= 32'd0;
            exp_right_captured <= 32'd0;
            exp_left_prop <= 32'd0;
            exp_right_prop <= 32'd0;
            exp_left_stable <= 32'd0;
            exp_right_stable <= 32'd0;
            for (int i = 0; i < 4; i++) begin
                man_left_captured[i] <= 256'd0;
                man_right_captured[i] <= 256'd0;
                man_left_prop[i] <= 256'd0;
                man_right_prop[i] <= 256'd0;
                man_left_stable[i] <= 256'd0;
                man_right_stable[i] <= 256'd0;
            end
        end else begin
            // Stage 1: Capture new data when i_input_valid is high
            if (i_input_valid) begin
                exp_left_captured <= i_exp_left;
                exp_right_captured <= i_exp_right;
                man_left_captured <= i_man_left;
                man_right_captured <= i_man_right;
                `ifdef SIMULATION
                $display("[NV_DOT_CAPTURE] @%0t Stage 1: man_left[0]=0x%064x",
                         $time, i_man_left[0]);
                $display("[NV_DOT_CAPTURE] @%0t Stage 1 bytes[0:3]: 0x%02x%02x%02x%02x",
                         $time, i_man_left[0][7:0], i_man_left[0][15:8], 
                         i_man_left[0][23:16], i_man_left[0][31:24]);
                `endif
            end
            
            // Stage 2: Propagate captured → prop (1 cycle delay)
            exp_left_prop <= exp_left_captured;
            exp_right_prop <= exp_right_captured;
            man_left_prop <= man_left_captured;
            man_right_prop <= man_right_captured;
            
            // Stage 3: Propagate prop → stable (1 more cycle delay)
            exp_left_stable <= exp_left_prop;
            exp_right_stable <= exp_right_prop;
            man_left_stable <= man_left_prop;
            man_right_stable <= man_right_prop;
            // `ifdef SIMULATION
            // if (man_left_prop[0] != 0) begin
            //     $display("[NV_DOT_STABLE_WRITE] @%0t man_left_stable[0]=0x%064x (from prop)",
            //              $time, man_left_prop[0]);
            //     $display("[NV_DOT_STABLE_WRITE] @%0t man_left_stable[3]=0x%064x (from prop)",
            //              $time, man_left_prop[3]);
            // end
            // `endif
        end
    end
    
    // ===================================================================
    // Unpack Byte-Aligned Exponents (from registered inputs)
    // ===================================================================
    
    // Extract 5-bit exponents from byte-aligned registered input
    logic [4:0] exp_left_unpacked [0:3];
    logic [4:0] exp_right_unpacked [0:3];
    
    assign exp_left_unpacked[0] = exp_left_stable[7:0]   & 5'h1F;  // Group 0, mask to 5 bits
    assign exp_left_unpacked[1] = exp_left_stable[15:8]  & 5'h1F;  // Group 1
    assign exp_left_unpacked[2] = exp_left_stable[23:16] & 5'h1F;  // Group 2
    assign exp_left_unpacked[3] = exp_left_stable[31:24] & 5'h1F;  // Group 3
    
    assign exp_right_unpacked[0] = exp_right_stable[7:0]   & 5'h1F;
    assign exp_right_unpacked[1] = exp_right_stable[15:8]  & 5'h1F;
    assign exp_right_unpacked[2] = exp_right_stable[23:16] & 5'h1F;
    assign exp_right_unpacked[3] = exp_right_stable[31:24] & 5'h1F;
    
    `ifdef SIMULATION
    always @(exp_left_stable or exp_right_stable) begin
        if (exp_left_stable != 0 || exp_right_stable != 0) begin
            $display("[NV_DOT_STABLE] @%0t exp_left_stable=0x%08x, exp_right_stable=0x%08x", $time, exp_left_stable, exp_right_stable);
            $display("  exp_left_unpacked:  [0]=%0d [1]=%0d [2]=%0d [3]=%0d",
                     exp_left_unpacked[0], exp_left_unpacked[1], exp_left_unpacked[2], exp_left_unpacked[3]);
            $display("  exp_right_unpacked: [0]=%0d [1]=%0d [2]=%0d [3]=%0d",
                     exp_right_unpacked[0], exp_right_unpacked[1], exp_right_unpacked[2], exp_right_unpacked[3]);
        end
    end
    `endif
    
    // ===================================================================
    // Internal Signals - Group Dot Product Results
    // ===================================================================
    
    // Results from 4 group dot products
    logic signed [31:0] group_mantissa [0:3];
    logic signed [7:0]  group_exponent [0:3];
    
    // ===================================================================
    // Instantiate 4× gfp8_group_dot (one per group)
    // ===================================================================
    
    // Original implementation (commented out)
    /*
    genvar g;
    generate
        for (g = 0; g < 4; g++) begin : gen_group_dots
            gfp8_group_dot #(.GROUP_ID(g)) u_group_dot (
                .i_clk              (i_clk),
                .i_reset_n          (i_reset_n),
                .i_exp_left         (exp_left_unpacked[g]),
                .i_man_left         (man_left_stable[g]),    // Use STABLE mantissas (2-cycle delay)
                .i_exp_right        (exp_right_unpacked[g]),
                .i_man_right        (man_right_stable[g]),   // Use STABLE mantissas (2-cycle delay)
                .o_result_mantissa  (group_mantissa[g]),
                .o_result_exponent  (group_exponent[g])
            );
        end
    endgenerate
    */
    
    // MLP72 Hardware-Accelerated Implementation
    genvar g;
    generate
        for (g = 0; g < 4; g++) begin : gen_group_dots_mlp
            gfp8_group_dot_mlp #(.GROUP_ID(g)) u_group_dot_mlp (
                .i_clk              (i_clk),
                .i_reset_n          (i_reset_n),
                .i_exp_left         (exp_left_unpacked[g]),
                .i_man_left         (man_left_stable[g]),    // Use STABLE mantissas (2-cycle delay)
                .i_exp_right        (exp_right_unpacked[g]),
                .i_man_right        (man_right_stable[g]),   // Use STABLE mantissas (2-cycle delay)
                .o_result_mantissa  (group_mantissa[g]),
                .o_result_exponent  (group_exponent[g])
            );
        end
    endgenerate
    
    // ===================================================================
    // Exponent Alignment and Summation (Combinational)
    // ===================================================================
    
    // Aligned mantissas
    logic signed [31:0] aligned_mantissa [0:3];
    
    // Maximum exponent
    logic signed [7:0] max_exponent;
    
    // Exponent differences
    logic [7:0] exp_diff [0:3];
    
    // Final sum
    logic signed [31:0] sum_mantissa;
    
    always_comb begin
        // Find maximum exponent among all 4 groups
        max_exponent = group_exponent[0];
        for (int i = 1; i < 4; i++) begin
            if (group_exponent[i] > max_exponent) begin
                max_exponent = group_exponent[i];
            end
        end
        
        // Align all mantissas to the maximum exponent
        for (int i = 0; i < 4; i++) begin
            exp_diff[i] = max_exponent - group_exponent[i];
            
            if (exp_diff[i] > 31) begin
                // Underflow - set to zero
                aligned_mantissa[i] = 32'sd0;
            end else begin
                // Arithmetic right-shift to preserve sign
                aligned_mantissa[i] = $signed(group_mantissa[i]) >>> exp_diff[i];
            end
        end
        
        // Sum all aligned mantissas
        sum_mantissa = aligned_mantissa[0] + aligned_mantissa[1] + 
                       aligned_mantissa[2] + aligned_mantissa[3];
    end
    
    // ===================================================================
    // Output Registers (2nd cycle latency)
    // ===================================================================
    logic signed [31:0] result_mantissa_reg;
    logic signed [7:0]  result_exponent_reg;
    
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            result_mantissa_reg <= 32'sd0;
            result_exponent_reg <= 8'sd0;
        end else begin
            result_mantissa_reg <= sum_mantissa;
            result_exponent_reg <= max_exponent;
        end
    end
    
    // ===================================================================
    // Output Assignment
    // ===================================================================
    assign o_result_mantissa = result_mantissa_reg;
    assign o_result_exponent = result_exponent_reg;

endmodule


