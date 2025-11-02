// ------------------------------------------------------------------
// GFP8 Native Vector Dot Product Module (Registered)
//
// Purpose: Compute dot product of 128-pair GFP8 vectors (one Native Vector)
// Architecture: Instantiates 4x gfp8_group_dot modules and sums results
//
// Input Format:
//  - 32-bit packed exponents per side (4 bytes, one per group, byte-aligned)
//  - Four 256-bit mantissa vectors per side (4 groups x 32 elements = 128 elements)
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
// Latency: 4 clock cycles (optimized - removed unnecessary pipeline stages)
//  - Cycle 0: input_valid assertion + input capture
//  - Cycle 1: group_dot computation
//  - Cycle 2: Exponent alignment + summation
//  - Cycle 3: Final output valid
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
    input  logic [255:0] i_man_left [0:3],    // 4 x 256-bit mantissas
    
    // Right Native Vector (128 elements = 4 groups)
    input  logic [31:0]  i_exp_right,         // 4 bytes: [31:24]=G3, [23:16]=G2, [15:8]=G1, [7:0]=G0
    input  logic [255:0] i_man_right [0:3],   // 4 x 256-bit mantissas
    
    // Result (GFP format) - registered outputs
    output logic signed [31:0] o_result_mantissa,  // Sum of 4 group results
    output logic signed [7:0]  o_result_exponent   // Maximum exponent
);

    // ===================================================================
    // INPUT REGISTERS (Single stage - inputs are stable from BCV controller)
    // ===================================================================
    // BCV controller guarantees stable inputs during ST_COMPUTE_NV state
    // Input registers capture data when i_input_valid pulses high
    
    // Single capture stage
    logic [31:0]  exp_left_captured, exp_right_captured;
    logic [255:0] man_left_captured [0:3], man_right_captured [0:3];
    
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            exp_left_captured <= 32'd0;
            exp_right_captured <= 32'd0;
            for (int i = 0; i < 4; i++) begin
                man_left_captured[i] <= 256'd0;
                man_right_captured[i] <= 256'd0;
            end
        end else begin
            // Capture new data when i_input_valid is high
            if (i_input_valid) begin
                exp_left_captured <= i_exp_left;
                exp_right_captured <= i_exp_right;
                man_left_captured <= i_man_left;
                man_right_captured <= i_man_right;
                // `ifdef SIMULATION
                // $display("[NV_DOT_CAPTURE] @%0t Captured: man_left[0]=0x%064x",
                //          $time, i_man_left[0]);
                // `endif
            end
        end
    end
    
    // ===================================================================
    // Unpack Byte-Aligned Exponents (from captured inputs)
    // ===================================================================
    
    // Extract 8-bit exponents from byte-aligned captured input
    logic [7:0] exp_left_unpacked [0:3];
    logic [7:0] exp_right_unpacked [0:3];
    
    assign exp_left_unpacked[0] = exp_left_captured[7:0];    // Group 0
    assign exp_left_unpacked[1] = exp_left_captured[15:8];   // Group 1
    assign exp_left_unpacked[2] = exp_left_captured[23:16];  // Group 2
    assign exp_left_unpacked[3] = exp_left_captured[31:24];  // Group 3
    
    assign exp_right_unpacked[0] = exp_right_captured[7:0];
    assign exp_right_unpacked[1] = exp_right_captured[15:8];
    assign exp_right_unpacked[2] = exp_right_captured[23:16];
    assign exp_right_unpacked[3] = exp_right_captured[31:24];
    
    // `ifdef SIMULATION
    // always @(exp_left_captured or exp_right_captured) begin
    //     if (exp_left_captured != 0 || exp_right_captured != 0) begin
    //         $display("[NV_DOT_UNPACK] @%0t exp_left=0x%08x, exp_right=0x%08x", 
    //                  $time, exp_left_captured, exp_right_captured);
    //     end
    // end
    // `endif
    
    // ===================================================================
    // Internal Signals - Group Dot Product Results
    // ===================================================================
    
    // Results from 4 group dot products
    logic signed [31:0] group_mantissa [0:3];
    logic signed [7:0]  group_exponent [0:3];
    
    // ===================================================================
    // Instantiate 4x gfp8_group_dot_mlp (MLP72 Hardware-Accelerated)
    // ===================================================================

    // MLP72 Hardware-Accelerated Implementation
    genvar g;
    generate
        for (g = 0; g < 4; g++) begin : gen_group_dots_mlp
            gfp8_group_dot_mlp #(.GROUP_ID(g)) u_group_dot_mlp (
                .i_clk              (i_clk),
                .i_reset_n          (i_reset_n),
                .i_exp_left         (exp_left_unpacked[g]),
                .i_man_left         (man_left_captured[g]),    // Use captured mantissas directly
                .i_exp_right        (exp_right_unpacked[g]),
                .i_man_right        (man_right_captured[g]),   // Use captured mantissas directly
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
    // Output Registers (Final cycle latency)
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


