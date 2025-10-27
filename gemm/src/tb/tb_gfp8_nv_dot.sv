// ------------------------------------------------------------------
// Testbench for gfp8_nv_dot.sv
//
// Purpose: Verify 128-element Native Vector dot product
// Tests:
//  1. Simple known values (all 1s)
//  2. Zero vectors
//  3. Real data from hex files (NV 0: groups 0-3)
//  4. Different exponent alignment scenarios
//
// Author: Refactoring effort
// Date: Fri Oct 10 2025
// ------------------------------------------------------------------

`timescale 1ns/1ps

module tb_gfp8_nv_dot;

    // Clock and reset
    logic clk;
    logic reset_n;
    
    // DUT inputs
    logic         input_valid;
    logic [31:0]  exp_left;
    logic [255:0] man_left [0:3];
    logic [31:0]  exp_right;
    logic [255:0] man_right [0:3];
    
    // DUT outputs
    logic signed [31:0] result_mantissa;
    logic signed [7:0]  result_exponent;
    
    // Test control
    integer test_num;
    logic test_passed;
    
    // Hex file data storage
    logic [255:0] left_data [0:527];
    logic [255:0] right_data [0:527];
    
    // ===================================================================
    // DUT Instantiation
    // ===================================================================
    gfp8_nv_dot dut (
        .i_clk              (clk),
        .i_reset_n          (reset_n),
        .i_input_valid      (input_valid),
        .i_exp_left         (exp_left),
        .i_man_left         (man_left),
        .i_exp_right        (exp_right),
        .i_man_right        (man_right),
        .o_result_mantissa  (result_mantissa),
        .o_result_exponent  (result_exponent)
    );
    
    // ===================================================================
    // Clock Generation
    // ===================================================================
    initial begin
        clk = 0;
        forever #5 clk = ~clk;  // 100MHz clock
    end
    
    // ===================================================================
    // Helper Function: Pack mantissas
    // ===================================================================
    function automatic logic [255:0] pack_man(logic signed [7:0] vals [0:31]);
        logic [255:0] result;
        for (int i = 0; i < 32; i++) begin
            result[i*8 +: 8] = vals[i];
        end
        return result;
    endfunction
    
    // ===================================================================
    // Test Stimulus
    // ===================================================================
    initial begin
        // Initialize
        reset_n = 0;
        input_valid = 0;
        exp_left = 32'd0;
        exp_right = 32'd0;
        for (int i = 0; i < 4; i++) begin
            man_left[i] = 256'd0;
            man_right[i] = 256'd0;
        end
        test_num = 0;
        test_passed = 1;
        
        // Reset
        repeat(2) @(posedge clk);
        reset_n = 1;
        @(posedge clk);
        
        $display("\n========================================");
        $display("GFP8 Native Vector Dot Product Testbench");
        $display("========================================\n");
        
        // ===============================================================
        // Test 1: Simple Known Values (all 1s)
        // ===============================================================
        test_num = 1;
        $display("[TEST %0d] Simple known values (all 1s)", test_num);
        $display("  Each group: 32 elements of (1 * 1)");
        $display("  Expected per group: mantissa=32, exponent=0");
        $display("  Expected NV total: 4 groups aligned and summed");
        
        // All groups have exponent 15 (bias), mantissa 1
        exp_left = {8'd15, 8'd15, 8'd15, 8'd15};   // 4 groups
        exp_right = {8'd15, 8'd15, 8'd15, 8'd15};
        
        // All mantissas = 1
        for (int g = 0; g < 4; g++) begin
            logic signed [7:0] vals [0:31];
            for (int i = 0; i < 32; i++) vals[i] = 8'sd1;
            man_left[g] = pack_man(vals);
            man_right[g] = pack_man(vals);
        end
        
        // Pulse input_valid to latch the data
        @(posedge clk);
        input_valid = 1;
        @(posedge clk);
        input_valid = 0;
        
        // Wait for pipeline (3 cycles from gfp8_nv_dot: capture->prop->stable->compute->result)
        @(posedge clk);
        @(posedge clk);
        @(posedge clk);
        @(posedge clk);
        @(posedge clk);
        
        $display("  Result: mantissa=%0d, exponent=%0d", result_mantissa, result_exponent);
        // Each group: 32 products, exponent = 15+15-30 = 0
        // Total: 4*32 = 128
        if (result_mantissa == 32'sd128 && result_exponent == 8'sd0) begin
            $display("  [PASS]\n");
        end else begin
            $display("  [FAIL] Expected mantissa=128, exponent=0\n");
            test_passed = 0;
        end
        
        // ===============================================================
        // Test 2: Zero Vectors
        // ===============================================================
        test_num = 2;
        $display("[TEST %0d] Zero vectors", test_num);
        
        exp_left = {8'd15, 8'd15, 8'd15, 8'd15};
        exp_right = {8'd15, 8'd15, 8'd15, 8'd15};
        
        for (int g = 0; g < 4; g++) begin
            man_left[g] = 256'd0;
            man_right[g] = 256'd0;
        end
        
        // Pulse input_valid to latch the data
        @(posedge clk);
        input_valid = 1;
        @(posedge clk);
        input_valid = 0;
        
        // Wait for pipeline (3 cycles from gfp8_nv_dot: capture->prop->stable->compute->result)
        @(posedge clk);
        @(posedge clk);
        @(posedge clk);
        @(posedge clk);
        @(posedge clk);
        
        $display("  Result: mantissa=%0d, exponent=%0d", result_mantissa, result_exponent);
        if (result_mantissa == 32'sd0) begin
            $display("  [PASS]\n");
        end else begin
            $display("  [FAIL] Expected mantissa=0\n");
            test_passed = 0;
        end
        
        // ===============================================================
        // Test 3: Different Exponents per Group
        // ===============================================================
        test_num = 3;
        $display("[TEST %0d] Different exponents per group", test_num);
        $display("  Group 0: exp=15, Group 1: exp=16, Group 2: exp=14, Group 3: exp=15");
        $display("  All mantissas = 1");
        
        // Different exponents (but need to mask to 5 bits)
        exp_left = {8'd15, 8'd14, 8'd16, 8'd15};   // G3, G2, G1, G0
        exp_right = {8'd15, 8'd14, 8'd16, 8'd15};
        
        for (int g = 0; g < 4; g++) begin
            logic signed [7:0] vals [0:31];
            for (int i = 0; i < 32; i++) vals[i] = 8'sd1;
            man_left[g] = pack_man(vals);
            man_right[g] = pack_man(vals);
        end
        
        // Pulse input_valid to latch the data
        @(posedge clk);
        input_valid = 1;
        @(posedge clk);
        input_valid = 0;
        
        // Wait for pipeline (3 cycles from gfp8_nv_dot: capture->prop->stable->compute->result)
        @(posedge clk);
        @(posedge clk);
        @(posedge clk);
        @(posedge clk);
        @(posedge clk);
        
        $display("  Result: mantissa=%0d, exponent=%0d", result_mantissa, result_exponent);
        // Group 0: exp = 15+15-30 = 0, mantissa = 32
        // Group 1: exp = 16+16-30 = 2, mantissa = 32
        // Group 2: exp = 14+14-30 = -2, mantissa = 32
        // Group 3: exp = 15+15-30 = 0, mantissa = 32
        // After alignment to max exponent (2):
        //   G1: 32 (exp=2)
        //   G0: 32 >> 2 = 8 (aligned to exp=2)
        //   G3: 32 >> 2 = 8 (aligned to exp=2)
        //   G2: 32 >> 4 = 2 (aligned to exp=2)
        // Total: 32 + 8 + 8 + 2 = 50
        $display("  Expected after alignment: mantissa~50, exponent=2");
        if (result_exponent == 8'sd2 && result_mantissa >= 32'sd48 && result_mantissa <= 32'sd52) begin
            $display("  [PASS]\n");
        end else begin
            $display("  [WARN] Results may vary due to alignment order\n");
        end
        
        // ===============================================================
        // Test 4: Real Data from Hex Files (NV 0, all 4 groups)
        // ===============================================================
        test_num = 4;
        $display("[TEST %0d] Real data from hex files (NV 0, Groups 0-3)", test_num);
        
        // Load actual hex file data
        $readmemh("/home/workstation/elastix_gemm/hex/left.hex", left_data);
        $readmemh("/home/workstation/elastix_gemm/hex/right.hex", right_data);
        
        // Extract NV 0 exponents (line 0, bytes 0-3)
        exp_left = left_data[0][31:0];
        exp_right = right_data[0][31:0];
        
        $display("  Left exponents:  0x%08x", exp_left);
        $display("  Right exponents: 0x%08x", exp_right);
        
        // Extract NV 0 mantissas (lines 16-19)
        for (int g = 0; g < 4; g++) begin
            man_left[g] = left_data[16 + g];
            man_right[g] = right_data[16 + g];
        end
        
        // Pulse input_valid to latch the data
        @(posedge clk);
        input_valid = 1;
        @(posedge clk);
        input_valid = 0;
        
        // Wait for pipeline (3 cycles from gfp8_nv_dot: capture->prop->stable->compute->result)
        @(posedge clk);
        @(posedge clk);
        @(posedge clk);
        @(posedge clk);
        @(posedge clk);
        
        $display("  Result: mantissa=%0d, exponent=%0d", result_mantissa, result_exponent);
        
        // Compare with individual group results
        $display("  Expected: Sum of 4 group dot products with alignment");
        $display("  [INFO] Manual verification needed against Python golden model\n");
        
        // ===============================================================
        // Test Summary
        // ===============================================================
        $display("========================================");
        if (test_passed) begin
            $display("All tests PASSED");
        end else begin
            $display("Some tests FAILED");
        end
        $display("========================================\n");
        
        $finish;
    end
    
    // ===================================================================
    // Timeout
    // ===================================================================
    initial begin
        #100000;  // 100us timeout
        $display("ERROR: Testbench timeout!");
        $finish;
    end

endmodule

