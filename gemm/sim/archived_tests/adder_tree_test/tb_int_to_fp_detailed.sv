`timescale 1ns/1ps

// Detailed test for int_to_fp conversion
// Tests 128-bit fixed-point integer → FP16 with diverse cases

module tb_int_to_fp_detailed;

    parameter INT_WIDTH = 128;
    parameter FP_WIDTH = 16;
    parameter FRAC_BITS = 48;
    
    logic clk, rst_n;
    logic [INT_WIDTH-1:0] i_int;
    logic i_valid;
    logic [FP_WIDTH-1:0] o_fp;
    logic o_valid;
    
    integer test_count, pass_count, fail_count;
    
    // Clock
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end
    
    // DUT
    int_to_fp #(
        .INT_WIDTH(INT_WIDTH),
        .FP_WIDTH(FP_WIDTH),
        .FRAC_BITS(FRAC_BITS)
    ) dut (.*);
    
    // Debug probes
    wire [6:0] debug_lzc = dut.s1_lzc;
    wire signed [15:0] debug_msb_pos = dut.msb_pos;
    wire signed [15:0] debug_exp_unbiased = dut.exp_unbiased;
    wire signed [15:0] debug_exp_biased = dut.exp_biased;
    wire signed [15:0] debug_adjusted_exp = dut.adjusted_exp;
    wire debug_is_overflow = dut.is_overflow;
    wire debug_is_underflow = dut.is_underflow;
    
    // Test
    initial begin
        $display("========================================");
        $display("Integer → FP16 Conversion Test");
        $display("Fixed-point format: %0d.%0d (FRAC_BITS=%0d)", INT_WIDTH-FRAC_BITS, FRAC_BITS, FRAC_BITS);
        $display("========================================\n");
        
        test_count = 0;
        pass_count = 0;
        fail_count = 0;
        
        rst_n = 0;
        i_int = 0;
        i_valid = 0;
        repeat(5) @(posedge clk);
        rst_n = 1;
        repeat(2) @(posedge clk);
        
        // Test 1: Zero
        test_int(128'h0, 16'h0000, "Zero");
        
        // Test 2-4: Small integers (1 << FRAC_BITS = 1.0)
        test_int(128'h1000000000000, 16'h3C00, "1.0");
        test_int(128'h2000000000000, 16'h4000, "2.0");
        test_int(128'h4000000000000, 16'h4400, "4.0");
        
        // Test 5-6: Fractions
        test_int(128'h800000000000, 16'h3800, "0.5");
        test_int(128'h400000000000, 16'h3400, "0.25");
        
        // Test 7-8: Negative (2's complement)
        test_int(128'hFFFFFFFFFFFFFFFFFFFFFFFF000000000000, 16'hBC00, "-1.0");
        test_int(128'hFFFFFFFFFFFFFFFFFFFFFFFE000000000000, 16'hC000, "-2.0");
        
        // Test 9-10: Larger values
        test_int(128'hA000000000000, 16'h4900, "10.0");
        test_int(128'h64000000000000, 16'h5640, "100.0");
        
        // Test 11-12: Sum-like values (what adder tree produces)
        test_int(128'h4000000000000, 16'h4400, "4.0 (sum of 4×1.0)");
        test_int(128'h8000000000000, 16'h4800, "8.0 (sum of 8×1.0)");
        
        // Test 13-14: Mixed sums
        test_int(128'h2800000000000, 16'h4280, "2.5");
        test_int(128'hC00000000000, 16'h3600, "0.75");
        
        // Test 15: Large value (sum of large numbers)
        test_int(128'h9C40000000000000, 16'h7000, "~10000.0");
        
        $display("\n========================================");
        $display("Total: %0d  Pass: %0d  Fail: %0d", test_count, pass_count, fail_count);
        $display("========================================");
        
        if (fail_count == 0)
            $display("✓ ALL TESTS PASSED\n");
        else
            $display("✗ %0d TESTS FAILED\n", fail_count);
        
        $finish;
    end
    
    task test_int(input logic [127:0] int_val, input logic [15:0] expected_fp16, input string desc);
        begin
            @(posedge clk);
            i_int = int_val;
            i_valid = 1;
            
            @(posedge clk);
            i_valid = 0;
            
            repeat(2) @(posedge clk);  // Wait for 2-cycle latency
            
            test_count++;
            
            if (o_valid) begin
                $display("[%2d] %s", test_count, desc);
                $display("     INT: 0x%032x", int_val);
                $display("     DEBUG: lzc=%0d msb_pos=%0d exp_unbiased=%0d exp_biased=%0d adj_exp=%0d ovf=%b udf=%b",
                         debug_lzc, debug_msb_pos, debug_exp_unbiased, debug_exp_biased, 
                         debug_adjusted_exp, debug_is_overflow, debug_is_underflow);
                $display("     FP16: 0x%04x  sign=%b exp=%2d mant=0x%03x",
                         o_fp, o_fp[15], o_fp[14:10], o_fp[9:0]);
                
                // Check if it matches expected (with some tolerance)
                if (o_fp == expected_fp16) begin
                    $display("     ✓ EXACT MATCH (expected 0x%04x)", expected_fp16);
                    pass_count++;
                end else if ((o_fp ^ expected_fp16) <= 16'h0003) begin
                    $display("     ~ CLOSE (expected 0x%04x, diff=%0d LSB)", expected_fp16, (o_fp ^ expected_fp16));
                    pass_count++;
                end else begin
                    $display("     ✗ MISMATCH (expected 0x%04x, diff=%0d LSB)", expected_fp16, (o_fp ^ expected_fp16));
                    fail_count++;
                end
            end else begin
                $display("[%2d] %s - ERROR: o_valid not asserted", test_count, desc);
                fail_count++;
            end
            $display("");
        end
    endtask

endmodule

