`timescale 1ns/1ps

// Debug testbench for subnormal conversion
// Trying to reproduce the mismatch: HW=0x8008 vs Golden=0x80a0

module tb_subnormal_debug;

    parameter INT_WIDTH = 64;
    parameter FP_WIDTH = 16;
    parameter FRAC_BITS = 32;
    
    logic clk, rst_n;
    logic [INT_WIDTH-1:0] i_int;
    logic i_valid;
    logic [FP_WIDTH-1:0] o_fp;
    logic o_valid;
    
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
    wire [9:0] debug_raw_mant = dut.raw_mant;
    wire [9:0] debug_rounded_mant = dut.rounded_mant;
    wire debug_round_up = dut.round_up;
    wire debug_mant_overflow = dut.mant_overflow;
    wire debug_is_underflow = dut.is_underflow;
    wire signed [15:0] debug_subnormal_shift = dut.subnormal_shift;
    
    // Clock
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end
    
    // Test
    initial begin
        $display("\n========================================");
        $display("Subnormal Conversion Debug");
        $display("========================================\n");
        
        rst_n = 0;
        i_int = 0;
        i_valid = 0;
        repeat(5) @(posedge clk);
        rst_n = 1;
        repeat(2) @(posedge clk);
        
        // Test Case 1: Value that should produce 0x80a0 (golden)
        // Subnormal: -9.536743e-06
        // In Q32.32: multiply by 2^32 = -9.536743e-06 * 4294967296 ≈ -40960
        $display("Test 1: Value = -9.536743e-06 (should produce 0x80a0)");
        test_value(-64'd40960, 16'h80a0, "-9.536743e-06");
        
        // Test Case 2: Value that should produce 0x81f0 (golden)
        // Subnormal: -2.956390e-05
        // In Q32.32: multiply by 2^32 = -2.956390e-05 * 4294967296 ≈ -127000
        $display("\nTest 2: Value = -2.956390e-05 (should produce 0x81f0)");
        test_value(-64'd127000, 16'h81f0, "-2.956390e-05");
        
        // Test Case 3: Simpler subnormal
        // FP16 subnormal: 2^-14 × (mant/1024)
        // For mant=1: value = 2^-14 / 1024 = 2^-24 ≈ 5.96e-08
        // In Q32.32: 5.96e-08 * 2^32 ≈ 256
        $display("\nTest 3: Value = 5.96e-08 (min positive subnormal)");
        test_value(64'd256, 16'h0001, "5.96e-08");
        
        // Test Case 4: Normal value near subnormal boundary
        // FP16 min normal: 2^-14 ≈ 6.1e-05
        // In Q32.32: 6.1e-05 * 2^32 ≈ 262144
        $display("\nTest 4: Value = 6.1e-05 (min normal)");
        test_value(64'd262144, 16'h0400, "6.1e-05");
        
        $display("\n========================================");
        $display("Debug complete!");
        $display("========================================");
        $finish;
    end
    
    task test_value(input logic [63:0] int_val, input logic [15:0] expected, input string desc);
        begin
            @(posedge clk);
            i_int = int_val;
            i_valid = 1;
            
            @(posedge clk);
            i_valid = 0;
            
            repeat(2) @(posedge clk);  // Wait for 2-cycle latency
            
            if (o_valid) begin
                $display("  Input: 0x%016x (%s)", int_val, desc);
                $display("  DEBUG: lzc=%0d msb_pos=%0d exp_unbiased=%0d exp_biased=%0d adj_exp=%0d",
                         debug_lzc, debug_msb_pos, debug_exp_unbiased, debug_exp_biased, debug_adjusted_exp);
                $display("  DEBUG: raw_mant=0x%03x rounded_mant=0x%03x round_up=%b mant_ovf=%b",
                         debug_raw_mant, debug_rounded_mant, debug_round_up, debug_mant_overflow);
                $display("  DEBUG: is_underflow=%b subnormal_shift=%0d",
                         debug_is_underflow, debug_subnormal_shift);
                $display("  Output: 0x%04x (sign=%b exp=%0d mant=%0d)",
                         o_fp, o_fp[15], o_fp[14:10], o_fp[9:0]);
                $display("  Expected: 0x%04x", expected);
                if (o_fp == expected) begin
                    $display("  ✓ MATCH");
                end else begin
                    $display("  ✗ MISMATCH (diff=%0d LSB)", abs_diff(o_fp, expected));
                end
            end else begin
                $display("  ERROR: o_valid not asserted");
            end
        end
    endtask
    
    function integer abs_diff(input logic [15:0] a, input logic [15:0] b);
        abs_diff = (a > b) ? (a - b) : (b - a);
    endfunction

endmodule




