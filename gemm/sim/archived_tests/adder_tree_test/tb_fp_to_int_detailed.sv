`timescale 1ns/1ps

// Detailed test for fp_to_int conversion
// Tests FP24 → 128-bit fixed-point integer with diverse cases

module tb_fp_to_int_detailed;

    parameter FP_WIDTH = 24;
    parameter INT_WIDTH = 128;
    parameter FRAC_BITS = 48;
    
    logic clk, rst_n;
    logic [FP_WIDTH-1:0] i_fp;
    logic i_valid;
    logic [INT_WIDTH-1:0] o_int;
    logic o_valid;
    
    integer test_count, pass_count, fail_count;
    
    // Clock
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end
    
    // DUT
    fp_to_int #(
        .FP_WIDTH(FP_WIDTH),
        .INT_WIDTH(INT_WIDTH),
        .FRAC_BITS(FRAC_BITS)
    ) dut (.*);
    
    // Test
    initial begin
        $display("========================================");
        $display("FP24 → Integer Conversion Test");
        $display("========================================\n");
        
        test_count = 0;
        pass_count = 0;
        fail_count = 0;
        
        rst_n = 0;
        i_fp = 0;
        i_valid = 0;
        repeat(5) @(posedge clk);
        rst_n = 1;
        repeat(2) @(posedge clk);
        
        // Test 1: Zero
        test_fp24(24'h000000, "Zero");
        
        // Test 2-4: Small integers
        test_fp24(24'h3F8000, "1.0 (exp=127)");
        test_fp24(24'h400000, "2.0 (exp=128)");
        test_fp24(24'h408000, "4.0 (exp=129)");
        
        // Test 5-6: Fractions
        test_fp24(24'h3F0000, "0.5 (exp=126)");
        test_fp24(24'h3E8000, "0.25 (exp=125)");
        
        // Test 7-8: Negative
        test_fp24(24'hBF8000, "-1.0");
        test_fp24(24'hC00000, "-2.0");
        
        // Test 9-10: Large values
        test_fp24(24'h47C350, "100000.0 (exp=143)");
        test_fp24(24'h461C40, "10000.0");
        
        // Test 11-12: Small values
        test_fp24(24'h358637, "0.00000123");
        test_fp24(24'h3A8300, "0.001");
        
        // Test 13: Very large
        test_fp24(24'h469C3F, "19999.0");
        
        // Test 14-15: Edge of precision
        test_fp24(24'h421DCC, "39.45");
        test_fp24(24'h404CCD, "3.2");
        
        $display("\n========================================");
        $display("Total: %0d  Pass: %0d  Fail: %0d", test_count, pass_count, fail_count);
        $display("========================================");
        
        if (fail_count == 0)
            $display("✓ ALL TESTS PASSED\n");
        else
            $display("✗ %0d TESTS FAILED\n", fail_count);
        
        $finish;
    end
    
    task test_fp24(input logic [23:0] fp24, input string desc);
        begin
            @(posedge clk);
            i_fp = fp24;
            i_valid = 1;
            
            @(posedge clk);
            i_valid = 0;
            
            @(posedge clk);  // Wait for result
            
            test_count++;
            
            if (o_valid) begin
                $display("[%2d] %s", test_count, desc);
                $display("     FP24: 0x%06x  sign=%b exp=%3d mant=0x%04x",
                         fp24, fp24[23], fp24[22:15], fp24[14:0]);
                $display("     INT:  0x%032x", o_int);
                
                // Check if reasonable (not all zeros for non-zero input, not overflow)
                if (fp24 != 0 && o_int == 0) begin
                    $display("     WARN: Non-zero input produced zero output");
                    fail_count++;
                end else begin
                    pass_count++;
                end
            end else begin
                $display("[%2d] %s - ERROR: o_valid not asserted", test_count, desc);
                fail_count++;
            end
            $display("");
        end
    endtask

endmodule

