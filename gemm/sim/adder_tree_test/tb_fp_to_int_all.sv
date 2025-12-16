`timescale 1ns/1ps

// Comprehensive test for fp_to_int: FP24→Int and FP16→Int

module tb_fp_to_int_all;

    parameter INT_WIDTH = 64;
    parameter FRAC_BITS = 32;
    
    logic clk, rst_n;
    
    // FP24 → Int
    logic [23:0] i_fp24;
    logic i_valid24;
    logic [INT_WIDTH-1:0] o_int24;
    logic o_valid24;
    
    // FP16 → Int
    logic [15:0] i_fp16;
    logic i_valid16;
    logic [INT_WIDTH-1:0] o_int16;
    logic o_valid16;
    
    integer test_count, pass_count, fail_count;
    
    // Clock
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end
    
    // DUT: FP24 → Int
    fp_to_int #(
        .FP_WIDTH(24),
        .INT_WIDTH(INT_WIDTH),
        .FRAC_BITS(FRAC_BITS)
    ) dut_fp24 (
        .clk(clk),
        .rst_n(rst_n),
        .i_fp(i_fp24),
        .i_valid(i_valid24),
        .o_int(o_int24),
        .o_valid(o_valid24)
    );
    
    // DUT: FP16 → Int
    fp_to_int #(
        .FP_WIDTH(16),
        .INT_WIDTH(INT_WIDTH),
        .FRAC_BITS(FRAC_BITS)
    ) dut_fp16 (
        .clk(clk),
        .rst_n(rst_n),
        .i_fp(i_fp16),
        .i_valid(i_valid16),
        .o_int(o_int16),
        .o_valid(o_valid16)
    );
    
    // Test
    initial begin
        $display("\n========================================");
        $display("FP → Integer Conversion Comprehensive Test");
        $display("========================================\n");
        
        test_count = 0;
        pass_count = 0;
        fail_count = 0;
        
        rst_n = 0;
        i_fp24 = 0;
        i_fp16 = 0;
        i_valid24 = 0;
        i_valid16 = 0;
        repeat(5) @(posedge clk);
        rst_n = 1;
        repeat(2) @(posedge clk);
        
        $display("=== Testing FP24 → Integer ===\n");
        test_fp24(24'h000000, "Zero");
        test_fp24(24'h3F8000, "1.0");
        test_fp24(24'h400000, "2.0");
        test_fp24(24'h408000, "4.0");
        test_fp24(24'h3F0000, "0.5");
        test_fp24(24'h3E8000, "0.25");
        test_fp24(24'hBF8000, "-1.0");
        test_fp24(24'hC00000, "-2.0");
        test_fp24(24'h47C350, "100000.0");
        test_fp24(24'h358637, "0.00000123");
        test_fp24(24'h469C3F, "19999.0");
        test_fp24(24'h421DCC, "39.45");
        
        $display("\n=== Testing FP16 → Integer ===\n");
        test_fp16(16'h0000, "Zero");
        test_fp16(16'h3C00, "1.0");
        test_fp16(16'h4000, "2.0");
        test_fp16(16'h4400, "4.0");
        test_fp16(16'h3800, "0.5");
        test_fp16(16'h3400, "0.25");
        test_fp16(16'hBC00, "-1.0");
        test_fp16(16'hC000, "-2.0");
        test_fp16(16'h4900, "10.0");
        test_fp16(16'h5640, "100.0");
        test_fp16(16'h7000, "~10000.0");
        test_fp16(16'h5111, "67.066");
        
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
            i_fp24 = fp24;
            i_valid24 = 1;
            
            @(posedge clk);
            i_valid24 = 0;
            
            @(posedge clk);  // Wait for result
            
            test_count++;
            
            if (o_valid24) begin
                $display("[%2d] FP24 %s: 0x%06x → 0x%032x", test_count, desc, fp24, o_int24);
                if (fp24 != 0 && o_int24 == 0) begin
                    $display("     ✗ FAIL: Non-zero input produced zero output");
                    fail_count++;
                end else begin
                    pass_count++;
                end
            end else begin
                $display("[%2d] %s - ERROR: o_valid not asserted", test_count, desc);
                fail_count++;
            end
        end
    endtask
    
    task test_fp16(input logic [15:0] fp16, input string desc);
        begin
            @(posedge clk);
            i_fp16 = fp16;
            i_valid16 = 1;
            
            @(posedge clk);
            i_valid16 = 0;
            
            @(posedge clk);  // Wait for result
            
            test_count++;
            
            if (o_valid16) begin
                $display("[%2d] FP16 %s: 0x%04x → 0x%032x", test_count, desc, fp16, o_int16);
                if (fp16 != 0 && o_int16 == 0) begin
                    $display("     ✗ FAIL: Non-zero input produced zero output");
                    fail_count++;
                end else begin
                    pass_count++;
                end
            end else begin
                $display("[%2d] %s - ERROR: o_valid not asserted", test_count, desc);
                fail_count++;
            end
        end
    endtask

endmodule


