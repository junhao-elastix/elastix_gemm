`timescale 1ns/1ps

// Comprehensive test for int_to_fp: Int→FP24 and Int→FP16

module tb_int_to_fp_all;

    parameter INT_WIDTH = 64;
    parameter FRAC_BITS = 32;
    
    logic clk, rst_n;
    
    // Int → FP24
    logic [INT_WIDTH-1:0] i_int24;
    logic i_valid24;
    logic [23:0] o_fp24;
    logic o_valid24;
    
    // Int → FP16
    logic [INT_WIDTH-1:0] i_int16;
    logic i_valid16;
    logic [15:0] o_fp16;
    logic o_valid16;
    
    integer test_count, pass_count, fail_count;
    
    // Clock
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end
    
    // DUT: Int → FP24
    int_to_fp #(
        .INT_WIDTH(INT_WIDTH),
        .FP_WIDTH(24),
        .FRAC_BITS(FRAC_BITS)
    ) dut_fp24 (
        .clk(clk),
        .rst_n(rst_n),
        .i_int(i_int24),
        .i_valid(i_valid24),
        .o_fp(o_fp24),
        .o_valid(o_valid24)
    );
    
    // DUT: Int → FP16
    int_to_fp #(
        .INT_WIDTH(INT_WIDTH),
        .FP_WIDTH(16),
        .FRAC_BITS(FRAC_BITS)
    ) dut_fp16 (
        .clk(clk),
        .rst_n(rst_n),
        .i_int(i_int16),
        .i_valid(i_valid16),
        .o_fp(o_fp16),
        .o_valid(o_valid16)
    );
    
    // Test
    initial begin
        $display("\n========================================");
        $display("Integer → FP Conversion Comprehensive Test");
        $display("========================================\n");
        
        test_count = 0;
        pass_count = 0;
        fail_count = 0;
        
        rst_n = 0;
        i_int24 = 0;
        i_int16 = 0;
        i_valid24 = 0;
        i_valid16 = 0;
        repeat(5) @(posedge clk);
        rst_n = 1;
        repeat(2) @(posedge clk);
        
        $display("=== Testing Integer → FP24 ===\n");
        test_to_fp24(128'h0, "Zero");
        test_to_fp24(128'h1000000000000, "1.0");
        test_to_fp24(128'h2000000000000, "2.0");
        test_to_fp24(128'h4000000000000, "4.0");
        test_to_fp24(128'h800000000000, "0.5");
        test_to_fp24(128'h400000000000, "0.25");
        test_to_fp24(128'hFFFFFFFFFFFFFFFFFFFFFFFF000000000000, "-1.0");
        test_to_fp24(128'hFFFFFFFFFFFFFFFFFFFFFFFE000000000000, "-2.0");
        test_to_fp24(128'hA000000000000, "10.0");
        test_to_fp24(128'h64000000000000, "100.0");
        test_to_fp24(128'h4000000000000, "4.0 (sum)");
        test_to_fp24(128'h8000000000000, "8.0 (sum)");
        
        $display("\n=== Testing Integer → FP16 ===\n");
        test_to_fp16(128'h0, "Zero");
        test_to_fp16(128'h1000000000000, "1.0");
        test_to_fp16(128'h2000000000000, "2.0");
        test_to_fp16(128'h4000000000000, "4.0");
        test_to_fp16(128'h800000000000, "0.5");
        test_to_fp16(128'h400000000000, "0.25");
        test_to_fp16(128'hFFFFFFFFFFFFFFFFFFFFFFFF000000000000, "-1.0");
        test_to_fp16(128'hFFFFFFFFFFFFFFFFFFFFFFFE000000000000, "-2.0");
        test_to_fp16(128'hA000000000000, "10.0");
        test_to_fp16(128'h64000000000000, "100.0");
        test_to_fp16(128'h10000000000000, "16.0 (sum)");
        test_to_fp16(128'h20000000000000, "32.0 (sum)");
        
        $display("\n========================================");
        $display("Total: %0d  Pass: %0d  Fail: %0d", test_count, pass_count, fail_count);
        $display("========================================");
        
        if (fail_count == 0)
            $display("✓ ALL TESTS PASSED\n");
        else
            $display("✗ %0d TESTS FAILED\n", fail_count);
        
        $finish;
    end
    
    task test_to_fp24(input logic [127:0] int_val, input string desc);
        begin
            @(posedge clk);
            i_int24 = int_val;
            i_valid24 = 1;
            
            @(posedge clk);
            i_valid24 = 0;
            
            repeat(2) @(posedge clk);  // 2-cycle latency
            
            test_count++;
            
            if (o_valid24) begin
                $display("[%2d] FP24 %s: 0x%032x → 0x%06x (exp=%3d)", 
                         test_count, desc, int_val, o_fp24, o_fp24[22:15]);
                if (int_val != 0 && o_fp24 == 0) begin
                    $display("     ✗ FAIL: Non-zero input produced zero output");
                    fail_count++;
                end else if (o_fp24[22:15] == 8'hFF) begin
                    $display("     ✗ FAIL: Overflow to infinity");
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
    
    task test_to_fp16(input logic [127:0] int_val, input string desc);
        begin
            @(posedge clk);
            i_int16 = int_val;
            i_valid16 = 1;
            
            @(posedge clk);
            i_valid16 = 0;
            
            repeat(2) @(posedge clk);  // 2-cycle latency
            
            test_count++;
            
            if (o_valid16) begin
                $display("[%2d] FP16 %s: 0x%032x → 0x%04x (exp=%2d)", 
                         test_count, desc, int_val, o_fp16, o_fp16[14:10]);
                if (int_val != 0 && o_fp16 == 0) begin
                    $display("     ✗ FAIL: Non-zero input produced zero output");
                    fail_count++;
                end else if (o_fp16[14:10] == 5'h1F) begin
                    $display("     ✗ FAIL: Overflow to infinity");
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


