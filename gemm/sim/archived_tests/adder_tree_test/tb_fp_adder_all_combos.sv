`timescale 1ns/1ps

// Comprehensive FP Adder Pipeline Test - All Combinations
// Tests: FP24→FP24, FP24→FP16, FP16→FP16, FP16→FP24
// Input counts: 4, 8, 16, 32

module tb_fp_adder_all_combos;

    parameter INT_WIDTH = 64;
    parameter FRAC_BITS = 32;
    
    logic clk, rst_n;
    
    // Test statistics
    integer total_tests, passed_tests, failed_tests;
    real total_squared_error;
    real max_error;
    string current_config;
    
    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end
    
    // ===== DUT Instantiations =====
    
    // FP24→FP24 with 4 inputs
    logic [3:0][23:0] fp24_24_4_in;
    logic fp24_24_4_valid_in;
    logic [23:0] fp24_24_4_out;
    logic fp24_24_4_valid_out;
    
    fp_adder_pipeline #(.NUM_INPUTS(4), .FP_IN_WIDTH(24), .FP_OUT_WIDTH(24), 
                        .INT_WIDTH(INT_WIDTH), .FRAC_BITS(FRAC_BITS))
    dut_fp24_24_4 (
        .clk(clk), .rst_n(rst_n), .en(1'b1),
        .i_fp(fp24_24_4_in), .i_valid(fp24_24_4_valid_in),
        .o_fp(fp24_24_4_out), .o_valid(fp24_24_4_valid_out)
    );
    
    // FP24→FP24 with 8 inputs
    logic [7:0][23:0] fp24_24_8_in;
    logic fp24_24_8_valid_in;
    logic [23:0] fp24_24_8_out;
    logic fp24_24_8_valid_out;
    
    fp_adder_pipeline #(.NUM_INPUTS(8), .FP_IN_WIDTH(24), .FP_OUT_WIDTH(24),
                        .INT_WIDTH(INT_WIDTH), .FRAC_BITS(FRAC_BITS))
    dut_fp24_24_8 (
        .clk(clk), .rst_n(rst_n), .en(1'b1),
        .i_fp(fp24_24_8_in), .i_valid(fp24_24_8_valid_in),
        .o_fp(fp24_24_8_out), .o_valid(fp24_24_8_valid_out)
    );
    
    // FP24→FP24 with 16 inputs
    logic [15:0][23:0] fp24_24_16_in;
    logic fp24_24_16_valid_in;
    logic [23:0] fp24_24_16_out;
    logic fp24_24_16_valid_out;
    
    fp_adder_pipeline #(.NUM_INPUTS(16), .FP_IN_WIDTH(24), .FP_OUT_WIDTH(24),
                        .INT_WIDTH(INT_WIDTH), .FRAC_BITS(FRAC_BITS))
    dut_fp24_24_16 (
        .clk(clk), .rst_n(rst_n), .en(1'b1),
        .i_fp(fp24_24_16_in), .i_valid(fp24_24_16_valid_in),
        .o_fp(fp24_24_16_out), .o_valid(fp24_24_16_valid_out)
    );
    
    // FP24→FP16 with 4 inputs
    logic [3:0][23:0] fp24_16_4_in;
    logic fp24_16_4_valid_in;
    logic [15:0] fp24_16_4_out;
    logic fp24_16_4_valid_out;
    
    fp_adder_pipeline #(.NUM_INPUTS(4), .FP_IN_WIDTH(24), .FP_OUT_WIDTH(16),
                        .INT_WIDTH(INT_WIDTH), .FRAC_BITS(FRAC_BITS))
    dut_fp24_16_4 (
        .clk(clk), .rst_n(rst_n), .en(1'b1),
        .i_fp(fp24_16_4_in), .i_valid(fp24_16_4_valid_in),
        .o_fp(fp24_16_4_out), .o_valid(fp24_16_4_valid_out)
    );
    
    // FP24→FP16 with 8 inputs
    logic [7:0][23:0] fp24_16_8_in;
    logic fp24_16_8_valid_in;
    logic [15:0] fp24_16_8_out;
    logic fp24_16_8_valid_out;
    
    fp_adder_pipeline #(.NUM_INPUTS(8), .FP_IN_WIDTH(24), .FP_OUT_WIDTH(16),
                        .INT_WIDTH(INT_WIDTH), .FRAC_BITS(FRAC_BITS))
    dut_fp24_16_8 (
        .clk(clk), .rst_n(rst_n), .en(1'b1),
        .i_fp(fp24_16_8_in), .i_valid(fp24_16_8_valid_in),
        .o_fp(fp24_16_8_out), .o_valid(fp24_16_8_valid_out)
    );
    
    // FP16→FP16 with 4 inputs
    logic [3:0][15:0] fp16_16_4_in;
    logic fp16_16_4_valid_in;
    logic [15:0] fp16_16_4_out;
    logic fp16_16_4_valid_out;
    
    fp_adder_pipeline #(.NUM_INPUTS(4), .FP_IN_WIDTH(16), .FP_OUT_WIDTH(16),
                        .INT_WIDTH(INT_WIDTH), .FRAC_BITS(FRAC_BITS))
    dut_fp16_16_4 (
        .clk(clk), .rst_n(rst_n), .en(1'b1),
        .i_fp(fp16_16_4_in), .i_valid(fp16_16_4_valid_in),
        .o_fp(fp16_16_4_out), .o_valid(fp16_16_4_valid_out)
    );
    
    // FP16→FP16 with 8 inputs
    logic [7:0][15:0] fp16_16_8_in;
    logic fp16_16_8_valid_in;
    logic [15:0] fp16_16_8_out;
    logic fp16_16_8_valid_out;
    
    fp_adder_pipeline #(.NUM_INPUTS(8), .FP_IN_WIDTH(16), .FP_OUT_WIDTH(16),
                        .INT_WIDTH(INT_WIDTH), .FRAC_BITS(FRAC_BITS))
    dut_fp16_16_8 (
        .clk(clk), .rst_n(rst_n), .en(1'b1),
        .i_fp(fp16_16_8_in), .i_valid(fp16_16_8_valid_in),
        .o_fp(fp16_16_8_out), .o_valid(fp16_16_8_valid_out)
    );
    
    // FP16→FP24 with 4 inputs
    logic [3:0][15:0] fp16_24_4_in;
    logic fp16_24_4_valid_in;
    logic [23:0] fp16_24_4_out;
    logic fp16_24_4_valid_out;
    
    fp_adder_pipeline #(.NUM_INPUTS(4), .FP_IN_WIDTH(16), .FP_OUT_WIDTH(24),
                        .INT_WIDTH(INT_WIDTH), .FRAC_BITS(FRAC_BITS))
    dut_fp16_24_4 (
        .clk(clk), .rst_n(rst_n), .en(1'b1),
        .i_fp(fp16_24_4_in), .i_valid(fp16_24_4_valid_in),
        .o_fp(fp16_24_4_out), .o_valid(fp16_24_4_valid_out)
    );
    
    // FP16→FP24 with 8 inputs
    logic [7:0][15:0] fp16_24_8_in;
    logic fp16_24_8_valid_in;
    logic [23:0] fp16_24_8_out;
    logic fp16_24_8_valid_out;
    
    fp_adder_pipeline #(.NUM_INPUTS(8), .FP_IN_WIDTH(16), .FP_OUT_WIDTH(24),
                        .INT_WIDTH(INT_WIDTH), .FRAC_BITS(FRAC_BITS))
    dut_fp16_24_8 (
        .clk(clk), .rst_n(rst_n), .en(1'b1),
        .i_fp(fp16_24_8_in), .i_valid(fp16_24_8_valid_in),
        .o_fp(fp16_24_8_out), .o_valid(fp16_24_8_valid_out)
    );
    
    // ===== Test Main =====
    initial begin
        $display("\n========================================================================");
        $display("FP Adder Pipeline - Comprehensive Test Suite");
        $display("Testing all 4 combinations with 4, 8, 16 input counts");
        $display("========================================================================\n");
        
        total_tests = 0;
        passed_tests = 0;
        failed_tests = 0;
        total_squared_error = 0.0;
        max_error = 0.0;
        
        // Reset
        rst_n = 0;
        fp24_24_4_valid_in = 0;
        fp24_24_8_valid_in = 0;
        fp24_24_16_valid_in = 0;
        fp24_16_4_valid_in = 0;
        fp24_16_8_valid_in = 0;
        fp16_16_4_valid_in = 0;
        fp16_16_8_valid_in = 0;
        fp16_24_4_valid_in = 0;
        fp16_24_8_valid_in = 0;
        repeat(5) @(posedge clk);
        rst_n = 1;
        repeat(2) @(posedge clk);
        
        // Run all test configurations
        test_fp24_to_fp24_4();
        test_fp24_to_fp24_8();
        test_fp24_to_fp24_16();
        
        test_fp24_to_fp16_4();
        test_fp24_to_fp16_8();
        
        test_fp16_to_fp16_4();
        test_fp16_to_fp16_8();
        
        test_fp16_to_fp24_4();
        test_fp16_to_fp24_8();
        
        // Final summary
        $display("\n========================================================================");
        $display("FINAL RESULTS");
        $display("========================================================================");
        $display("Total Tests:     %0d", total_tests);
        $display("Passed:          %0d (%.1f%%)", passed_tests, 100.0*passed_tests/total_tests);
        $display("Failed:          %0d (%.1f%%)", failed_tests, 100.0*failed_tests/total_tests);
        if (total_tests > 0) begin
            $display("RMSE:            %.6e", $sqrt(total_squared_error / total_tests));
            $display("Max Error:       %.6e", max_error);
        end
        $display("========================================================================");
        
        if (failed_tests == 0)
            $display("✓ ALL TESTS PASSED\n");
        else
            $display("✗ SOME TESTS FAILED\n");
        
        $finish;
    end
    
    // ===== Test Tasks for Each Configuration =====
    
    task test_fp24_to_fp24_4();
        real inputs[4];
        real golden;
        
        current_config = "FP24→FP24 (4 inputs)";
        $display("\n=== %s ===", current_config);
        
        // Test 1: All zeros
        inputs = '{0.0, 0.0, 0.0, 0.0};
        golden = 0.0;
        run_test_24_24_4(inputs, golden, "All zeros");
        
        // Test 2: All ones
        inputs = '{1.0, 1.0, 1.0, 1.0};
        golden = 4.0;
        run_test_24_24_4(inputs, golden, "All ones");
        
        // Test 3: Powers of 2
        inputs = '{1.0, 2.0, 4.0, 8.0};
        golden = 15.0;
        run_test_24_24_4(inputs, golden, "Powers of 2");
        
        // Test 4: Mixed small
        inputs = '{0.1, 0.2, 0.3, 0.4};
        golden = 1.0;
        run_test_24_24_4(inputs, golden, "Mixed small");
        
        // Test 5: Wide range
        inputs = '{0.00000123, 19931.015, 39.45, 19999.0};
        golden = 39969.465;
        run_test_24_24_4(inputs, golden, "Wide range");
        
        // Test 6: Alternating signs
        inputs = '{10.0, -10.0, 5.0, -5.0};
        golden = 0.0;
        run_test_24_24_4(inputs, golden, "Alt signs");
    endtask
    
    task test_fp24_to_fp24_8();
        real inputs[8];
        real golden;
        
        current_config = "FP24→FP24 (8 inputs)";
        $display("\n=== %s ===", current_config);
        
        inputs = '{1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0};
        golden = 8.0;
        run_test_24_24_8(inputs, golden, "8 ones");
        
        inputs = '{1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0};
        golden = 36.0;
        run_test_24_24_8(inputs, golden, "1..8");
        
        inputs = '{100.0, 200.0, 300.0, 400.0, 0.1, 0.2, 0.3, 0.4};
        golden = 1001.0;
        run_test_24_24_8(inputs, golden, "Large+small");
    endtask
    
    task test_fp24_to_fp24_16();
        real inputs[16];
        real golden;
        integer i;
        
        current_config = "FP24→FP24 (16 inputs)";
        $display("\n=== %s ===", current_config);
        
        for (i = 0; i < 16; i = i + 1) inputs[i] = 1.0;
        golden = 16.0;
        run_test_24_24_16(inputs, golden, "16 ones");
        
        for (i = 0; i < 16; i = i + 1) inputs[i] = i + 1.0;
        golden = 136.0;  // Sum 1..16
        run_test_24_24_16(inputs, golden, "1..16");
    endtask
    
    task test_fp24_to_fp16_4();
        real inputs[4];
        real golden;
        
        current_config = "FP24→FP16 (4 inputs)";
        $display("\n=== %s ===", current_config);
        
        inputs = '{1.0, 1.0, 1.0, 1.0};
        golden = 4.0;
        run_test_24_16_4(inputs, golden, "All ones");
        
        inputs = '{10.5, 20.25, 30.75, 40.5};
        golden = 102.0;
        run_test_24_16_4(inputs, golden, "Decimals");
    endtask
    
    task test_fp24_to_fp16_8();
        real inputs[8];
        real golden;
        
        current_config = "FP24→FP16 (8 inputs)";
        $display("\n=== %s ===", current_config);
        
        inputs = '{1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0};
        golden = 8.0;
        run_test_24_16_8(inputs, golden, "8 ones");
    endtask
    
    task test_fp16_to_fp16_4();
        real inputs[4];
        real golden;
        
        current_config = "FP16→FP16 (4 inputs)";
        $display("\n=== %s ===", current_config);
        
        inputs = '{1.0, 1.0, 1.0, 1.0};
        golden = 4.0;
        run_test_16_16_4(inputs, golden, "All ones");
        
        inputs = '{0.5, 0.5, 0.5, 0.5};
        golden = 2.0;
        run_test_16_16_4(inputs, golden, "All 0.5");
    endtask
    
    task test_fp16_to_fp16_8();
        real inputs[8];
        real golden;
        
        current_config = "FP16→FP16 (8 inputs)";
        $display("\n=== %s ===", current_config);
        
        inputs = '{1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0};
        golden = 8.0;
        run_test_16_16_8(inputs, golden, "8 ones");
    endtask
    
    task test_fp16_to_fp24_4();
        real inputs[4];
        real golden;
        
        current_config = "FP16→FP24 (4 inputs)";
        $display("\n=== %s ===", current_config);
        
        inputs = '{1.0, 1.0, 1.0, 1.0};
        golden = 4.0;
        run_test_16_24_4(inputs, golden, "All ones");
    endtask
    
    task test_fp16_to_fp24_8();
        real inputs[8];
        real golden;
        
        current_config = "FP16→FP24 (8 inputs)";
        $display("\n=== %s ===", current_config);
        
        inputs = '{1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0};
        golden = 8.0;
        run_test_16_24_8(inputs, golden, "8 ones");
    endtask
    
    // ===== Run Test Helper Tasks =====
    
    task run_test_24_24_4(input real vals[4], input real golden, input string desc);
        integer i, wait_cnt;
        for (i = 0; i < 4; i = i + 1) fp24_24_4_in[i] = real_to_fp24(vals[i]);
        
        $display("  DEBUG: Inputs = [0x%06x, 0x%06x, 0x%06x, 0x%06x]", 
                 fp24_24_4_in[0], fp24_24_4_in[1], fp24_24_4_in[2], fp24_24_4_in[3]);
        
        @(posedge clk);
        fp24_24_4_valid_in = 1;
        @(posedge clk);
        fp24_24_4_valid_in = 0;
        
        wait_cnt = 0;
        while (!fp24_24_4_valid_out && wait_cnt < 30) begin
            @(posedge clk);
            wait_cnt = wait_cnt + 1;
        end
        
        $display("  DEBUG: wait_cnt=%0d valid_out=%b output=0x%06x", 
                 wait_cnt, fp24_24_4_valid_out, fp24_24_4_out);
        
        check_result(fp24_24_4_valid_out, fp24_to_real(fp24_24_4_out), golden, desc);
    endtask
    
    task run_test_24_24_8(input real vals[8], input real golden, input string desc);
        integer i, wait_cnt;
        for (i = 0; i < 8; i = i + 1) fp24_24_8_in[i] = real_to_fp24(vals[i]);
        @(posedge clk);
        fp24_24_8_valid_in = 1;
        @(posedge clk);
        fp24_24_8_valid_in = 0;
        wait_cnt = 0;
        while (!fp24_24_8_valid_out && wait_cnt < 30) begin @(posedge clk); wait_cnt++; end
        check_result(fp24_24_8_valid_out, fp24_to_real(fp24_24_8_out), golden, desc);
    endtask
    
    task run_test_24_24_16(input real vals[16], input real golden, input string desc);
        integer i, wait_cnt;
        for (i = 0; i < 16; i = i + 1) fp24_24_16_in[i] = real_to_fp24(vals[i]);
        @(posedge clk);
        fp24_24_16_valid_in = 1;
        @(posedge clk);
        fp24_24_16_valid_in = 0;
        wait_cnt = 0;
        while (!fp24_24_16_valid_out && wait_cnt < 30) begin @(posedge clk); wait_cnt++; end
        check_result(fp24_24_16_valid_out, fp24_to_real(fp24_24_16_out), golden, desc);
    endtask
    
    task run_test_24_16_4(input real vals[4], input real golden, input string desc);
        integer i, wait_cnt;
        for (i = 0; i < 4; i = i + 1) fp24_16_4_in[i] = real_to_fp24(vals[i]);
        @(posedge clk);
        fp24_16_4_valid_in = 1;
        @(posedge clk);
        fp24_16_4_valid_in = 0;
        wait_cnt = 0;
        while (!fp24_16_4_valid_out && wait_cnt < 30) begin @(posedge clk); wait_cnt++; end
        check_result(fp24_16_4_valid_out, fp16_to_real(fp24_16_4_out), golden, desc);
    endtask
    
    task run_test_24_16_8(input real vals[8], input real golden, input string desc);
        integer i, wait_cnt;
        for (i = 0; i < 8; i = i + 1) fp24_16_8_in[i] = real_to_fp24(vals[i]);
        @(posedge clk);
        fp24_16_8_valid_in = 1;
        @(posedge clk);
        fp24_16_8_valid_in = 0;
        wait_cnt = 0;
        while (!fp24_16_8_valid_out && wait_cnt < 30) begin @(posedge clk); wait_cnt++; end
        check_result(fp24_16_8_valid_out, fp16_to_real(fp24_16_8_out), golden, desc);
    endtask
    
    task run_test_16_16_4(input real vals[4], input real golden, input string desc);
        integer i, wait_cnt;
        for (i = 0; i < 4; i = i + 1) fp16_16_4_in[i] = real_to_fp16(vals[i]);
        @(posedge clk);
        fp16_16_4_valid_in = 1;
        @(posedge clk);
        fp16_16_4_valid_in = 0;
        wait_cnt = 0;
        while (!fp16_16_4_valid_out && wait_cnt < 30) begin @(posedge clk); wait_cnt++; end
        check_result(fp16_16_4_valid_out, fp16_to_real(fp16_16_4_out), golden, desc);
    endtask
    
    task run_test_16_16_8(input real vals[8], input real golden, input string desc);
        integer i, wait_cnt;
        for (i = 0; i < 8; i = i + 1) fp16_16_8_in[i] = real_to_fp16(vals[i]);
        @(posedge clk);
        fp16_16_8_valid_in = 1;
        @(posedge clk);
        fp16_16_8_valid_in = 0;
        wait_cnt = 0;
        while (!fp16_16_8_valid_out && wait_cnt < 30) begin @(posedge clk); wait_cnt++; end
        check_result(fp16_16_8_valid_out, fp16_to_real(fp16_16_8_out), golden, desc);
    endtask
    
    task run_test_16_24_4(input real vals[4], input real golden, input string desc);
        integer i, wait_cnt;
        for (i = 0; i < 4; i = i + 1) fp16_24_4_in[i] = real_to_fp16(vals[i]);
        @(posedge clk);
        fp16_24_4_valid_in = 1;
        @(posedge clk);
        fp16_24_4_valid_in = 0;
        wait_cnt = 0;
        while (!fp16_24_4_valid_out && wait_cnt < 30) begin @(posedge clk); wait_cnt++; end
        check_result(fp16_24_4_valid_out, fp24_to_real(fp16_24_4_out), golden, desc);
    endtask
    
    task run_test_16_24_8(input real vals[8], input real golden, input string desc);
        integer i, wait_cnt;
        for (i = 0; i < 8; i = i + 1) fp16_24_8_in[i] = real_to_fp16(vals[i]);
        @(posedge clk);
        fp16_24_8_valid_in = 1;
        @(posedge clk);
        fp16_24_8_valid_in = 0;
        wait_cnt = 0;
        while (!fp16_24_8_valid_out && wait_cnt < 30) begin @(posedge clk); wait_cnt++; end
        check_result(fp16_24_8_valid_out, fp24_to_real(fp16_24_8_out), golden, desc);
    endtask
    
    // Check result
    task check_result(input logic valid_signal, input real hw_result, input real golden, input string desc);
        real error, rel_error;
        
        total_tests = total_tests + 1;
        
        if (valid_signal) begin
            error = (golden > hw_result) ? (golden - hw_result) : (hw_result - golden);
            rel_error = (golden != 0.0) ? error / ((golden < 0) ? -golden : golden) : error;
            
            total_squared_error = total_squared_error + error * error;
            if (error > max_error) max_error = error;
            
            // Pass if absolute error < 0.01 OR relative error < 1%
            if (error < 0.01 || rel_error < 0.01) begin
                passed_tests = passed_tests + 1;
                $display("  [%2d] PASS: %-20s golden=%.6e hw=%.6e err=%.2e", 
                         total_tests, desc, golden, hw_result, error);
            end else begin
                failed_tests = failed_tests + 1;
                $display("  [%2d] FAIL: %-20s golden=%.6e hw=%.6e err=%.2e (%.2f%%)",
                         total_tests, desc, golden, hw_result, error, rel_error*100);
            end
        end else begin
            failed_tests = failed_tests + 1;
            $display("  [%2d] FAIL: %-20s TIMEOUT waiting for o_valid", total_tests, desc);
        end
    endtask
    
    // ===== Conversion Functions =====
    
    function automatic logic [23:0] real_to_fp24(input real val);
        logic sign;
        integer exp;
        real mant, abs_val;
        logic [14:0] mant_bits;
        integer iter_cnt;
        
        if (val == 0.0) return 24'h0;
        
        sign = (val < 0.0);
        abs_val = (val < 0.0) ? -val : val;
        
        exp = 127;
        mant = abs_val;
        
        // Normalize: get mantissa in range [1.0, 2.0)
        iter_cnt = 0;
        while (mant >= 2.0 && exp < 254 && iter_cnt < 500) begin
            mant = mant / 2.0;
            exp = exp + 1;
            iter_cnt = iter_cnt + 1;
        end
        
        iter_cnt = 0;
        while (mant < 1.0 && exp > 0 && iter_cnt < 500) begin
            mant = mant * 2.0;
            exp = exp - 1;
            iter_cnt = iter_cnt + 1;
        end
        
        // Extract mantissa bits (fractional part)
        mant_bits = $rtoi((mant - 1.0) * 32768.0);  // 2^15 = 32768
        
        return {sign, exp[7:0], mant_bits};
    endfunction
    
    function automatic logic [15:0] real_to_fp16(input real val);
        logic sign;
        integer exp;
        real mant, abs_val;
        logic [9:0] mant_bits;
        integer iter_cnt;
        
        if (val == 0.0) return 16'h0;
        
        sign = (val < 0.0);
        abs_val = (val < 0.0) ? -val : val;
        
        exp = 15;
        mant = abs_val;
        
        // Normalize: get mantissa in range [1.0, 2.0)
        iter_cnt = 0;
        while (mant >= 2.0 && exp < 30 && iter_cnt < 500) begin
            mant = mant / 2.0;
            exp = exp + 1;
            iter_cnt = iter_cnt + 1;
        end
        
        iter_cnt = 0;
        while (mant < 1.0 && exp > 0 && iter_cnt < 500) begin
            mant = mant * 2.0;
            exp = exp - 1;
            iter_cnt = iter_cnt + 1;
        end
        
        // Extract mantissa bits (fractional part)
        mant_bits = $rtoi((mant - 1.0) * 1024.0);  // 2^10 = 1024
        
        return {sign, exp[4:0], mant_bits};
    endfunction
    
    function automatic real fp24_to_real(input logic [23:0] fp);
        logic sign;
        integer exp;
        real mant;
        
        if (fp == 24'h0) return 0.0;
        if (fp[22:15] == 8'hFF) return 999999.9;  // Infinity
        
        sign = fp[23];
        exp = fp[22:15];
        mant = 1.0 + ($itor(fp[14:0]) / 32768.0);
        
        fp24_to_real = mant * (2.0 ** (exp - 127));
        if (sign) fp24_to_real = -fp24_to_real;
    endfunction
    
    function automatic real fp16_to_real(input logic [15:0] fp);
        logic sign;
        integer exp;
        real mant;
        
        if (fp == 16'h0) return 0.0;
        if (fp[14:10] == 5'h1F) return 999999.9;  // Infinity
        
        sign = fp[15];
        exp = fp[14:10];
        mant = 1.0 + ($itor(fp[9:0]) / 1024.0);
        
        fp16_to_real = mant * (2.0 ** (exp - 15));
        if (sign) fp16_to_real = -fp16_to_real;
    endfunction

endmodule

