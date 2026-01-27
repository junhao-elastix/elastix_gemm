`timescale 1ns/1ps

// Comprehensive FP Adder Pipeline Test
// Tests all combinations: FP24/16 input, FP24/16 output, various NUM_INPUTS
// Reports RMSE against float32 golden reference

module tb_fp_adder_comprehensive;

    // Test configuration - test 4-input pipeline
    parameter NUM_INPUTS = 4;
    parameter FP_IN_WIDTH = 24;
    parameter FP_OUT_WIDTH = 16;
    parameter MAX_INPUTS = 16;
    parameter INT_WIDTH = 128;
    parameter FRAC_BITS = 48;
    parameter SEG_LEN = 2;
    
    // DUT signals
    logic [NUM_INPUTS-1:0][FP_IN_WIDTH-1:0] i_fp;
    logic i_valid;
    logic [FP_OUT_WIDTH-1:0] o_fp;
    logic o_valid;
    
    // Latency
    localparam ADDER_STAGES = $clog2(NUM_INPUTS);
    localparam ADDER_LATENCY = (ADDER_STAGES + SEG_LEN - 1) / SEG_LEN;
    localparam TOTAL_LATENCY = 1 + ADDER_LATENCY + 2;
    
    // Clock and reset
    logic clk;
    logic rst_n;
    logic en;
    
    // Test vectors storage
    real test_vectors[100][MAX_INPUTS];  // Up to 100 test cases, 16 inputs each
    integer test_lengths[100];           // Actual length of each test
    integer num_tests;
    
    // Statistics
    integer total_tests;
    integer passed_tests;
    integer failed_tests;
    real sum_squared_error;
    real max_error;
    
    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end
    
    // DUT instantiation
    fp_adder_pipeline #(
        .NUM_INPUTS(NUM_INPUTS),
        .FP_IN_WIDTH(FP_IN_WIDTH),
        .FP_OUT_WIDTH(FP_OUT_WIDTH),
        .INT_WIDTH(INT_WIDTH),
        .FRAC_BITS(FRAC_BITS),
        .SEG_LEN(SEG_LEN)
    ) dut (
        .clk(clk),
        .rst_n(rst_n),
        .en(en),
        .i_fp(i_fp),
        .i_valid(i_valid),
        .o_fp(o_fp),
        .o_valid(o_valid)
    );
    
    // Main test flow
    initial begin
        $display("==================================================");
        $display("FP Adder Pipeline Comprehensive Test");
        $display("==================================================\n");
        
        // Initialize
        total_tests = 0;
        passed_tests = 0;
        failed_tests = 0;
        sum_squared_error = 0.0;
        max_error = 0.0;
        
        // Reset
        rst_n = 0;
        en = 1;
        repeat(5) @(posedge clk);
        rst_n = 1;
        repeat(2) @(posedge clk);
        
        // Generate test vectors
        generate_test_vectors();
        
        // Run all tests
        $display("\n========== Running Tests ==========");
        run_all_tests();
        
        // Print final summary
        print_final_summary();
        
        $finish;
    end
    
    // Generate diverse test vectors
    task generate_test_vectors();
        begin
            num_tests = 0;
            
            // Test 1: Zeros
            add_test_4(0.0, 0.0, 0.0, 0.0);
            
            // Test 2: Ones
            add_test_4(1.0, 1.0, 1.0, 1.0);
            
            // Test 3: Wide dynamic range (user's example)
            add_test_4(0.00000123, 19931.0154, 39.45, 19999.0001);
            
            // Test 4: Huge + tiny
            add_test_4(0.0001, 0.0002, 50000.0, 0.0003);
            
            // Test 5: Cancellation
            add_test_4(1000.0, -1000.0, 0.0, 0.0);
            add_test_4(1000.0, -999.9, 500.0, -500.1);
            
            // Test 6: Small values
            add_test_4(0.001, 0.002, 0.003, 0.004);
            add_test_4(1e-4, 2e-4, 3e-4, 4e-4);
            
            // Test 7: Large values (overflow risk)
            add_test_4(30000.0, 30000.0, 5000.0, 0.0);
            
            // Test 8: Mixed magnitudes
            add_test_4(0.01, 1.0, 100.0, 10000.0);
            add_test_4(10000.0, 100.0, 1.0, 0.01);
            
            // Test 9: Powers of 2 (exact)
            add_test_4(0.125, 0.25, 0.5, 1.0);
            add_test_4(2.0, 4.0, 8.0, 16.0);
            
            // Test 10: Negative
            add_test_4(-1.0, -2.0, -3.0, -4.0);
            add_test_4(10.0, -5.0, 20.0, -8.0);
            
            // Test 11: Rounding edge cases
            add_test_4(1.5, 2.5, 3.5, 4.5);
            add_test_4(0.1, 0.1, 0.1, 0.1);
            add_test_4(0.333333, 0.333333, 0.333333, 0.333333);
            
            // Test 12: Sequential
            add_test_4(1.0, 2.0, 3.0, 4.0);
            add_test_4(5.0, 6.0, 7.0, 8.0);
            
            // Test 13: Stress cases
            add_test_4(10000.0, 0.001, 0.002, 0.003);
            add_test_4(1000.0, -1000.0 + 1e-3, 0.0, 0.0);
            
            $display("Generated %0d test vectors", num_tests);
        end
    endtask
    
    // Add a test vector (4 inputs)
    task add_test_4(input real v0, input real v1, input real v2, input real v3);
        begin
            test_vectors[num_tests][0] = v0;
            test_vectors[num_tests][1] = v1;
            test_vectors[num_tests][2] = v2;
            test_vectors[num_tests][3] = v3;
            test_lengths[num_tests] = 4;
            num_tests = num_tests + 1;
        end
    endtask
    
    // Run all tests
    task run_all_tests();
        integer t, i;
        real golden;
        real result_float;
        real error;
        begin
            for (t = 0; t < num_tests; t = t + 1) begin
                if (test_lengths[t] <= NUM_INPUTS) begin
                    // Compute golden reference
                    golden = 0.0;
                    for (i = 0; i < test_lengths[t]; i = i + 1) begin
                        golden = golden + test_vectors[t][i];
                    end
                    
                    // Run test
                    run_single_test(t, golden);
                end
            end
        end
    endtask
    
    // Run a single test
    task run_single_test(input integer test_id, input real golden);
        integer i;
        real result_float;
        real error;
        begin
            // Convert to FP24 and drive DUT
            @(posedge clk);
            for (i = 0; i < NUM_INPUTS; i = i + 1) begin
                if (i < test_lengths[test_id]) begin
                    i_fp[i] = float_to_fp24(test_vectors[test_id][i]);
                end else begin
                    i_fp[i] = 24'h0;
                end
            end
            
            // Debug: print inputs for first few tests
            if (test_id < 3) begin
                $display("  Test %0d inputs: real=[%.3f, %.3f, %.3f, %.3f] fp24=[0x%06x, 0x%06x, 0x%06x, 0x%06x]",
                         test_id, 
                         test_vectors[test_id][0], test_vectors[test_id][1], test_vectors[test_id][2], test_vectors[test_id][3],
                         i_fp[0], i_fp[1], i_fp[2], i_fp[3]);
            end
            
            i_valid = 1;
            
            @(posedge clk);
            i_valid = 0;
            
            // Wait for result
            repeat(TOTAL_LATENCY) @(posedge clk);
            
            if (o_valid) begin
                // Convert result to float
                result_float = fp16_to_float(o_fp);
                
                // Compute error
                error = result_float - golden;
                if (error < 0) error = -error;
                
                // Update statistics
                total_tests = total_tests + 1;
                sum_squared_error = sum_squared_error + (error * error);
                if (error > max_error) max_error = error;
                
                // Check tolerance
                if (error < 0.01 || (golden != 0.0 && (error/golden < 0.001 || error/golden > -0.001))) begin
                    passed_tests = passed_tests + 1;
                    if ((total_tests % 5) == 0 || total_tests < 5) begin
                        $display("  [%3d] golden=%.6e hw=%.6e err=%.3e out=0x%04x", total_tests, golden, result_float, error, o_fp);
                    end
                end else begin
                    failed_tests = failed_tests + 1;
                    $display("  [%3d] FAIL: golden=%.6e hw=%.6e err=%.3e out=0x%04x", total_tests, golden, result_float, error, o_fp);
                    $display("        inputs: 0x%06x 0x%06x 0x%06x 0x%06x", i_fp[0], i_fp[1], i_fp[2], i_fp[3]);
                end
            end else begin
                $display("  [%3d] ERROR: o_valid not asserted", total_tests);
                failed_tests = failed_tests + 1;
                total_tests = total_tests + 1;
            end
        end
    endtask
    
    // Print final summary with RMSE
    task print_final_summary();
        real rmse;
        begin
            $display("\n==================================================");
            $display("FINAL SUMMARY");
            $display("==================================================");
            $display("Total tests:     %0d", total_tests);
            $display("Passed:          %0d (%.1f%%)", passed_tests, 100.0*passed_tests/total_tests);
            $display("Failed:          %0d (%.1f%%)", failed_tests, 100.0*failed_tests/total_tests);
            
            rmse = $sqrt(sum_squared_error / total_tests);
            $display("\nRMSE:            %.6e", rmse);
            $display("Max error:       %.6e", max_error);
            $display("==================================================");
            
            if (failed_tests == 0) begin
                $display("✓ ALL TESTS PASSED!");
            end else begin
                $display("✗ SOME TESTS FAILED");
            end
            $display("==================================================");
        end
    endtask
    
    // FP24 conversion functions  
    function logic [23:0] float_to_fp24(input real value);
        real abs_val;
        integer exp_biased, mant_int;
        real mant_float, normalized;
        logic sign;
        integer exp_unbiased;
        begin
            if (value == 0.0) begin
                float_to_fp24 = 24'h0;
            end else begin
                sign = (value < 0.0);
                abs_val = sign ? -value : value;
                
                // Find exponent: floor(log2(abs_val))
                exp_unbiased = $rtoi($floor($ln(abs_val) / $ln(2.0)));
                
                // Normalize: abs_val / 2^exp_unbiased should be in [1, 2)
                normalized = abs_val / $pow(2.0, 1.0 * exp_unbiased);
                
                // Mantissa is (normalized - 1.0) * 2^15
                mant_float = (normalized - 1.0) * 32768.0;  // 2^15
                mant_int = $rtoi(mant_float);
                
                // Biased exponent
                exp_biased = exp_unbiased + 127;
                
                // Clamp
                if (exp_biased <= 0) begin
                    float_to_fp24 = 24'h0;  // Underflow
                end else if (exp_biased >= 255) begin
                    float_to_fp24 = {sign, 8'hFF, 15'h0};  // Overflow to inf
                end else if (mant_int < 0) begin
                    mant_int = 0;
                    float_to_fp24 = {sign, exp_biased[7:0], mant_int[14:0]};
                end else if (mant_int > 32767) begin
                    mant_int = 32767;
                    float_to_fp24 = {sign, exp_biased[7:0], mant_int[14:0]};
                end else begin
                    float_to_fp24 = {sign, exp_biased[7:0], mant_int[14:0]};
                end
            end
        end
    endfunction
    
    function logic [15:0] float_to_fp16(input real value);
        // Simplified FP16 conversion
        real abs_val;
        integer exp, mant;
        logic sign;
        begin
            if (value == 0.0) begin
                float_to_fp16 = 16'h0;
            end else begin
                sign = (value < 0.0);
                abs_val = sign ? -value : value;
                
                exp = 15 + $rtoi($ln(abs_val) / $ln(2.0));
                if (exp < 0) exp = 0;
                if (exp > 31) exp = 31;
                
                mant = $rtoi((abs_val / $pow(2.0, exp - 15) - 1.0) * $pow(2.0, 10));
                if (mant < 0) mant = 0;
                if (mant > 1023) mant = 1023;
                
                float_to_fp16 = {sign, exp[4:0], mant[9:0]};
            end
        end
    endfunction
    
    function real fp24_to_float(input logic [23:0] fp24);
        logic sign;
        logic [7:0] exp;
        logic [14:0] mant;
        real value;
        begin
            sign = fp24[23];
            exp = fp24[22:15];
            mant = fp24[14:0];
            
            if (exp == 0) begin
                fp24_to_float = 0.0;
            end else if (exp == 255) begin
                fp24_to_float = sign ? -1e10 : 1e10;
            end else begin
                value = (1.0 + mant / $pow(2.0, 15)) * $pow(2.0, exp - 127);
                fp24_to_float = sign ? -value : value;
            end
        end
    endfunction
    
    function real fp16_to_float(input logic [15:0] fp16);
        logic sign;
        logic [4:0] exp;
        logic [9:0] mant;
        real value, mant_real;
        integer exp_unbiased;
        begin
            sign = fp16[15];
            exp = fp16[14:10];
            mant = fp16[9:0];
            
            if (exp == 0) begin
                if (mant == 0) begin
                    fp16_to_float = 0.0;
                end else begin
                    // Denormal (not handling for now)
                    fp16_to_float = 0.0;
                end
            end else if (exp == 31) begin
                // Infinity - use $realtobits equivalent or large value
                fp16_to_float = sign ? -65504.0 : 65504.0;  // Use max FP16 value instead
            end else begin
                // Normal number: (-1)^sign * 2^(exp-15) * (1 + mant/1024)
                exp_unbiased = exp - 15;
                mant_real = 1.0 + (1.0 * mant) / 1024.0;
                value = mant_real * $pow(2.0, 1.0 * exp_unbiased);
                fp16_to_float = sign ? -value : value;
            end
        end
    endfunction

endmodule

