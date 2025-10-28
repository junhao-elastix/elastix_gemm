// ------------------------------------------------------------------
// Testbench for compute_engine_modular.sv (with integrated tile_bram)
//
// Purpose: Verify complete compute engine with integrated tile_bram and FP16 output
// Tests:
//  1. Simple case: B=1, C=1, V=1 (single NV dot product)
//  2. Small V loop: B=1, C=1, V=4 (accumulation test)
//  3. Multiple outputs: B=2, C=2, V=2 (full BCV test)
//  4-8. Real data with validation: Various B/C/V configurations
//
// Key Features:
//  - Simulates DISPATCH operation (writes data to tile_bram write ports)
//  - Four parallel tile_bram write paths (mantissa + exponent, left + right)
//  - FP16 result validation against golden references
//  - Golden reference loading from hex files
//
// Architecture:
//  testbench BRAM models → [DISPATCH] → DUT tile_bram → [TILE] → results
//
// Author: Compute Engine Modular Testing + Tile BRAM Integration
// Date: Mon Oct 27 2025
// ------------------------------------------------------------------

`timescale 1ns/1ps

module tb_compute_engine_modular;

    import gemm_pkg::*;

    // Clock and reset
    logic clk;
    logic reset_n;

    // TILE command interface (per SINGLE_ROW_REFERENCE.md)
    logic        tile_en;
    logic [15:0] left_addr;         // 16 bits: Left matrix start address
    logic [15:0] right_addr;        // 16 bits: Right matrix start address
    logic [7:0]  left_ugd_len;      // 8 bits: Left UGD vectors (Batch dimension)
    logic [7:0]  right_ugd_len;     // 8 bits: Right UGD vectors (Column dimension)
    logic [7:0]  vec_len;           // 8 bits: UGD vector size (Vector count)
    logic        left_man_4b;       // 1 bit: Left mantissa width (0=8b, 1=4b)
    logic        right_man_4b;      // 1 bit: Right mantissa width (0=8b, 1=4b)
    logic        main_loop_over_left; // 1 bit: Main loop dimension selector
    logic        tile_done;

    // Tile BRAM Write Interface (simulating DISPATCH operation)
    // Four parallel write ports - all can write in same cycle
    logic [8:0]    man_left_wr_addr;
    logic [255:0]  man_left_wr_data;
    logic          man_left_wr_en;

    logic [8:0]    man_right_wr_addr;
    logic [255:0]  man_right_wr_data;
    logic          man_right_wr_en;

    logic [8:0]    left_exp_wr_addr;
    logic [7:0]    left_exp_wr_data;
    logic          left_exp_wr_en;

    logic [8:0]    right_exp_wr_addr;
    logic [7:0]    right_exp_wr_data;
    logic          right_exp_wr_en;

    // Result interface (FP16)
    logic [15:0] result_data;
    logic        result_valid;
    logic        result_full;
    logic        result_afull;

    // Debug interface
    logic [3:0]  ce_state;
    logic [15:0] result_count;

    // Test control
    integer test_num;
    logic test_passed;
    integer results_collected;

    // BRAM models (mantissa storage)
    logic [255:0] bram_left_mantissa [0:2047];
    logic [255:0] bram_right_mantissa [0:2047];

    // Exponent models (separate from mantissa)
    logic [7:0] bram_left_exponent [0:511];   // 512 exponents for 512 mantissa lines
    logic [7:0] bram_right_exponent [0:511];

    // Result collection (FP16 values)
    logic [15:0] results_fp16 [0:16383];  // Up to 128×128 results
    logic [15:0] golden_fp16 [0:16383];   // Golden reference

    // ===================================================================
    // DUT Instantiation (with integrated tile_bram)
    // ===================================================================
    compute_engine_modular dut (
        .i_clk                  (clk),
        .i_reset_n              (reset_n),

        // TILE command (spec-compliant per SINGLE_ROW_REFERENCE.md)
        .i_tile_en              (tile_en),
        .i_left_addr            (left_addr),       // 16 bits
        .i_right_addr           (right_addr),      // 16 bits
        .i_left_ugd_len         (left_ugd_len),    // 8 bits: dim_b (Batch)
        .i_right_ugd_len        (right_ugd_len),   // 8 bits: dim_c (Column)
        .i_vec_len              (vec_len),         // 8 bits: dim_v (Vector size)
        .i_left_man_4b          (left_man_4b),
        .i_right_man_4b         (right_man_4b),
        .i_main_loop_over_left  (main_loop_over_left),
        .o_tile_done            (tile_done),

        // Tile BRAM Write Interface (simulating DISPATCH operation)
        .i_man_left_wr_addr     (man_left_wr_addr),
        .i_man_left_wr_data     (man_left_wr_data),
        .i_man_left_wr_en       (man_left_wr_en),

        .i_man_right_wr_addr    (man_right_wr_addr),
        .i_man_right_wr_data    (man_right_wr_data),
        .i_man_right_wr_en      (man_right_wr_en),

        .i_left_exp_wr_addr     (left_exp_wr_addr),
        .i_left_exp_wr_data     (left_exp_wr_data),
        .i_left_exp_wr_en       (left_exp_wr_en),

        .i_right_exp_wr_addr    (right_exp_wr_addr),
        .i_right_exp_wr_data    (right_exp_wr_data),
        .i_right_exp_wr_en      (right_exp_wr_en),

        // Result interface (FP16)
        .o_result_data          (result_data),
        .o_result_valid         (result_valid),
        .i_result_full          (result_full),
        .i_result_afull         (result_afull),

        // Debug
        .o_ce_state             (ce_state),
        .o_result_count         (result_count)
    );

    // ===================================================================
    // Clock Generation
    // ===================================================================
    initial begin
        clk = 0;
        forever #5 clk = ~clk;  // 100MHz clock
    end

    // ===================================================================
    // Write Enable Initialization
    // ===================================================================
    initial begin
        man_left_wr_en = 1'b0;
        man_right_wr_en = 1'b0;
        left_exp_wr_en = 1'b0;
        right_exp_wr_en = 1'b0;
    end

    // ===================================================================
    // Result FIFO Backpressure Model (simple, no backpressure)
    // ===================================================================
    assign result_full = 1'b0;
    assign result_afull = 1'b0;

    // ===================================================================
    // Result Collection Monitor
    // ===================================================================
    always @(posedge clk) begin
        if (result_valid && !result_full) begin
            results_fp16[results_collected] = result_data;
            $display("  [%0t] Result %0d: FP16=0x%04x",
                     $time, results_collected, result_data);
            results_collected = results_collected + 1;
        end
    end

    // ===================================================================
    // Helper Task: Initialize BRAM with Simple Pattern
    // ===================================================================
    task init_bram_simple();
        $display("  Initializing BRAM with simple pattern (all 1s)...");

        // Exponents (all 15 = bias for GFP8)
        for (int i = 0; i < 512; i++) begin
            bram_left_exponent[i] = 8'd15;
            bram_right_exponent[i] = 8'd15;
        end

        // Mantissas (all 1s)
        for (int i = 0; i < 2048; i++) begin
            bram_left_mantissa[i] = {32{8'sd1}};
            bram_right_mantissa[i] = {32{8'sd1}};
        end
    endtask

    // ===================================================================
    // Helper Task: Simulate DISPATCH - Write Data to Tile BRAM
    // ===================================================================
    task dispatch_to_tile_bram(input integer num_lines);
        integer i;

        $display("  Dispatching %0d lines to tile_bram...", num_lines);

        // Write data in parallel (mantissa + exponent, left + right)
        // Four parallel writes per cycle, simulating DISPATCH operation
        for (i = 0; i < num_lines; i++) begin
            @(posedge clk);

            // Left mantissa write
            man_left_wr_addr <= i[8:0];
            man_left_wr_data <= bram_left_mantissa[i];
            man_left_wr_en <= 1'b1;

            // Right mantissa write
            man_right_wr_addr <= i[8:0];
            man_right_wr_data <= bram_right_mantissa[i];
            man_right_wr_en <= 1'b1;

            // Left exponent write
            left_exp_wr_addr <= i[8:0];
            left_exp_wr_data <= bram_left_exponent[i];
            left_exp_wr_en <= 1'b1;

            // Right exponent write
            right_exp_wr_addr <= i[8:0];
            right_exp_wr_data <= bram_right_exponent[i];
            right_exp_wr_en <= 1'b1;
        end

        // Disable all write enables
        @(posedge clk);
        man_left_wr_en <= 1'b0;
        man_right_wr_en <= 1'b0;
        left_exp_wr_en <= 1'b0;
        right_exp_wr_en <= 1'b0;

        $display("  DISPATCH complete: %0d lines written", num_lines);
    endtask

    // ===================================================================
    // Helper Task: Load BRAM from Hex Files (using proper file parsing)
    // ===================================================================
    task load_bram_from_hex();
        integer fd_left, fd_right;
        string line_str;
        integer line_idx, byte_idx, exp_idx;
        logic [7:0] hex_bytes[0:31];
        integer scan_result;

        $display("  Loading BRAM from hex files...");

        // Load left matrix
        fd_left = $fopen("../../../hex/left.hex", "r");
        if (fd_left == 0) begin
            $display("  ERROR: Cannot open ../../../hex/left.hex");
            return;
        end

        line_idx = 0;
        while (!$feof(fd_left) && line_idx < 528) begin
            if ($fgets(line_str, fd_left)) begin
                // Parse 32 space-separated hex bytes
                scan_result = $sscanf(line_str,
                    "%h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h",
                    hex_bytes[0], hex_bytes[1], hex_bytes[2], hex_bytes[3],
                    hex_bytes[4], hex_bytes[5], hex_bytes[6], hex_bytes[7],
                    hex_bytes[8], hex_bytes[9], hex_bytes[10], hex_bytes[11],
                    hex_bytes[12], hex_bytes[13], hex_bytes[14], hex_bytes[15],
                    hex_bytes[16], hex_bytes[17], hex_bytes[18], hex_bytes[19],
                    hex_bytes[20], hex_bytes[21], hex_bytes[22], hex_bytes[23],
                    hex_bytes[24], hex_bytes[25], hex_bytes[26], hex_bytes[27],
                    hex_bytes[28], hex_bytes[29], hex_bytes[30], hex_bytes[31]);

                if (scan_result == 32) begin
                    // Lines 0-15: Exponents
                    if (line_idx < 16) begin
                        for (byte_idx = 0; byte_idx < 32; byte_idx++) begin
                            exp_idx = line_idx * 32 + byte_idx;
                            bram_left_exponent[exp_idx] = hex_bytes[byte_idx];
                        end
                    end
                    // Lines 16-527: Mantissas (stored at BRAM addresses 0-511)
                    else begin
                        for (byte_idx = 0; byte_idx < 32; byte_idx++) begin
                            bram_left_mantissa[line_idx - 16][(byte_idx*8) +: 8] = hex_bytes[byte_idx];
                        end
                    end
                end
                line_idx++;
            end
        end
        $fclose(fd_left);
        $display("  Loaded %0d lines from left.hex", line_idx);

        // Load right matrix
        fd_right = $fopen("../../../hex/right.hex", "r");
        if (fd_right == 0) begin
            $display("  ERROR: Cannot open ../../../hex/right.hex");
            return;
        end

        line_idx = 0;
        while (!$feof(fd_right) && line_idx < 528) begin
            if ($fgets(line_str, fd_right)) begin
                scan_result = $sscanf(line_str,
                    "%h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h",
                    hex_bytes[0], hex_bytes[1], hex_bytes[2], hex_bytes[3],
                    hex_bytes[4], hex_bytes[5], hex_bytes[6], hex_bytes[7],
                    hex_bytes[8], hex_bytes[9], hex_bytes[10], hex_bytes[11],
                    hex_bytes[12], hex_bytes[13], hex_bytes[14], hex_bytes[15],
                    hex_bytes[16], hex_bytes[17], hex_bytes[18], hex_bytes[19],
                    hex_bytes[20], hex_bytes[21], hex_bytes[22], hex_bytes[23],
                    hex_bytes[24], hex_bytes[25], hex_bytes[26], hex_bytes[27],
                    hex_bytes[28], hex_bytes[29], hex_bytes[30], hex_bytes[31]);

                if (scan_result == 32) begin
                    if (line_idx < 16) begin
                        for (byte_idx = 0; byte_idx < 32; byte_idx++) begin
                            exp_idx = line_idx * 32 + byte_idx;
                            bram_right_exponent[exp_idx] = hex_bytes[byte_idx];
                        end
                    end
                    else begin
                        for (byte_idx = 0; byte_idx < 32; byte_idx++) begin
                            bram_right_mantissa[line_idx - 16][(byte_idx*8) +: 8] = hex_bytes[byte_idx];
                        end
                    end
                end
                line_idx++;
            end
        end
        $fclose(fd_right);
        $display("  Loaded %0d lines from right.hex", line_idx);
    endtask

    // ===================================================================
    // Helper Task: Load Golden Reference
    // ===================================================================
    task load_golden_reference(input string filename, input integer expected_count);
        integer file_handle;
        integer scan_result;
        integer idx;

        $display("  Loading golden reference: %s", filename);

        file_handle = $fopen(filename, "r");
        if (file_handle == 0) begin
            $display("  ERROR: Cannot open golden file: %s", filename);
            test_passed = 0;
            return;
        end

        idx = 0;
        while (!$feof(file_handle) && idx < expected_count) begin
            scan_result = $fscanf(file_handle, "%h\n", golden_fp16[idx]);
            if (scan_result == 1) idx++;
        end
        $fclose(file_handle);

        $display("  Loaded %0d golden FP16 values", idx);

        if (idx != expected_count) begin
            $display("  WARNING: Expected %0d values, got %0d", expected_count, idx);
        end
    endtask

    // ===================================================================
    // Helper Task: Send TILE Command
    // ===================================================================
    task send_tile_command(
        input logic [7:0] b,
        input logic [7:0] c,
        input logic [7:0] v
    );
        $display("  Sending TILE command: B=%0d, C=%0d, V=%0d", b, c, v);
        @(posedge clk);
        tile_en <= 1'b1;
        left_addr <= 16'd0;
        right_addr <= 16'd0;
        left_ugd_len <= b;     // dim_b (Batch dimension)
        right_ugd_len <= c;    // dim_c (Column dimension)
        vec_len <= v;          // dim_v (Vector size)
        left_man_4b <= 1'b0;
        right_man_4b <= 1'b0;
        main_loop_over_left <= 1'b0;
        @(posedge clk);
        tile_en <= 1'b0;
    endtask

    // ===================================================================
    // Helper Task: Wait for TILE Done
    // ===================================================================
    task wait_tile_done(input integer timeout_cycles);
        integer cycle_count;
        cycle_count = 0;

        $display("  Waiting for TILE completion...");
        while (!tile_done && cycle_count < timeout_cycles) begin
            @(posedge clk);
            cycle_count++;
        end

        if (tile_done) begin
            $display("  TILE completed in %0d cycles", cycle_count);
        end else begin
            $display("  ERROR: TILE timeout after %0d cycles", timeout_cycles);
            test_passed = 0;
        end

        // Wait additional cycles for final results
        repeat(10) @(posedge clk);
    endtask

    // ===================================================================
    // Helper Task: Validate FP16 Results
    // ===================================================================
    task validate_fp16_results(input integer expected_count);
        integer mismatches;
        integer diff;
        real rel_err;

        $display("  Validating %0d FP16 results...", expected_count);

        if (results_collected != expected_count) begin
            $display("  [FAIL] Expected %0d results, got %0d", expected_count, results_collected);
            test_passed = 0;
            return;
        end

        mismatches = 0;
        for (int i = 0; i < expected_count; i++) begin
            diff = (results_fp16[i] > golden_fp16[i]) ?
                   (results_fp16[i] - golden_fp16[i]) :
                   (golden_fp16[i] - results_fp16[i]);

            // FP16 tolerance: ±2 LSB (same as hardware test)
            if (diff > 2) begin
                $display("    MISMATCH[%0d]: hw=0x%04x golden=0x%04x diff=%0d",
                         i, results_fp16[i], golden_fp16[i], diff);
                mismatches++;
            end
        end

        $display("  Matches: %0d/%0d (%0d mismatches)",
                 expected_count - mismatches, expected_count, mismatches);

        if (mismatches == 0) begin
            $display("  [PASS] All results match!\n");
        end else begin
            $display("  [FAIL] %0d mismatches detected\n", mismatches);
            test_passed = 0;
        end
    endtask

    // ===================================================================
    // Test Stimulus
    // ===================================================================
    initial begin
        // Initialize
        reset_n = 0;
        tile_en = 0;
        left_addr = 16'd0;
        right_addr = 16'd0;
        left_ugd_len = 8'd0;
        right_ugd_len = 8'd0;
        vec_len = 8'd0;
        left_man_4b = 1'b0;
        right_man_4b = 1'b0;
        main_loop_over_left = 1'b0;
        test_num = 0;
        test_passed = 1;
        results_collected = 0;

        // Initialize BRAM
        for (int i = 0; i < 2048; i++) begin
            bram_left_mantissa[i] = 256'd0;
            bram_right_mantissa[i] = 256'd0;
        end
        for (int i = 0; i < 512; i++) begin
            bram_left_exponent[i] = 8'd0;
            bram_right_exponent[i] = 8'd0;
        end

        // Reset
        repeat(5) @(posedge clk);
        reset_n = 1;
        repeat(2) @(posedge clk);

        $display("\n========================================");
        $display("Compute Engine Modular Testbench");
        $display("Running 10 Test Configurations (matching test_gemm.cpp)");
        $display("========================================\n");

        // ===============================================================
        // Test 1/10: B1_C1_V1
        // ===============================================================
        test_num = 1;
        $display("[TEST %0d/10] B1_C1_V1", test_num);

        load_bram_from_hex();
        dispatch_to_tile_bram(512);
        load_golden_reference("../../../hex/golden_B1_C1_V1.hex", 1);
        results_collected = 0;

        send_tile_command(8'd1, 8'd1, 8'd1);
        wait_tile_done(10000);

        validate_fp16_results(1);

        // ===============================================================
        // Test 2/10: B2_C2_V2
        // ===============================================================
        test_num = 2;
        $display("[TEST %0d/10] B2_C2_V2", test_num);

        load_bram_from_hex();
        dispatch_to_tile_bram(512);
        load_golden_reference("../../../hex/golden_B2_C2_V2.hex", 4);
        results_collected = 0;

        send_tile_command(8'd2, 8'd2, 8'd2);
        wait_tile_done(30000);

        validate_fp16_results(4);

        // ===============================================================
        // Test 3/10: B4_C4_V4
        // ===============================================================
        test_num = 3;
        $display("[TEST %0d/10] B4_C4_V4", test_num);

        load_bram_from_hex();
        dispatch_to_tile_bram(512);
        load_golden_reference("../../../hex/golden_B4_C4_V4.hex", 16);
        results_collected = 0;

        send_tile_command(8'd4, 8'd4, 8'd4);
        wait_tile_done(50000);

        validate_fp16_results(16);

        // ===============================================================
        // Test 4/10: B2_C2_V64
        // ===============================================================
        test_num = 4;
        $display("[TEST %0d/10] B2_C2_V64", test_num);

        load_bram_from_hex();
        dispatch_to_tile_bram(512);
        load_golden_reference("../../../hex/golden_B2_C2_V64.hex", 4);
        results_collected = 0;

        send_tile_command(8'd2, 8'd2, 8'd64);
        wait_tile_done(150000);

        validate_fp16_results(4);

        // ===============================================================
        // Test 5/10: B4_C4_V32
        // ===============================================================
        test_num = 5;
        $display("[TEST %0d/10] B4_C4_V32", test_num);

        load_bram_from_hex();
        dispatch_to_tile_bram(512);
        load_golden_reference("../../../hex/golden_B4_C4_V32.hex", 16);
        results_collected = 0;

        send_tile_command(8'd4, 8'd4, 8'd32);
        wait_tile_done(200000);

        validate_fp16_results(16);

        // ===============================================================
        // Test 6/10: B8_C8_V16
        // ===============================================================
        test_num = 6;
        $display("[TEST %0d/10] B8_C8_V16", test_num);

        load_bram_from_hex();
        dispatch_to_tile_bram(512);
        load_golden_reference("../../../hex/golden_B8_C8_V16.hex", 64);
        results_collected = 0;

        send_tile_command(8'd8, 8'd8, 8'd16);
        wait_tile_done(300000);

        validate_fp16_results(64);

        // ===============================================================
        // Test 7/10: B16_C16_V8
        // ===============================================================
        test_num = 7;
        $display("[TEST %0d/10] B16_C16_V8", test_num);

        load_bram_from_hex();
        dispatch_to_tile_bram(512);
        load_golden_reference("../../../hex/golden_B16_C16_V8.hex", 256);
        results_collected = 0;

        send_tile_command(8'd16, 8'd16, 8'd8);
        wait_tile_done(500000);

        validate_fp16_results(256);

        // ===============================================================
        // Test 8/10: B1_C128_V1
        // ===============================================================
        test_num = 8;
        $display("[TEST %0d/10] B1_C128_V1", test_num);

        load_bram_from_hex();
        dispatch_to_tile_bram(512);
        load_golden_reference("../../../hex/golden_B1_C128_V1.hex", 128);
        results_collected = 0;

        send_tile_command(8'd1, 8'd128, 8'd1);
        wait_tile_done(200000);

        validate_fp16_results(128);

        // ===============================================================
        // Test 9/10: B128_C1_V1
        // ===============================================================
        test_num = 9;
        $display("[TEST %0d/10] B128_C1_V1", test_num);

        load_bram_from_hex();
        dispatch_to_tile_bram(512);
        load_golden_reference("../../../hex/golden_B128_C1_V1.hex", 128);
        results_collected = 0;

        send_tile_command(8'd128, 8'd1, 8'd1);
        wait_tile_done(200000);

        validate_fp16_results(128);

        // ===============================================================
        // Test 10/10: B1_C1_V128
        // ===============================================================
        test_num = 10;
        $display("[TEST %0d/10] B1_C1_V128", test_num);

        load_bram_from_hex();
        dispatch_to_tile_bram(512);
        load_golden_reference("../../../hex/golden_B1_C1_V128.hex", 1);
        results_collected = 0;

        send_tile_command(8'd1, 8'd1, 8'd128);
        wait_tile_done(100000);

        validate_fp16_results(1);

        // ===============================================================
        // Test Summary
        // ===============================================================
        $display("========================================");
        $display("TEST SUMMARY");
        $display("========================================");
        $display("Total tests: 10/10 (matching test_gemm.cpp)");
        if (test_passed) begin
            $display("STATUS: ALL TESTS PASSED");
        end else begin
            $display("STATUS: SOME TESTS FAILED");
        end
        $display("========================================\n");

        $finish;
    end

    // ===================================================================
    // Timeout
    // ===================================================================
    initial begin
        #10000000;  // 10ms timeout
        $display("ERROR: Testbench timeout!");
        $finish;
    end

endmodule
