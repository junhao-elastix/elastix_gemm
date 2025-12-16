// ------------------------------------------------------------------
// Testbench for compute_engine_mlp.sv
//
// Purpose: Verify MLP compute engine with direct path architecture
// Tests:
//  - Various B/C/V configurations where C is divisible by 16
//  - Golden reference validation against hex files
//
// Key Features:
//  - Simulates DISPATCH operation (writes data to row_bram write ports)
//  - Four parallel write paths (mantissa + exponent, left + right)
//  - FP16 result validation against golden references
//  - Golden reference loading from hex files
//
// MLP Compute Engine:
//  - Fixed 16 columns per compute cycle
//  - Supports C = 16, 32, 64, 128 via column group iteration
//  - 256-bit result output (16 × FP16 per batch)
//  - Internal exponent conversion: GFP8E5 (bias=15) → GFP8E8 (bias=133)
//
// Architecture:
//  testbench BRAM models → [DISPATCH] → DUT row_bram → [TILE] → results
//
// Author: Compute Engine Testing
// Date: Dec 2025
// ------------------------------------------------------------------

`timescale 1ns/1ps

module tb_compute_engine_mlp;

    // Clock and reset
    logic clk;
    logic reset_n;

    // TILE command interface (per SINGLE_ROW_REFERENCE.md)
    logic        tile_en;           // Static enable (configuration)
    logic        tile_start;        // Dynamic pulse (start computing!)
    logic [15:0] left_addr;         // 16 bits: Left matrix start address
    logic [15:0] right_addr;        // 16 bits: Right matrix start address
    logic [7:0]  left_ugd_len;      // 8 bits: Left UGD vectors (Batch dimension)
    logic [7:0]  right_ugd_len;     // 8 bits: Right UGD vectors (Column dimension)
    logic [7:0]  vec_len;           // 8 bits: UGD vector size (Vector count)
    logic        left_man_4b;       // 1 bit: Left mantissa width (0=8b, 1=4b)
    logic        right_man_4b;      // 1 bit: Right mantissa width (0=8b, 1=4b)
    logic        main_loop_over_left; // 1 bit: Main loop dimension selector
    logic [23:0] mc_tile_en;        // Per-tile enable mask
    logic        tile_done;

    // row_bram Write Interface (simulating DISPATCH operation)
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

    // Result interface (256-bit = 16 × FP16)
    logic [255:0] result_data_wide;  // MLP outputs 16 × FP16
    logic [15:0]  result_data;       // First FP16 for quick checking
    logic         result_valid_wide; // MLP result valid
    logic         result_valid;      // Alias for result_valid_wide
    logic        result_full;
    logic        result_afull;

    // Debug interface
    logic [3:0]  ce_state;
    logic [15:0] result_count;

    // Test control
    integer test_num;
    logic test_passed;
    integer results_collected;
    integer tests_run;
    integer tests_skipped;

    // BRAM models (mantissa storage)
    logic [255:0] bram_left_mantissa [0:2047];
    logic [255:0] bram_right_mantissa [0:2047];

    // Exponent models (separate from mantissa)
    // NOTE: Exponents stored in GFP8E5 format (bias=15)
    // RTL compute_engine_mlp.sv converts to GFP8E8 (bias=133) internally
    logic [7:0] bram_left_exponent [0:511];
    logic [7:0] bram_right_exponent [0:511];

    // Result collection (FP16 values)
    logic [15:0] results_fp16 [0:16383];  // Up to 128×128 results
    logic [15:0] golden_fp16 [0:16383];   // Golden reference

    // ===================================================================
    // DUT Instantiation - MLP Compute Engine
    // ===================================================================
    compute_engine_mlp #(
        .TILE_ID(0),
        .MAN_WIDTH(256),
        .EXP_WIDTH(8),
        .BRAM_DEPTH(512),
        .NUM_COLUMNS(16),
        .NUM_MLPS(8)
    ) dut (
        .i_clk                  (clk),
        .i_reset_n              (reset_n),

        // TILE command
        .i_tile_en              (tile_en),
        .i_tile_start           (tile_start),
        .i_tile_left_addr       (left_addr),
        .i_tile_right_addr      (right_addr),
        .i_tile_left_ugd_len    (left_ugd_len),
        .i_tile_right_ugd_len   (right_ugd_len),
        .i_tile_vec_len         (vec_len),
        .i_tile_left_man_4b     (left_man_4b),
        .i_tile_right_man_4b    (right_man_4b),
        .i_tile_main_loop_over_left (main_loop_over_left),
        .i_mc_tile_en           (mc_tile_en),
        .o_tile_done            (tile_done),

        // Write Interface
        .i_man_left_wr_addr     (man_left_wr_addr),
        .i_man_left_wr_data     (man_left_wr_data),
        .i_man_left_wr_en       (man_left_wr_en),

        .i_man_right_wr_addr    (man_right_wr_addr),
        .i_man_right_wr_data    (man_right_wr_data),
        .i_man_right_wr_en      (man_right_wr_en),

        .i_exp_left_wr_addr     (left_exp_wr_addr),
        .i_exp_left_wr_data     (left_exp_wr_data),
        .i_exp_left_wr_en       (left_exp_wr_en),

        .i_exp_right_wr_addr    (right_exp_wr_addr),
        .i_exp_right_wr_data    (right_exp_wr_data),
        .i_exp_right_wr_en      (right_exp_wr_en),

        // Result interface (256-bit = 16 × FP16)
        .o_result_data          (result_data_wide),
        .o_result_valid         (result_valid_wide),
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
    // Result Collection (256-bit → 16 × 16-bit)
    // When result_valid_wide pulses, extract all 16 FP16 values
    // ===================================================================
    always @(posedge clk) begin
        if (result_valid_wide && !result_full) begin
            // Extract all 16 FP16 values from the 256-bit result
            for (int i = 0; i < 16; i++) begin
                results_fp16[results_collected + i] = result_data_wide[i*16 +: 16];
            end
            $display("  [%0t] Result pulse: 16 FP16 values starting at index %0d, first=0x%04x",
                     $time, results_collected, result_data_wide[15:0]);
            results_collected = results_collected + 16;
        end
    end

    // For compatibility, derive single-value signals
    assign result_data = result_data_wide[15:0];
    assign result_valid = result_valid_wide;

    // ===================================================================
    // Helper Task: Initialize BRAM with Simple Pattern
    // ===================================================================
    task init_bram_simple();
        $display("  Initializing BRAM with simple pattern (all 1s)...");

        // Exponents (all 15 = bias for GFP8E5)
        // Note: RTL converts to E8 format internally
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
    // Helper Task: Simulate DISPATCH - Write Data to row_bram
    // ===================================================================
    task dispatch_to_tile_bram(input integer num_lines);
        integer i;

        $display("  Dispatching %0d lines to row_bram...", num_lines);

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

            // Left exponent write (raw GFP8E5 - RTL converts internally)
            left_exp_wr_addr <= i[8:0];
            left_exp_wr_data <= bram_left_exponent[i];
            left_exp_wr_en <= 1'b1;

            // Right exponent write (raw GFP8E5 - RTL converts internally)
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
    // Helper Task: Load BRAM from Hex Files
    // Exponents are stored in GFP8E5 format - RTL converts to E8 internally
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
                    // Lines 0-15: Exponents (store raw GFP8E5)
                    if (line_idx < 16) begin
                        for (byte_idx = 0; byte_idx < 32; byte_idx++) begin
                            exp_idx = line_idx * 32 + byte_idx;
                            // Store raw E5 format - RTL converts to E8 internally
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
                            // Store raw E5 format - RTL converts to E8 internally
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
        // Setup command parameters (tile_en stays HIGH as static enable)
        tile_en <= 1'b1;          // Static enable - keep HIGH
        left_addr <= 16'd0;
        right_addr <= 16'd0;
        left_ugd_len <= b;        // dim_b (Batch dimension)
        right_ugd_len <= c;       // dim_c (Column dimension)
        vec_len <= v;             // dim_v (Vector size)
        left_man_4b <= 1'b0;
        right_man_4b <= 1'b0;
        main_loop_over_left <= 1'b0;
        mc_tile_en <= 24'h000001; // Single tile enabled (tile 0)
        @(posedge clk);
        // Pulse tile_start to trigger computation
        tile_start <= 1'b1;
        @(posedge clk);
        tile_start <= 1'b0;
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
    // Helper Task: Validate FP16 Results with Reordering for C>16
    // Hardware outputs: Group-major (all batches for group 0, then group 1, ...)
    // Golden expects: Batch-major (batch 0 all cols, batch 1 all cols, ...)
    // ===================================================================
    task validate_fp16_results_bcv(input integer B, input integer C, input integer V);
        integer expected_count;
        integer num_col_groups;
        integer mismatches;
        integer exact_matches;
        integer close_matches;
        integer diff;
        integer golden_idx, batch_idx, col_idx, group_idx, col_within_group, pulse_idx, hw_idx;
        logic [15:0] hw_val, golden_val;
        // Match software test tolerance (4 LSB)
        localparam int ABS_TOL = 4;    // 4 LSB tolerance (matches test_gemm.cpp)

        expected_count = B * C;
        num_col_groups = (C + 15) / 16;  // Ceiling division

        $display("  Validating %0d FP16 results (B=%0d, C=%0d, groups=%0d, tolerance=%0d LSB)...",
                 expected_count, B, C, num_col_groups, ABS_TOL);

        if (results_collected != expected_count) begin
            $display("  [FAIL] Expected %0d results, got %0d", expected_count, results_collected);
            test_passed = 0;
            return;
        end

        mismatches = 0;
        exact_matches = 0;
        close_matches = 0;

        // Compare with reordering for C>16 (matches test_gemm.cpp logic)
        for (golden_idx = 0; golden_idx < expected_count; golden_idx++) begin
            golden_val = golden_fp16[golden_idx];

            if (num_col_groups > 1) begin
                // Multi-group: apply reordering to find hw_idx
                batch_idx = golden_idx / C;
                col_idx = golden_idx % C;
                group_idx = col_idx / 16;
                col_within_group = col_idx % 16;
                pulse_idx = group_idx * B + batch_idx;
                hw_idx = pulse_idx * 16 + col_within_group;
            end else begin
                // Single group: no reordering
                hw_idx = golden_idx;
            end

            hw_val = results_fp16[hw_idx];
            diff = (hw_val > golden_val) ? (hw_val - golden_val) : (golden_val - hw_val);

            if (diff == 0) begin
                exact_matches++;
            end else if (diff <= ABS_TOL) begin
                close_matches++;
            end else begin
                // Mismatch - show first 10
                if (mismatches < 10) begin
                    $display("    MISMATCH[%0d→hw%0d]: hw=0x%04x golden=0x%04x diff=%0d LSB",
                             golden_idx, hw_idx, hw_val, golden_val, diff);
                end
                mismatches++;
            end
        end

        $display("  Validation: %0d/%0d within tolerance (%0d exact, %0d within %0d LSB)",
                 exact_matches + close_matches, expected_count, exact_matches, close_matches, ABS_TOL);

        if (mismatches == 0) begin
            $display("  [PASS] All results within tolerance!\n");
        end else begin
            $display("  [FAIL] %0d mismatches (diff > %0d LSB)\n", mismatches, ABS_TOL);
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
        tile_start = 0;
        left_addr = 16'd0;
        right_addr = 16'd0;
        left_ugd_len = 8'd0;
        right_ugd_len = 8'd0;
        vec_len = 8'd0;
        left_man_4b = 1'b0;
        right_man_4b = 1'b0;
        main_loop_over_left = 1'b0;
        mc_tile_en = 24'h000001;  // Single tile enabled
        test_num = 0;
        test_passed = 1;
        results_collected = 0;
        tests_run = 0;
        tests_skipped = 0;

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
        $display("Compute Engine MLP Testbench");
        $display("Tests: C must be divisible by 16");
        $display("========================================\n");

        // Load BRAM once (same data for all tests)
        load_bram_from_hex();
        dispatch_to_tile_bram(512);

        // ===============================================================
        // Test 1: B16_C16_V8 (baseline test)
        // ===============================================================
        test_num = 1;
        $display("[TEST %0d] B16_C16_V8 (B×C = 16×16 = 256 results)", test_num);

        load_golden_reference("../../../hex/golden_B16_C16_V8.hex", 256);
        results_collected = 0;

        send_tile_command(8'd16, 8'd16, 8'd8);
        wait_tile_done(500000);

        validate_fp16_results_bcv(16, 16, 8);
        tests_run++;

        // ===============================================================
        // Test 2: B1_C128_V1 (8 column groups)
        // ===============================================================
        test_num = 2;
        $display("[TEST %0d] B1_C128_V1 (8 column groups, B×C = 1×128 = 128 results)", test_num);

        load_golden_reference("../../../hex/golden_B1_C128_V1.hex", 128);
        results_collected = 0;

        send_tile_command(8'd1, 8'd128, 8'd1);
        wait_tile_done(500000);

        validate_fp16_results_bcv(1, 128, 1);
        tests_run++;

        // ===============================================================
        // Test 3: B4_C16_V8
        // ===============================================================
        test_num = 3;
        $display("[TEST %0d] B4_C16_V8 (B×C = 4×16 = 64 results)", test_num);

        load_golden_reference("../../../hex/golden_B4_C16_V8.hex", 64);
        results_collected = 0;

        send_tile_command(8'd4, 8'd16, 8'd8);
        wait_tile_done(500000);

        validate_fp16_results_bcv(4, 16, 8);
        tests_run++;

        // ===============================================================
        // Test 4: B8_C16_V4
        // ===============================================================
        test_num = 4;
        $display("[TEST %0d] B8_C16_V4 (B×C = 8×16 = 128 results)", test_num);

        load_golden_reference("../../../hex/golden_B8_C16_V4.hex", 128);
        results_collected = 0;

        send_tile_command(8'd8, 8'd16, 8'd4);
        wait_tile_done(500000);

        validate_fp16_results_bcv(8, 16, 4);
        tests_run++;

        // ===============================================================
        // Test 5: B4_C32_V4 (2 column groups)
        // ===============================================================
        test_num = 5;
        $display("[TEST %0d] B4_C32_V4 (2 column groups, B×C = 4×32 = 128 results)", test_num);

        load_golden_reference("../../../hex/golden_B4_C32_V4.hex", 128);
        results_collected = 0;

        send_tile_command(8'd4, 8'd32, 8'd4);
        wait_tile_done(500000);

        validate_fp16_results_bcv(4, 32, 4);
        tests_run++;

        // ===============================================================
        // Test 6: B8_C32_V2 (2 column groups)
        // ===============================================================
        test_num = 6;
        $display("[TEST %0d] B8_C32_V2 (2 column groups, B×C = 8×32 = 256 results)", test_num);

        load_golden_reference("../../../hex/golden_B8_C32_V2.hex", 256);
        results_collected = 0;

        send_tile_command(8'd8, 8'd32, 8'd2);
        wait_tile_done(500000);

        validate_fp16_results_bcv(8, 32, 2);
        tests_run++;

        // ===============================================================
        // Test 7: B8_C64_V2 (4 column groups)
        // ===============================================================
        test_num = 7;
        $display("[TEST %0d] B8_C64_V2 (4 column groups, B×C = 8×64 = 512 results)", test_num);

        load_golden_reference("../../../hex/golden_B8_C64_V2.hex", 512);
        results_collected = 0;

        send_tile_command(8'd8, 8'd64, 8'd2);
        wait_tile_done(500000);

        validate_fp16_results_bcv(8, 64, 2);
        tests_run++;

        // ===============================================================
        // Test 8: B2_C128_V1 (8 column groups)
        // ===============================================================
        test_num = 8;
        $display("[TEST %0d] B2_C128_V1 (8 column groups, B×C = 2×128 = 256 results)", test_num);

        load_golden_reference("../../../hex/golden_B2_C128_V1.hex", 256);
        results_collected = 0;

        send_tile_command(8'd2, 8'd128, 8'd1);
        wait_tile_done(500000);

        validate_fp16_results_bcv(2, 128, 1);
        tests_run++;

        // ===============================================================
        // Test Summary
        // ===============================================================
        $display("========================================");
        $display("TEST SUMMARY");
        $display("========================================");
        $display("Tests run: %0d", tests_run);
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
        #100000000;  // 100ms timeout (8 tests)
        $display("ERROR: Testbench timeout!");
        $finish;
    end

endmodule
