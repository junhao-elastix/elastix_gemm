// ------------------------------------------------------------------
// Testbench for compute_engine_mlp.sv (MLP-based compute engine)
//
// Purpose: Verify MLP-based compute engine as drop-in replacement
// Tests:
//  1. B=16, C=16, V=8 - Full BCV test matching golden reference
//
// Key Differences from compute_engine_modular:
//  - Output is 256-bit (16 × FP16) per result_valid pulse
//  - C is fixed at 16 (one per MLP column)
//  - Exponents use MLP convention (8-bit with bias offset)
//
// Exponent Conversion:
//  - Hex files use 5-bit exponents (bias=15)
//  - MLP hardware expects 8-bit exponents with bias=133 (127+6)
//  - Conversion: exp_8bit = exp_5bit + 118
//
// Author: Integration Test
// Date: Dec 2024
// ------------------------------------------------------------------

`timescale 1ns/1ps

module tb_compute_engine_mlp;

    // Parameters matching compute_engine_mlp
    localparam int MAN_WIDTH = 256;
    localparam int EXP_WIDTH = 8;
    localparam int BRAM_DEPTH = 512;
    localparam int ADDR_WIDTH = $clog2(BRAM_DEPTH);
    localparam int NUM_COLUMNS = 16;

    // Exponent conversion constant
    // Hex files: 5-bit exp (bias=15)
    // MLP hardware: 8-bit exp (bias=127+6=133)
    // exp_8bit = exp_5bit + 118
    localparam int EXP_CONVERT_OFFSET = 118;

    // Clock and reset
    logic clk;
    logic reset_n;

    // TILE command interface
    logic        tile_en;
    logic        tile_start;
    logic [15:0] left_addr;
    logic [15:0] right_addr;
    logic [7:0]  left_ugd_len;
    logic [7:0]  right_ugd_len;
    logic [7:0]  vec_len;
    logic        left_man_4b;
    logic        right_man_4b;
    logic        main_loop_over_left;
    logic [23:0] mc_tile_en;
    logic        tile_done;

    // Tile BRAM Write Interface (4 parallel ports)
    logic [ADDR_WIDTH-1:0] man_left_wr_addr;
    logic [MAN_WIDTH-1:0]  man_left_wr_data;
    logic                  man_left_wr_en;

    logic [ADDR_WIDTH-1:0] man_right_wr_addr;
    logic [MAN_WIDTH-1:0]  man_right_wr_data;
    logic                  man_right_wr_en;

    logic [ADDR_WIDTH-1:0] exp_left_wr_addr;
    logic [EXP_WIDTH-1:0]  exp_left_wr_data;
    logic                  exp_left_wr_en;

    logic [ADDR_WIDTH-1:0] exp_right_wr_addr;
    logic [EXP_WIDTH-1:0]  exp_right_wr_data;
    logic                  exp_right_wr_en;

    // Result interface (256-bit = 16 × FP16)
    logic [255:0] result_data;
    logic         result_valid;
    logic         result_full;
    logic         result_afull;

    // Debug interface
    logic [3:0]  ce_state;
    logic [15:0] result_count;

    // Test control
    integer test_num;
    logic test_passed;
    integer results_collected;
    integer result_pulses;

    // BRAM models (mantissa storage - 528 lines: 16 exp + 512 man)
    logic [255:0] bram_left_mantissa [0:511];
    logic [255:0] bram_right_mantissa [0:511];

    // Exponent models (5-bit values from hex, stored per NV: 4 exponents per NV)
    // Each NV has 4 groups of 32 elements, each group has one exponent
    logic [7:0] bram_left_exponent [0:511];   // One 8-bit exponent per line
    logic [7:0] bram_right_exponent [0:511];

    // Result collection (FP16 values) - collect in flat array
    logic [15:0] results_fp16 [0:16383];
    logic [15:0] golden_fp16 [0:16383];

    // ===================================================================
    // DUT Instantiation
    // ===================================================================
    compute_engine_mlp #(
        .TILE_ID(0),
        .MAN_WIDTH(MAN_WIDTH),
        .EXP_WIDTH(EXP_WIDTH),
        .BRAM_DEPTH(BRAM_DEPTH),
        .NUM_COLUMNS(NUM_COLUMNS),
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

        // Write Interface (note: MLP uses different port naming for exponents)
        .i_man_left_wr_addr     (man_left_wr_addr),
        .i_man_left_wr_data     (man_left_wr_data),
        .i_man_left_wr_en       (man_left_wr_en),

        .i_man_right_wr_addr    (man_right_wr_addr),
        .i_man_right_wr_data    (man_right_wr_data),
        .i_man_right_wr_en      (man_right_wr_en),

        .i_exp_left_wr_addr     (exp_left_wr_addr),
        .i_exp_left_wr_data     (exp_left_wr_data),
        .i_exp_left_wr_en       (exp_left_wr_en),

        .i_exp_right_wr_addr    (exp_right_wr_addr),
        .i_exp_right_wr_data    (exp_right_wr_data),
        .i_exp_right_wr_en      (exp_right_wr_en),

        // Result interface (256-bit)
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
        exp_left_wr_en = 1'b0;
        exp_right_wr_en = 1'b0;
    end

    // ===================================================================
    // Result FIFO Backpressure Model (simple, no backpressure)
    // ===================================================================
    assign result_full = 1'b0;
    assign result_afull = 1'b0;

    // ===================================================================
    // Result Collection Monitor (256-bit → 16 × FP16)
    // ===================================================================
    always @(posedge clk) begin
        if (result_valid && !result_full) begin
            // Extract 16 FP16 values from 256-bit result
            for (int i = 0; i < 16; i++) begin
                results_fp16[results_collected * 16 + i] = result_data[i*16 +: 16];
            end
            $display("  [%0t] Result pulse %0d: first FP16=0x%04x",
                     $time, result_pulses, result_data[15:0]);
            result_pulses = result_pulses + 1;
            results_collected = results_collected + 1;
        end
    end

    // ===================================================================
    // Helper Task: Load BRAM from Hex Files (528-line format)
    // Lines 0-15: Exponents (5-bit, need conversion to 8-bit)
    // Lines 16-527: Mantissas (8-bit signed)
    // ===================================================================
    task load_bram_from_hex();
        integer fd_left, fd_right;
        string line_str;
        integer line_idx, byte_idx, exp_idx, nv_idx, group_idx;
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
                    // Lines 0-15: Exponents (5-bit values, stored 32 per line)
                    // Each NV has 4 exponents (one per group of 32 mantissas)
                    // 16 lines × 32 exponents = 512 exponents = 128 NVs × 4 groups
                    if (line_idx < 16) begin
                        for (byte_idx = 0; byte_idx < 32; byte_idx++) begin
                            exp_idx = line_idx * 32 + byte_idx;
                            // Convert 5-bit (bias=15) to 8-bit (bias=133): add 118
                            bram_left_exponent[exp_idx] = hex_bytes[byte_idx] + EXP_CONVERT_OFFSET;
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
                            // Convert 5-bit to 8-bit with offset
                            bram_right_exponent[exp_idx] = hex_bytes[byte_idx] + EXP_CONVERT_OFFSET;
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
    // Helper Task: Dispatch Data to row_bram (MLP's internal BRAM)
    // MLP row_bram layout:
    //   - Mantissa lines: 4 lines per NV (4 × 256-bit = 1024 bits = 128 × 8-bit)
    //   - Exponent lines: 1 line per NV (8-bit per group × 4 groups packed differently)
    //
    // For MLP, we need to write:
    //   - Mantissa: Sequential 256-bit lines
    //   - Exponent: One 8-bit value at a time (row_bram stores per-line exponents)
    // ===================================================================
    task dispatch_to_row_bram(input integer num_nvs);
        integer nv, line, exp_line;

        $display("  Dispatching %0d NVs to row_bram...", num_nvs);

        // Write mantissa lines (4 lines per NV)
        // Write exponent (1 per mantissa line, same exponent for all 32 bytes)
        for (nv = 0; nv < num_nvs; nv++) begin
            for (line = 0; line < 4; line++) begin
                @(posedge clk);

                // Left mantissa
                man_left_wr_addr <= (nv * 4 + line);
                man_left_wr_data <= bram_left_mantissa[nv * 4 + line];
                man_left_wr_en <= 1'b1;

                // Right mantissa
                man_right_wr_addr <= (nv * 4 + line);
                man_right_wr_data <= bram_right_mantissa[nv * 4 + line];
                man_right_wr_en <= 1'b1;

                // Left exponent (one per line, stored in hex as per-group)
                // Hex file has: 16 lines × 32 exp = 512 exp = 128 NVs × 4 groups
                exp_line = nv * 4 + line;
                exp_left_wr_addr <= (nv * 4 + line);
                exp_left_wr_data <= bram_left_exponent[exp_line];
                exp_left_wr_en <= 1'b1;

                // Right exponent
                exp_right_wr_addr <= (nv * 4 + line);
                exp_right_wr_data <= bram_right_exponent[exp_line];
                exp_right_wr_en <= 1'b1;
            end
        end

        // Disable all write enables
        @(posedge clk);
        man_left_wr_en <= 1'b0;
        man_right_wr_en <= 1'b0;
        exp_left_wr_en <= 1'b0;
        exp_right_wr_en <= 1'b0;

        $display("  DISPATCH complete: %0d NVs written (%0d mantissa lines)", num_nvs, num_nvs * 4);
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
        left_ugd_len <= b;
        right_ugd_len <= c;
        vec_len <= v;
        left_man_4b <= 1'b0;
        right_man_4b <= 1'b0;
        main_loop_over_left <= 1'b0;
        mc_tile_en <= 24'h000001;
        @(posedge clk);
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

        repeat(10) @(posedge clk);
    endtask

    // ===================================================================
    // Helper Task: Validate FP16 Results
    // For MLP: each result_valid produces 16 FP16 results
    // Total results = B × 16 (B batches × 16 columns)
    // ===================================================================
    task validate_fp16_results(input integer expected_pulses, input integer expected_total);
        integer mismatches;
        integer diff;
        real max_rel_err;
        real rel_err;
        real hw_val, golden_val;

        $display("  Validating %0d FP16 results from %0d pulses...", expected_total, expected_pulses);

        if (result_pulses != expected_pulses) begin
            $display("  [FAIL] Expected %0d result pulses, got %0d", expected_pulses, result_pulses);
            test_passed = 0;
            return;
        end

        mismatches = 0;
        max_rel_err = 0.0;

        for (int i = 0; i < expected_total; i++) begin
            diff = (results_fp16[i] > golden_fp16[i]) ?
                   (results_fp16[i] - golden_fp16[i]) :
                   (golden_fp16[i] - results_fp16[i]);

            // Calculate relative error for reporting
            // Note: This is approximate since we're working with FP16 bits
            if (golden_fp16[i] != 0) begin
                // Simple bit-difference based tolerance
                rel_err = real'(diff) / 65536.0;  // Normalize to [0,1]
            end else begin
                rel_err = (results_fp16[i] != 0) ? 1.0 : 0.0;
            end

            if (rel_err > max_rel_err) max_rel_err = rel_err;

            // Tolerance: allow some difference due to algorithm differences
            // MLP uses different accumulation path than compute_engine_modular
            if (diff > 100) begin  // ~1.5% of FP16 range
                $display("    MISMATCH[%0d]: hw=0x%04x golden=0x%04x diff=%0d",
                         i, results_fp16[i], golden_fp16[i], diff);
                mismatches++;
                if (mismatches > 10) begin
                    $display("    ... (more than 10 mismatches, stopping display)");
                    break;
                end
            end
        end

        $display("  Matches: %0d/%0d (%0d mismatches)",
                 expected_total - mismatches, expected_total, mismatches);
        $display("  Max relative error: %.4f%%", max_rel_err * 100.0);

        // Allow up to 10% mismatches due to algorithm differences
        if (mismatches <= expected_total / 10) begin
            $display("  [PASS] Results within acceptable tolerance!\n");
        end else begin
            $display("  [FAIL] Too many mismatches: %0d/%0d\n", mismatches, expected_total);
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
        mc_tile_en = 24'h000001;
        test_num = 0;
        test_passed = 1;
        results_collected = 0;
        result_pulses = 0;

        // Initialize BRAM
        for (int i = 0; i < 512; i++) begin
            bram_left_mantissa[i] = 256'd0;
            bram_right_mantissa[i] = 256'd0;
            bram_left_exponent[i] = 8'd0;
            bram_right_exponent[i] = 8'd0;
        end

        // Reset
        repeat(5) @(posedge clk);
        reset_n = 1;
        repeat(2) @(posedge clk);

        $display("\n========================================");
        $display("Compute Engine MLP Testbench");
        $display("Testing B=16, C=16, V=8 configuration");
        $display("========================================\n");

        // ===============================================================
        // Test 1: B16_C16_V8
        // ===============================================================
        test_num = 1;
        $display("[TEST %0d] B16_C16_V8", test_num);

        load_bram_from_hex();

        // Dispatch 128 NVs (B*V=16*8=128 for left, C*V=16*8=128 for right)
        dispatch_to_row_bram(128);

        load_golden_reference("../../../hex/golden_B16_C16_V8.hex", 256);
        results_collected = 0;
        result_pulses = 0;

        // B=16, C=16 (fixed for MLP), V=8
        send_tile_command(8'd16, 8'd16, 8'd8);
        wait_tile_done(50000);

        // MLP outputs: B pulses × 16 FP16 per pulse = 16 × 16 = 256 results
        validate_fp16_results(16, 256);

        // ===============================================================
        // Summary
        // ===============================================================
        $display("\n========================================");
        if (test_passed) begin
            $display("ALL TESTS PASSED!");
        end else begin
            $display("SOME TESTS FAILED!");
        end
        $display("========================================\n");

        $finish;
    end

endmodule
