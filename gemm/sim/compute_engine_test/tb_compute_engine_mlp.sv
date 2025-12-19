// ------------------------------------------------------------------
// Testbench for compute_engine_mlp.sv
//
// Purpose: Verify MLP compute engine with golden reference validation
//
// Test Coverage:
//   - Single-dispatch tests (C <= 16, single column group)
//   - Multi-dispatch stress tests (C > 16, multiple column groups)
//
// Architecture:
//   hex files → TB BRAM models → [write_row_bram] → DUT row_bram
//   → [cmd_dispatch_right] → MLP BRAM → [cmd_tile] → FP16 results
//
// Author: Compute Engine Testing
// Date: Dec 2025
// ------------------------------------------------------------------

`timescale 1ns/1ps

module tb_compute_engine_mlp;

    // =========================================================================
    // Parameters
    // =========================================================================
    localparam int CLK_PERIOD_NS    = 10;       // 100MHz clock
    localparam int TIMEOUT_NS       = 2000000000; // 2s timeout
    localparam int ABS_TOLERANCE    = 32;       // FP16 LSB tolerance
    localparam int NUM_COLUMNS      = 16;       // Hardware columns per group
    localparam string HEX_PATH      = "../../../hex/";

    // =========================================================================
    // Test Configuration
    // =========================================================================
    typedef enum {
        TEST_SINGLE_DISPATCH,   // Standard: one FETCH+DISPATCH, one TILE
        TEST_MULTI_DISPATCH     // Stress: multiple FETCH+DISPATCH, one TILE
    } test_type_e;

    typedef struct {
        int         B;              // Batch dimension
        int         C;              // Column dimension
        int         V;              // Vector dimension (NVs per dot product)
        string      name;           // Test name for display/golden file
        test_type_e test_type;      // Single or multi-dispatch
        int         dispatches_per_group; // For multi-dispatch: how many per group
    } test_config_t;

    // =========================================================================
    // Test Suite Definition
    // =========================================================================
    test_config_t test_suite[] = '{
        // Test 1: Simple single-dispatch (1 column group)
        '{B: 4, C: 4,  V: 4,  name: "B4_C4_V4",
          test_type: TEST_SINGLE_DISPATCH, dispatches_per_group: 1},

        // Test 2: 16-dispatch stress test (4 column groups, 4 dispatches each)
        '{B: 4, C: 64, V: 32, name: "B4_C64_V32_multi_dispatch",
          test_type: TEST_MULTI_DISPATCH, dispatches_per_group: 4}
    };

    // =========================================================================
    // Clock and Reset
    // =========================================================================
    logic clk;
    logic reset_n;

    // =========================================================================
    // DUT Interface Signals
    // =========================================================================
    // TILE command interface
    logic        tile_en;
    logic        tile_start;
    logic [15:0] tile_left_addr;
    logic [15:0] tile_right_addr;
    logic [7:0]  tile_left_ugd_len;
    logic [7:0]  tile_right_ugd_len;
    logic [7:0]  tile_vec_len;
    logic        tile_left_man_4b;
    logic        tile_right_man_4b;
    logic        tile_main_loop_over_left;
    logic [23:0] tile_mc_en;
    logic        tile_done;

    // DISPATCH command interface
    logic        disp_start;
    logic [7:0]  disp_ugd_vec_size;
    logic [7:0]  disp_right_ugd_len;
    logic [15:0] disp_tile_addr;
    logic [4:0]  disp_col_start;
    logic        disp_right;
    logic        disp_done;

    // row_bram write interface (4 parallel ports)
    logic [8:0]   wr_man_left_addr,  wr_man_right_addr;
    logic [255:0] wr_man_left_data,  wr_man_right_data;
    logic         wr_man_left_en,    wr_man_right_en;
    logic [8:0]   wr_exp_left_addr,  wr_exp_right_addr;
    logic [7:0]   wr_exp_left_data,  wr_exp_right_data;
    logic         wr_exp_left_en,    wr_exp_right_en;

    // Result interface
    logic [255:0] result_data;
    logic         result_valid;
    logic         result_full;
    logic         result_afull;

    // Debug interface
    logic [3:0]  ce_state;
    logic [15:0] ce_result_count;

    // =========================================================================
    // Testbench Storage
    // =========================================================================
    // BRAM models (staging area before writing to DUT)
    logic [255:0] tb_man_left  [0:511];
    logic [255:0] tb_man_right [0:511];
    logic [7:0]   tb_exp_left  [0:511];
    logic [7:0]   tb_exp_right [0:511];

    // Result collection
    logic [15:0] results_fp16 [0:16383];
    logic [15:0] golden_fp16  [0:16383];
    int          results_collected;

    // Test status
    int     tests_run;
    int     tests_passed;
    logic   current_test_ok;

    // =========================================================================
    // DUT Instantiation
    // =========================================================================
    compute_engine_mlp #(
        .TILE_ID     (0),
        .MAN_WIDTH   (256),
        .EXP_WIDTH   (8),
        .BRAM_DEPTH  (512),
        .NUM_COLUMNS (16),
        .NUM_MLPS    (8)
    ) dut (
        .i_clk                      (clk),
        .i_reset_n                  (reset_n),

        // DISPATCH command
        .i_disp_start               (disp_start),
        .i_disp_man_nv_cnt          (disp_right_ugd_len * disp_ugd_vec_size),
        .i_disp_ugd_vec_size        (disp_ugd_vec_size),
        .i_disp_tile_addr           (disp_tile_addr),
        .i_disp_man_4b              (1'b0),
        .i_disp_col_en              (24'h00_FFFF),
        .i_disp_col_start           (disp_col_start),
        .i_disp_right               (disp_right),
        .i_disp_broadcast           (1'b0),
        .o_disp_done                (disp_done),

        // TILE command
        .i_tile_en                  (tile_en),
        .i_tile_start               (tile_start),
        .i_tile_left_addr           (tile_left_addr),
        .i_tile_right_addr          (tile_right_addr),
        .i_tile_left_ugd_len        (tile_left_ugd_len),
        .i_tile_right_ugd_len       (tile_right_ugd_len),
        .i_tile_vec_len             (tile_vec_len),
        .i_tile_left_man_4b         (tile_left_man_4b),
        .i_tile_right_man_4b        (tile_right_man_4b),
        .i_tile_main_loop_over_left (tile_main_loop_over_left),
        .i_mc_tile_en               (tile_mc_en),
        .o_tile_done                (tile_done),

        // row_bram write ports
        .i_man_left_wr_addr         (wr_man_left_addr),
        .i_man_left_wr_data         (wr_man_left_data),
        .i_man_left_wr_en           (wr_man_left_en),
        .i_man_right_wr_addr        (wr_man_right_addr),
        .i_man_right_wr_data        (wr_man_right_data),
        .i_man_right_wr_en          (wr_man_right_en),
        .i_exp_left_wr_addr         (wr_exp_left_addr),
        .i_exp_left_wr_data         (wr_exp_left_data),
        .i_exp_left_wr_en           (wr_exp_left_en),
        .i_exp_right_wr_addr        (wr_exp_right_addr),
        .i_exp_right_wr_data        (wr_exp_right_data),
        .i_exp_right_wr_en          (wr_exp_right_en),

        // Result interface
        .o_result_data              (result_data),
        .o_result_valid             (result_valid),
        .i_result_full              (result_full),
        .i_result_afull             (result_afull),

        // Debug
        .o_ce_state                 (ce_state),
        .o_result_count             (ce_result_count)
    );

    // No backpressure
    assign result_full  = 1'b0;
    assign result_afull = 1'b0;

    // =========================================================================
    // Clock Generation
    // =========================================================================
    initial begin
        clk = 0;
        forever #(CLK_PERIOD_NS/2) clk = ~clk;
    end

    // =========================================================================
    // Result Collection (always running)
    // =========================================================================
    always_ff @(posedge clk) begin
        if (result_valid && !result_full) begin
            for (int i = 0; i < 16; i++) begin
                results_fp16[results_collected + i] = result_data[i*16 +: 16];
            end
            $display("  [%0t] Result pulse %0d: first=0x%04x",
                     $time, results_collected/16, result_data[15:0]);
            results_collected = results_collected + 16;
        end
    end

    // =========================================================================
    // File I/O: Parse Hex Line (32 space-separated bytes)
    // =========================================================================
    function automatic int parse_hex_line(
        input string line_str,
        output logic [7:0] bytes[32]
    );
        return $sscanf(line_str,
            "%h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h",
            bytes[0],  bytes[1],  bytes[2],  bytes[3],  bytes[4],  bytes[5],  bytes[6],  bytes[7],
            bytes[8],  bytes[9],  bytes[10], bytes[11], bytes[12], bytes[13], bytes[14], bytes[15],
            bytes[16], bytes[17], bytes[18], bytes[19], bytes[20], bytes[21], bytes[22], bytes[23],
            bytes[24], bytes[25], bytes[26], bytes[27], bytes[28], bytes[29], bytes[30], bytes[31]);
    endfunction

    // =========================================================================
    // File I/O: Load Matrix from Hex File
    // Format: Lines 0-15 = packed exponents, Lines 16-527 = mantissas
    // =========================================================================
    task automatic load_matrix_hex(
        input  string       filename,
        output logic [255:0] man_out[512],
        output logic [7:0]   exp_out[512]
    );
        int fd, line_idx;
        string line_str;
        logic [7:0] bytes[32];

        fd = $fopen(filename, "r");
        if (fd == 0) begin
            $display("  ERROR: Cannot open %s", filename);
            return;
        end

        line_idx = 0;
        while (!$feof(fd) && line_idx < 528) begin
            if ($fgets(line_str, fd) && parse_hex_line(line_str, bytes) == 32) begin
                if (line_idx < 16) begin
                    // Lines 0-15: Packed exponents (32 per line)
                    for (int b = 0; b < 32; b++) begin
                        exp_out[line_idx * 32 + b] = bytes[b];
                    end
                end else begin
                    // Lines 16-527: Mantissas (pack 32 bytes into 256-bit)
                    for (int b = 0; b < 32; b++) begin
                        man_out[line_idx - 16][b*8 +: 8] = bytes[b];
                    end
                end
                line_idx++;
            end
        end
        $fclose(fd);
        $display("  Loaded %0d lines from %s", line_idx, filename);
    endtask

    // =========================================================================
    // File I/O: Load Golden Reference (one FP16 hex value per line)
    // =========================================================================
    task automatic load_golden_hex(
        input  string filename,
        input  int    expected_count,
        input  int    offset
    );
        int fd, idx, scan_result;
        logic [15:0] val;

        fd = $fopen(filename, "r");
        if (fd == 0) begin
            $display("  ERROR: Cannot open golden file %s", filename);
            current_test_ok = 0;
            return;
        end

        idx = 0;
        while (!$feof(fd) && idx < expected_count) begin
            scan_result = $fscanf(fd, "%h\n", val);
            if (scan_result == 1) begin
                golden_fp16[offset + idx] = val;
                idx++;
            end
        end
        $fclose(fd);

        if (idx != expected_count)
            $display("  WARNING: Expected %0d golden values, got %0d", expected_count, idx);
    endtask

    // =========================================================================
    // Data Movement: Write TB BRAM to DUT row_bram
    // =========================================================================
    task automatic write_row_bram(input int num_lines);
        $display("  Writing %0d lines to row_bram...", num_lines);

        for (int i = 0; i < num_lines; i++) begin
            @(posedge clk);
            // Left side
            wr_man_left_addr <= i[8:0];
            wr_man_left_data <= tb_man_left[i];
            wr_man_left_en   <= 1'b1;
            wr_exp_left_addr <= i[8:0];
            wr_exp_left_data <= tb_exp_left[i];
            wr_exp_left_en   <= 1'b1;
            // Right side
            wr_man_right_addr <= i[8:0];
            wr_man_right_data <= tb_man_right[i];
            wr_man_right_en   <= 1'b1;
            wr_exp_right_addr <= i[8:0];
            wr_exp_right_data <= tb_exp_right[i];
            wr_exp_right_en   <= 1'b1;
        end

        @(posedge clk);
        wr_man_left_en  <= 1'b0;
        wr_man_right_en <= 1'b0;
        wr_exp_left_en  <= 1'b0;
        wr_exp_right_en <= 1'b0;
    endtask

    // =========================================================================
    // Command: DISPATCH RIGHT (row_bram → MLP BRAM)
    // =========================================================================
    task automatic cmd_dispatch_right(
        input logic [7:0]  c,           // Number of columns in this dispatch
        input logic [7:0]  v,           // NVs per column
        input logic [15:0] tile_addr,   // Write base address in MLP BRAM
        input logic [4:0]  col_start    // Starting column for distribution
    );
        $display("  DISPATCH RIGHT: C=%0d, V=%0d, tile_addr=%0d, col_start=%0d",
                 c, v, tile_addr, col_start);

        @(posedge clk);
        disp_right_ugd_len <= c;
        disp_ugd_vec_size  <= v;
        disp_tile_addr     <= tile_addr;
        disp_col_start     <= col_start;
        disp_right         <= 1'b1;
        disp_start         <= 1'b1;

        @(posedge clk);
        disp_start <= 1'b0;

        // Wait for done
        @(posedge clk);  // Allow disp_done to clear
        while (!disp_done) @(posedge clk);
        repeat (2) @(posedge clk);
        disp_right <= 1'b0;
    endtask

    // =========================================================================
    // Command: TILE (Compute MATMUL)
    // =========================================================================
    task automatic cmd_tile(
        input logic [7:0]  b,
        input logic [7:0]  c,
        input logic [7:0]  v,
        input logic [15:0] left_addr  = 16'd0,
        input logic [15:0] right_addr = 16'd0
    );
        $display("  TILE: B=%0d, C=%0d, V=%0d, left_addr=%0d, right_addr=%0d",
                 b, c, v, left_addr, right_addr);

        @(posedge clk);
        tile_en                 <= 1'b1;
        tile_left_addr          <= left_addr;
        tile_right_addr         <= right_addr;
        tile_left_ugd_len       <= b;
        tile_right_ugd_len      <= c;
        tile_vec_len            <= v;
        tile_left_man_4b        <= 1'b0;
        tile_right_man_4b       <= 1'b0;
        tile_main_loop_over_left <= 1'b0;
        tile_mc_en              <= 24'h000001;

        @(posedge clk);
        tile_start <= 1'b1;
        @(posedge clk);
        tile_start <= 1'b0;
    endtask

    // =========================================================================
    // Command: Wait for TILE completion
    // =========================================================================
    task automatic wait_tile_done(input int timeout_cycles);
        int cycles = 0;

        while (!tile_done && cycles < timeout_cycles) begin
            @(posedge clk);
            cycles++;
        end

        if (tile_done) begin
            $display("  TILE completed in %0d cycles", cycles);
        end else begin
            $display("  ERROR: TILE timeout after %0d cycles", timeout_cycles);
            current_test_ok = 0;
        end

        repeat (10) @(posedge clk);  // Allow final results to propagate
    endtask

    // =========================================================================
    // Validation: Compare results against golden reference
    // =========================================================================
    task automatic validate_results(
        input int B,
        input int C,
        input int V
    );
        int expected_count, expected_hw_count, num_groups;
        int mismatches, exact_matches, close_matches;
        int batch_idx, col_idx, group_idx, col_in_group, pulse_idx, hw_idx, diff;
        logic [15:0] hw_val, golden_val;

        expected_count = B * C;
        num_groups = (C + 15) / 16;
        expected_hw_count = B * num_groups * 16;

        $display("  Validating %0d results (B=%0d, C=%0d, groups=%0d, tol=%0d LSB)...",
                 expected_count, B, C, num_groups, ABS_TOLERANCE);

        if (results_collected != expected_hw_count) begin
            $display("  [FAIL] Expected %0d HW results, got %0d",
                     expected_hw_count, results_collected);
            current_test_ok = 0;
            return;
        end

        mismatches = 0;
        exact_matches = 0;
        close_matches = 0;

        for (int golden_idx = 0; golden_idx < expected_count; golden_idx++) begin
            golden_val = golden_fp16[golden_idx];
            batch_idx  = golden_idx / C;
            col_idx    = golden_idx % C;

            // Map golden index to hardware output index
            if (num_groups > 1) begin
                group_idx    = col_idx / 16;
                col_in_group = col_idx % 16;
                pulse_idx    = batch_idx * num_groups + group_idx;
                hw_idx       = pulse_idx * 16 + col_in_group;
            end else begin
                hw_idx = batch_idx * 16 + col_idx;
            end

            hw_val = results_fp16[hw_idx];
            diff = (hw_val > golden_val) ? (hw_val - golden_val) : (golden_val - hw_val);

            if (diff == 0) begin
                exact_matches++;
            end else if (diff <= ABS_TOLERANCE) begin
                close_matches++;
            end else begin
                if (mismatches < 10)
                    $display("    MISMATCH[%0d→hw%0d]: hw=0x%04x golden=0x%04x diff=%0d",
                             golden_idx, hw_idx, hw_val, golden_val, diff);
                mismatches++;
            end
        end

        $display("  Validation: %0d/%0d within tolerance (%0d exact, %0d close)",
                 exact_matches + close_matches, expected_count, exact_matches, close_matches);

        if (mismatches == 0) begin
            $display("  [PASS] All results within tolerance!\n");
        end else begin
            $display("  [FAIL] %0d mismatches (diff > %0d LSB)\n", mismatches, ABS_TOLERANCE);
            current_test_ok = 0;
        end
    endtask

    // =========================================================================
    // Test Execution: Single-Dispatch Test
    // =========================================================================
    task automatic run_single_dispatch_test(input test_config_t cfg);
        int num_lines;
        string golden_file;

        // Load golden reference
        golden_file = $sformatf("%sgolden_%s.hex", HEX_PATH, cfg.name);
        load_golden_hex(golden_file, cfg.B * cfg.C, 0);

        // Calculate lines to transfer: C * V * 4 (4 lines per NV)
        num_lines = cfg.C * cfg.V * 4;

        // FETCH: Load hex data to TB BRAM, write to DUT row_bram
        write_row_bram(num_lines);

        // DISPATCH RIGHT: Move weights from row_bram to MLP BRAM
        cmd_dispatch_right(cfg.C, cfg.V, 16'd0, 5'd0);

        // TILE: Execute MATMUL
        cmd_tile(cfg.B, cfg.C, cfg.V);

        // Wait and validate
        wait_tile_done(500000);
        validate_results(cfg.B, cfg.C, cfg.V);
    endtask

    // =========================================================================
    // Test Execution: Multi-Dispatch Test
    // =========================================================================
    task automatic run_multi_dispatch_test(input test_config_t cfg);
        int num_groups, dispatches_total, cols_per_dispatch;
        int group_idx, col_start_val, tile_addr_val;
        int num_lines, d, b, c_idx, idx, global_col;
        int fd, scan_result;
        string right_file, golden_file;
        logic [15:0] seg_golden[16];

        num_groups = (cfg.C + 15) / 16;
        dispatches_total = num_groups * cfg.dispatches_per_group;
        cols_per_dispatch = 16 / cfg.dispatches_per_group;

        $display("  Multi-dispatch: %0d dispatches (%0d groups × %0d per group)",
                 dispatches_total, num_groups, cfg.dispatches_per_group);

        // Load golden references (one per dispatch, then assemble)
        for (d = 0; d < dispatches_total; d++) begin
            golden_file = $sformatf("%sgolden_B%0d_C%0d_V%0d_%0d.hex",
                                    HEX_PATH, cfg.B, cols_per_dispatch, cfg.V, d);

            fd = $fopen(golden_file, "r");
            if (fd == 0) begin
                $display("  ERROR: Cannot open %s", golden_file);
                current_test_ok = 0;
                return;
            end

            // Read this dispatch's golden values
            idx = 0;
            while (!$feof(fd) && idx < cfg.B * cols_per_dispatch) begin
                scan_result = $fscanf(fd, "%h\n", seg_golden[idx]);
                if (scan_result == 1) idx++;
            end
            $fclose(fd);

            // Map to full golden array (batch-major order)
            for (b = 0; b < cfg.B; b++) begin
                for (c_idx = 0; c_idx < cols_per_dispatch; c_idx++) begin
                    global_col = d * cols_per_dispatch + c_idx;
                    golden_fp16[b * cfg.C + global_col] = seg_golden[b * cols_per_dispatch + c_idx];
                end
            end
        end
        $display("  Loaded %0d golden files (%0d total results)", dispatches_total, cfg.B * cfg.C);

        // Execute dispatch sequence
        for (d = 0; d < dispatches_total; d++) begin
            group_idx     = d / cfg.dispatches_per_group;
            col_start_val = (d % cfg.dispatches_per_group) * cols_per_dispatch;
            tile_addr_val = group_idx * cfg.V * 8;

            $display("  Dispatch %0d/%0d: col_start=%0d, tile_addr=%0d (group %0d)",
                     d + 1, dispatches_total, col_start_val, tile_addr_val, group_idx);

            // Load right matrix for this dispatch
            right_file = $sformatf("%sright_%0d.hex", HEX_PATH, d);
            load_matrix_hex(right_file, tb_man_right, tb_exp_right);

            // Write to row_bram and dispatch
            num_lines = cols_per_dispatch * cfg.V * 4;
            write_row_bram(num_lines);
            cmd_dispatch_right(cols_per_dispatch, cfg.V, tile_addr_val[15:0], col_start_val[4:0]);
        end

        $display("  All %0d dispatches complete", dispatches_total);

        // TILE: Execute full MATMUL
        cmd_tile(cfg.B, cfg.C, cfg.V);

        // Wait and validate
        wait_tile_done(500000);
        validate_results(cfg.B, cfg.C, cfg.V);
    endtask

    // =========================================================================
    // Signal Initialization
    // =========================================================================
    task automatic init_signals();
        reset_n          = 0;
        tile_en          = 0;
        tile_start       = 0;
        tile_left_addr   = 0;
        tile_right_addr  = 0;
        tile_left_ugd_len = 0;
        tile_right_ugd_len = 0;
        tile_vec_len     = 0;
        tile_left_man_4b = 0;
        tile_right_man_4b = 0;
        tile_main_loop_over_left = 0;
        tile_mc_en       = 24'h000001;

        disp_start       = 0;
        disp_ugd_vec_size = 0;
        disp_right_ugd_len = 0;
        disp_tile_addr   = 0;
        disp_col_start   = 0;
        disp_right       = 0;

        wr_man_left_en   = 0;
        wr_man_right_en  = 0;
        wr_exp_left_en   = 0;
        wr_exp_right_en  = 0;

        tests_run        = 0;
        tests_passed     = 0;
        results_collected = 0;
        current_test_ok  = 1;

        // Clear TB BRAM
        for (int i = 0; i < 512; i++) begin
            tb_man_left[i]  = 256'd0;
            tb_man_right[i] = 256'd0;
            tb_exp_left[i]  = 8'd0;
            tb_exp_right[i] = 8'd0;
        end
    endtask

    // =========================================================================
    // Main Test Sequence
    // =========================================================================
    initial begin
        init_signals();

        // Reset sequence
        repeat (5) @(posedge clk);
        reset_n = 1;
        repeat (2) @(posedge clk);

        $display("\n========================================");
        $display("Compute Engine MLP Testbench");
        $display("========================================\n");

        // Load left matrix once (shared across tests)
        $display("Loading left matrix (shared)...");
        load_matrix_hex({HEX_PATH, "left.hex"}, tb_man_left, tb_exp_left);

        // Load default right matrix
        load_matrix_hex({HEX_PATH, "right.hex"}, tb_man_right, tb_exp_right);

        // Run test suite
        begin
            test_config_t cfg;
            int num_groups;

            foreach (test_suite[i]) begin
                cfg = test_suite[i];
                num_groups = (cfg.C + 15) / 16;

                $display("\n[TEST %0d] %s (B×C×V = %0d×%0d×%0d, groups=%0d)",
                         i + 1, cfg.name, cfg.B, cfg.C, cfg.V, num_groups);

                results_collected = 0;
                current_test_ok = 1;

                case (cfg.test_type)
                    TEST_SINGLE_DISPATCH: run_single_dispatch_test(cfg);
                    TEST_MULTI_DISPATCH:  run_multi_dispatch_test(cfg);
                endcase

                tests_run++;
                if (current_test_ok) tests_passed++;
            end
        end

        // Summary
        $display("========================================");
        $display("TEST SUMMARY");
        $display("========================================");
        $display("Tests run:    %0d", tests_run);
        $display("Tests passed: %0d", tests_passed);
        if (tests_passed == tests_run) begin
            $display("STATUS: ALL TESTS PASSED");
        end else begin
            $display("STATUS: %0d TEST(S) FAILED", tests_run - tests_passed);
        end
        $display("========================================\n");

        $finish;
    end

    // =========================================================================
    // Timeout Watchdog
    // =========================================================================
    initial begin
        #TIMEOUT_NS;
        $display("ERROR: Testbench timeout!");
        $finish;
    end

endmodule
