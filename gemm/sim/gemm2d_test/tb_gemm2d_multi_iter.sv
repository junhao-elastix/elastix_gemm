// ------------------------------------------------------------------
// 2-D GEMM Multi-Iteration Testbench
//
// Purpose: Validate weight persistence across multiple MATMUL operations
//   - Weights loaded once at init (persist in BRAM)
//   - Activations reloaded each iteration
//   - Results verified: all 10 iterations should produce identical output
//
// Configuration: B=4, C=4, V=32 with 16 per-row hex file pairs
// Iterations: 10
// Total results: 10 × 16 = 160 FP16 values
//
// Author: Junhao Pan
// Date: 01/22/2026
// ------------------------------------------------------------------

`timescale 1ns/1ps

`include "nap_interfaces.svh"

module tb_gemm2d_multi_iter;

    // ====================================================================
    // Test Configuration
    // ====================================================================
    localparam int NUM_ROWS = 16;
    localparam int NUM_COLS = 16;
    localparam int NUM_MLPS = 8;

    // BCV configuration from hex files
    localparam int B = 4;
    localparam int C = 4;
    localparam int V = 32;                      // V per row
    localparam int V_TOTAL = V * NUM_ROWS;      // Total V across all rows (512)

    // Multi-iteration configuration
    localparam int NUM_ITERATIONS = 10;
    localparam int RESULTS_PER_ITER = B * C;    // 16 FP16 values per iteration
    localparam int TOTAL_RESULTS = NUM_ITERATIONS * RESULTS_PER_ITER;  // 160

    // Memory block configuration
    localparam int LINES_PER_BLOCK = 528;
    localparam int MAN_WIDTH = 256;
    localparam int EXP_WIDTH = 8;
    localparam int BRAM_DEPTH = 512;

    // AXI configuration
    localparam int AXI_ADDR_WIDTH = 42;
    localparam int AXI_DATA_WIDTH = 256;

    // Clock configuration (400 MHz)
    localparam CLK_PERIOD = 2.5;

    // Hex file base path
    localparam string HEX_BASE_PATH = "/home/dev/Dev/elastix_gemm/hex/B4_C4_V32/";

    // ====================================================================
    // Opcodes (from gemm_pkg)
    // ====================================================================
    localparam logic [7:0] OPC_NOP       = 8'h00;
    localparam logic [7:0] OPC_FETCH     = 8'hF0;
    localparam logic [7:0] OPC_DISP      = 8'hF1;
    localparam logic [7:0] OPC_MATMUL    = 8'hF2;
    localparam logic [7:0] OPC_WAIT_DISP = 8'hF3;
    localparam logic [7:0] OPC_WAIT_MATMUL = 8'hF4;
    localparam logic [7:0] OPC_READOUT   = 8'hF5;

    // ====================================================================
    // Clock and Reset
    // ====================================================================
    logic clk = 1'b0;
    logic reset_n;

    always #(CLK_PERIOD/2) clk <= ~clk;

    // ====================================================================
    // Test Control
    // ====================================================================
    integer test_errors;
    integer cycle_count;
    integer tests_run;
    integer tests_passed;

    // ====================================================================
    // Command FIFO Interface
    // ====================================================================
    logic [31:0] cmd_fifo_wdata;
    logic        cmd_fifo_wen;
    logic        cmd_fifo_full;
    logic        cmd_fifo_afull;
    logic [12:0] cmd_fifo_count;

    // ====================================================================
    // Result Interface
    // ====================================================================
    logic        result_ready;
    logic        result_valid;
    logic        result_last;
    logic [15:0] result_keep;
    logic [255:0] result_data;

    // ====================================================================
    // Status Interface
    // ====================================================================
    logic        engine_busy;
    logic [3:0]  mc_state;
    logic [3:0]  rc_state;

    // ====================================================================
    // AXI Interfaces (16 channels)
    // ====================================================================
    t_AXI4 #(
        .DATA_WIDTH(AXI_DATA_WIDTH),
        .ADDR_WIDTH(AXI_ADDR_WIDTH),
        .LEN_WIDTH(8),
        .ID_WIDTH(8)
    ) axi_ddr_if [NUM_ROWS-1:0] ();

    // ====================================================================
    // DUT: 2-D GEMM Engine
    // ====================================================================
    engine_top_2d #(
        .NUM_MLPS      (NUM_MLPS),
        .STACK_DEPTH   (4),
        .NUM_ROWS      (NUM_ROWS),
        .NUM_COLS      (NUM_COLS),
        .MAN_WIDTH     (MAN_WIDTH),
        .EXP_WIDTH     (EXP_WIDTH),
        .BRAM_DEPTH    (BRAM_DEPTH)
    ) u_dut (
        .i_clk              (clk),
        .i_reset_n          (reset_n),

        // Command FIFO Interface
        .i_cmd_fifo_wdata   (cmd_fifo_wdata),
        .i_cmd_fifo_wen     (cmd_fifo_wen),
        .o_cmd_fifo_full    (cmd_fifo_full),
        .o_cmd_fifo_afull   (cmd_fifo_afull),
        .o_cmd_fifo_count   (cmd_fifo_count),

        // AXI Interfaces (16 channels)
        .axi_ddr_if         (axi_ddr_if),

        // Result Interface
        .i_result_ready     (result_ready),
        .o_result_valid     (result_valid),
        .o_result_last      (result_last),
        .o_result_keep      (result_keep),
        .o_result_data      (result_data),

        // Status
        .o_engine_busy      (engine_busy),
        .o_mc_state         (mc_state),
        .o_rc_state         (rc_state)
    );

    // ====================================================================
    // Memory Models (16 instances - one per GDDR6 channel)
    // Uses multi-iter variant: weights @ 0-527, activations @ 528-1055
    // ====================================================================
    generate
        for (genvar r = 0; r < NUM_ROWS; r++) begin : gen_mem_model

            // Memory statistics
            logic [31:0] mem_outstanding_count;
            logic [31:0] mem_total_ar_received;
            logic [31:0] mem_total_r_issued;

            tb_mem_model_multi_iter #(
                .DATA_WIDTH(AXI_DATA_WIDTH),
                .ADDR_WIDTH(AXI_ADDR_WIDTH),
                .LINES_PER_BLOCK(LINES_PER_BLOCK),
                .NUM_BLOCKS(2),
                .LATENCY_CYCLES(40),      // 100ns @ 400MHz
                .MAX_OUTSTANDING(32),
                .VERBOSITY(1),            // Show loading messages
                .CHANNEL_ID(r),           // Channel-specific hex files
                .HEX_BASE_PATH(HEX_BASE_PATH)
            ) u_mem_model (
                .i_clk(clk),
                .i_reset_n(reset_n),
                .axi_mem_if(axi_ddr_if[r].responder),
                .o_outstanding_count(mem_outstanding_count),
                .o_total_ar_received(mem_total_ar_received),
                .o_total_r_issued(mem_total_r_issued)
            );
        end
    endgenerate

    // ====================================================================
    // Result Storage - All 160 results across 10 iterations
    // ====================================================================
    logic [15:0] all_results [0:TOTAL_RESULTS-1];
    integer total_captured;

    // Golden Results Storage (per-row golden for iteration 0 verification)
    logic [15:0] golden_per_row [0:NUM_ROWS-1][0:B*C-1];

    // ====================================================================
    // FP16 Utility Functions
    // ====================================================================
    function automatic real fp16_to_real(input logic [15:0] fp16_val);
        logic sign;
        logic [4:0] exp;
        logic [9:0] mant;
        real result;
        int exp_int;

        sign = fp16_val[15];
        exp = fp16_val[14:10];
        mant = fp16_val[9:0];
        exp_int = int'(exp) - 15;

        if (exp == 5'h00) begin
            if (mant == 10'h000) begin
                result = 0.0;
            end else begin
                result = (real'(mant) / 1024.0) * (2.0 ** (-14));
            end
        end else if (exp == 5'h1F) begin
            result = (mant == 10'h000) ? 1.0e38 : 0.0/0.0;
        end else begin
            result = (1.0 + (real'(mant) / 1024.0)) * (2.0 ** exp_int);
        end

        if (sign) result = -result;
        return result;
    endfunction

    function automatic bit is_nan(input real val);
        return (val != val);
    endfunction

    // ====================================================================
    // Golden Results Loading Task
    // ====================================================================
    task automatic load_golden_results();
        string golden_file;
        string line_str;
        integer fd;
        logic [15:0] fp16_val;
        integer scan_result;
        integer load_errors;
        integer values_loaded;

        $display("[TB] Loading golden results...");
        load_errors = 0;

        // Initialize all golden values to zero
        for (int r = 0; r < NUM_ROWS; r++) begin
            for (int i = 0; i < B*C; i++) begin
                golden_per_row[r][i] = 16'h0000;
            end
        end

        // Load per-row golden files
        for (int r = 0; r < NUM_ROWS; r++) begin
            $sformat(golden_file, "%sgolden_B%0d_C%0d_V%0d_%0d.hex", HEX_BASE_PATH, B, C, V, r);

            fd = $fopen(golden_file, "r");
            if (fd == 0) begin
                $error("[TB] Cannot open golden file: %s", golden_file);
                load_errors++;
                continue;
            end

            values_loaded = 0;
            while (!$feof(fd) && values_loaded < B*C) begin
                if ($fgets(line_str, fd)) begin
                    scan_result = $sscanf(line_str, "%h", fp16_val);
                    if (scan_result == 1) begin
                        golden_per_row[r][values_loaded] = fp16_val;
                        values_loaded++;
                    end
                end
            end

            $fclose(fd);

            if (values_loaded < B*C) begin
                $warning("[TB] Only loaded %0d/%0d values from %s", values_loaded, B*C, golden_file);
                load_errors++;
            end
        end

        if (load_errors > 0) begin
            $error("[TB] Golden loading had %0d errors!", load_errors);
        end else begin
            $display("[TB] Golden results loaded successfully\n");
        end
    endtask

    // ====================================================================
    // Command Writing Task
    // ====================================================================
    task automatic write_cmd(input logic [31:0] word);
        while (cmd_fifo_full) @(posedge clk);
        cmd_fifo_wdata = word;
        cmd_fifo_wen = 1'b1;
        @(posedge clk);
        cmd_fifo_wen = 1'b0;
    endtask

    // ====================================================================
    // Issue Command Sequence Tasks
    // ====================================================================
    task automatic issue_fetch_command(
        input logic [7:0] cmd_id,
        input logic [31:0] start_addr,
        input logic [15:0] ugd_len,
        input logic [15:0] len,
        input logic fetch_right
    );
        logic [31:0] header, word1, word2, word3;

        header = {16'h0010, cmd_id, OPC_FETCH};
        word1 = start_addr;
        word2 = {ugd_len, len};
        word3 = {31'b0, fetch_right};

        $display("[TB] FETCH CMD: id=%0d, addr=0x%08x, ugd_len=%0d, len=%0d, right=%0d",
                 cmd_id, start_addr, ugd_len, len, fetch_right);

        write_cmd(header);
        write_cmd(word1);
        write_cmd(word2);
        write_cmd(word3);
    endtask

    task automatic issue_dispatch_command(
        input logic [7:0] cmd_id,
        input logic [15:0] nv_cnt,
        input logic [15:0] ugd_len,
        input logic [15:0] tile_addr,
        input logic [7:0] col_start,
        input logic disp_right
    );
        logic [31:0] header, word1, word2, word3;
        logic broadcast;

        broadcast = ~disp_right;
        header = {16'h0010, cmd_id, OPC_DISP};
        word1 = {nv_cnt, ugd_len};
        word2 = {16'b0, tile_addr};
        word3 = {16'b0, col_start, 5'b0, disp_right, broadcast, 1'b0};

        $display("[TB] DISPATCH CMD: id=%0d, nv=%0d, ugd=%0d, tile=0x%04x, col=%0d, right=%0d",
                 cmd_id, nv_cnt, ugd_len, tile_addr, col_start, disp_right);

        write_cmd(header);
        write_cmd(word1);
        write_cmd(word2);
        write_cmd(word3);
    endtask

    task automatic issue_wait_disp_command(
        input logic [7:0] cmd_id,
        input logic [7:0] wait_id
    );
        logic [31:0] header, word1, word2, word3;

        header = {16'h0010, cmd_id, OPC_WAIT_DISP};
        word1 = {24'd0, wait_id};
        word2 = 32'd0;
        word3 = 32'd0;

        $display("[TB] WAIT_DISP CMD: id=%0d, wait_id=%0d", cmd_id, wait_id);

        write_cmd(header);
        write_cmd(word1);
        write_cmd(word2);
        write_cmd(word3);
    endtask

    task automatic issue_matmul_command(
        input logic [7:0] cmd_id,
        input logic [15:0] left_addr,
        input logic [15:0] right_addr,
        input logic [15:0] left_len,
        input logic [15:0] right_len,
        input logic [15:0] ugd_len
    );
        logic [31:0] header, word1, word2, word3;

        header = {16'h0010, cmd_id, OPC_MATMUL};
        word1 = {left_addr, right_addr};
        word2 = {left_len, right_len};
        word3 = {ugd_len, 13'b0, 1'b0, 1'b0, 1'b0};

        $display("[TB] MATMUL CMD: id=%0d, left_addr=%0d, right_addr=%0d, B=%0d, C=%0d, V=%0d",
                 cmd_id, left_addr, right_addr, left_len, right_len, ugd_len);

        write_cmd(header);
        write_cmd(word1);
        write_cmd(word2);
        write_cmd(word3);
    endtask

    task automatic issue_wait_tile_command(
        input logic [7:0] cmd_id,
        input logic [7:0] wait_id
    );
        logic [31:0] header, word1, word2, word3;

        header = {16'h0010, cmd_id, OPC_WAIT_MATMUL};
        word1 = {24'd0, wait_id};
        word2 = 32'd0;
        word3 = 32'd0;

        $display("[TB] WAIT_MATMUL CMD: id=%0d, wait_id=%0d", cmd_id, wait_id);

        write_cmd(header);
        write_cmd(word1);
        write_cmd(word2);
        write_cmd(word3);
    endtask

    task automatic issue_readout_command(
        input logic [7:0] cmd_id,
        input logic [15:0] left_len,
        input logic [15:0] right_len,
        input logic [15:0] ugd_len
    );
        logic [31:0] header, word1, word2, word3;

        header = {16'h0010, cmd_id, OPC_READOUT};
        word1 = {left_len, right_len};
        word2 = {16'b0, ugd_len};
        word3 = 32'd0;

        $display("[TB] READOUT CMD: id=%0d, B=%0d, C=%0d, V=%0d", cmd_id, left_len, right_len, ugd_len);

        write_cmd(header);
        write_cmd(word1);
        write_cmd(word2);
        write_cmd(word3);
    endtask

    // ====================================================================
    // Task: Reload activations in all memory models via hierarchical access
    // Note: Generate block indices must be constant, so we unroll manually
    // ====================================================================
    task automatic reload_all_activations();
        $display("[TB] Reloading activations to DDR addr 528-1055 for all 16 channels");
        gen_mem_model[0].u_mem_model.reload_activations();
        gen_mem_model[1].u_mem_model.reload_activations();
        gen_mem_model[2].u_mem_model.reload_activations();
        gen_mem_model[3].u_mem_model.reload_activations();
        gen_mem_model[4].u_mem_model.reload_activations();
        gen_mem_model[5].u_mem_model.reload_activations();
        gen_mem_model[6].u_mem_model.reload_activations();
        gen_mem_model[7].u_mem_model.reload_activations();
        gen_mem_model[8].u_mem_model.reload_activations();
        gen_mem_model[9].u_mem_model.reload_activations();
        gen_mem_model[10].u_mem_model.reload_activations();
        gen_mem_model[11].u_mem_model.reload_activations();
        gen_mem_model[12].u_mem_model.reload_activations();
        gen_mem_model[13].u_mem_model.reload_activations();
        gen_mem_model[14].u_mem_model.reload_activations();
        gen_mem_model[15].u_mem_model.reload_activations();
    endtask

    // ====================================================================
    // Task: Wait for engine to become idle
    // ====================================================================
    task automatic wait_for_engine_idle();
        integer timeout;
        timeout = 0;
        while (engine_busy && timeout < 50000) begin
            @(posedge clk);
            timeout++;
        end
        if (timeout >= 50000) begin
            $error("[TB] Timeout waiting for engine idle!");
        end else begin
            $display("[TB] Engine idle after %0d cycles", timeout);
        end
        // Extra cycles to ensure all results are captured
        repeat(100) @(posedge clk);
    endtask

    // ====================================================================
    // Result Capture Task - Called after each iteration to capture 16 results
    // ====================================================================
    task automatic capture_iteration_results(input integer iter_num, input integer expected_count);
        integer timeout;
        integer line_idx;
        integer captured_this_iter;

        $display("[TB] Capturing results for iteration %0d (expected %0d)...", iter_num, expected_count);

        captured_this_iter = 0;
        line_idx = 0;
        timeout = 0;
        result_ready = 1'b1;

        while (captured_this_iter < expected_count && timeout < 100000) begin
            @(posedge clk);
            timeout++;

            if (result_valid) begin
                // Extract FP16 values from 256-bit line (16 x FP16)
                for (int i = 0; i < 16 && captured_this_iter < expected_count; i++) begin
                    if (result_keep[i]) begin
                        all_results[total_captured] = result_data[i*16 +: 16];
                        total_captured++;
                        captured_this_iter++;
                    end
                end

                line_idx++;

                if (result_last) begin
                    $display("[TB] Iteration %0d: Last result received at line %0d", iter_num, line_idx);
                    break;
                end
            end
        end

        result_ready = 1'b0;

        if (timeout >= 100000) begin
            $error("[TB] Iteration %0d: Timeout! Captured %0d/%0d", iter_num, captured_this_iter, expected_count);
        end else begin
            $display("[TB] Iteration %0d: Captured %0d results in %0d cycles (total: %0d)",
                     iter_num, captured_this_iter, timeout, total_captured);
        end
    endtask

    // ====================================================================
    // Verification Task - Check all 160 results at the end
    // ====================================================================
    task automatic verify_all_iterations();
        integer errors;
        integer iter_errors;
        integer zero_count;
        real actual_real, golden_sum, diff, tolerance;
        logic [15:0] iter0_results [0:RESULTS_PER_ITER-1];
        logic [15:0] curr_result;

        $display("\n========================================================");
        $display("[TB] Verifying %0d total results (%0d iterations x %0d results)",
                 TOTAL_RESULTS, NUM_ITERATIONS, RESULTS_PER_ITER);
        $display("========================================================\n");

        errors = 0;
        zero_count = 0;

        // Store iteration 0 results for comparison
        for (int i = 0; i < RESULTS_PER_ITER; i++) begin
            iter0_results[i] = all_results[i];
        end

        // Check iteration 0 against golden (computed from per-row golden sums)
        $display("[TB] Verifying iteration 0 against golden reference...");
        for (int i = 0; i < RESULTS_PER_ITER; i++) begin
            // Compute expected sum across all rows
            golden_sum = 0.0;
            for (int r = 0; r < NUM_ROWS; r++) begin
                golden_sum = golden_sum + fp16_to_real(golden_per_row[r][i]);
            end

            actual_real = fp16_to_real(all_results[i]);

            if (all_results[i] == 16'h0000) zero_count++;

            // 1% tolerance for FP16 tree reduction
            tolerance = (golden_sum < 0) ? -golden_sum * 0.01 : golden_sum * 0.01;
            if (tolerance < 0.001) tolerance = 0.001;

            diff = actual_real - golden_sum;
            if (diff < 0) diff = -diff;

            if (diff > tolerance && !is_nan(golden_sum)) begin
                if (errors < 10) begin
                    $display("[TB] GOLDEN ERROR at result[%0d]: got 0x%04x (%.4f), expected ~%.4f",
                             i, all_results[i], actual_real, golden_sum);
                end
                errors++;
            end else if (i < 4) begin
                $display("[TB] GOLDEN MATCH at result[%0d]: got 0x%04x (%.4f) ~ %.4f",
                         i, all_results[i], actual_real, golden_sum);
            end
        end

        // Critical: check if all outputs are zero
        if (zero_count == RESULTS_PER_ITER) begin
            $display("[TB] CRITICAL: All iteration 0 results are ZERO!");
            errors = RESULTS_PER_ITER;
        end

        $display("[TB] Iteration 0 golden check: %0d errors\n", errors);

        // Now check all subsequent iterations match iteration 0
        for (int iter = 1; iter < NUM_ITERATIONS; iter++) begin
            iter_errors = 0;

            for (int i = 0; i < RESULTS_PER_ITER; i++) begin
                curr_result = all_results[iter * RESULTS_PER_ITER + i];

                if (curr_result != iter0_results[i]) begin
                    if (iter_errors < 5) begin
                        $display("[TB] ITER MISMATCH: iter[%0d][%0d]=0x%04x != iter[0][%0d]=0x%04x",
                                 iter, i, curr_result, i, iter0_results[i]);
                    end
                    iter_errors++;
                    errors++;
                end
            end

            if (iter_errors == 0) begin
                $display("[TB] Iteration %0d: MATCH (identical to iter 0)", iter);
            end else begin
                $display("[TB] Iteration %0d: MISMATCH (%0d differences from iter 0)", iter, iter_errors);
            end
        end

        // Final summary
        $display("\n========================================================");
        if (errors == 0) begin
            $display("[TB] PASS: All %0d results verified (%0d iterations identical)",
                     TOTAL_RESULTS, NUM_ITERATIONS);
            tests_passed++;
        end else begin
            $display("[TB] FAIL: %0d total errors across %0d iterations", errors, NUM_ITERATIONS);
        end
        $display("========================================================\n");

        test_errors += errors;
        tests_run++;
    endtask

    // ====================================================================
    // Main Test Sequence
    // ====================================================================
    initial begin
        // Initialize
        reset_n = 1'b0;
        test_errors = 0;
        cycle_count = 0;
        tests_run = 0;
        tests_passed = 0;
        cmd_fifo_wdata = 32'd0;
        cmd_fifo_wen = 1'b0;

        $display("\n===============================================");
        $display("2-D GEMM MULTI-ITERATION TESTBENCH");
        $display("Configuration: B=%0d, C=%0d, V=%0d, Rows=%0d", B, C, V, NUM_ROWS);
        $display("Iterations: %0d, Total results: %0d", NUM_ITERATIONS, TOTAL_RESULTS);
        $display("===============================================\n");

        // Reset sequence
        repeat(10) @(posedge clk);
        reset_n = 1'b1;
        repeat(10) @(posedge clk);

        // Initialize result storage
        total_captured = 0;
        for (int i = 0; i < TOTAL_RESULTS; i++) begin
            all_results[i] = 16'h0000;
        end

        // Load golden results
        load_golden_results();

        // =================================================================
        // Phase 1: Load Weights Once (from addr 0 in memory model)
        //          Memory layout: weights @ 0-527, activations @ 528-1055
        // =================================================================
        $display("\n=== PHASE 1: LOADING WEIGHTS (once) ===\n");

        // Fetch weights from addr 0 (where right_*.hex is loaded)
        issue_fetch_command(
            .cmd_id(8'd1),
            .start_addr(32'd0),              // Weights at line addr 0
            .ugd_len(V_TOTAL),               // Total V (512)
            .len(16'd528),                   // Full block
            .fetch_right(1'b1)
        );

        // Wait for fetch complete
        issue_wait_disp_command(
            .cmd_id(8'd2),
            .wait_id(8'd1)
        );

        // Dispatch weights to mlp_bram
        issue_dispatch_command(
            .cmd_id(8'd3),
            .nv_cnt(C),                      // C columns
            .ugd_len(V_TOTAL),               // Total V (512)
            .tile_addr(16'd0),
            .col_start(8'd0),
            .disp_right(1'b1)                // Right = weights
        );

        // Wait for dispatch complete
        issue_wait_disp_command(
            .cmd_id(8'd4),
            .wait_id(8'd3)
        );

        $display("[TB] Weights loaded and dispatched to MLP BRAMs\n");

        // =================================================================
        // Phase 2: Iterate 10 times - activations reloaded each time
        // =================================================================
        for (int iter = 0; iter < NUM_ITERATIONS; iter++) begin
            $display("\n=== ITERATION %0d of %0d ===\n", iter, NUM_ITERATIONS);

            // Reload activations to memory models (addr 528-1055)
            reload_all_activations();

            // Fetch activations from addr 528
            issue_fetch_command(
                .cmd_id(8'(10 + iter*10 + 1)),    // Unique cmd_id per iteration
                .start_addr(32'd528),              // Activations at line addr 528
                .ugd_len(V_TOTAL),
                .len(16'd528),
                .fetch_right(1'b0)                 // Left = activations
            );

            // Wait for fetch complete
            issue_wait_disp_command(
                .cmd_id(8'(10 + iter*10 + 2)),
                .wait_id(8'(10 + iter*10 + 1))
            );

            // Dispatch activations to row_bram
            issue_dispatch_command(
                .cmd_id(8'(10 + iter*10 + 3)),
                .nv_cnt(B),                        // B batches
                .ugd_len(V_TOTAL),
                .tile_addr(16'd0),
                .col_start(8'd0),
                .disp_right(1'b0)                  // Left = activations (broadcast)
            );

            // Wait for dispatch complete
            issue_wait_disp_command(
                .cmd_id(8'(10 + iter*10 + 4)),
                .wait_id(8'(10 + iter*10 + 3))
            );

            // Issue MATMUL
            issue_matmul_command(
                .cmd_id(8'(10 + iter*10 + 5)),
                .left_addr(16'd0),
                .right_addr(16'd0),
                .left_len(16'd4),                  // B = 4
                .right_len(16'd4),                 // C = 4
                .ugd_len(V_TOTAL)
            );

            // Issue READOUT (before WAIT_MATMUL)
            issue_readout_command(
                .cmd_id(8'(10 + iter*10 + 6)),
                .left_len(16'd4),                  // B = 4
                .right_len(16'd4),                 // C = 4
                .ugd_len(V_TOTAL)
            );

            // Wait for MATMUL complete
            issue_wait_tile_command(
                .cmd_id(8'(10 + iter*10 + 7)),
                .wait_id(8'(10 + iter*10 + 5))
            );

            // Wait for commands to be processed then capture results
            repeat(100) @(posedge clk);

            // Capture 16 results for this iteration
            capture_iteration_results(iter, RESULTS_PER_ITER);
        end

        // =================================================================
        // Phase 3: Verify all results
        // =================================================================
        $display("\n=== PHASE 3: VERIFYING ALL RESULTS ===\n");

        // Small delay to ensure all processing is complete
        repeat(100) @(posedge clk);

        $display("[TB] Total captured: %0d results\n", total_captured);

        // =================================================================
        // Verify all results
        // =================================================================
        verify_all_iterations();

        // =================================================================
        // Test Summary
        // =================================================================
        repeat(100) @(posedge clk);

        $display("\n===============================================");
        $display("TEST SUMMARY");
        $display("===============================================");
        $display("Tests run:    %0d", tests_run);
        $display("Tests passed: %0d", tests_passed);
        $display("Total errors: %0d", test_errors);
        $display("Total cycles: %0d", cycle_count);
        $display("===============================================");

        if (test_errors == 0) begin
            $display("\n*** ALL TESTS PASSED ***\n");
        end else begin
            $display("\n*** TESTS FAILED ***\n");
        end

        $finish;
    end

    // ====================================================================
    // Cycle Counter
    // ====================================================================
    always @(posedge clk) begin
        if (reset_n) cycle_count <= cycle_count + 1;
        else cycle_count <= 0;
    end

    // ====================================================================
    // Timeout (30ms = 12,000,000 cycles @ 400MHz)
    // Extended for 10 iterations
    // ====================================================================
    initial begin
        #30000000ns;
        $error("[TB] TIMEOUT after 30ms!");
        $finish;
    end

    // ====================================================================
    // Debug: Monitor State Changes (sparse output)
    // ====================================================================
    logic [3:0] prev_mc_state;

    always @(posedge clk) begin
        if (reset_n) begin
            if (mc_state != prev_mc_state) begin
                $display("[MC_STATE] @cycle %0d: %0d -> %0d", cycle_count, prev_mc_state, mc_state);
            end
            prev_mc_state <= mc_state;
        end
    end

endmodule : tb_gemm2d_multi_iter
