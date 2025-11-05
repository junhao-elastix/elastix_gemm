// ------------------------------------------------------------------
// Fetcher Module Testbench
//
// Purpose: Validate fetcher.sv performance and correctness
// Use Case: Golden reference for fetcher optimization
//
// Architecture:
//   - DUT: fetcher.sv (reads from GDDR6 via AXI)
//   - BRAM: dispatcher_bram.sv (matches hardware exactly)
//   - Memory: tb_memory_model_behavioral.sv (zero-latency for baseline)
//
// Test Flow:
//   1. Load left.hex and right.hex into GDDR6 model
//   2. Issue FETCH command for left matrix (target=0)
//   3. Verify BRAM contents (exp_packed, exp_aligned, mantissa)
//   4. Issue FETCH command for right matrix (target=1)
//   5. Verify BRAM contents
//   6. Report cycle counts and performance metrics
//
// Golden Reference:
//   - Current fetcher.sv is the baseline implementation
//   - Future optimizations must produce identical BRAM contents
//   - Cycle count improvements are measured against this baseline
//
// Author: Fetcher Optimization Project
// Date: 2025-11-03
// ------------------------------------------------------------------

`timescale 1ns/1ps

`include "nap_interfaces.svh"

module tb_fetcher;

    // ====================================================================
    // Clock and Reset
    // ====================================================================
    logic clk = 1'b0;
    logic reset_n;

    localparam CLK_PERIOD = 2.5;  // 400MHz (2.5ns period)
    always #(CLK_PERIOD/2) clk <= ~clk;

    // ====================================================================
    // Test Control
    // ====================================================================
    logic test_start;
    logic test_complete;
    integer test_errors;
    integer cycle_count;

    // Performance tracking
    integer fetch_left_start_cycle;
    integer fetch_left_end_cycle;
    integer fetch_right_start_cycle;
    integer fetch_right_end_cycle;

    // ====================================================================
    // AXI Interface (NAP to GDDR6)
    // ====================================================================
    t_AXI4 #(
        .DATA_WIDTH(256),
        .ADDR_WIDTH(42),
        .LEN_WIDTH(8),
        .ID_WIDTH(8)
    ) axi_nap();

    // ====================================================================
    // GDDR6 Memory Model (Behavioral - Zero Latency for Baseline)
    // ====================================================================
    logic [31:0] mem_read_count;
    logic [31:0] mem_last_addr;

    tb_memory_model #(
        .DATA_WIDTH(256),
        .ADDR_WIDTH(42),
        .LINES_PER_BLOCK(528),
        .NUM_BLOCKS(2),
        .LATENCY_CYCLES(0)  // Zero latency for baseline measurement
    ) u_gddr6_model (
        .i_clk(clk),
        .i_reset_n(reset_n),
        .axi_mem_if(axi_nap.responder),
        .o_read_count(mem_read_count),
        .o_last_addr(mem_last_addr)
    );

    // ====================================================================
    // Dispatcher BRAM (Exact Hardware Match)
    // ====================================================================
    // Write interface (from fetcher)
    logic [255:0] bram_wr_data;
    logic [9:0]   bram_wr_addr;
    logic         bram_wr_en;
    logic         bram_wr_target;  // 0=left, 1=right

    // Exponent aligned write interface (from fetcher unpacking)
    logic [7:0]   exp_left_wr_data;
    logic [8:0]   exp_left_wr_addr;
    logic         exp_left_wr_en;
    logic [7:0]   exp_right_wr_data;
    logic [8:0]   exp_right_wr_addr;
    logic         exp_right_wr_en;

    // Exponent packed read interface (for fetcher unpacking loop)
    logic [4:0]   exp_packed_rd_addr;
    logic         exp_packed_rd_target;
    logic [255:0] exp_packed_rd_data;

    // Read interface (for verification)
    logic [8:0]   bram_rd_addr_left_exp;
    logic [8:0]   bram_rd_addr_left_man;
    logic [8:0]   bram_rd_addr_right_exp;
    logic [8:0]   bram_rd_addr_right_man;
    logic [7:0]   bram_rd_data_left_exp;
    logic [255:0] bram_rd_data_left_man;
    logic [7:0]   bram_rd_data_right_exp;
    logic [255:0] bram_rd_data_right_man;

    dispatcher_bram #(
        .BRAM_DEPTH(528),
        .DATA_WIDTH(256)
    ) u_dispatcher_bram (
        .i_clk(clk),
        .i_reset_n(reset_n),

        // Write interface (from fetcher)
        .i_wr_data(bram_wr_data),
        .i_wr_addr(bram_wr_addr),
        .i_wr_en(bram_wr_en),
        .i_wr_target(bram_wr_target),

        // Exponent aligned write interface
        .i_exp_left_wr_data(exp_left_wr_data),
        .i_exp_left_wr_addr(exp_left_wr_addr),
        .i_exp_left_wr_en(exp_left_wr_en),
        .i_exp_right_wr_data(exp_right_wr_data),
        .i_exp_right_wr_addr(exp_right_wr_addr),
        .i_exp_right_wr_en(exp_right_wr_en),

        // Exponent packed read interface (for unpacking)
        .i_exp_packed_rd_addr(exp_packed_rd_addr),
        .i_exp_packed_rd_target(exp_packed_rd_target),
        .o_exp_packed_rd_data(exp_packed_rd_data),

        // Read interface (for verification)
        .i_rd_addr_left_exp(bram_rd_addr_left_exp),
        .i_rd_addr_left_man(bram_rd_addr_left_man),
        .i_rd_addr_right_exp(bram_rd_addr_right_exp),
        .i_rd_addr_right_man(bram_rd_addr_right_man),
        .o_rd_data_left_exp(bram_rd_data_left_exp),
        .o_rd_data_left_man(bram_rd_data_left_man),
        .o_rd_data_right_exp(bram_rd_data_right_exp),
        .o_rd_data_right_man(bram_rd_data_right_man)
    );

    // ====================================================================
    // DUT: Fetcher Module
    // ====================================================================
    logic        fetch_en;
    logic [25:0] fetch_start_addr;  // GDDR6 line address
    logic [15:0] fetch_num_lines;   // Number of lines to fetch (528)
    logic        fetch_target;      // 0=left, 1=right
    logic        fetch_done;
    logic [9:0]  fetch_page_id;

    fetcher #(
        .GDDR6_PAGE_ID(10'd2),  // Page 2 for GDDR6 channel
        .TGT_DATA_WIDTH(256),
        .AXI_ADDR_WIDTH(42)
    ) u_fetcher (
        .i_clk(clk),
        .i_reset_n(reset_n),

        // Control interface
        .i_fetch_en(fetch_en),
        .i_fetch_start_addr(fetch_start_addr),
        .i_fetch_num_lines(fetch_num_lines),
        .i_fetch_target(fetch_target),
        .o_fetch_done(fetch_done),

        // AXI interface to GDDR6
        .o_nap_ar_valid(axi_nap.arvalid),
        .i_nap_ar_ready(axi_nap.arready),
        .o_nap_ar_addr(axi_nap.araddr),
        .o_nap_ar_id(axi_nap.arid),
        .o_nap_ar_len(axi_nap.arlen),
        .o_nap_ar_size(axi_nap.arsize),
        .o_nap_ar_burst(axi_nap.arburst),

        .i_nap_r_valid(axi_nap.rvalid),
        .o_nap_r_ready(axi_nap.rready),
        .i_nap_r_data(axi_nap.rdata),
        .i_nap_r_last(axi_nap.rlast),
        .i_nap_r_id(axi_nap.rid),
        .i_nap_r_resp(axi_nap.rresp),

        // Dispatcher BRAM write interface
        .o_wr_data(bram_wr_data),
        .o_wr_addr(bram_wr_addr),
        .o_wr_en(bram_wr_en),
        .o_wr_target(bram_wr_target),

        // Exponent aligned write interface
        .o_exp_left_wr_data(exp_left_wr_data),
        .o_exp_left_wr_addr(exp_left_wr_addr),
        .o_exp_left_wr_en(exp_left_wr_en),
        .o_exp_right_wr_data(exp_right_wr_data),
        .o_exp_right_wr_addr(exp_right_wr_addr),
        .o_exp_right_wr_en(exp_right_wr_en),

        // Exponent packed read interface (for unpacking)
        .o_exp_packed_rd_addr(exp_packed_rd_addr),
        .o_exp_packed_rd_target(exp_packed_rd_target),
        .i_exp_packed_rd_data(exp_packed_rd_data)
    );

    // ====================================================================
    // Golden Reference Storage
    // ====================================================================
    // Store BRAM contents after each fetch for verification
    logic [7:0]   golden_left_exp[0:511];
    logic [255:0] golden_left_man[0:511];
    logic [7:0]   golden_right_exp[0:511];
    logic [255:0] golden_right_man[0:511];

    // ====================================================================
    // Verification Tasks
    // ====================================================================
    task automatic verify_bram_contents(
        input logic is_left,  // 0=right, 1=left
        input string matrix_name
    );
        integer errors = 0;
        integer i;
        logic [7:0] exp_val;
        logic [255:0] man_val;

        $display("\n[VERIFY] Checking %s matrix BRAM contents...", matrix_name);

        // Verify exponent aligned array (512 entries)
        for (i = 0; i < 512; i = i + 1) begin
            if (is_left) begin
                bram_rd_addr_left_exp = i[8:0];
                #(CLK_PERIOD);
                exp_val = bram_rd_data_left_exp;
                if (exp_val !== golden_left_exp[i]) begin
                    $error("[VERIFY] %s exp_aligned[%0d] mismatch: got 0x%02x, expected 0x%02x",
                           matrix_name, i, exp_val, golden_left_exp[i]);
                    errors++;
                end
            end else begin
                bram_rd_addr_right_exp = i[8:0];
                #(CLK_PERIOD);
                exp_val = bram_rd_data_right_exp;
                if (exp_val !== golden_right_exp[i]) begin
                    $error("[VERIFY] %s exp_aligned[%0d] mismatch: got 0x%02x, expected 0x%02x",
                           matrix_name, i, exp_val, golden_right_exp[i]);
                    errors++;
                end
            end
        end

        // Verify mantissa array (512 entries)
        for (i = 0; i < 512; i = i + 1) begin
            if (is_left) begin
                bram_rd_addr_left_man = i[8:0];
                #(CLK_PERIOD);
                man_val = bram_rd_data_left_man;
                if (man_val !== golden_left_man[i]) begin
                    $error("[VERIFY] %s mantissa[%0d] mismatch: got 0x%064x, expected 0x%064x",
                           matrix_name, i, man_val, golden_left_man[i]);
                    errors++;
                    if (errors > 10) begin
                        $display("[VERIFY] Too many errors, stopping verification");
                        break;
                    end
                end
            end else begin
                bram_rd_addr_right_man = i[8:0];
                #(CLK_PERIOD);
                man_val = bram_rd_data_right_man;
                if (man_val !== golden_right_man[i]) begin
                    $error("[VERIFY] %s mantissa[%0d] mismatch: got 0x%064x, expected 0x%064x",
                           matrix_name, i, man_val, golden_right_man[i]);
                    errors++;
                    if (errors > 10) begin
                        $display("[VERIFY] Too many errors, stopping verification");
                        break;
                    end
                end
            end
        end

        if (errors == 0) begin
            $display("[VERIFY] %s matrix: PASS (all 1024 entries correct)", matrix_name);
        end else begin
            $display("[VERIFY] %s matrix: FAIL (%0d errors found)", matrix_name, errors);
            test_errors = test_errors + errors;
        end
    endtask

    task automatic capture_golden_bram(input logic is_left);
        integer i;

        $display("[GOLDEN] Capturing %s matrix BRAM contents...", is_left ? "left" : "right");

        for (i = 0; i < 512; i = i + 1) begin
            if (is_left) begin
                bram_rd_addr_left_exp = i[8:0];
                bram_rd_addr_left_man = i[8:0];
                #(CLK_PERIOD);
                golden_left_exp[i] = bram_rd_data_left_exp;
                golden_left_man[i] = bram_rd_data_left_man;
            end else begin
                bram_rd_addr_right_exp = i[8:0];
                bram_rd_addr_right_man = i[8:0];
                #(CLK_PERIOD);
                golden_right_exp[i] = bram_rd_data_right_exp;
                golden_right_man[i] = bram_rd_data_right_man;
            end
        end

        $display("[GOLDEN] Capture complete");
    endtask

    // ====================================================================
    // Fetch Task
    // ====================================================================
    task automatic run_fetch(
        input logic [25:0] start_addr,
        input logic        target,      // 0=left, 1=right
        input string       test_name
    );
        integer start_cycle, end_cycle, duration;

        $display("\n========================================");
        $display("[TEST] %s", test_name);
        $display("[TEST] Start address: 0x%07x (line %0d)", start_addr, start_addr);
        $display("[TEST] Target: %s", target ? "RIGHT" : "LEFT");
        $display("========================================");

        // Record start cycle
        start_cycle = cycle_count;

        // Issue fetch command
        fetch_start_addr = start_addr;
        fetch_num_lines = 16'd528;
        fetch_target = target;
        fetch_en = 1'b1;

        @(posedge clk);
        fetch_en = 1'b0;

        // Wait for fetch completion
        wait(fetch_done == 1'b1);
        @(posedge clk);

        // Record end cycle
        end_cycle = cycle_count;
        duration = end_cycle - start_cycle;

        $display("[TEST] Fetch complete in %0d cycles", duration);
        $display("[TEST] Memory reads: %0d", mem_read_count);
        $display("[TEST] Throughput: %.2f lines/cycle", 528.0 / duration);

        // Store performance data
        if (target == 1'b0) begin
            fetch_left_start_cycle = start_cycle;
            fetch_left_end_cycle = end_cycle;
        end else begin
            fetch_right_start_cycle = start_cycle;
            fetch_right_end_cycle = end_cycle;
        end

        // Wait a few cycles for final writes to settle
        repeat(10) @(posedge clk);

    endtask

    // ====================================================================
    // Main Test Sequence
    // ====================================================================
    initial begin
        // Initialize
        reset_n = 1'b0;
        test_start = 1'b0;
        test_complete = 1'b0;
        test_errors = 0;
        cycle_count = 0;

        fetch_en = 1'b0;
        fetch_start_addr = '0;
        fetch_num_lines = '0;
        fetch_target = 1'b0;

        bram_rd_addr_left_exp = '0;
        bram_rd_addr_left_man = '0;
        bram_rd_addr_right_exp = '0;
        bram_rd_addr_right_man = '0;

        $display("\n================================================================================");
        $display("FETCHER TESTBENCH - Golden Reference Validation");
        $display("================================================================================");
        $display("Purpose: Establish baseline performance for fetcher optimization");
        $display("DUT:     fetcher.sv (current implementation)");
        $display("Memory:  tb_memory_model (zero-latency behavioral model)");
        $display("BRAM:    dispatcher_bram.sv (exact hardware match)");
        $display("================================================================================\n");

        // Wait for memory model to initialize
        $display("[TB] Waiting for memory initialization...");
        repeat(10) @(posedge clk);

        // Release reset
        reset_n = 1'b1;
        repeat(10) @(posedge clk);

        $display("[TB] Reset released, starting tests\n");
        test_start = 1'b1;

        // ================================================================
        // Test 1: Fetch Left Matrix
        // ================================================================
        run_fetch(
            26'd0,      // Start at line 0 (left matrix in GDDR6)
            1'b0,       // Target = left
            "FETCH LEFT MATRIX (528 lines from GDDR6 block 0)"
        );

        // Capture golden reference for left matrix
        capture_golden_bram(1'b1);

        // ================================================================
        // Test 2: Fetch Right Matrix
        // ================================================================
        run_fetch(
            26'd528,    // Start at line 528 (right matrix in GDDR6)
            1'b1,       // Target = right
            "FETCH RIGHT MATRIX (528 lines from GDDR6 block 1)"
        );

        // Capture golden reference for right matrix
        capture_golden_bram(1'b0);

        // ================================================================
        // Verification: Re-run and compare
        // ================================================================
        $display("\n================================================================================");
        $display("VERIFICATION PHASE: Re-run fetches and compare against golden");
        $display("================================================================================\n");

        // Re-fetch left and verify
        run_fetch(26'd0, 1'b0, "VERIFY LEFT MATRIX");
        verify_bram_contents(1'b1, "LEFT");

        // Re-fetch right and verify
        run_fetch(26'd528, 1'b1, "VERIFY RIGHT MATRIX");
        verify_bram_contents(1'b0, "RIGHT");

        // ================================================================
        // Performance Summary
        // ================================================================
        $display("\n================================================================================");
        $display("PERFORMANCE SUMMARY - BASELINE (Current fetcher.sv)");
        $display("================================================================================");
        $display("Left Matrix Fetch:");
        $display("  Cycles:     %0d", fetch_left_end_cycle - fetch_left_start_cycle);
        $display("  Lines:      528");
        $display("  Throughput: %.2f lines/cycle", 528.0 / (fetch_left_end_cycle - fetch_left_start_cycle));
        $display("");
        $display("Right Matrix Fetch:");
        $display("  Cycles:     %0d", fetch_right_end_cycle - fetch_right_start_cycle);
        $display("  Lines:      528");
        $display("  Throughput: %.2f lines/cycle", 528.0 / (fetch_right_end_cycle - fetch_right_start_cycle));
        $display("");
        $display("Memory Model:");
        $display("  Total reads: %0d", mem_read_count);
        $display("  Latency:     0 cycles (behavioral model)");
        $display("================================================================================");

        // ================================================================
        // Final Results
        // ================================================================
        test_complete = 1'b1;

        if (test_errors == 0) begin
            $display("\n*** TEST PASSED ***");
            $display("Golden reference established for fetcher optimization");
        end else begin
            $display("\n*** TEST FAILED ***");
            $display("Total errors: %0d", test_errors);
        end

        $display("\n================================================================================\n");
        $finish;
    end

    // ====================================================================
    // Cycle Counter
    // ====================================================================
    always @(posedge clk) begin
        if (reset_n) begin
            cycle_count <= cycle_count + 1;
        end else begin
            cycle_count <= 0;
        end
    end

    // ====================================================================
    // Timeout Watchdog
    // ====================================================================
    initial begin
        #(CLK_PERIOD * 100000);  // 100k cycles timeout
        $error("[TB] Simulation timeout!");
        $finish;
    end

    // ====================================================================
    // Waveform Dump (Optional)
    // ====================================================================
    initial begin
        $dumpfile("tb_fetcher.vcd");
        $dumpvars(0, tb_fetcher);
    end

endmodule
