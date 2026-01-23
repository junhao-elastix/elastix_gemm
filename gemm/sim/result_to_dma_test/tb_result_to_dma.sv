// ------------------------------------------------------------------
// Testbench for result_to_dma Module (Simple Registered Adapter)
//
// Purpose: Verify the result_to_dma module converts ready-valid stream
//          to BRAM write interface correctly.
//
// Test Cases:
//   1. Single write with full keep (0xFFFF)
//   2. Multiple back-to-back writes
//   3. Partial keep masks
//   4. Address counter verification
//   5. Data integrity verification
//
// Author: Junhao Pan
// Date: Jan 23, 2026
// ------------------------------------------------------------------

`timescale 1ns/1ps

module tb_result_to_dma;

    // ===================================================================
    // Parameters
    // ===================================================================
    localparam DATA_WIDTH = 256;
    localparam ADDR_WIDTH = 9;
    localparam CLK_PERIOD = 10;

    // ===================================================================
    // DUT Signals
    // ===================================================================
    logic                    clk;
    logic                    reset_n;

    // Input interface
    logic [DATA_WIDTH-1:0]   i_data;
    logic [15:0]             i_keep;
    logic                    i_last;
    logic                    i_valid;
    logic                    o_ready;

    // BRAM output interface
    logic                    o_bram_wr_en;
    logic [ADDR_WIDTH-1:0]   o_bram_wr_addr;
    logic [DATA_WIDTH-1:0]   o_bram_wr_data;
    logic [31:0]             o_bram_wr_strobe;

    // ===================================================================
    // Test Variables
    // ===================================================================
    int test_pass_count;
    int test_fail_count;
    int total_tests;

    // Captured BRAM writes for verification
    logic [DATA_WIDTH-1:0]   captured_data   [0:63];
    logic [ADDR_WIDTH-1:0]   captured_addr   [0:63];
    logic [31:0]             captured_strobe [0:63];
    int                      capture_count;

    // ===================================================================
    // DUT Instantiation
    // ===================================================================
    result_to_dma #(
        .DATA_WIDTH (DATA_WIDTH),
        .ADDR_WIDTH (ADDR_WIDTH)
    ) dut (
        .i_clk          (clk),
        .i_reset_n      (reset_n),

        .i_data         (i_data),
        .i_keep         (i_keep),
        .i_last         (i_last),
        .i_valid        (i_valid),
        .o_ready        (o_ready),

        .o_bram_wr_en   (o_bram_wr_en),
        .o_bram_wr_addr (o_bram_wr_addr),
        .o_bram_wr_data (o_bram_wr_data),
        .o_bram_wr_strobe(o_bram_wr_strobe)
    );

    // ===================================================================
    // Clock Generation
    // ===================================================================
    initial clk = 0;
    always #(CLK_PERIOD/2) clk = ~clk;

    // ===================================================================
    // BRAM Write Capture
    // ===================================================================
    logic capture_enable;

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            capture_count <= 0;
        end else if (capture_enable && o_bram_wr_en && capture_count < 64) begin
            captured_data[capture_count]   <= o_bram_wr_data;
            captured_addr[capture_count]   <= o_bram_wr_addr;
            captured_strobe[capture_count] <= o_bram_wr_strobe;
            capture_count <= capture_count + 1;
        end
    end

    // ===================================================================
    // Helper Tasks
    // ===================================================================

    // Reset DUT
    task reset_dut();
        capture_enable = 0;
        reset_n = 0;
        i_data  = 0;
        i_keep  = 0;
        i_last  = 0;
        i_valid = 0;
        repeat(10) @(posedge clk);
        reset_n = 1;
        capture_enable = 1;
        repeat(5) @(posedge clk);
    endtask

    // Send single data beat
    task send_data(
        input [DATA_WIDTH-1:0] data,
        input [15:0]           keep,
        input                  last
    );
        @(posedge clk);
        i_data  = data;
        i_keep  = keep;
        i_last  = last;
        i_valid = 1;
        @(posedge clk);
        i_valid = 0;
        i_last  = 0;
    endtask

    // Wait for writes to complete (1-cycle latency)
    task wait_writes_done(input int num_writes);
        repeat(num_writes + 5) @(posedge clk);
    endtask

    // Check test result
    task check_test(input string test_name, input logic passed);
        total_tests++;
        if (passed) begin
            test_pass_count++;
            $display("[PASS] %s", test_name);
        end else begin
            test_fail_count++;
            $display("[FAIL] %s", test_name);
        end
    endtask

    // Expected strobe from keep
    function automatic [31:0] expected_strobe(input [15:0] keep);
        logic [31:0] strobe;
        for (int i = 0; i < 16; i++) begin
            strobe[i*2 +: 2] = {2{keep[i]}};
        end
        return strobe;
    endfunction

    // Generate test pattern based on index
    function automatic [DATA_WIDTH-1:0] gen_pattern(input int idx);
        logic [DATA_WIDTH-1:0] pattern;
        for (int i = 0; i < 8; i++) begin
            pattern[i*32 +: 32] = idx + i;
        end
        return pattern;
    endfunction

    // ===================================================================
    // Test Cases
    // ===================================================================

    // Test 1: Single write with full keep
    task test_single_full_keep();
        logic [DATA_WIDTH-1:0] test_data;
        logic passed;

        $display("\n--- Test 1: Single write with full keep ---");
        reset_dut();

        test_data = 256'hDEADBEEF_CAFEBABE_12345678_9ABCDEF0_DEADBEEF_CAFEBABE_12345678_9ABCDEF0;
        send_data(test_data, 16'hFFFF, 1'b1);
        wait_writes_done(1);

        passed = (capture_count == 1) &&
                 (captured_data[0] == test_data) &&
                 (captured_addr[0] == 9'd0) &&
                 (captured_strobe[0] == 32'hFFFFFFFF);

        if (!passed) begin
            $display("  Expected: data=%h, addr=0, strobe=FFFFFFFF", test_data);
            $display("  Got:      data=%h, addr=%d, strobe=%h",
                     captured_data[0], captured_addr[0], captured_strobe[0]);
            $display("  Capture count: %d (expected 1)", capture_count);
        end

        check_test("Single write with full keep (0xFFFF)", passed);
    endtask

    // Test 2: Multiple back-to-back writes
    task test_multiple_writes();
        logic passed;
        logic [DATA_WIDTH-1:0] test_pattern;
        int num_writes;

        $display("\n--- Test 2: Multiple back-to-back writes ---");
        reset_dut();

        num_writes = 8;
        for (int i = 0; i < num_writes; i++) begin
            test_pattern = gen_pattern(i * 8);
            send_data(test_pattern, 16'hFFFF, (i == num_writes-1));
        end
        wait_writes_done(num_writes);

        passed = (capture_count == num_writes);

        // Verify sequential addresses
        for (int i = 0; i < num_writes && passed; i++) begin
            if (captured_addr[i] != i) begin
                $display("  Address mismatch at write %d: expected %d, got %d",
                         i, i, captured_addr[i]);
                passed = 0;
            end
        end

        check_test("Multiple back-to-back writes (8 writes)", passed);
    endtask

    // Test 3: Partial keep masks
    task test_partial_keep();
        logic passed;
        logic [31:0] exp_strobe;

        $display("\n--- Test 3: Partial keep masks ---");
        reset_dut();

        // Test keep = 0x000F (lower 4 FP16 values)
        send_data(256'hAAAAAAAA_BBBBBBBB_CCCCCCCC_DDDDDDDD_EEEEEEEE_FFFFFFFF_11111111_22222222,
                  16'h000F, 1'b0);

        // Test keep = 0xF000 (upper 4 FP16 values)
        send_data(256'h33333333_44444444_55555555_66666666_77777777_88888888_99999999_AAAAAAAA,
                  16'hF000, 1'b0);

        // Test keep = 0x0FF0 (middle 8 FP16 values)
        send_data(256'hBBBBBBBB_CCCCCCCC_DDDDDDDD_EEEEEEEE_FFFFFFFF_00000000_11111111_22222222,
                  16'h0FF0, 1'b1);

        wait_writes_done(3);

        passed = (capture_count == 3);

        // Verify strobes
        if (passed) begin
            exp_strobe = expected_strobe(16'h000F);
            if (captured_strobe[0] != exp_strobe) begin
                $display("  Strobe 0 mismatch: expected %h, got %h", exp_strobe, captured_strobe[0]);
                passed = 0;
            end

            exp_strobe = expected_strobe(16'hF000);
            if (captured_strobe[1] != exp_strobe) begin
                $display("  Strobe 1 mismatch: expected %h, got %h", exp_strobe, captured_strobe[1]);
                passed = 0;
            end

            exp_strobe = expected_strobe(16'h0FF0);
            if (captured_strobe[2] != exp_strobe) begin
                $display("  Strobe 2 mismatch: expected %h, got %h", exp_strobe, captured_strobe[2]);
                passed = 0;
            end
        end

        check_test("Partial keep masks (0x000F, 0xF000, 0x0FF0)", passed);
    endtask

    // Test 4: Address counter verification
    task test_address_counter();
        logic passed;
        logic [DATA_WIDTH-1:0] test_pattern;
        int num_writes;

        $display("\n--- Test 4: Address counter verification ---");
        reset_dut();

        num_writes = 16;
        for (int i = 0; i < num_writes; i++) begin
            test_pattern = gen_pattern(i);
            send_data(test_pattern, 16'hFFFF, (i == num_writes-1));
        end
        wait_writes_done(num_writes);

        passed = (capture_count == num_writes);

        // Verify strictly sequential addresses starting from 0
        for (int i = 0; i < num_writes && passed; i++) begin
            if (captured_addr[i] != i) begin
                $display("  Address error at write %d: expected %d, got %d",
                         i, i, captured_addr[i]);
                passed = 0;
            end
        end

        check_test("Address counter sequential (0 to 15)", passed);
    endtask

    // Test 5: Data integrity
    task test_data_integrity();
        logic passed;
        logic [DATA_WIDTH-1:0] test_patterns [0:3];

        $display("\n--- Test 5: Data integrity ---");
        reset_dut();

        // Different test patterns
        test_patterns[0] = 256'h0;
        test_patterns[1] = 256'hFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF;
        test_patterns[2] = 256'hAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA;
        test_patterns[3] = 256'h5555555555555555555555555555555555555555555555555555555555555555;

        for (int i = 0; i < 4; i++) begin
            send_data(test_patterns[i], 16'hFFFF, (i == 3));
        end
        wait_writes_done(4);

        passed = (capture_count == 4);

        for (int i = 0; i < 4 && passed; i++) begin
            if (captured_data[i] != test_patterns[i]) begin
                $display("  Data mismatch at write %d:", i);
                $display("    Expected: %h", test_patterns[i]);
                $display("    Got:      %h", captured_data[i]);
                passed = 0;
            end
        end

        check_test("Data integrity (various patterns)", passed);
    endtask

    // Test 6: o_ready always asserted
    task test_always_ready();
        logic passed;

        $display("\n--- Test 6: o_ready always asserted ---");
        reset_dut();

        // Check ready is always 1
        passed = o_ready;

        // Send some data and verify ready stays high
        for (int i = 0; i < 10; i++) begin
            send_data(gen_pattern(i), 16'hFFFF, 0);
            if (!o_ready) passed = 0;
        end

        check_test("o_ready always asserted", passed);
    endtask

    // ===================================================================
    // Main Test Sequence
    // ===================================================================
    initial begin
        $display("======================================================================");
        $display("  result_to_dma Module Testbench (Simple Registered)");
        $display("======================================================================");
        $display("  DATA_WIDTH = %0d", DATA_WIDTH);
        $display("  ADDR_WIDTH = %0d", ADDR_WIDTH);
        $display("======================================================================");

        test_pass_count = 0;
        test_fail_count = 0;
        total_tests = 0;
        capture_enable = 0;

        // Run all tests
        test_single_full_keep();
        test_multiple_writes();
        test_partial_keep();
        test_address_counter();
        test_data_integrity();
        test_always_ready();

        // Summary
        $display("\n======================================================================");
        $display("  TEST SUMMARY");
        $display("======================================================================");
        $display("  Total Tests: %0d", total_tests);
        $display("  Passed:      %0d", test_pass_count);
        $display("  Failed:      %0d", test_fail_count);
        $display("======================================================================");

        if (test_fail_count == 0) begin
            $display("  ALL TESTS PASSED");
        end else begin
            $display("  SOME TESTS FAILED");
        end
        $display("======================================================================\n");

        $finish;
    end

endmodule : tb_result_to_dma
