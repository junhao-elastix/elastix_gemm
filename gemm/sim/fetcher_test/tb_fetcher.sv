// ------------------------------------------------------------------
// Fetcher 2D Testbench
//
// Purpose: Validate fetcher_2d.sv correctness
// Method: Load hex files, fetch via AXI, drain FIFO, compare
//
// Date: 2026-01-21
// ------------------------------------------------------------------

`timescale 1ns/1ps

`include "nap_interfaces.svh"

module tb_fetcher;

    // ====================================================================
    // Parameters
    // ====================================================================
    localparam DATA_WIDTH = 256;
    localparam AXI_ADDR_WIDTH = 42;
    localparam [8:0] GDDR6_CTRL_ID = 9'd2;
    localparam LINES_PER_BLOCK = 528;
    localparam FIFO_DEPTH = 1024;

    // ====================================================================
    // Clock and Reset
    // ====================================================================
    logic clk = 1'b0;
    logic reset_n;

    localparam CLK_PERIOD = 2.5;  // 400MHz
    always #(CLK_PERIOD/2) clk <= ~clk;

    // ====================================================================
    // Test Control
    // ====================================================================
    integer test_errors;
    integer cycle_count;

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
    // GDDR6 Memory Model (Realistic - 32 Outstanding Limit)
    // ====================================================================
    logic [31:0] mem_outstanding_count;
    logic [31:0] mem_total_ar_received;
    logic [31:0] mem_total_r_issued;

    tb_memory_model_realistic #(
        .DATA_WIDTH(256),
        .ADDR_WIDTH(42),
        .LINES_PER_BLOCK(528),
        .NUM_BLOCKS(2),
        .LATENCY_CYCLES(40),      // 100ns @ 400MHz = realistic GDDR6
        .MAX_OUTSTANDING(32),     // Achronix GDDR6 NoC limit
        .VERBOSITY(1)             // 0=quiet, 1=summary, 2=detailed
    ) u_gddr6_model (
        .i_clk(clk),
        .i_reset_n(reset_n),
        .axi_mem_if(axi_nap.responder),
        .o_outstanding_count(mem_outstanding_count),
        .o_total_ar_received(mem_total_ar_received),
        .o_total_r_issued(mem_total_r_issued)
    );

    // ====================================================================
    // Fetcher Control Signals
    // ====================================================================
    logic                         fetch_en;
    logic [25:0]                  fetch_addr;
    logic [15:0]                  fetch_len;
    logic                         fetch_done;

    // ====================================================================
    // FIFO Interface
    // ====================================================================
    logic [DATA_WIDTH-1:0]        fifo_wr_data;
    logic                         fifo_wr_en;
    logic                         fifo_afull;
    logic [DATA_WIDTH-1:0]        fifo_rd_data;
    logic                         fifo_rd_en;
    logic                         fifo_empty;
    logic                         fifo_full;
    logic [$clog2(FIFO_DEPTH):0]  fifo_count;

    // ====================================================================
    // Debug Signals
    // ====================================================================
    logic [3:0]                   fetcher_state;
    logic [15:0]                  lines_received;

    // ====================================================================
    // DUT: Fetcher 2D Module
    // ====================================================================
    fetcher_2d #(
        .DATA_WIDTH     (DATA_WIDTH),
        .AXI_ADDR_WIDTH (AXI_ADDR_WIDTH),
        .GDDR6_CTRL_ID  (GDDR6_CTRL_ID)
    ) u_fetcher (
        .i_clk              (clk),
        .i_reset_n          (reset_n),
        .i_fetch_en         (fetch_en),
        .i_fetch_addr       (fetch_addr),
        .i_fetch_len        (fetch_len),
        .o_fetch_done       (fetch_done),
        .o_fifo_wr_data     (fifo_wr_data),
        .o_fifo_wr_en       (fifo_wr_en),
        .i_fifo_afull       (fifo_afull),
        .axi_ddr_if         (axi_nap.initiator),
        .o_fetcher_state    (fetcher_state),
        .o_lines_received   (lines_received)
    );

    // ====================================================================
    // Output FIFO (depth 1024 > 528 lines)
    // ====================================================================
    flex_fifo #(
        .DATA_WIDTH(DATA_WIDTH),
        .DEPTH(FIFO_DEPTH)
    ) u_output_fifo (
        .i_clk      (clk),
        .i_reset_n  (reset_n),
        .i_wr_data  (fifo_wr_data),
        .i_wr_en    (fifo_wr_en),
        .o_full     (fifo_full),
        .o_afull    (fifo_afull),
        .o_rd_data  (fifo_rd_data),
        .i_rd_en    (fifo_rd_en),
        .o_empty    (fifo_empty),
        .o_count    (fifo_count)
    );

    // ====================================================================
    // Golden Reference Storage (loaded from hex files)
    // ====================================================================
    logic [DATA_WIDTH-1:0] golden_left  [0:LINES_PER_BLOCK-1];
    logic [DATA_WIDTH-1:0] golden_right [0:LINES_PER_BLOCK-1];

    // ====================================================================
    // Hex File Loading Task
    // ====================================================================
    task automatic load_hex_file(
        input string filename,
        ref logic [DATA_WIDTH-1:0] storage [0:LINES_PER_BLOCK-1]
    );
        integer fd, line_idx, byte_idx, scan_result;
        logic [7:0] bytes [0:31];
        logic [DATA_WIDTH-1:0] packed_line;

        fd = $fopen(filename, "r");
        if (fd == 0) begin
            $error("[HEX] Failed to open file: %s", filename);
            return;
        end

        $display("[HEX] Loading %s...", filename);
        line_idx = 0;

        while (!$feof(fd) && line_idx < LINES_PER_BLOCK) begin
            // Read 32 space-separated hex bytes per line
            scan_result = $fscanf(fd, "%h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h\n",
                bytes[0],  bytes[1],  bytes[2],  bytes[3],  bytes[4],  bytes[5],  bytes[6],  bytes[7],
                bytes[8],  bytes[9],  bytes[10], bytes[11], bytes[12], bytes[13], bytes[14], bytes[15],
                bytes[16], bytes[17], bytes[18], bytes[19], bytes[20], bytes[21], bytes[22], bytes[23],
                bytes[24], bytes[25], bytes[26], bytes[27], bytes[28], bytes[29], bytes[30], bytes[31]);

            if (scan_result == 32) begin
                // Pack bytes into 256-bit line (bytes[0] is LSB)
                packed_line = '0;
                for (byte_idx = 0; byte_idx < 32; byte_idx++) begin
                    packed_line[byte_idx*8 +: 8] = bytes[byte_idx];
                end
                storage[line_idx] = packed_line;
                line_idx++;
            end
        end

        $fclose(fd);
        $display("[HEX] Loaded %0d lines from %s", line_idx, filename);
    endtask

    // Note: Memory model auto-loads hex files from ../../hex/left.hex and ../../hex/right.hex
    // Block 0: left.hex  (lines 0-527)
    // Block 1: right.hex (lines 528-1055)

    // ====================================================================
    // Run Fetch Task
    // ====================================================================
    task automatic run_fetch(
        input logic [25:0] start_addr,
        input logic [15:0] num_lines,
        input string       test_name
    );
        integer start_cycle, duration;

        $display("\n========================================");
        $display("[TEST] %s", test_name);
        $display("[TEST] Address: 0x%07x (line %0d)", start_addr, start_addr);
        $display("[TEST] Lines: %0d", num_lines);
        $display("========================================");

        start_cycle = cycle_count;

        // Issue fetch command
        fetch_addr = start_addr;
        fetch_len = num_lines;
        fetch_en = 1'b1;
        @(posedge clk);
        fetch_en = 1'b0;

        // Wait for completion
        wait(fetch_done == 1'b1);
        @(posedge clk);

        duration = cycle_count - start_cycle;
        $display("[TEST] Complete in %0d cycles (%.2f lines/cycle)",
                 duration, real'(num_lines)/real'(duration));
        $display("[TEST] FIFO count: %0d", fifo_count);

        repeat(10) @(posedge clk);
    endtask

    // ====================================================================
    // Drain FIFO and Verify Task
    // ====================================================================
    task automatic drain_and_verify(
        ref logic [DATA_WIDTH-1:0] golden [0:LINES_PER_BLOCK-1],
        input integer expected_lines,
        input string matrix_name
    );
        integer idx, errors;
        logic [DATA_WIDTH-1:0] actual;

        errors = 0;
        idx = 0;

        $display("\n[VERIFY] Draining FIFO and checking %s data...", matrix_name);

        while (!fifo_empty && idx < expected_lines) begin
            // Request read
            fifo_rd_en = 1'b1;
            @(posedge clk);
            fifo_rd_en = 1'b0;
            @(posedge clk);  // 1-cycle read latency

            actual = fifo_rd_data;

            if (actual !== golden[idx]) begin
                if (errors < 10) begin
                    $error("[VERIFY] %s line %0d mismatch:", matrix_name, idx);
                    $error("  Got:      0x%064x", actual);
                    $error("  Expected: 0x%064x", golden[idx]);
                end
                errors++;
            end
            idx++;
        end

        if (idx != expected_lines) begin
            $error("[VERIFY] %s: Only %0d lines drained (expected %0d)", matrix_name, idx, expected_lines);
            errors++;
        end

        if (errors == 0) begin
            $display("[VERIFY] %s: PASS (%0d lines verified)", matrix_name, idx);
        end else begin
            $display("[VERIFY] %s: FAIL (%0d errors)", matrix_name, errors);
            test_errors += errors;
        end
    endtask

    // ====================================================================
    // Main Test Sequence
    // ====================================================================
    initial begin
        // Initialize
        reset_n = 1'b0;
        test_errors = 0;
        cycle_count = 0;
        fetch_en = 1'b0;
        fetch_addr = '0;
        fetch_len = '0;
        fifo_rd_en = 1'b0;

        $display("\n===============================================");
        $display("FETCHER_2D TESTBENCH - Generic Block Reader");
        $display("===============================================\n");

        // Load hex files into golden storage (absolute paths for simulation)
        load_hex_file("/home/dev/Dev/elastix_gemm/hex/left.hex", golden_left);
        load_hex_file("/home/dev/Dev/elastix_gemm/hex/right.hex", golden_right);

        // Reset sequence
        repeat(10) @(posedge clk);
        reset_n = 1'b1;
        repeat(10) @(posedge clk);

        // Memory model auto-loads hex files, no manual loading needed

        // =================================================================
        // Test 1: Fetch block 0 (left data)
        // =================================================================
        $display("\n=== TEST 1: FETCH BLOCK 0 ===");
        run_fetch(26'd0, 16'd528, "FETCH BLOCK 0");
        drain_and_verify(golden_left, 528, "BLOCK_0");

        // =================================================================
        // Test 2: Fetch block 1 (right data)
        // =================================================================
        $display("\n=== TEST 2: FETCH BLOCK 1 ===");
        run_fetch(26'd528, 16'd528, "FETCH BLOCK 1");
        drain_and_verify(golden_right, 528, "BLOCK_1");

        // =================================================================
        // Summary
        // =================================================================
        $display("\n===============================================");
        $display("TEST SUMMARY");
        $display("===============================================");
        $display("Total AR received: %0d", mem_total_ar_received);
        $display("Total R issued:    %0d", mem_total_r_issued);
        $display("===============================================");

        if (test_errors == 0) begin
            $display("\n*** ALL TESTS PASSED ***\n");
        end else begin
            $display("\n*** TESTS FAILED (%0d errors) ***\n", test_errors);
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
    // Timeout (500us = 200000 cycles @ 400MHz)
    // ====================================================================
    initial begin
        #500000ns;
        $error("[TB] Timeout!");
        $finish;
    end

endmodule
