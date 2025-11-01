// =============================================================================
// tb_result_packing.sv - Testbench for Result Packing Optimization
// =============================================================================
// Purpose: Validates the packed FP16 result storage with circular FIFO
//
// Tests:
//   1. Packing 16 FP16 values per 256-bit BRAM line
//   2. Write_top counter accumulation across multiple blocks
//   3. Reset functionality (write_top → 0) and continuation
//   4. Backpressure signal at 7/8 threshold (7168 results)
//   5. Circular wrap-around at 8192
// =============================================================================

`timescale 1ps/1ps

module tb_result_packing();

    // =========================================================================
    // Parameters
    // =========================================================================
    localparam CLK_PERIOD = 10000;  // 10ns = 100MHz

    // =========================================================================
    // Signals
    // =========================================================================
    logic        clk;
    logic        reset_n;

    // Result FIFO interface (input side)
    logic [15:0] fifo_rdata;
    logic        fifo_ren;
    logic        fifo_empty;

    // BRAM interface (output side)
    logic [8:0]  bram_wr_addr;
    logic [255:0] bram_wr_data;
    logic        bram_wr_en;

    // First 4 results
    logic [15:0] result_0, result_1, result_2, result_3;

    // Circular buffer interface (UPDATED for circular buffer optimization)
    logic [12:0] rd_ptr;          // Read pointer (host-controlled)
    logic [12:0] wr_ptr;          // Write pointer (hardware)
    logic [13:0] used_entries;    // Used entries (0-8192)
    logic        empty;           // Empty flag
    logic        write_top_reset; // Reset signal
    logic        almost_full;     // Backpressure signal

    // Test control
    logic [15:0] test_fifo [0:8191];  // Test data queue
    logic [12:0] fifo_rd_ptr;
    int          fifo_wr_ptr;
    int          fifo_count;

    // BRAM model (for verification)
    logic [255:0] bram_model [0:511];
    int           results_written;
    logic [9:0]   bram_lines_written;

    // =========================================================================
    // Clock Generation
    // =========================================================================
    initial begin
        clk = 1'b0;
        forever #(CLK_PERIOD/2) clk = ~clk;
    end

    // =========================================================================
    // DUT Instantiation
    // =========================================================================
    result_fifo_to_simple_bram u_dut (
        .i_clk              (clk),
        .i_reset_n          (reset_n),

        // Result FIFO interface
        .i_fifo_rdata       (fifo_rdata),
        .o_fifo_ren         (fifo_ren),
        .i_fifo_empty       (fifo_empty),

        // BRAM interface
        .o_bram_wr_addr     (bram_wr_addr),
        .o_bram_wr_data     (bram_wr_data),
        .o_bram_wr_en       (bram_wr_en),

        // First 4 results
        .o_result_0         (result_0),
        .o_result_1         (result_1),
        .o_result_2         (result_2),
        .o_result_3         (result_3),

        // Circular buffer interface (UPDATED for circular buffer optimization)
        .i_rd_ptr           (rd_ptr),
        .o_wr_ptr           (wr_ptr),
        .o_used_entries     (used_entries),
        .o_empty            (empty),
        .i_write_top_reset  (write_top_reset),
        .o_almost_full      (almost_full)
    );

    // =========================================================================
    // FIFO Model (provides data to DUT) - 2-cycle BRAM latency
    // =========================================================================
    logic [15:0] fifo_rdata_d1;   // First pipeline stage
    logic [15:0] fifo_rdata_d2;   // Second pipeline stage

    // Update read pointer
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            fifo_rd_ptr <= 0;
        end else if (fifo_ren && !fifo_empty) begin
            fifo_rd_ptr <= fifo_rd_ptr + 1;
        end
    end

    // Two-stage pipeline for 2-cycle read latency
    // Stage 1: Read from array based on current pointer
    logic [3:0] debug_fifo_reads;  // Counter for debug output
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            fifo_rdata_d1 <= 16'hxxxx;
            fifo_rdata_d2 <= 16'hxxxx;
            debug_fifo_reads <= 0;
        end else begin
            // When read enable, capture data from current pointer
            if (fifo_ren && !fifo_empty) begin
                fifo_rdata_d1 <= test_fifo[fifo_rd_ptr];
                // Debug: Print first few reads
                if (debug_fifo_reads < 5) begin
                    $display("[TB] FIFO Read: ptr=%0d, data=0x%04x", fifo_rd_ptr, test_fifo[fifo_rd_ptr]);
                    debug_fifo_reads <= debug_fifo_reads + 1;
                end
            end else begin
                fifo_rdata_d1 <= 16'hxxxx;
            end
            // Stage 2: Pipeline the data
            fifo_rdata_d2 <= fifo_rdata_d1;
        end
    end

    // Provide data with 2-cycle latency
    assign fifo_rdata = fifo_rdata_d2;
    assign fifo_empty = (fifo_count == 0);

    // Debug signals (disabled for cleaner output)

    // =========================================================================
    // BRAM Model (captures DUT writes)
    // =========================================================================
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            bram_lines_written <= 10'b0;
            // Initialize BRAM to known value
            for (int i = 0; i < 512; i++) begin
                bram_model[i] <= 256'h0;
            end
        end else if (bram_wr_en) begin
            bram_model[bram_wr_addr] <= bram_wr_data;
            bram_lines_written <= bram_lines_written + 1'b1;
            // Debug: Print BRAM writes for first few transactions
            if (bram_lines_written < 5) begin
                $display("[TB] BRAM Write: addr=%0d, data[15:0]=0x%04x, data[31:16]=0x%04x",
                         bram_wr_addr, bram_wr_data[15:0], bram_wr_data[31:16]);
            end
        end
    end

    // =========================================================================
    // Test Tasks
    // =========================================================================

    // Load test data into FIFO
    task load_test_data(input int count);
        for (int i = 0; i < count; i++) begin
            test_fifo[fifo_wr_ptr] = 16'h1000 + i;  // Simple pattern: 0x1000, 0x1001, ...
            fifo_wr_ptr = (fifo_wr_ptr + 1) % 8192;
            fifo_count++;
        end
        $display("[TB] Loaded %0d test values into FIFO (wr_ptr now %0d, count=%0d)",
                 count, fifo_wr_ptr, fifo_count);
        // Debug: Check first few values
        if (count >= 4) begin
            $display("[TB] First 4 values in test_fifo: 0x%04x 0x%04x 0x%04x 0x%04x",
                     test_fifo[0], test_fifo[1], test_fifo[2], test_fifo[3]);
        end
    endtask

    // Wait for DUT to process all FIFO data
    task wait_for_processing();
        int timeout = 10000;
        while (fifo_count > 0 && timeout > 0) begin
            @(posedge clk);
            if (fifo_ren && !fifo_empty) begin
                fifo_count--;
                results_written++;
            end
            timeout--;
        end
        if (timeout == 0) begin
            $display("[TB] ERROR: Timeout waiting for processing");
        end else begin
            $display("[TB] Processing complete: %0d results written", results_written);
        end
    endtask

    // Verify BRAM packing (16 FP16s per line)
    task verify_packing(input int start_result, input int count);
        int errors = 0;
        int line_idx, pos_idx;
        logic [15:0] expected, actual;

        $display("[TB] Verifying packing for results %0d to %0d", start_result, start_result + count - 1);

        for (int i = 0; i < count; i++) begin
            line_idx = (start_result + i) / 16;
            pos_idx = (start_result + i) % 16;

            expected = 16'h1000 + start_result + i;
            actual = bram_model[line_idx][pos_idx*16 +: 16];

            if (actual !== expected) begin
                $display("[TB] ERROR: Result[%0d] at line %0d pos %0d: expected=0x%04x actual=0x%04x",
                        start_result + i, line_idx, pos_idx, expected, actual);
                errors++;
            end
        end

        if (errors == 0) begin
            $display("[TB] PASS: All %0d results correctly packed", count);
        end else begin
            $display("[TB] FAIL: %0d packing errors found", errors);
        end
    endtask

    // Reset write_top counter (now wr_ptr)
    task reset_write_top();
        $display("[TB] Resetting wr_ptr counter (was %0d)", wr_ptr);
        write_top_reset = 1'b1;
        @(posedge clk);
        write_top_reset = 1'b0;
        @(posedge clk);
        $display("[TB] wr_ptr after reset: %0d", wr_ptr);
    endtask

    // Update read pointer (simulating host DMA consumption)
    task update_rd_ptr(input int new_rd_ptr);
        $display("[TB] Updating rd_ptr from %0d to %0d", rd_ptr, new_rd_ptr);
        rd_ptr = new_rd_ptr[12:0];
        @(posedge clk);
        $display("[TB] used_entries: %0d, empty: %b", used_entries, empty);
    endtask

    // =========================================================================
    // Main Test Sequence
    // =========================================================================
    initial begin
        $display("\n[TB] =====================================");
        $display("[TB] Result Packing Testbench Started");
        $display("[TB] =====================================\n");

        // Initialize
        reset_n = 1'b0;
        write_top_reset = 1'b0;
        rd_ptr = 13'b0;  // Host read pointer starts at 0
        fifo_wr_ptr = 0;
        fifo_count = 0;
        results_written = 0;

        repeat(5) @(posedge clk);
        reset_n = 1'b1;
        repeat(10) @(posedge clk);  // Give DUT more time to initialize

        $display("[TB] Initial state: wr_ptr=%0d, rd_ptr=%0d, used_entries=%0d, empty=%b",
                 wr_ptr, rd_ptr, used_entries, empty);

        // =====================================================================
        // Test 1: Basic packing (65 results = 4 full lines + 1 partial)
        // =====================================================================
        $display("\n[TB] Test 1: Basic packing (65 results)");
        $display("[TB] Expected: 4 full lines written, 1 partial in buffer");

        load_test_data(65);
        wait_for_processing();

        $display("[TB] wr_ptr: %0d (expected: 65 - counts all processed)", wr_ptr);
        $display("[TB] rd_ptr: %0d (expected: 0 - not yet consumed)", rd_ptr);
        $display("[TB] used_entries: %0d (expected: 65)", used_entries);
        $display("[TB] BRAM lines written: %0d (expected: 4)", bram_lines_written);

        // Only verify the 64 results that were written (4 complete lines)
        verify_packing(0, 64);

        // Check first 4 captured results
        $display("[TB] First 4 results: 0x%04x 0x%04x 0x%04x 0x%04x (expected: 0x1000-0x1003)",
                 result_0, result_1, result_2, result_3);

        repeat(10) @(posedge clk);

        // =====================================================================
        // Test 2: Circular buffer with rd_ptr update (simulating host consumption)
        // =====================================================================
        $display("\n[TB] Test 2: Host consumes 32 results (updating rd_ptr)");

        update_rd_ptr(32);  // Host has read and consumed first 32 results

        $display("[TB] After consumption: wr_ptr=%0d, rd_ptr=%0d, used_entries=%0d",
                 wr_ptr, rd_ptr, used_entries);
        $display("[TB] Expected: used_entries=33 (65-32)");

        repeat(10) @(posedge clk);

        // =====================================================================
        // Test 3: Accumulation (add 100 more results)
        // =====================================================================
        $display("\n[TB] Test 3: Accumulation (100 more results)");
        $display("[TB] Previous partial (1) + new (100) = 101 results");
        $display("[TB] Expected: 6 more full lines written (96 results), 5 in buffer");

        load_test_data(100);
        wait_for_processing();

        // 65 + 100 = 165 total processed
        $display("[TB] wr_ptr: %0d (expected: 165)", wr_ptr);
        $display("[TB] rd_ptr: %0d (expected: 32 - unchanged)", rd_ptr);
        $display("[TB] used_entries: %0d (expected: 133 = 165-32)", used_entries);
        $display("[TB] Total BRAM lines: %0d (expected: 10)", bram_lines_written);

        // Verify results 64-159 (lines 4-9, 96 results)
        verify_packing(64, 96);

        repeat(10) @(posedge clk);

        // =====================================================================
        // Test 4: Reset and continue
        // =====================================================================
        $display("\n[TB] Test 4: Reset wr_ptr and continue");
        $display("[TB] Note: Reset will flush the 5 results in buffer first");

        reset_write_top();

        // Reset rd_ptr as well (simulating complete buffer drain)
        update_rd_ptr(0);

        // Add 32 more results after reset
        load_test_data(32);
        wait_for_processing();

        // 32 results processed after reset
        $display("[TB] wr_ptr after new data: %0d (expected: 32)", wr_ptr);
        $display("[TB] used_entries: %0d (expected: 32)", used_entries);

        // Results 165-196 should be at positions 0-31 after reset
        // (The 5 in buffer were results 160-164 and got flushed at line 10)
        verify_packing(0, 32);

        repeat(10) @(posedge clk);

        // =====================================================================
        // Test 5: Approach threshold (load many results)
        // =====================================================================
        $display("\n[TB] Test 5: Approach backpressure threshold (updated to 7936)");

        // Reset first
        reset_write_top();
        update_rd_ptr(0);
        results_written = 0;

        // Load 7900 results (approaching 7936 threshold)
        $display("[TB] Loading 7900 results...");
        load_test_data(7900);
        wait_for_processing();

        $display("[TB] wr_ptr: %0d", wr_ptr);
        $display("[TB] used_entries: %0d", used_entries);
        $display("[TB] Almost_full: %b (should be 0)", almost_full);

        // Add 50 more to exceed threshold
        $display("[TB] Adding 50 more results to exceed threshold...");
        load_test_data(50);
        wait_for_processing();

        $display("[TB] wr_ptr: %0d (should be >= 7936)", wr_ptr);
        $display("[TB] used_entries: %0d (should be >= 7936)", used_entries);
        $display("[TB] Almost_full: %b (should be 1)", almost_full);

        if (almost_full && used_entries >= 7936) begin
            $display("[TB] PASS: Backpressure activated correctly at new threshold");
        end else begin
            $display("[TB] FAIL: Backpressure not working properly (used=%0d, afull=%b)",
                     used_entries, almost_full);
        end

        repeat(10) @(posedge clk);

        // =====================================================================
        // Test 6: Circular wrap-around
        // =====================================================================
        $display("\n[TB] Test 6: Circular wrap-around at 8192");

        // Reset and load exactly 8191 results
        reset_write_top();
        update_rd_ptr(0);
        fifo_wr_ptr = 0;
        fifo_count = 0;

        load_test_data(8191);
        wait_for_processing();

        $display("[TB] wr_ptr at 8191: %0d", wr_ptr);
        $display("[TB] used_entries: %0d", used_entries);

        // Add one more to trigger wrap
        load_test_data(1);
        wait_for_processing();

        $display("[TB] wr_ptr after wrap: %0d (should be 0)", wr_ptr);
        $display("[TB] used_entries: %0d (should be 8192)", used_entries);

        if (wr_ptr == 0 && used_entries == 8192) begin
            $display("[TB] PASS: Circular wrap-around works correctly");
        end else begin
            $display("[TB] FAIL: Wrap-around failed (wr_ptr=%0d, used=%0d)", wr_ptr, used_entries);
        end

        // =====================================================================
        // Summary
        // =====================================================================
        $display("\n[TB] =====================================");
        $display("[TB] Test Complete");
        $display("[TB] Total results processed: %0d", results_written);
        $display("[TB] BRAM efficiency: %.1f%% (optimal: 100%%)",
                 (results_written * 100.0) / (bram_lines_written * 16));
        $display("[TB] =====================================\n");

        $finish;
    end

    // =========================================================================
    // Timeout Watchdog
    // =========================================================================
    initial begin
        #10ms;
        $display("[TB] ERROR: Simulation timeout!");
        $finish;
    end

endmodule