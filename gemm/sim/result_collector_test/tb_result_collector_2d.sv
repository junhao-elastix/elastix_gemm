// ------------------------------------------------------------------
// Testbench for Result Collector 2D + Result to DMA Chain
//
// Purpose: Validate the complete result data path:
//   CE FIFOs -> result_collector_2d -> result_to_dma -> Result BRAM
//
// Features:
//   - Mock CE FIFO interface with random FP16 data
//   - result_collector_2d auto-drain behavior
//   - result_to_dma always-drain circular buffer
//   - Mock result BRAM captures output via BRAM write interface
//   - Verifies results using wr_ptr and rd_ptr
//
// Test Cases:
//   1. B=1, C=1   - Minimal: 1 batch, 1 column
//   2. B=2, C=4   - 2 batches, 4 columns
//   3. B=4, C=16  - 4 batches, full 16 columns
//   4. B=8, C=8   - 8 batches, 8 columns
//   5. B=1, C=17  - Partial last line (17 results)
//
// Author: Testbench for result_collector_2d + result_to_dma
// Date: Jan 29, 2026 (Integrated with result_to_dma)
// ------------------------------------------------------------------

`timescale 1ps / 1ps

module tb_result_collector_2d;

    // ===================================================================
    // Parameters
    // ===================================================================
    localparam int NUM_ROWS = 16;
    localparam int NUM_COLS = 16;
    localparam int OUTPUT_FIFO_DEPTH = 1024;
    localparam int MOCK_FIFO_DEPTH = 512;  // Large enough for C=256 tests (256 entries per column)

    // Result BRAM parameters (matching result_to_dma)
    localparam int RESULT_DATA_WIDTH = 256;
    localparam int RESULT_ADDR_WIDTH = 9;   // 512 lines
    localparam int RESULT_BUFFER_DEPTH = 512;

    // Clock period
    localparam int CLK_PERIOD = 2000; // 2ns = 500MHz

    // ===================================================================
    // Signals
    // ===================================================================
    logic clk;
    logic rstn;

    // Results Ready Signal (simulates CE completion)
    logic ce_results_ready;

    // Command Interface (kept for compatibility, not used for flow control)
    logic [7:0]  mc_cmd_op;
    logic [7:0]  mc_cmd_id;
    logic [31:0] cmd_payload_word1;
    logic [31:0] cmd_payload_word2;
    logic [31:0] cmd_payload_word3;
    logic        rc_ack_readout;

    // CE FIFO Interface (unpacked arrays to match result_collector_2d ports)
    logic [15:0] ce_result_data  [NUM_ROWS-1:0][NUM_COLS-1:0];
    logic        ce_result_empty [NUM_ROWS-1:0][NUM_COLS-1:0];
    logic        ce_result_rd_en [NUM_ROWS-1:0][NUM_COLS-1:0];

    // Result Collector -> Result to DMA Interface
    logic        rc_output_valid;
    logic        rc_output_last;
    logic [15:0] rc_output_keep;
    logic [255:0] rc_output_data;
    logic        r2d_ready;  // From result_to_dma

    // Result to DMA -> BRAM Interface
    logic                           bram_wr_en;
    logic [RESULT_ADDR_WIDTH-1:0]   bram_wr_addr;
    logic [RESULT_DATA_WIDTH-1:0]   bram_wr_data;
    logic [31:0]                    bram_wr_strobe;

    // Circular Buffer Control/Status
    logic [RESULT_ADDR_WIDTH-1:0]   rd_ptr;       // Simulated host read pointer
    logic [RESULT_ADDR_WIDTH-1:0]   wr_ptr;       // From result_to_dma
    logic [RESULT_ADDR_WIDTH:0]     used_entries; // From result_to_dma
    logic                           almost_full;
    logic                           buffer_empty;

    // Status
    logic [3:0]  rc_state;
    logic        rc_busy;
    logic [7:0]  rc_cmd_id;
    logic        output_fifo_afull;

    // ===================================================================
    // Mock CE FIFOs - Using flex_fifo instances for realistic behavior
    // ===================================================================
    logic [15:0] fifo_wr_data [NUM_ROWS-1:0][NUM_COLS-1:0];
    logic        fifo_wr_en   [NUM_ROWS-1:0][NUM_COLS-1:0];
    logic        fifo_full    [NUM_ROWS-1:0][NUM_COLS-1:0];

    generate
        for (genvar r = 0; r < NUM_ROWS; r++) begin : gen_row_fifos
            for (genvar c = 0; c < NUM_COLS; c++) begin : gen_col_fifos
                flex_fifo #(
                    .DATA_WIDTH(16),
                    .DEPTH(MOCK_FIFO_DEPTH)
                ) u_mock_fifo (
                    .i_clk      (clk),
                    .i_reset_n  (rstn),
                    .i_wr_data  (fifo_wr_data[r][c]),
                    .i_wr_en    (fifo_wr_en[r][c]),
                    .o_full     (fifo_full[r][c]),
                    .o_afull    (),
                    .o_rd_data  (ce_result_data[r][c]),
                    .i_rd_en    (ce_result_rd_en[r][c]),
                    .o_empty    (ce_result_empty[r][c]),
                    .o_count    ()
                );
            end
        end
    endgenerate

    // ===================================================================
    // Mock Result BRAM - Captures output from result_to_dma
    // ===================================================================
    logic [255:0] result_bram [0:RESULT_BUFFER_DEPTH-1];
    logic [31:0]  result_strobe [0:RESULT_BUFFER_DEPTH-1];  // For verification
    int           total_bram_writes;

    // BRAM write process
    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            total_bram_writes <= 0;
        end else if (bram_wr_en) begin
            // Write with byte strobes (simulate real BRAM behavior)
            for (int i = 0; i < 32; i++) begin
                if (bram_wr_strobe[i]) begin
                    result_bram[bram_wr_addr][i*8 +: 8] <= bram_wr_data[i*8 +: 8];
                end
            end
            result_strobe[bram_wr_addr] <= bram_wr_strobe;
            total_bram_writes <= total_bram_writes + 1;
        end
    end

    // ===================================================================
    // Golden Reference Data
    // ===================================================================
    // golden_results[batch][col] = sum of all rows for that batch/col
    logic [15:0] golden_results [0:255][0:511];  // Up to 256 batches, 512 cols
    int golden_result_count;

    // ===================================================================
    // DUT 1: Result Collector 2D
    // ===================================================================
    result_collector_2d #(
        .NUM_ROWS           (NUM_ROWS),
        .NUM_COLS           (NUM_COLS),
        .ADDER_SEG_LEN      (2),
        .OUTPUT_FIFO_DEPTH  (OUTPUT_FIFO_DEPTH)
    ) u_result_collector (
        .i_clk              (clk),
        .i_reset_n          (rstn),

        // Results Ready Signal (from CEs)
        .i_ce_results_ready (ce_results_ready),

        // Command Interface (kept for compatibility)
        .i_mc_cmd_op        (mc_cmd_op),
        .i_mc_cmd_id        (mc_cmd_id),
        .i_cmd_payload_word1(cmd_payload_word1),
        .i_cmd_payload_word2(cmd_payload_word2),
        .i_cmd_payload_word3(cmd_payload_word3),
        .o_rc_ack_readout   (rc_ack_readout),

        // CE FIFO Interface
        .i_ce_result_data   (ce_result_data),
        .i_ce_result_empty  (ce_result_empty),
        .o_ce_result_rd_en  (ce_result_rd_en),

        // Output Interface -> goes to result_to_dma
        .i_output_ready     (r2d_ready),
        .o_output_valid     (rc_output_valid),
        .o_output_last      (rc_output_last),
        .o_output_keep      (rc_output_keep),
        .o_output_data      (rc_output_data),

        // Status
        .o_rc_state         (rc_state),
        .o_rc_busy          (rc_busy),
        .o_rc_cmd_id        (rc_cmd_id),
        .o_output_fifo_afull(output_fifo_afull)
    );

    // ===================================================================
    // DUT 2: Result to DMA (Always-Drain Circular Buffer)
    // ===================================================================
    result_to_dma #(
        .DATA_WIDTH         (RESULT_DATA_WIDTH),
        .ADDR_WIDTH         (RESULT_ADDR_WIDTH),
        .ALMOST_FULL_MARGIN (16)
    ) u_result_to_dma (
        .i_clk              (clk),
        .i_reset_n          (rstn),

        // Ready-Valid Input (from result_collector_2d)
        .i_data             (rc_output_data),
        .i_keep             (rc_output_keep),
        .i_last             (rc_output_last),
        .i_valid            (rc_output_valid),
        .o_ready            (r2d_ready),

        // Circular Buffer Control (from host register)
        .i_rd_ptr           (rd_ptr),

        // Circular Buffer Status (to host registers)
        .o_wr_ptr           (wr_ptr),
        .o_used_entries     (used_entries),
        .o_almost_full      (almost_full),
        .o_empty            (buffer_empty),

        // BRAM Write Output (to mock BRAM)
        .o_bram_wr_en       (bram_wr_en),
        .o_bram_wr_addr     (bram_wr_addr),
        .o_bram_wr_data     (bram_wr_data),
        .o_bram_wr_strobe   (bram_wr_strobe)
    );

    // ===================================================================
    // Clock Generation
    // ===================================================================
    initial begin
        clk = 0;
        forever #(CLK_PERIOD/2) clk = ~clk;
    end

    // ===================================================================
    // Test Variables
    // ===================================================================
    int test_num;
    int errors;
    int total_errors;

    // ===================================================================
    // FP16 Conversion Functions
    // ===================================================================
    // Convert real to FP16 (approximate)
    function automatic logic [15:0] real_to_fp16(input real val);
        logic sign;
        int exp;
        real mant;
        logic [4:0] biased_exp;
        logic [9:0] mant_bits;
        real abs_val;

        if (val == 0.0) return 16'h0000;

        sign = (val < 0.0);
        abs_val = sign ? -val : val;

        // Find exponent
        exp = 0;
        mant = abs_val;

        if (mant >= 2.0) begin
            while (mant >= 2.0 && exp < 15) begin
                mant = mant / 2.0;
                exp = exp + 1;
            end
        end else if (mant < 1.0 && mant > 0.0) begin
            while (mant < 1.0 && exp > -14) begin
                mant = mant * 2.0;
                exp = exp - 1;
            end
        end

        // Bias exponent (FP16 bias = 15)
        biased_exp = exp + 15;

        // Extract mantissa (remove implicit 1)
        mant_bits = (mant - 1.0) * 1024.0;

        return {sign, biased_exp, mant_bits};
    endfunction

    // Convert FP16 to real (approximate)
    function automatic real fp16_to_real(input logic [15:0] fp16);
        logic sign;
        logic [4:0] exp;
        logic [9:0] mant;
        real result;
        int unbiased_exp;

        sign = fp16[15];
        exp = fp16[14:10];
        mant = fp16[9:0];

        if (exp == 0 && mant == 0) return 0.0;
        if (exp == 5'h1F) return 0.0;  // Inf/NaN -> 0 for simplicity

        unbiased_exp = exp - 15;
        result = (1.0 + real'(mant) / 1024.0) * (2.0 ** unbiased_exp);

        return sign ? -result : result;
    endfunction

    // FP16 addition using real conversion (for golden model)
    function automatic logic [15:0] fp16_add(input logic [15:0] a, input logic [15:0] b);
        real a_real, b_real, sum_real;
        a_real = fp16_to_real(a);
        b_real = fp16_to_real(b);
        sum_real = a_real + b_real;
        return real_to_fp16(sum_real);
    endfunction

    // ===================================================================
    // LFSR for Random FP16 Generation
    // ===================================================================
    logic [31:0] lfsr_state;

    function automatic logic [31:0] lfsr_next(input logic [31:0] state);
        logic feedback;
        feedback = state[31] ^ state[21] ^ state[1] ^ state[0];
        return {state[30:0], feedback};
    endfunction

    function automatic logic [15:0] get_random_fp16();
        logic [15:0] result;
        // Generate small positive FP16 values (exponent 10-17, small mantissa)
        // This keeps values in a reasonable range for summation
        logic [4:0] exp;
        logic [9:0] mant;

        lfsr_state = lfsr_next(lfsr_state);
        exp = 5'd10 + lfsr_state[4:2];  // Exponent 10-17 (values ~0.001 to ~0.1)
        mant = lfsr_state[13:4];

        // Always positive
        result = {1'b0, exp, mant};
        return result;
    endfunction

    // ===================================================================
    // Task: Reset DUT
    // ===================================================================
    task automatic reset_dut();
        rstn = 1'b0;
        ce_results_ready = 1'b0;
        mc_cmd_op = 8'h00;
        mc_cmd_id = 8'h00;
        cmd_payload_word1 = 32'h0;
        cmd_payload_word2 = 32'h0;
        cmd_payload_word3 = 32'h0;
        rd_ptr = {RESULT_ADDR_WIDTH{1'b0}};  // Host read pointer starts at 0

        // Clear FIFO write signals
        for (int r = 0; r < NUM_ROWS; r++) begin
            for (int c = 0; c < NUM_COLS; c++) begin
                fifo_wr_data[r][c] = 16'h0;
                fifo_wr_en[r][c] = 1'b0;
            end
        end

        // Clear mock BRAM
        for (int i = 0; i < RESULT_BUFFER_DEPTH; i++) begin
            result_bram[i] = 256'h0;
            result_strobe[i] = 32'h0;
        end

        // Clear golden
        golden_result_count = 0;
        for (int b = 0; b < 256; b++) begin
            for (int c = 0; c < 512; c++) begin
                golden_results[b][c] = 16'h0;
            end
        end

        repeat (10) @(posedge clk);
        rstn = 1'b1;
        repeat (5) @(posedge clk);
    endtask

    // ===================================================================
    // Task: Populate Mock FIFOs
    // ===================================================================
    task automatic populate_mock_fifos(input int B, input int C, input logic [31:0] seed);
        logic [15:0] fp16_val;
        logic [15:0] row_sum;
        int col_idx;

        lfsr_state = seed;
        golden_result_count = 0;

        $display("[TB] Populating mock FIFOs: B=%0d, C=%0d, seed=0x%08x", B, C, seed);

        // For each batch
        for (int b = 0; b < B; b++) begin
            // For each column (up to C, but only use NUM_COLS columns per pass)
            for (int c_iter = 0; c_iter < C; c_iter++) begin
                col_idx = c_iter % NUM_COLS;  // Wrap column index

                // Reset sum for this batch/col
                row_sum = 16'h0;

                // For each row, generate random FP16 and write to FIFO
                for (int r = 0; r < NUM_ROWS; r++) begin
                    fp16_val = get_random_fp16();

                    // Write to FIFO via wr_data/wr_en interface
                    fifo_wr_data[r][col_idx] = fp16_val;
                    fifo_wr_en[r][col_idx] = 1'b1;
                    @(posedge clk);
                    // Check if write was accepted
                    if (fifo_full[r][col_idx]) begin
                        $display("[TB] WARNING: FIFO[%0d][%0d] was full during write!", r, col_idx);
                    end
                    fifo_wr_en[r][col_idx] = 1'b0;
                    @(posedge clk);  // Give extra cycle for FIFO to register the write

                    // Accumulate for golden reference (FP16 addition)
                    row_sum = fp16_add(row_sum, fp16_val);
                end

                // Store golden result
                golden_results[b][c_iter] = row_sum;
                golden_result_count++;

                // Debug: trace golden computation for c=81
                if (C == 256 && c_iter == 81) begin
                    $display("[TB] GOLDEN c=81: row_sum=0x%04x (%.4f)", row_sum, fp16_to_real(row_sum));
                end
            end
        end

        // Clear all write enables
        for (int r = 0; r < NUM_ROWS; r++) begin
            for (int c = 0; c < NUM_COLS; c++) begin
                fifo_wr_en[r][c] = 1'b0;
            end
        end

        $display("[TB] Generated %0d golden results", golden_result_count);

        // Debug: check if FIFOs are populated (check empty flags for all rows col 0)
        @(posedge clk);
        $display("[TB] FIFO empty check for col 0 (all rows should be 0 if B*G >= 1):");
        for (int r = 0; r < 4; r++) begin  // Just show first 4 rows
            $display("[TB]   Row %0d: empty=%b", r, ce_result_empty[r][0]);
        end
    endtask

    // ===================================================================
    // Task: Signal Results Ready
    // ===================================================================
    task automatic signal_results_ready();
        $display("[TB] Asserting ce_results_ready (signaling CE completion)");
        ce_results_ready = 1'b1;
        @(posedge clk);
        // Keep it high - the RC will latch it
        $display("[TB] ce_results_ready asserted, RC should now know results are complete");
    endtask

    // ===================================================================
    // Task: Wait for Completion (monitoring wr_ptr)
    // ===================================================================
    task automatic wait_completion(input int timeout_cycles, input int expected_lines);
        int cycle_cnt;
        logic [RESULT_ADDR_WIDTH-1:0] prev_wr_ptr;
        int idle_cycles;

        cycle_cnt = 0;
        prev_wr_ptr = wr_ptr;
        idle_cycles = 0;

        $display("[TB] Waiting for completion (timeout=%0d cycles, expected_lines=%0d)...",
                 timeout_cycles, expected_lines);
        $display("[TB] Monitoring wr_ptr and rd_ptr for circular buffer verification");

        while (cycle_cnt < timeout_cycles) begin
            @(posedge clk);
            cycle_cnt++;

            // Track wr_ptr changes
            if (wr_ptr != prev_wr_ptr) begin
                $display("[TB] @cycle %0d: wr_ptr changed %0d -> %0d, used_entries=%0d",
                         cycle_cnt, prev_wr_ptr, wr_ptr, used_entries);
                prev_wr_ptr = wr_ptr;
                idle_cycles = 0;
            end else begin
                idle_cycles++;
            end

            // Check if all expected lines have been written
            if (total_bram_writes >= expected_lines && idle_cycles > 50) begin
                $display("[TB] Received all %0d expected lines, wr_ptr=%0d, rd_ptr=%0d",
                         expected_lines, wr_ptr, rd_ptr);
                // Give a few more cycles for any final operations
                repeat (10) @(posedge clk);
                return;
            end

            // Debug: periodically show state
            if (cycle_cnt % 500 == 0) begin
                $display("[TB] @cycle %0d: state=%0d, busy=%b, wr_ptr=%0d, rd_ptr=%0d, used=%0d",
                         cycle_cnt, rc_state, rc_busy, wr_ptr, rd_ptr, used_entries);
                $display("[TB]   total_bram_writes=%0d, almost_full=%b, empty=%b",
                         total_bram_writes, almost_full, buffer_empty);
            end

            // Debug: trace first 30 cycles in detail
            if (cycle_cnt < 30) begin
                $display("[TB] @cycle %0d: rc_state=%0d, r2d_ready=%b, rc_valid=%b, bram_wr_en=%b",
                         cycle_cnt, rc_state, r2d_ready, rc_output_valid, bram_wr_en);
            end
        end

        $display("[TB] ERROR: Timeout waiting for completion after %0d cycles", timeout_cycles);
        $display("[TB]   Final state=%0d, busy=%b, wr_ptr=%0d, rd_ptr=%0d",
                 rc_state, rc_busy, wr_ptr, rd_ptr);
        $display("[TB]   total_bram_writes=%0d, expected=%0d", total_bram_writes, expected_lines);
        errors++;
    endtask

    // ===================================================================
    // Task: Verify Results via Circular Buffer
    // ===================================================================
    task automatic verify_results(input int B, input int C);
        int lines_expected;
        int total_results;
        int result_idx;
        int slot;
        logic [15:0] actual_fp16;
        logic [15:0] expected_fp16;
        real actual_real;
        real expected_real;
        real diff;
        real tolerance;
        logic [RESULT_ADDR_WIDTH-1:0] read_addr;

        total_results = B * C;
        lines_expected = (total_results + 15) / 16;  // Ceiling division

        $display("[TB] Verifying: B=%0d, C=%0d, total_results=%0d, lines_expected=%0d",
                 B, C, total_results, lines_expected);
        $display("[TB] Circular buffer status: wr_ptr=%0d, rd_ptr=%0d, used_entries=%0d, writes=%0d",
                 wr_ptr, rd_ptr, used_entries, total_bram_writes);

        // Verify total BRAM writes match expected lines
        if (total_bram_writes != lines_expected) begin
            $display("[TB] ERROR: BRAM write count mismatch. Expected %0d, got %0d",
                     lines_expected, total_bram_writes);
            errors++;
        end

        // Verify wr_ptr matches expected (assuming rd_ptr stayed at 0)
        if (wr_ptr != lines_expected % RESULT_BUFFER_DEPTH) begin
            $display("[TB] ERROR: wr_ptr mismatch. Expected %0d, got %0d",
                     lines_expected % RESULT_BUFFER_DEPTH, wr_ptr);
            errors++;
        end

        // Verify used_entries
        if (used_entries != lines_expected) begin
            $display("[TB] ERROR: used_entries mismatch. Expected %0d, got %0d",
                     lines_expected, used_entries);
            errors++;
        end

        // Verify each result by reading from circular buffer starting at rd_ptr
        result_idx = 0;
        for (int b = 0; b < B; b++) begin
            for (int c_iter = 0; c_iter < C; c_iter++) begin
                // Calculate line address in circular buffer
                read_addr = (rd_ptr + result_idx / 16) % RESULT_BUFFER_DEPTH;
                slot = result_idx % 16;

                actual_fp16 = result_bram[read_addr][slot*16 +: 16];
                expected_fp16 = golden_results[b][c_iter];

                // Check strobe was set for this slot
                if (!result_strobe[read_addr][slot*2] || !result_strobe[read_addr][slot*2+1]) begin
                    $display("[TB] ERROR: Byte strobe not set for result[%0d][%0d] at addr %0d, slot %0d",
                             b, c_iter, read_addr, slot);
                    errors++;
                end

                // Convert to real for comparison
                actual_real = fp16_to_real(actual_fp16);
                expected_real = fp16_to_real(expected_fp16);

                // Allow 25% tolerance due to FP16 precision differences between
                // sequential accumulation (golden) and tree reduction (hardware)
                // Note: FP16 addition is not associative, so different order = different results
                tolerance = (expected_real == 0.0) ? 0.001 : (expected_real < 0 ? -expected_real : expected_real) * 0.25;
                diff = actual_real - expected_real;
                if (diff < 0) diff = -diff;

                // Debug: print drains around c=81 for test 6 only (C=256)
                if (C == 256 && c_iter >= 78 && c_iter <= 84) begin
                    $display("[TB] DEBUG T6 c=%0d (col=%0d): addr=%0d, slot=%0d, expected=0x%04x(%.4f), got=0x%04x(%.4f), diff=%.4f",
                             c_iter, c_iter % 16, read_addr, slot, expected_fp16, expected_real, actual_fp16, actual_real, diff);
                end

                if (diff > tolerance) begin
                    $display("[TB] ERROR: Mismatch at b=%0d, c=%0d (addr=%0d, slot=%0d): expected 0x%04x (%.6f), got 0x%04x (%.6f)",
                             b, c_iter, read_addr, slot, expected_fp16, expected_real, actual_fp16, actual_real);
                    errors++;
                end

                result_idx++;
            end
        end

        // Simulate host advancing rd_ptr after consuming all data
        $display("[TB] Simulating host read: advancing rd_ptr from %0d to %0d",
                 rd_ptr, wr_ptr);
        rd_ptr = wr_ptr;
        @(posedge clk);
        @(posedge clk);

        // Verify buffer is now empty
        if (!buffer_empty) begin
            $display("[TB] ERROR: Buffer should be empty after advancing rd_ptr");
            errors++;
        end
        if (used_entries != 0) begin
            $display("[TB] ERROR: used_entries should be 0 after advancing rd_ptr, got %0d", used_entries);
            errors++;
        end

        $display("[TB] After host read: empty=%b, used_entries=%0d", buffer_empty, used_entries);

        if (errors == 0) begin
            $display("[TB] All %0d results verified successfully", total_results);
        end
    endtask

    // ===================================================================
    // Task: Run Single Test
    // ===================================================================
    task automatic run_test(input int test_id, input int B, input int C, input logic [31:0] seed);
        int expected_lines;

        $display("");
        $display("======================================================================");
        $display("  TEST %0d: B=%0d, C=%0d (Auto-Drain with result_to_dma)", test_id, B, C);
        $display("======================================================================");

        test_num = test_id;
        errors = 0;
        expected_lines = (B * C + 15) / 16;

        // Reset
        reset_dut();

        // Populate FIFOs (RC will start draining automatically as data appears)
        populate_mock_fifos(B, C, seed);

        // Signal that all results are computed (CE completion)
        // This allows RC to know when to flush partial buffer
        signal_results_ready();

        // Wait for completion (monitor wr_ptr updates)
        wait_completion(10000 + B * C * 100, expected_lines);

        // Deassert results_ready for next test
        ce_results_ready = 1'b0;

        // Verify results via circular buffer
        verify_results(B, C);

        // Report
        if (errors == 0) begin
            $display("[TB] TEST %0d: PASS", test_id);
        end else begin
            $display("[TB] TEST %0d: FAIL (%0d errors)", test_id, errors);
            total_errors += errors;
        end
    endtask

    // ===================================================================
    // Main Test Sequence
    // ===================================================================
    initial begin
        $display("");
        $display("======================================================================");
        $display("  Result Collector 2D + Result to DMA Testbench");
        $display("======================================================================");
        $display("");
        $display("  This testbench validates the complete result data path:");
        $display("    CE FIFOs -> result_collector_2d -> result_to_dma -> Result BRAM");
        $display("");
        $display("  Features:");
        $display("  - Auto-drain behavior from both modules");
        $display("  - result_to_dma always accepts (o_ready=1)");
        $display("  - Circular buffer with wr_ptr/rd_ptr verification");
        $display("  - used_entries and empty flag validation");
        $display("");

        total_errors = 0;

        // Initialize
        clk = 0;
        rstn = 0;
        ce_results_ready = 0;
        mc_cmd_op = 8'h00;
        mc_cmd_id = 8'h00;
        cmd_payload_word1 = 32'h0;
        cmd_payload_word2 = 32'h0;
        cmd_payload_word3 = 32'h0;
        rd_ptr = {RESULT_ADDR_WIDTH{1'b0}};

        // Initialize FIFO write signals
        for (int r = 0; r < NUM_ROWS; r++) begin
            for (int c = 0; c < NUM_COLS; c++) begin
                fifo_wr_data[r][c] = 16'h0;
                fifo_wr_en[r][c] = 1'b0;
            end
        end

        repeat (5) @(posedge clk);

        // Test 1: Minimal - 1 batch, 1 column
        run_test(1, 1, 1, 32'hDEADBEEF);

        // Test 2: 2 batches, 4 columns
        run_test(2, 2, 4, 32'h12345678);

        // Test 3: 4 batches, full 16 columns
        run_test(3, 4, 16, 32'hCAFEBABE);

        // Test 4: 8 batches, 8 columns
        run_test(4, 8, 8, 32'hFEEDFACE);

        // Test 5: 1 batch, 17 columns (partial last line)
        run_test(5, 1, 17, 32'hBEEFCAFE);

        // Test 6: B=1, C=256 (16 full lines, larger workload)
        run_test(6, 1, 256, 32'hABCD1234);

        // Summary
        $display("");
        $display("======================================================================");
        $display("  SUMMARY");
        $display("======================================================================");
        if (total_errors == 0) begin
            $display("  ALL TESTS PASSED");
        end else begin
            $display("  TOTAL ERRORS: %0d", total_errors);
        end
        $display("======================================================================");
        $display("");

        $finish;
    end

endmodule
