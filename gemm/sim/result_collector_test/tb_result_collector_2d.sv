// ------------------------------------------------------------------
// Testbench for Result Collector 2D
//
// Purpose: Validate result_collector_2d data flow:
//   - Mock CE FIFO interface with random FP16 data
//   - Issue READOUT commands with varying B/C dimensions
//   - Capture output to mock BRAM and verify results
//
// Test Cases:
//   1. B=1, C=1   - Minimal: 1 batch, 1 column
//   2. B=2, C=4   - 2 batches, 4 columns
//   3. B=4, C=16  - 4 batches, full 16 columns
//   4. B=8, C=8   - 8 batches, 8 columns
//   5. B=1, C=17  - Partial last line (17 results)
//
// Author: Testbench for result_collector_2d
// Date: Jan 22, 2026
// ------------------------------------------------------------------

`timescale 1ps / 1ps

module tb_result_collector_2d;

    // ===================================================================
    // Parameters
    // ===================================================================
    localparam int NUM_ROWS = 16;
    localparam int NUM_COLS = 16;
    localparam int OUTPUT_FIFO_DEPTH = 256;
    localparam int MOCK_FIFO_DEPTH = 64;

    // READOUT opcode
    localparam logic [7:0] OPC_READOUT = 8'hF5;
    localparam logic [7:0] OPC_NOP = 8'h00;

    // Clock period
    localparam int CLK_PERIOD = 2000; // 2ns = 500MHz

    // ===================================================================
    // Signals
    // ===================================================================
    logic clk;
    logic rstn;

    // Command Interface
    logic [7:0]  mc_cmd_op;
    logic [7:0]  mc_cmd_id;
    logic [31:0] cmd_payload_word1;
    logic [31:0] cmd_payload_word2;
    logic [31:0] cmd_payload_word3;
    logic        rc_ack_readout;

    // CE FIFO Interface
    logic [NUM_ROWS-1:0][NUM_COLS-1:0][15:0] ce_result_data;
    logic [NUM_ROWS-1:0][NUM_COLS-1:0]       ce_result_empty;
    logic [NUM_ROWS-1:0][NUM_COLS-1:0]       ce_result_rd_en;

    // Output Interface
    logic        output_ready;
    logic        output_valid;
    logic        output_last;
    logic [15:0] output_keep;
    logic [255:0] output_data;

    // Status
    logic [3:0]  rc_state;
    logic        rc_busy;
    logic [7:0]  rc_cmd_id;

    // ===================================================================
    // Mock CE FIFOs - Using flex_fifo instances for realistic behavior
    // ===================================================================
    logic [NUM_ROWS-1:0][NUM_COLS-1:0][15:0] fifo_wr_data;
    logic [NUM_ROWS-1:0][NUM_COLS-1:0]       fifo_wr_en;
    logic [NUM_ROWS-1:0][NUM_COLS-1:0]       fifo_full;

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
    // Mock BRAM - Captures output
    // ===================================================================
    logic [255:0] mock_bram [0:511];
    int           bram_wr_ptr;
    logic         bram_wr_en;
    logic [15:0]  bram_keep [0:511];  // Keep masks for verification
    logic         bram_last [0:511];  // Last flags for verification

    assign bram_wr_en = output_valid && output_ready;

    always @(posedge clk) begin
        if (!rstn) begin
            bram_wr_ptr <= 0;
        end else if (bram_wr_en) begin
            mock_bram[bram_wr_ptr]  <= output_data;
            bram_keep[bram_wr_ptr]  <= output_keep;
            bram_last[bram_wr_ptr]  <= output_last;
            bram_wr_ptr <= bram_wr_ptr + 1;
        end
    end

    // ===================================================================
    // Golden Reference Data
    // ===================================================================
    // golden_results[batch][col] = sum of all rows for that batch/col
    logic [15:0] golden_results [0:255][0:31];  // Up to 256 batches, 32 cols
    int golden_result_count;

    // ===================================================================
    // DUT Instantiation
    // ===================================================================
    result_collector_2d #(
        .NUM_ROWS           (NUM_ROWS),
        .NUM_COLS           (NUM_COLS),
        .ADDER_SEG_LEN      (2),
        .OUTPUT_FIFO_DEPTH  (OUTPUT_FIFO_DEPTH)
    ) dut (
        .i_clk              (clk),
        .i_reset_n          (rstn),

        // Command Interface
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

        // Output Interface
        .i_output_ready     (output_ready),
        .o_output_valid     (output_valid),
        .o_output_last      (output_last),
        .o_output_keep      (output_keep),
        .o_output_data      (output_data),

        // Status
        .o_rc_state         (rc_state),
        .o_rc_busy          (rc_busy),
        .o_rc_cmd_id        (rc_cmd_id)
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
        mc_cmd_op = OPC_NOP;
        mc_cmd_id = 8'h00;
        cmd_payload_word1 = 32'h0;
        cmd_payload_word2 = 32'h0;
        cmd_payload_word3 = 32'h0;
        output_ready = 1'b1;  // Always ready to receive
        
        // Clear FIFO write signals
        for (int r = 0; r < NUM_ROWS; r++) begin
            for (int c = 0; c < NUM_COLS; c++) begin
                fifo_wr_data[r][c] = 16'h0;
                fifo_wr_en[r][c] = 1'b0;
            end
        end
        
        // Clear mock BRAM (in testbench control)
        for (int i = 0; i < 512; i++) begin
            mock_bram[i] = 256'h0;
            bram_keep[i] = 16'h0;
            bram_last[i] = 1'b0;
        end
        
        // Clear golden
        golden_result_count = 0;
        for (int b = 0; b < 256; b++) begin
            for (int c = 0; c < 32; c++) begin
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
        $display("[TB] FIFO empty check for col 0 (all rows should be 0):");
        for (int r = 0; r < NUM_ROWS; r++) begin
            $display("[TB]   Row %0d: empty=%b", r, ce_result_empty[r][0]);
        end
    endtask

    // ===================================================================
    // Task: Issue READOUT Command
    // ===================================================================
    task automatic issue_readout(input int B, input int C, input logic [7:0] cmd_id);
        $display("[TB] Issuing READOUT: B=%0d, C=%0d, cmd_id=0x%02x", B, C, cmd_id);
        
        // Pack payload: word1 = {left_len[15:0], right_len[15:0]} = {B, C}
        cmd_payload_word1 = {B[15:0], C[15:0]};
        cmd_payload_word2 = 32'h0;
        cmd_payload_word3 = 32'h0;
        mc_cmd_id = cmd_id;
        mc_cmd_op = OPC_READOUT;
        
        @(posedge clk);
        
        // Debug: show state before ACK
        $display("[TB] Before ACK: state=%0d, col_idx=%0d, col_remaining=%0d, batch_cnt=%0d",
                 dut.state_reg, dut.col_idx, dut.col_remaining, dut.batch_cnt);
        
        // Wait for ACK
        repeat (100) begin
            @(posedge clk);
            if (rc_ack_readout) begin
                $display("[TB] READOUT ACK received");
                $display("[TB] After ACK: state=%0d, col_idx=%0d, col_remaining=%0d, batch_cnt=%0d",
                         dut.state_reg, dut.col_idx, dut.col_remaining, dut.batch_cnt);
                mc_cmd_op = OPC_NOP;
                @(posedge clk);
                // Debug: show ST_FIFO_LATENCY (should be state=3)
                $display("[TB] +1clk: state=%0d, col_fifos_ready=%b, drain_enable=%b, adder_valid_in=%b",
                         dut.state_reg, dut.col_fifos_ready, dut.drain_enable, dut.adder_valid_in);
                $display("[TB]   FIFO[0][0] empty=%b data=0x%04x", ce_result_empty[0][0], ce_result_data[0][0]);
                $display("[TB]   FIFO[15][0] empty=%b data=0x%04x", ce_result_empty[15][0], ce_result_data[15][0]);
                $display("[TB]   adder_inputs[0]=0x%04x, adder_inputs[15]=0x%04x",
                         dut.adder_inputs[0], dut.adder_inputs[15]);
                @(posedge clk);
                // Debug: show ST_WAIT_REDUCE (should be state=4)
                $display("[TB] +2clk: state=%0d, adder_valid_in=%b",
                         dut.state_reg, dut.adder_valid_in);
                $display("[TB]   adder_inputs[0]=0x%04x, adder_inputs[15]=0x%04x",
                         dut.adder_inputs[0], dut.adder_inputs[15]);
                return;
            end
        end
        
        $display("[TB] ERROR: ACK timeout");
        errors++;
        mc_cmd_op = OPC_NOP;
    endtask

    // ===================================================================
    // Task: Wait for Completion
    // ===================================================================
    task automatic wait_completion(input int timeout_cycles);
        int cycle_cnt;
        cycle_cnt = 0;
        
        $display("[TB] Waiting for completion (timeout=%0d cycles)...", timeout_cycles);
        
        // Wait for output_last or not busy
        while (cycle_cnt < timeout_cycles) begin
            @(posedge clk);
            cycle_cnt++;
            
            if (output_valid && output_last && output_ready) begin
                $display("[TB] Received last output at cycle %0d", cycle_cnt);
                // Give a few more cycles for any final operations
                repeat (10) @(posedge clk);
                return;
            end
            
            // Debug: periodically show state
            if (cycle_cnt % 1000 == 0) begin
                $display("[TB] @cycle %0d: state=%0d, valid=%b, last=%b, col_idx=%0d, batch_cnt=%0d, col_rem=%0d",
                         cycle_cnt, rc_state, output_valid, output_last,
                         dut.col_idx, dut.batch_cnt, dut.col_remaining);
            end
            
            // Also check for any output_valid events
            if (output_valid) begin
                $display("[TB] @cycle %0d: OUTPUT VALID! last=%b, data[15:0]=0x%04x, batch=%0d, col_rem=%0d",
                         cycle_cnt, output_last, output_data[15:0], dut.batch_cnt, dut.col_remaining);
            end
            
            // Debug drain_enable
            if (dut.drain_enable) begin
                $display("[TB] @cycle %0d: DRAIN col_idx=%0d, input[0]=0x%04x, input[15]=0x%04x",
                         cycle_cnt, dut.col_idx, ce_result_data[0][dut.col_idx], ce_result_data[15][dut.col_idx]);
            end
            
            // Debug: trace first 20 cycles in detail
            if (cycle_cnt < 20) begin
                $display("[TB] @cycle %0d: state=%0d, col_idx=%0d, col_fifos_ready=%b, drain_en=%b, adder_valid_in=%b, adder_valid_out=%b, adder_result=0x%04x",
                         cycle_cnt, rc_state, dut.col_idx, dut.col_fifos_ready, dut.drain_enable, 
                         dut.adder_valid_in, dut.adder_valid_out, dut.adder_result);
                // In ST_FIFO_LATENCY (state 3), show adder inputs
                if (rc_state == 3) begin
                    $display("[TB]   Adder inputs: [0]=0x%04x, [1]=0x%04x, [15]=0x%04x",
                             dut.adder_inputs[0], dut.adder_inputs[1], dut.adder_inputs[15]);
                end
                // In ST_SERIALIZE (state 5), show what we're storing
                if (rc_state == 5) begin
                    $display("[TB]   Storing adder_result=0x%04x to serial_buffer[%0d]",
                             dut.adder_result, dut.serial_idx);
                end
            end
        end
        
        $display("[TB] ERROR: Timeout waiting for completion after %0d cycles", timeout_cycles);
        $display("[TB]   Final state=%0d, busy=%b, bram_wr_ptr=%0d", rc_state, rc_busy, bram_wr_ptr);
        errors++;
    endtask

    // ===================================================================
    // Task: Verify Results
    // ===================================================================
    task automatic verify_results(input int B, input int C);
        int lines_expected;
        int total_results;
        int line_idx;
        int result_idx;
        int slot;
        logic [15:0] actual_fp16;
        logic [15:0] expected_fp16;
        real actual_real;
        real expected_real;
        real diff;
        real tolerance;
        
        total_results = B * C;
        lines_expected = (total_results + 15) / 16;  // Ceiling division
        
        $display("[TB] Verifying: B=%0d, C=%0d, total_results=%0d, lines_expected=%0d, lines_received=%0d",
                 B, C, total_results, lines_expected, bram_wr_ptr);
        
        if (bram_wr_ptr != lines_expected) begin
            $display("[TB] ERROR: Line count mismatch. Expected %0d, got %0d", 
                     lines_expected, bram_wr_ptr);
            errors++;
        end
        
        // Verify each result
        result_idx = 0;
        for (int b = 0; b < B; b++) begin
            for (int c_iter = 0; c_iter < C; c_iter++) begin
                line_idx = result_idx / 16;
                slot = result_idx % 16;
                
                actual_fp16 = mock_bram[line_idx][slot*16 +: 16];
                expected_fp16 = golden_results[b][c_iter];
                
                // Check keep mask
                if (!bram_keep[line_idx][slot]) begin
                    $display("[TB] ERROR: Keep mask not set for result[%0d][%0d] at line %0d, slot %0d",
                             b, c_iter, line_idx, slot);
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
                
                if (diff > tolerance) begin
                    $display("[TB] ERROR: Mismatch at b=%0d, c=%0d: expected 0x%04x (%.6f), got 0x%04x (%.6f)",
                             b, c_iter, expected_fp16, expected_real, actual_fp16, actual_real);
                    errors++;
                end
                
                result_idx++;
            end
        end
        
        // Verify last flag on final line
        if (bram_wr_ptr > 0) begin
            if (!bram_last[bram_wr_ptr - 1]) begin
                $display("[TB] ERROR: Last flag not set on final line %0d", bram_wr_ptr - 1);
                errors++;
            end
        end
        
        // Verify no extra last flags
        for (int i = 0; i < bram_wr_ptr - 1; i++) begin
            if (bram_last[i]) begin
                $display("[TB] ERROR: Unexpected last flag on line %0d", i);
                errors++;
            end
        end
        
        if (errors == 0) begin
            $display("[TB] All %0d results verified successfully", total_results);
        end
    endtask

    // ===================================================================
    // Task: Run Single Test
    // ===================================================================
    task automatic run_test(input int test_id, input int B, input int C, input logic [31:0] seed);
        $display("");
        $display("======================================================================");
        $display("  TEST %0d: B=%0d, C=%0d", test_id, B, C);
        $display("======================================================================");
        
        test_num = test_id;
        errors = 0;
        
        // Reset
        reset_dut();
        
        // Populate FIFOs
        populate_mock_fifos(B, C, seed);
        
        // Issue READOUT
        issue_readout(B, C, test_id[7:0]);
        
        // Wait for completion
        wait_completion(10000 + B * C * 100);
        
        // Verify results
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
        $display("  Result Collector 2D Testbench");
        $display("======================================================================");
        $display("");
        
        total_errors = 0;
        
        // Initialize
        clk = 0;
        rstn = 0;
        mc_cmd_op = OPC_NOP;
        mc_cmd_id = 8'h00;
        cmd_payload_word1 = 32'h0;
        cmd_payload_word2 = 32'h0;
        cmd_payload_word3 = 32'h0;
        output_ready = 1'b1;
        
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
