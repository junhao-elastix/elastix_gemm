// =============================================================================
// Testbench for gfp_norm_quant module
// =============================================================================
// E2E streaming test: 8 vectors of 32 GFP11e5 elements -> 8 vectors of 32 GFP8e5
// Each element has a unique exponent to stress test alignment
// =============================================================================

`timescale 1ns/1ps

module tb_gfp_norm_quant;

    // =========================================================================
    // Parameters (match DUT)
    // =========================================================================
    localparam int GFP11e5_TOTAL_BITS = 16;
    localparam int GFP11e5_EXP_BITS   = 5;
    localparam int GFP11e5_MAN_BITS   = 11;
    localparam int GFP8e5_MAN_BITS    = 8;
    localparam int GFP8e5_EXP_BITS    = 5;
    localparam int IN_ELEMENTS      = 32;
    localparam int INGRESS_FIFO_ELS = 8;
    localparam int DATA_FIFO_ELS    = 8;
    localparam int EGRESS_FIFO_ELS  = 4;

    localparam int ELEM_EN_WIDTH    = $clog2(IN_ELEMENTS + 1);

    // Test parameters
    localparam int NUM_VECTORS      = 8;
    localparam int TIMEOUT_CYCLES   = 5000;

    // =========================================================================
    // Clock and Reset
    // =========================================================================
    logic clk;
    logic reset;

    initial clk = 0;
    always #5 clk = ~clk;  // 100MHz

    // =========================================================================
    // DUT Signals
    // =========================================================================
    logic                                        ready_o;
    logic                                        valid_i;
    logic [IN_ELEMENTS-1:0][GFP11e5_TOTAL_BITS-1:0] data_i;
    logic [ELEM_EN_WIDTH-1:0]                    pad_i;
    logic                                        last_i;
    logic                                        ack_o;

    logic                                        ready_i;
    logic                                        valid_o;
    logic [IN_ELEMENTS-1:0][GFP8e5_MAN_BITS-1:0]   mantissa_o;
    logic [GFP8e5_EXP_BITS-1:0]                    exponent_o;
    logic [ELEM_EN_WIDTH-1:0]                    pad_o;
    logic                                        last_o;
    logic                                        ack_i;

    // =========================================================================
    // DUT Instantiation
    // =========================================================================
    gfp_norm_quant #(
        .GFP11e5_TOTAL_BITS (GFP11e5_TOTAL_BITS),
        .GFP11e5_EXP_BITS   (GFP11e5_EXP_BITS),
        .GFP11e5_MAN_BITS   (GFP11e5_MAN_BITS),
        .GFP8e5_MAN_BITS    (GFP8e5_MAN_BITS),
        .GFP8e5_EXP_BITS    (GFP8e5_EXP_BITS),
        .IN_ELEMENTS      (IN_ELEMENTS),
        .INGRESS_FIFO_ELS (INGRESS_FIFO_ELS),
        .DATA_FIFO_ELS    (DATA_FIFO_ELS),
        .EGRESS_FIFO_ELS  (EGRESS_FIFO_ELS)
    ) dut (
        .clk_i      (clk),
        .reset_i    (reset),
        .ready_o    (ready_o),
        .valid_i    (valid_i),
        .data_i     (data_i),
        .pad_i      (pad_i),
        .last_i     (last_i),
        .ack_o      (ack_o),
        .ready_i    (ready_i),
        .valid_o    (valid_o),
        .mantissa_o (mantissa_o),
        .exponent_o (exponent_o),
        .pad_o      (pad_o),
        .last_o     (last_o),
        .ack_i      (ack_i)
    );

    // =========================================================================
    // Test Data Storage
    // =========================================================================
    logic [GFP11e5_TOTAL_BITS-1:0] test_data    [NUM_VECTORS][IN_ELEMENTS];
    logic signed [GFP8e5_MAN_BITS-1:0] expected_mans [NUM_VECTORS][IN_ELEMENTS];
    logic [GFP8e5_EXP_BITS-1:0]    expected_exps [NUM_VECTORS];

    // Results
    logic signed [GFP8e5_MAN_BITS-1:0] actual_mans [NUM_VECTORS][IN_ELEMENTS];
    logic [GFP8e5_EXP_BITS-1:0]    actual_exps [NUM_VECTORS];

    // =========================================================================
    // Golden File Paths (relative to sim/riviera directory)
    // =========================================================================
    localparam string GOLDEN_INPUT_FILE  = "../../golden_models/golden_input.txt";
    localparam string GOLDEN_OUTPUT_FILE = "../../golden_models/golden_output.txt";

    // =========================================================================
    // Load Test Data from Golden Files
    // =========================================================================
    task automatic load_golden_files();
        int fd_in, fd_out;
        int scan_result;
        logic [15:0] input_val;
        logic [7:0]  output_val;

        // Load input file
        fd_in = $fopen(GOLDEN_INPUT_FILE, "r");
        if (fd_in == 0) begin
            $display("ERROR: Cannot open input file: %s", GOLDEN_INPUT_FILE);
            $finish;
        end

        for (int vec = 0; vec < NUM_VECTORS; vec++) begin
            for (int elem = 0; elem < IN_ELEMENTS; elem++) begin
                scan_result = $fscanf(fd_in, "%h", input_val);
                if (scan_result != 1) begin
                    $display("ERROR: Failed to read input[%0d][%0d]", vec, elem);
                    $finish;
                end
                test_data[vec][elem] = input_val;
            end
        end
        $fclose(fd_in);
        $display("[%0t] Loaded %0d input vectors from %s", $time, NUM_VECTORS, GOLDEN_INPUT_FILE);

        // Load output file (format: exp man0 man1 ... man31)
        fd_out = $fopen(GOLDEN_OUTPUT_FILE, "r");
        if (fd_out == 0) begin
            $display("ERROR: Cannot open output file: %s", GOLDEN_OUTPUT_FILE);
            $finish;
        end

        for (int vec = 0; vec < NUM_VECTORS; vec++) begin
            // First value is the shared exponent
            scan_result = $fscanf(fd_out, "%h", output_val);
            if (scan_result != 1) begin
                $display("ERROR: Failed to read exp[%0d]", vec);
                $finish;
            end
            expected_exps[vec] = output_val[GFP8e5_EXP_BITS-1:0];

            // Remaining 32 values are mantissas
            for (int elem = 0; elem < IN_ELEMENTS; elem++) begin
                scan_result = $fscanf(fd_out, "%h", output_val);
                if (scan_result != 1) begin
                    $display("ERROR: Failed to read mantissa[%0d][%0d]", vec, elem);
                    $finish;
                end
                expected_mans[vec][elem] = $signed(output_val);
            end
        end
        $fclose(fd_out);
        $display("[%0t] Loaded %0d output vectors from %s", $time, NUM_VECTORS, GOLDEN_OUTPUT_FILE);
    endtask

    // =========================================================================
    // Producer Task - Sends vectors to DUT
    // =========================================================================
    int vectors_sent;

    task automatic producer();
        vectors_sent = 0;

        for (int vec = 0; vec < NUM_VECTORS; vec++) begin
            // Wait for ready
            while (!ready_o) @(posedge clk);

            // Drive inputs
            valid_i <= 1'b1;
            for (int i = 0; i < IN_ELEMENTS; i++) begin
                data_i[i] <= test_data[vec][i];
            end
            pad_i <= '0;
            last_i <= (vec == NUM_VECTORS - 1);

            @(posedge clk);
            valid_i <= 1'b0;
            vectors_sent++;
            $display("[%0t] Producer: sent vector %0d", $time, vec);
        end

        $display("[%0t] Producer: all %0d vectors sent", $time, vectors_sent);
    endtask

    // =========================================================================
    // Consumer Task - Receives and checks outputs
    // =========================================================================
    int vectors_received;
    int total_errors;
    int max_error;

    task automatic consumer();
        int timeout_cnt;
        int error;

        vectors_received = 0;
        total_errors = 0;
        max_error = 0;

        while (vectors_received < NUM_VECTORS) begin
            // Wait for valid output with timeout
            timeout_cnt = 0;
            while (!valid_o && timeout_cnt < TIMEOUT_CYCLES) begin
                @(posedge clk);
                timeout_cnt++;
            end

            if (timeout_cnt >= TIMEOUT_CYCLES) begin
                $display("[%0t] ERROR: Consumer timeout waiting for vector %0d",
                         $time, vectors_received);
                break;
            end

            // Capture output
            actual_exps[vectors_received] = exponent_o;
            for (int i = 0; i < IN_ELEMENTS; i++) begin
                actual_mans[vectors_received][i] = $signed(mantissa_o[i]);
            end

            // Check exponent
            if (actual_exps[vectors_received] != expected_exps[vectors_received]) begin
                $display("[%0t] ERROR: Vec %0d exp mismatch: got %0d, expected %0d",
                         $time, vectors_received,
                         actual_exps[vectors_received], expected_exps[vectors_received]);
            end

            // Check mantissas
            for (int i = 0; i < IN_ELEMENTS; i++) begin
                error = (actual_mans[vectors_received][i] > expected_mans[vectors_received][i]) ?
                        (actual_mans[vectors_received][i] - expected_mans[vectors_received][i]) :
                        (expected_mans[vectors_received][i] - actual_mans[vectors_received][i]);

                if (error > 0) begin
                    total_errors++;
                    if (error > max_error) max_error = error;
                    if (error > 1) begin
                        $display("[%0t] ERROR: Vec %0d, elem %0d: got %0d, expected %0d, err=%0d",
                                 $time, vectors_received, i,
                                 actual_mans[vectors_received][i],
                                 expected_mans[vectors_received][i], error);
                    end
                end
            end

            $display("[%0t] Consumer: received vector %0d (exp=%0d)",
                     $time, vectors_received, actual_exps[vectors_received]);

            vectors_received++;
            @(posedge clk);
        end

        $display("[%0t] Consumer: received %0d vectors", $time, vectors_received);
    endtask

    // =========================================================================
    // Main Test
    // =========================================================================
    initial begin
        $display("============================================================");
        $display("  GFP11e5 to GFP8e5 Normalize and Quantize E2E Test");
        $display("  %0d vectors x %0d elements per vector", NUM_VECTORS, IN_ELEMENTS);
        $display("============================================================");

        // Initialize
        reset <= 1'b1;
        valid_i <= 1'b0;
        ready_i <= 1'b1;
        ack_i <= 1'b0;
        pad_i <= '0;
        last_i <= 1'b0;
        for (int i = 0; i < IN_ELEMENTS; i++) data_i[i] <= '0;

        // Load test data from golden files
        load_golden_files();

        // Release reset
        repeat (10) @(posedge clk);
        reset <= 1'b0;
        repeat (5) @(posedge clk);

        // Run producer and consumer concurrently
        fork
            producer();
            consumer();
        join

        // Report results
        $display("");
        $display("============================================================");
        $display("  E2E Accuracy Test Results:");
        $display("    Vectors processed: %0d", vectors_received);
        $display("    Elements per vector: %0d", IN_ELEMENTS);
        $display("    Total elements: %0d", vectors_received * IN_ELEMENTS);
        $display("    Elements with errors: %0d", total_errors);
        $display("    Max error: %0d", max_error);
        if (vectors_received * IN_ELEMENTS > 0) begin
            $display("    Accuracy: %0.2f%%",
                     100.0 * (vectors_received * IN_ELEMENTS - total_errors) /
                     (vectors_received * IN_ELEMENTS));
        end
        $display("============================================================");

        // Final verdict
        if (vectors_received == NUM_VECTORS && total_errors == 0) begin
            $display("");
            $display("*** ALL TESTS PASSED ***");
            $display("");
        end else begin
            $display("");
            $display("*** TESTS FAILED ***");
            if (vectors_received != NUM_VECTORS)
                $display("    Expected %0d vectors, received %0d", NUM_VECTORS, vectors_received);
            if (total_errors > 0)
                $display("    Found %0d element mismatches", total_errors);
            $display("");
        end

        #100;
        $finish;
    end

    // Timeout watchdog
    initial begin
        #(TIMEOUT_CYCLES * 20 * 10);  // 20x timeout per vector
        $display("ERROR: Global timeout reached");
        $finish;
    end

endmodule
