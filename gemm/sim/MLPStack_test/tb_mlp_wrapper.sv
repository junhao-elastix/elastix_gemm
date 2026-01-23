// ------------------------------------------------------------------
// Testbench for comp_MLPStack.sv
//
// Purpose: Validate 4-stack MLP BRAM column wrapper with golden reference
//
// Test Suite (14 configurations verified):
//   - B1_C1_V1 to B16_C16_V8 covering 1-256 results per test
//   - Golden files from /home/dev/Dev/elastix_gemm/hex/
//   - Input data: left.hex (activations), right.hex (weights)
//
// Memory Layout (528 lines per hex file):
//   Lines 0-15:   Exponent data (16 lines × 32 bytes = 512 exponents)
//   Lines 16-527: Mantissa data (512 lines × 32 bytes = 128 NVs × 4 chunks)
//
// NV Structure (128 elements per NV):
//   - 4 chunks × 32 elements = 128 elements
//   - Each chunk: 256 bits = 32 bytes = 32 elements
//   - Each chunk has 1 shared exponent (8-bit)
//
// Weight Write Pattern (Direct Write - No Handshake):
//   - 4 cycles per NV (one 256-bit chunk per cycle)
//   - i_wt_wr_addr provides direct BRAM write address
//   - External controller manages address sequencing
//
// Validation Tolerance:
//   - Combined tolerance: 5% relative OR 0.001 absolute
//   - Absolute tolerance handles near-zero values where relative error is meaningless
//   - Example: -0.000077 vs -0.000083 is 7% relative but only 0.000006 absolute (PASS)
//
// Author: MLP Wrapper Testing
// Date: Jan 20, 2026
// ------------------------------------------------------------------

`timescale 1ns/1ps

module tb_mlp_wrapper;

    // =========================================================================
    // Parameters
    // =========================================================================
    localparam int CLK_PERIOD_NS    = 10;        // 100MHz clock
    localparam int TIMEOUT_NS       = 100000000; // 100ms timeout
    localparam int NUM_MLPS         = 8;
    localparam int NUM_STACKS       = 4;
    localparam int NUM_COLUMNS      = 16;        // 8 MLPs × 2 banks
    localparam int CYCLES_PER_NV    = 4;         // 4 cycles per NV
    localparam int ELEMENTS_PER_NV  = 128;       // 128 elements per NV
    localparam int ELEMENTS_PER_CHUNK = 32;      // 32 elements per 256-bit chunk

    // Memory block constants
    localparam int EXP_LINES     = 16;           // Lines 0-15
    localparam int MAN_LINE_START = 16;          // Mantissa starts at line 16
    localparam int TOTAL_LINES   = 528;
    localparam int MAX_NVS       = 128;

    // =========================================================================
    // Hex File Paths
    // =========================================================================
    localparam string HEX_PATH = "/home/dev/Dev/elastix_gemm/hex/";

    // =========================================================================
    // Test Configuration
    // =========================================================================
    typedef struct {
        int         C;              // Number of columns (weight NVs)
        int         V;              // NVs per column (V-loop depth for accumulation)
        int         B;              // Number of batches (activation NVs per dot product)
        string      name;           // Golden file name (without .hex)
    } test_config_t;

    // =========================================================================
    // Test Suite - Use existing golden files from /hex directory
    // =========================================================================
    // Tests ordered from simple to complex
    test_config_t test_suite[] = '{
        '{C: 1,  V: 1,  B: 1,   name: "golden_B1_C1_V1"},      // Minimal smoke test
        '{C: 2,  V: 2,  B: 2,   name: "golden_B2_C2_V2"},      // Multi-batch, multi-column
        '{C: 4,  V: 4,  B: 4,   name: "golden_B4_C4_V4"},      // 4x4 test
        '{C: 6,  V: 4,  B: 4,   name: "golden_B4_C6_V4"},      // Odd column count
        '{C: 8,  V: 4,  B: 4,   name: "golden_B4_C8_V4"},      // 8 columns
        '{C: 8,  V: 8,  B: 4,   name: "golden_B4_C8_V8"},      // 8 columns, larger V
        '{C: 14, V: 4,  B: 4,   name: "golden_B4_C14_V4"},     // 14 columns
        '{C: 16, V: 8,  B: 4,   name: "golden_B4_C16_V8"},     // Full 16 columns
        '{C: 4,  V: 32, B: 4,   name: "golden_B4_C4_V32"},     // Deep V accumulation
        '{C: 4,  V: 16, B: 2,   name: "golden_B2_C4_V16"},     // 2 batches, larger V
        '{C: 8,  V: 16, B: 8,   name: "golden_B8_C8_V16"},     // 8 batches
        '{C: 16, V: 4,  B: 8,   name: "golden_B8_C16_V4"},     // 8 batches, 16 cols
        '{C: 16, V: 4,  B: 16,  name: "golden_B16_C16_V4"},    // 16 batches, 16 cols
        '{C: 16, V: 8,  B: 16,  name: "golden_B16_C16_V8"}     // Large: 16 batches, full cols
    };

    // =========================================================================
    // Clock and Reset
    // =========================================================================
    logic clk;
    logic rstn;

    // =========================================================================
    // DUT Interface Signals
    // =========================================================================
    logic [9:0]   rd_base_addr;
    logic         wt_wr_en;            // Weight write enable (no handshake)
    logic [255:0] wt_man;
    logic [7:0]   wt_exp;
    logic [2:0]   wt_mlp_sel;
    logic [9:0]   wt_wr_addr;          // Direct BRAM write address

    logic         act_valid;
    logic         act_ready;
    logic [255:0] nv_left_man;
    logic [7:0]   nv_left_exp;
    logic         new_dot;
    logic         last_nv;
    logic         last_matmul;
    logic [15:0]  result_fp16 [NUM_COLUMNS-1:0];
    logic         result_push;
    logic         result_fifo_full;

    // =========================================================================
    // Test Status
    // =========================================================================
    int     tests_run;
    int     tests_passed;
    logic   current_test_ok;
    int     num_results_collected;

    // Collected results (FP16 values)
    logic [15:0] collected_results [0:1023];

    // =========================================================================
    // Raw Hex Data Storage (memory block format)
    // =========================================================================
    // Exponent data: 16 lines × 32 bytes = 512 bytes
    logic [7:0] left_exp_data  [0:EXP_LINES-1][0:31];
    logic [7:0] right_exp_data [0:EXP_LINES-1][0:31];

    // Mantissa data: 512 lines × 32 bytes
    logic [7:0] left_man_data  [0:511][0:31];
    logic [7:0] right_man_data [0:511][0:31];

    int left_lines_loaded, right_lines_loaded;

    // =========================================================================
    // DUT Instantiation
    // =========================================================================
    comp_MLPStack #(
        .NUM_MLPS        (NUM_MLPS),
        .NUM_STACKS      (NUM_STACKS),
        .CYCLES_PER_NV   (CYCLES_PER_NV),
        .PIPELINE_LATENCY(2)
    ) dut (
        .clk             (clk),
        .rstn            (rstn),
        .i_rd_base_addr  (rd_base_addr),
        .i_wt_wr_en      (wt_wr_en),
        .i_nv_right_man  (wt_man),
        .i_nv_right_exp  (wt_exp),
        .i_wt_mlp_sel    (wt_mlp_sel),
        .i_wt_wr_addr    (wt_wr_addr),
        .i_act_valid     (act_valid),
        .o_act_ready     (act_ready),
        .i_nv_left_man   (nv_left_man),
        .i_nv_left_exp   (nv_left_exp),
        .i_new_dot       (new_dot),
        .i_last_nv       (last_nv),
        .i_last_matmul   (last_matmul),
        .o_result_fp16   (result_fp16),
        .o_result_push   (result_push),
        .i_result_fifo_full(result_fifo_full)
    );

    // =========================================================================
    // Clock Generation
    // =========================================================================
    initial begin
        clk = 0;
        forever #(CLK_PERIOD_NS/2) clk = ~clk;
    end

    // =========================================================================
    // Result Collection - Extract FP16 from wrapper output
    // =========================================================================
    always_ff @(posedge clk) begin
        if (result_push && !result_fifo_full) begin
            // New interface: o_result_fp16[c] is already column-ordered
            // col0 = MLP0 bank0, col1 = MLP0 bank1, col2 = MLP1 bank0, etc.
            for (int c = 0; c < NUM_COLUMNS; c++) begin
                collected_results[num_results_collected + c] = result_fp16[c];
            end
            num_results_collected = num_results_collected + NUM_COLUMNS;
            $display("[TB] @%0t Collected %0d results, col0=0x%04x col1=0x%04x col2=0x%04x col3=0x%04x",
                     $time, num_results_collected, result_fp16[0], result_fp16[1], result_fp16[2], result_fp16[3]);
        end
    end

    // =========================================================================
    // Load Memory Block Hex File
    // =========================================================================
    task automatic load_memory_block_hex(
        input string filename,
        output logic [7:0] exp_data [0:EXP_LINES-1][0:31],
        output logic [7:0] man_data [0:511][0:31],
        output int lines_loaded
    );
        integer fd;
        string line_str;
        logic [7:0] hex_bytes[0:31];
        integer scan_result;
        int line_idx;

        fd = $fopen(filename, "r");
        if (fd == 0) begin
            $display("[TB] ERROR: Cannot open %s", filename);
            lines_loaded = 0;
            return;
        end

        line_idx = 0;
        while (!$feof(fd) && line_idx < TOTAL_LINES) begin
            if ($fgets(line_str, fd)) begin
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
                    if (line_idx < EXP_LINES) begin
                        // Exponent region (lines 0-15)
                        for (int i = 0; i < 32; i++) begin
                            exp_data[line_idx][i] = hex_bytes[i];
                        end
                    end else begin
                        // Mantissa region (lines 16-527)
                        int man_idx = line_idx - MAN_LINE_START;
                        for (int i = 0; i < 32; i++) begin
                            man_data[man_idx][i] = hex_bytes[i];
                        end
                    end
                    line_idx++;
                end
            end
        end
        $fclose(fd);
        lines_loaded = line_idx;
    endtask

    // =========================================================================
    // Get Exponent for NV chunk
    // =========================================================================
    // Each NV has 4 chunks, each chunk has 1 exponent
    // Exponent index = nv_idx * 4 + chunk_idx
    // Stored in exp_data[line][byte] where line = exp_idx / 32, byte = exp_idx % 32
    //
    // IMPORTANT: Hex files use GFP5 format (5-bit exponent, bias=15)
    //            MLP hardware expects BFP8E8 format (8-bit exponent, bias=133)
    //            Conversion: new_exp = (raw_5bit - 15) + 133 = raw_5bit + 118
    localparam int GFP5_BIAS = 15;          // 5-bit exponent bias
    localparam int BFP8E8_BIAS = 133;       // MLP native 8-bit exponent bias
    localparam int ACX_BFP_BIAS_OFFSET = BFP8E8_BIAS - GFP5_BIAS;  // = 118

    function automatic logic [7:0] get_exponent(
        input logic [7:0] exp_data [0:EXP_LINES-1][0:31],
        input int nv_idx,
        input int chunk_idx
    );
        int exp_idx;
        int exp_line;
        int exp_byte;
        logic [7:0] raw_exp;

        exp_idx = nv_idx * 4 + chunk_idx;
        exp_line = exp_idx / 32;
        exp_byte = exp_idx % 32;

        raw_exp = exp_data[exp_line][exp_byte];
        // Apply bias adjustment for MLP format
        return raw_exp + ACX_BFP_BIAS_OFFSET;
    endfunction

    // =========================================================================
    // Get 256-bit Mantissa Chunk for NV
    // =========================================================================
    // Each NV has 4 chunks at mantissa lines: nv_idx * 4 + {0,1,2,3}
    function automatic logic [255:0] get_mantissa_chunk(
        input logic [7:0] man_data [0:511][0:31],
        input int nv_idx,
        input int chunk_idx
    );
        int man_line;
        logic [255:0] chunk;

        man_line = nv_idx * 4 + chunk_idx;

        // Pack 32 bytes into 256-bit chunk (LSB first - byte 0 is bits [7:0])
        for (int i = 0; i < 32; i++) begin
            chunk[i*8 +: 8] = man_data[man_line][i];
        end

        return chunk;
    endfunction

    // =========================================================================
    // Load Hex Files at Startup
    // =========================================================================
    initial begin
        load_memory_block_hex({HEX_PATH, "left.hex"}, left_exp_data, left_man_data, left_lines_loaded);
        load_memory_block_hex({HEX_PATH, "right.hex"}, right_exp_data, right_man_data, right_lines_loaded);
        $display("[TB] Loaded hex files from: %s", HEX_PATH);
        $display("[TB]   left.hex: %0d lines", left_lines_loaded);
        $display("[TB]   right.hex: %0d lines", right_lines_loaded);

        // Debug: show first NV's data
        $display("[TB] First NV (right.hex) mantissa preview:");
        $display("[TB]   Chunk 0 exp=0x%02x, man[0:3]=0x%02x_%02x_%02x_%02x",
                 get_exponent(right_exp_data, 0, 0),
                 right_man_data[0][3], right_man_data[0][2],
                 right_man_data[0][1], right_man_data[0][0]);
    end

    // =========================================================================
    // Weight Loading Task - Proper Bank Interleaving for Asymmetric BRAM
    // =========================================================================
    // BRAM Architecture:
    //   - Write: 72-bit at 10-bit wraddr
    //   - Read: 144-bit at 9-bit rdaddr (reads wraddrs 2*rdaddr and 2*rdaddr+1)
    //   - Bank 0: gets lower 72 bits (dout[71:0]) from EVEN wraddrs
    //   - Bank 1: gets upper 72 bits (dout[143:72]) from ODD wraddrs
    //
    // Wrapper write addressing: wraddr = {nv_idx[7:0], cycle[1:0]}
    //
    // CRITICAL INSIGHT: For a complete 128-element dot product, we need all
    // 4 chunks (each 32 elements). But asymmetric BRAM reads:
    //   - Bank 0 sees chunks at wraddrs 0,2,4,6 (even)
    //   - Bank 1 sees chunks at wraddrs 1,3,5,7 (odd)
    //
    // So chunks 0,1,2,3 written consecutively go to wraddrs 0,1,2,3:
    //   - rdaddr 0 → bank0=chunk0, bank1=chunk1
    //   - rdaddr 1 → bank0=chunk2, bank1=chunk3
    //
    // For PAIRED columns (C >= 2, even):
    //   - Column 0 (bank 0) and Column 1 (bank 1) share the same NV slot
    //   - Each bank gets its 2 chunks from the interleaved write pattern
    //
    // For SINGLE column (C = 1): Load same data to BOTH banks by using
    //   consecutive nv_idx values. Sum bank0+bank1 outputs for full result.
    //
    // TIMING: Set data BEFORE the clock edge where DUT samples it
    task automatic load_weights(
        input int num_cols,      // C: number of columns (1-16)
        input int num_nv_per_col // V: NVs per column
    );
        int mlp_idx;
        int src_nv;
        int bank;
        int wrapper_nv;
        logic [255:0] man_chunk;
        logic [7:0] exp_val;
        int timeout_cnt;
        int direct_wraddr;

        $display("[TB] Loading weights: %0d columns, %0d NVs/col", num_cols, num_nv_per_col);

        if (num_cols == 1) begin
            // =========================================================================
            // SINGLE COLUMN MODE (C=1): Direct write to even addresses
            // =========================================================================
            // For C=1, all 128 elements must go to bank0 (read from even wraddrs)
            // Write chunks 0,1,2,3 to wraddrs 0,2,4,6 (all even)
            // Then read with rdaddrs 0,1,2,3 will give all 4 chunks to bank0
            mlp_idx = 0;

            for (int v = 0; v < num_nv_per_col; v++) begin
                src_nv = v;

                // Write 4 chunks to EVEN wraddrs: 0, 2, 4, 6 (for first NV)
                // Base address for this V: v * 8 (each NV needs 4 rdaddrs = 8 wraddrs)
                for (int chunk = 0; chunk < CYCLES_PER_NV; chunk++) begin
                    man_chunk = get_mantissa_chunk(right_man_data, src_nv, chunk);
                    exp_val = get_exponent(right_exp_data, src_nv, chunk);

                    // Direct wraddr: base + chunk*2 (even addresses only)
                    // chunk 0 → wraddr 0, chunk 1 → wraddr 2, chunk 2 → wraddr 4, chunk 3 → wraddr 6
                    direct_wraddr = v * 8 + chunk * 2;

                    wt_wr_en   <= 1'b1;
                    wt_mlp_sel <= mlp_idx[2:0];
                    wt_wr_addr <= direct_wraddr[9:0];
                    wt_man     <= man_chunk;
                    wt_exp     <= exp_val;

                    @(posedge clk);

                    $display("[WT_DBG] @%0t C=1 mode: v=%0d chunk=%0d src_nv=%0d direct_wraddr=%0d (even) mlp=%0d exp=0x%02x",
                             $time, v, chunk, src_nv, direct_wraddr, mlp_idx, exp_val);
                end

                wt_wr_en <= 1'b0;
                @(posedge clk);
                repeat (2) @(posedge clk);
            end

            $display("[TB]   C=1: Loaded %0d NV(s) to MLP 0 bank0 (even wraddrs only)", num_nv_per_col);

        end else begin
            // =========================================================================
            // MULTI-COLUMN MODE (C >= 2): Direct write with interleaving
            // =========================================================================
            // For asymmetric BRAM (rdaddr N reads wraddrs 2N and 2N+1):
            //   - col0 (bank=0) chunks must go to EVEN wraddrs
            //   - col1 (bank=1) chunks must go to ODD wraddrs
            // Pattern: wraddr = v * 8 + chunk * 2 + bank
            //   - v=0, chunk=0: col0→wr0, col1→wr1
            //   - v=0, chunk=1: col0→wr2, col1→wr3
            //   - v=0, chunk=2: col0→wr4, col1→wr5
            //   - v=0, chunk=3: col0→wr6, col1→wr7
            //   - v=1, chunk=0: col0→wr8, col1→wr9
            //   etc.

            for (int c = 0; c < num_cols; c++) begin
                mlp_idx = c / 2;  // Which MLP (0-7)
                bank = c % 2;     // Which bank within MLP (0 or 1)

                for (int v = 0; v < num_nv_per_col; v++) begin
                    src_nv = c * num_nv_per_col + v;  // Standard: C*V + v

                    // Write 4 chunks with interleaved wraddrs
                    for (int chunk = 0; chunk < CYCLES_PER_NV; chunk++) begin
                        man_chunk = get_mantissa_chunk(right_man_data, src_nv, chunk);
                        exp_val = get_exponent(right_exp_data, src_nv, chunk);

                        // Direct wraddr: v * 8 + chunk * 2 + bank
                        // This interleaves col0 at even and col1 at odd addresses
                        direct_wraddr = v * 8 + chunk * 2 + bank;

                        wt_wr_en   <= 1'b1;
                        wt_mlp_sel <= mlp_idx[2:0];
                        wt_wr_addr <= direct_wraddr[9:0];
                        wt_man     <= man_chunk;
                        wt_exp     <= exp_val;

                        @(posedge clk);

                        $display("[WT_DBG] @%0t col=%0d bank=%0d v=%0d chunk=%0d src_nv=%0d direct_wraddr=%0d mlp=%0d exp=0x%02x",
                                 $time, c, bank, v, chunk, src_nv, direct_wraddr, mlp_idx, exp_val);
                    end

                    wt_wr_en <= 1'b0;
                    @(posedge clk);
                    repeat (2) @(posedge clk);
                end

                $display("[TB]   Column %0d loaded to MLP %0d bank %0d (src_nv base=%0d)",
                         c, mlp_idx, bank, c * num_nv_per_col);
            end
        end

        repeat (5) @(posedge clk);
        $display("[TB] Weight loading complete");
    endtask

    // =========================================================================
    // Initialize Companion Banks with Zeros
    // =========================================================================
    // When using fewer than 16 columns, initialize unused bank slots
    task automatic init_unused_columns(
        input int num_cols_used,
        input int num_nv_per_col
    );
        int mlp_idx;
        int wrapper_nv_idx;

        int bank;
        int direct_wraddr;

        $display("[TB] Initializing unused columns to zero");

        for (int c = num_cols_used; c < NUM_COLUMNS; c++) begin
            mlp_idx = c / 2;
            bank = c % 2;

            for (int v = 0; v < num_nv_per_col; v++) begin
                // Use same addressing scheme: v * 8 + chunk * 2 + bank
                for (int chunk = 0; chunk < CYCLES_PER_NV; chunk++) begin
                    direct_wraddr = v * 8 + chunk * 2 + bank;

                    wt_wr_en   <= 1'b1;
                    wt_mlp_sel <= mlp_idx[2:0];
                    wt_wr_addr <= direct_wraddr[9:0];
                    wt_man     <= 256'd0;
                    wt_exp     <= 8'd0;

                    @(posedge clk);
                end

                wt_wr_en <= 1'b0;
                @(posedge clk);
            end
        end

        repeat (5) @(posedge clk);
        $display("[TB] Unused column initialization complete");
    endtask

    // =========================================================================
    // Activation Streaming Task
    // =========================================================================
    // Streams activations through the wrapper for computation
    // For B batches with V NVs each:
    //   - Batch b uses NVs from left.hex at indices [b*V, b*V + V - 1]
    //   - Each NV = 4 chunks (4 cycles)
    //
    // TIMING: Set data BEFORE clock edge, then wait for handshake
    task automatic stream_activations(
        input int num_batches,   // B: number of batches
        input int num_nv_per_batch // V: NVs per batch (accumulation depth)
    );
        int nv_base;
        logic [255:0] man_chunk;
        logic [7:0] exp_val;
        int timeout_cnt;

        $display("[TB] Streaming activations: %0d batches, %0d NVs/batch", num_batches, num_nv_per_batch);

        for (int b = 0; b < num_batches; b++) begin
            nv_base = b * num_nv_per_batch;

            for (int v = 0; v < num_nv_per_batch; v++) begin
                int src_nv = nv_base + v;

                // Stream 4 chunks for this NV
                for (int chunk = 0; chunk < CYCLES_PER_NV; chunk++) begin
                    automatic bit dbg_new_dot, dbg_last_nv, dbg_last_matmul;

                    // CRITICAL: Calculate and set data BEFORE the clock edge
                    man_chunk = get_mantissa_chunk(left_man_data, src_nv, chunk);
                    exp_val = get_exponent(left_exp_data, src_nv, chunk);

                    // Calculate control signals
                    dbg_new_dot     = (v == 0) && (chunk == 0);
                    dbg_last_nv     = (v == num_nv_per_batch - 1) && (chunk == CYCLES_PER_NV - 1);
                    dbg_last_matmul = (b == num_batches - 1) && (v == num_nv_per_batch - 1) && (chunk == CYCLES_PER_NV - 1);

                    // Set data signals BEFORE clock edge
                    nv_left_man <= man_chunk;
                    nv_left_exp <= exp_val;
                    new_dot     <= dbg_new_dot;
                    last_nv     <= dbg_last_nv;
                    last_matmul <= dbg_last_matmul;
                    act_valid   <= 1'b1;

                    // Debug: Show what TB is setting
                    $display("[TB_ACT] @%0t TB_iter: b=%0d v=%0d chunk=%0d | new_dot=%b last_nv=%b last_matmul=%b",
                             $time, b, v, chunk, dbg_new_dot, dbg_last_nv, dbg_last_matmul);

                    // Wait for clock edge - DUT samples data here
                    @(posedge clk);

                    // Debug: Show read address and load signal timing
                    $display("[RD_DBG] @%0t rdaddr=%0d state=%0d nv=%0d->%0d chunk=%0d->%0d load=%b delay=%02b",
                             $time, dut.mlp_rdaddr, dut.comp_state_reg,
                             dut.nv_index, dut.next_nv_index, dut.chunk_cnt, dut.next_chunk_cnt,
                             dut.mlp_load, dut.new_dot_delay);

                    // Check handshake (data was consumed if ready was high)
                    timeout_cnt = 0;
                    while (!act_ready && timeout_cnt < 200) begin
                        @(posedge clk);
                        timeout_cnt++;
                    end
                    if (timeout_cnt >= 200) begin
                        $display("[TB] ERROR: Timeout waiting for act_ready at batch %0d, NV %0d, chunk %0d",
                                 b, v, chunk);
                        current_test_ok = 0;
                        return;
                    end
                end
            end

            // Brief pause between batches
            act_valid   <= 1'b0;
            new_dot     <= 1'b0;
            last_nv     <= 1'b0;
            last_matmul <= 1'b0;
            @(posedge clk);
            repeat (5) @(posedge clk);

            $display("[TB]   Batch %0d complete", b);
        end

        // Wait for pipeline to drain
        repeat (50) @(posedge clk);
        $display("[TB] Activation streaming complete");
    endtask

    // =========================================================================
    // Golden Reference Storage
    // =========================================================================
    logic [15:0] golden_results [0:255];
    int golden_count;

    // =========================================================================
    // Load Golden Reference File
    // =========================================================================
    task automatic load_golden_reference(input string golden_name);
        string filename;
        integer fd;
        string line_str;
        logic [15:0] hex_val;
        int scan_result;
        int idx;

        filename = {HEX_PATH, golden_name, ".hex"};
        fd = $fopen(filename, "r");
        if (fd == 0) begin
            $display("[TB] WARNING: Cannot open golden file %s", filename);
            golden_count = 0;
            return;
        end

        idx = 0;
        while (!$feof(fd) && idx < 256) begin
            if ($fgets(line_str, fd)) begin
                scan_result = $sscanf(line_str, "%h", hex_val);
                if (scan_result == 1) begin
                    golden_results[idx] = hex_val;
                    idx++;
                end
            end
        end
        $fclose(fd);
        golden_count = idx;
        $display("[TB] Loaded %0d golden values from %s", golden_count, filename);
        if (golden_count > 0) begin
            $display("[TB]   First golden value: 0x%04x (%.6f)",
                     golden_results[0], fp16_to_float(golden_results[0]));
        end
    endtask

    // =========================================================================
    // Validate Results - Golden Comparison
    // =========================================================================
    // For C=1: Only bank0 is valid (all 128 elements via even wraddrs)
    //          bank1 contains garbage and should be ignored
    // For C>=2: Both banks contain valid paired-column results
    //
    // Result storage: collected_results[batch * 16 + col]
    //   col 0 = MLP0 bank0 (dout[0][15:0])
    //   col 1 = MLP0 bank1 (dout[0][31:16])
    //   col 2 = MLP1 bank0 ... etc
    task automatic validate_results(
        input string golden_name,
        input int num_batches,
        input int num_cols
    );
        int failures;
        int mismatches;
        logic [15:0] hw_result;
        logic [15:0] golden_val;
        int expected_results;
        real hw_float;
        real golden_float;
        real diff;
        real abs_diff;

        // Load golden reference
        load_golden_reference(golden_name);

        expected_results = num_batches * num_cols;
        failures = 0;
        mismatches = 0;

        $display("[TB] Validating %0d results against golden reference:", expected_results);

        for (int b = 0; b < num_batches; b++) begin
            for (int c = 0; c < num_cols; c++) begin
                int result_idx = b * NUM_COLUMNS + c;  // Results stored in 16-col format
                int golden_idx = b * num_cols + c;     // Golden stored per-test dimensions

                if (num_cols == 1) begin
                    // =========================================================================
                    // SINGLE COLUMN MODE (C=1): Only bank0 is valid
                    // =========================================================================
                    // bank0 contains the full 128-element dot product result
                    // bank1 contains garbage (read from odd wraddrs which are empty)
                    logic [15:0] bank0_val = collected_results[result_idx];
                    logic [15:0] bank1_val = collected_results[result_idx + 1];
                    real bank0_float = fp16_to_float(bank0_val);
                    real bank1_float = fp16_to_float(bank1_val);

                    // Get golden reference for this result
                    if (golden_idx < golden_count) begin
                        golden_val = golden_results[golden_idx];
                        golden_float = fp16_to_float(golden_val);
                        abs_diff = (bank0_float - golden_float);
                        if (abs_diff < 0) abs_diff = -abs_diff;
                        diff = abs_diff;
                        if (golden_float != 0.0) diff = abs_diff / ((golden_float < 0) ? -golden_float : golden_float);

                        $display("[TB]   Batch %0d: bank0=0x%04x (%.6f) golden=0x%04x (%.6f) diff=%.2f%%",
                                 b, bank0_val, bank0_float, golden_val, golden_float, diff * 100.0);

                        // Combined tolerance: 5% relative OR 0.001 absolute for near-zero values
                        if (diff > 0.05 && abs_diff > 0.001) begin
                            mismatches++;
                            $display("[TB]   ERROR: Result mismatch exceeds tolerance (rel=%.2f%%, abs=%.6f)",
                                     diff * 100.0, abs_diff);
                        end
                    end else begin
                        $display("[TB]   Batch %0d: bank0=0x%04x (%.6f) [no golden reference]",
                                 b, bank0_val, bank0_float);
                    end

                    // Report bank1 for debugging (but don't validate it)
                    $display("[TB]          bank1=0x%04x (%.6f) [IGNORED - garbage for C=1]",
                             bank1_val, bank1_float);

                    // Check for NaN or Inf (indicates computation error)
                    if (bank0_val[14:10] == 5'h1F) begin
                        failures++;
                        $display("[TB]   ERROR: NaN/Inf detected in bank0");
                    end

                end else begin
                    // =========================================================================
                    // MULTI-COLUMN MODE (C >= 2): Both banks valid
                    // =========================================================================
                    hw_result = collected_results[result_idx];
                    hw_float = fp16_to_float(hw_result);

                    if (golden_idx < golden_count) begin
                        golden_val = golden_results[golden_idx];
                        golden_float = fp16_to_float(golden_val);
                        abs_diff = (hw_float - golden_float);
                        if (abs_diff < 0) abs_diff = -abs_diff;
                        diff = abs_diff;
                        if (golden_float != 0.0) diff = abs_diff / ((golden_float < 0) ? -golden_float : golden_float);

                        $display("[TB]   Batch %0d Col %0d: 0x%04x (%.6f) golden=0x%04x (%.6f) diff=%.2f%%",
                                 b, c, hw_result, hw_float, golden_val, golden_float, diff * 100.0);

                        // Combined tolerance: 5% relative OR 0.001 absolute for near-zero values
                        if (diff > 0.05 && abs_diff > 0.001) begin
                            mismatches++;
                            $display("[TB]   ERROR: Result mismatch exceeds tolerance (rel=%.2f%%, abs=%.6f)",
                                     diff * 100.0, abs_diff);
                        end
                    end else begin
                        $display("[TB]   Batch %0d Col %0d: 0x%04x (%.6f) [no golden reference]",
                                 b, c, hw_result, hw_float);
                    end

                    if (hw_result[14:10] == 5'h1F) begin
                        failures++;
                        $display("[TB]   ERROR: NaN/Inf detected");
                    end
                end
            end
        end

        // Summary
        if (failures > 0 || mismatches > 0) begin
            $display("[TB] VALIDATION FAILED: %0d NaN/Inf errors, %0d mismatches", failures, mismatches);
            current_test_ok = 0;
        end else if (golden_count > 0) begin
            $display("[TB] VALIDATION PASSED: All %0d results match golden reference", expected_results);
        end else begin
            $display("[TB] VALIDATION WARNING: No golden reference available, basic checks passed");
        end
    endtask

    // FP16 to float conversion helper
    function automatic real fp16_to_float(input logic [15:0] fp16);
        logic sign_bit;
        int exp_val;
        int mant_val;
        real result;
        real mant_real;

        sign_bit = fp16[15];
        exp_val = fp16[14:10];
        mant_val = fp16[9:0];

        if (exp_val == 0 && mant_val == 0) begin
            return 0.0;
        end else if (exp_val == 0) begin
            // Subnormal
            mant_real = mant_val;
            result = (mant_real / 1024.0) * (2.0 ** (-14));
        end else if (exp_val == 31) begin
            // Inf/NaN - return large value
            result = 1.0e10;
        end else begin
            // Normal: value = (1 + mant/1024) * 2^(exp-15)
            mant_real = mant_val;
            result = (1.0 + mant_real / 1024.0) * (2.0 ** (exp_val - 15));
        end

        if (sign_bit) result = -result;
        return result;
    endfunction

    // Float to FP16 conversion helper
    function automatic logic [15:0] float_to_fp16(input real val);
        logic sign_bit;
        int exp_int;
        real mant_float;
        logic [4:0] exp_out;
        logic [9:0] mant_out;
        real abs_val;

        if (val == 0.0) return 16'h0000;

        sign_bit = (val < 0.0);
        abs_val = sign_bit ? -val : val;

        // Find exponent by normalizing to [1,2)
        exp_int = 0;
        mant_float = abs_val;

        while (mant_float >= 2.0 && exp_int < 16) begin
            mant_float = mant_float / 2.0;
            exp_int = exp_int + 1;
        end

        while (mant_float < 1.0 && exp_int > -15) begin
            mant_float = mant_float * 2.0;
            exp_int = exp_int - 1;
        end

        // Convert to biased exponent and mantissa
        if (exp_int > 15) begin
            // Overflow - return max normal
            exp_out = 5'd30;
            mant_out = 10'h3FF;
        end else if (exp_int < -14) begin
            // Underflow - flush to zero
            exp_out = 5'd0;
            mant_out = 10'd0;
        end else begin
            exp_out = exp_int + 15;
            mant_out = int'((mant_float - 1.0) * 1024.0);
        end

        return {sign_bit, exp_out, mant_out};
    endfunction

    // =========================================================================
    // Run Single Test
    // =========================================================================
    task automatic run_test(input test_config_t cfg);
        $display("\n========================================");
        $display("[TEST] %s (B=%0d, C=%0d, V=%0d)", cfg.name, cfg.B, cfg.C, cfg.V);
        $display("========================================");

        // Reset collection state
        num_results_collected = 0;
        current_test_ok = 1;
        for (int i = 0; i < 1024; i++) begin
            collected_results[i] = 16'd0;
        end

        // Soft reset via deassert/assert rstn
        // Extended reset duration to ensure all MLP internal state is cleared
        rstn = 0;
        repeat (20) @(posedge clk);  // Extended from 5 to 20 cycles
        rstn = 1;
        repeat (20) @(posedge clk);  // Extended from 5 to 20 cycles

        // Phase 1: Load weights
        load_weights(cfg.C, cfg.V);

        // Initialize unused columns to zero (skip for C=1 since we use direct address mode)
        // For C=1, bank1 reads garbage from odd addresses, but we ignore it in validation
        if (cfg.C < NUM_COLUMNS && cfg.C > 1) begin
            init_unused_columns(cfg.C, cfg.V);
        end

        // Phase 2: Stream activations and compute
        stream_activations(cfg.B, cfg.V);

        // Phase 3: Validate
        validate_results(cfg.name, cfg.B, cfg.C);

        // Update test counters
        tests_run++;
        if (current_test_ok) tests_passed++;
    endtask

    // =========================================================================
    // Main Test Sequence
    // =========================================================================
    initial begin
        // Signal Initialization
        rstn          = 0;
        rd_base_addr  = 10'd0;
        wt_wr_en      = 0;
        wt_mlp_sel    = 3'd0;
        wt_wr_addr    = 10'd0;
        wt_exp        = 8'd0;
        wt_man        = 256'd0;
        act_valid     = 0;
        new_dot       = 0;
        last_nv       = 0;
        last_matmul   = 0;
        result_fifo_full = 0;  // Never assert full - always accept results
        nv_left_man   = 256'd0;
        nv_left_exp   = 8'd0;

        tests_run     = 0;
        tests_passed  = 0;
        current_test_ok = 1;
        num_results_collected = 0;

        for (int i = 0; i < 1024; i++) begin
            collected_results[i] = 16'd0;
        end

        // Wait for hex files to load
        repeat (10) @(posedge clk);

        // Release reset
        rstn = 1;
        repeat (10) @(posedge clk);

        $display("\n========================================");
        $display("comp_MLPStack Testbench");
        $display("(Golden Reference Validation)");
        $display("========================================");
        $display("Configuration:");
        $display("  NUM_MLPS = %0d", NUM_MLPS);
        $display("  NUM_STACKS = %0d", NUM_STACKS);
        $display("  NUM_COLUMNS = %0d", NUM_COLUMNS);
        $display("  CYCLES_PER_NV = %0d", CYCLES_PER_NV);
        $display("");

        // Run test suite
        foreach (test_suite[i]) begin
            run_test(test_suite[i]);
        end

        // Summary
        $display("\n========================================");
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
        $display("[TB] ERROR: Testbench timeout!");
        $finish;
    end

endmodule
