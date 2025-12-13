// ------------------------------------------------------------------
// Testbench for Engine Top Module (MS2.0 with Integrated Tile BRAM)
//
// Purpose: Complete testbench for engine_top with direct FIFO interface
// Features:
//  - Instantiates engine_top (DUT with integrated tile_bram in compute_engine)
//  - Instantiates tb_memory_model (GDDR6 emulation)
//  - Test sequence: FETCH → DISPATCH → WAIT_DISPATCH → TILE → WAIT_TILE
//  - Result verification with FP16 output checking
//
// Architecture (Three-Level Memory Hierarchy):
//  GDDR6 model → [FETCH] → dispatcher_bram (L2) → [DISPATCH] →
//    tile_bram (L1, inside compute_engine) → [TILE] → result_fifo
//
// Test Flow:
//  1. Reset system
//  2. Load commands into cmd_fifo
//  3. Wait for commands to execute
//  4. Read results from result_fifo
//  5. Verify FP16 format and values
//
// Author: MS2.0 FIFO Architecture Integration + Tile BRAM Integration
// Date: Mon Oct 27 2025
// ------------------------------------------------------------------

`timescale 1ps/1ps

`include "nap_interfaces.svh"

// Memory model latency configuration (from Makefile)
`ifndef LATENCY_CYCLES
    `define LATENCY_CYCLES 0  // Default: 0 for fast simulation
`endif

module tb_engine_top;

    import gemm_pkg::*;
    // NOTE: Command generation tasks defined inline below, no separate package needed

    // ===================================================================
    // Testbench Parameters
    // ===================================================================
    localparam CLK_PERIOD = 10000;  // 10000ps = 10ns = 100MHz
    localparam TGT_DATA_WIDTH = 256;
    localparam AXI_ADDR_WIDTH = 42;  // 42-bit for GDDR6 NoC addressing
    localparam GDDR6_PAGE_ID = 9'd0;  // Match ACX_GDDR6_SPACE for DMA compatibility
    localparam NUM_TILES = 8;


    // ===================================================================
    // Clock and Reset
    // ===================================================================
    logic clk;
    logic reset_n;

    initial begin
        clk = 1'b0;
        $display("========================================");
        $display("TB_ENGINE_TOP: COMMAND FORMAT FIX APPLIED - VERSION 2.9.1");
        $display("========================================");
        forever #(CLK_PERIOD/2) clk = ~clk;
    end

    initial begin
        reset_n = 1'b0;
        repeat (5) @(posedge clk);
        reset_n = 1'b1;
        $display("[TB] Reset released at time %0t", $time);
    end

    // ===================================================================
    // DUT Interface Signals
    // ===================================================================
    // Command FIFO interface
    logic [31:0]  cmd_fifo_wdata;
    logic         cmd_fifo_wen;
    logic         cmd_fifo_full;
    logic         cmd_fifo_afull;
    logic [12:0]  cmd_fifo_count;

    // 256-bit Result interface (MLP mode - 16 × FP16 per cycle)
    logic [255:0] result_256_data;
    logic         result_256_valid;
    logic [8:0]   result_256_wr_addr;

    // Flow control monitoring
    logic         result_almost_full;

    // Flow control - tied low for now (no backpressure)
    assign result_almost_full = 1'b0;

    // Status signals
    logic         engine_busy;
    logic [3:0]   mc_state;
    logic [3:0]   mc_state_next;
    logic [3:0]   dc_state;
    logic [3:0]   ce_state;
    logic [cmd_op_width_gp-1:0] last_opcode;
    logic [9:0]   bram_wr_count;
    logic [15:0]  result_count;
    
    // Probe signals (pipeline debugging)
    logic [15:0]  probe_disp_data;
    logic         probe_disp_valid;
    logic [15:0]  probe_rowbram_data;
    logic         probe_rowbram_valid;
    logic [23:0]  probe_fp24_data;
    logic         probe_fp24_valid;
    logic [15:0]  probe_fp16_data;
    logic         probe_fp16_valid;
    
    // Captured probe values (hold on valid)
    logic [15:0]  captured_probe_0 = 16'd0;  // dispatcher_bram data
    logic [15:0]  captured_probe_1 = 16'd0;  // row_bram data
    logic [23:0]  captured_probe_2 = 24'd0;  // FP24 compute result
    logic [15:0]  captured_probe_3 = 16'd0;  // FP16 final result

    // MLP mode (always enabled in this version)

    // ===================================================================
    // AXI Interface
    // ===================================================================
    t_AXI4 #(
        .DATA_WIDTH (TGT_DATA_WIDTH),
        .ADDR_WIDTH (AXI_ADDR_WIDTH),
        .LEN_WIDTH  (8),      // 8-bit ARLEN/AWLEN (AXI4 supports up to 256 beats)
        .ID_WIDTH   (8)       // 8-bit ARID/AWID
    ) axi_ddr_if();

    // ===================================================================
    // DUT Instantiation
    // ===================================================================
    engine_top #(
        .GDDR6_PAGE_ID      (GDDR6_PAGE_ID),
        .TGT_DATA_WIDTH     (TGT_DATA_WIDTH),
        .AXI_ADDR_WIDTH     (AXI_ADDR_WIDTH),
        .NUM_TILES          (NUM_TILES)
    ) u_dut (
        .i_clk                  (clk),
        .i_reset_n              (reset_n),

        // Command FIFO interface
        .i_cmd_fifo_wdata       (cmd_fifo_wdata),
        .i_cmd_fifo_wen         (cmd_fifo_wen),
        .o_cmd_fifo_full        (cmd_fifo_full),
        .o_cmd_fifo_afull       (cmd_fifo_afull),
        .o_cmd_fifo_count       (cmd_fifo_count),

        // 256-bit Result interface (MLP mode)
        .o_result_256_data      (result_256_data),
        .o_result_256_valid     (result_256_valid),
        .o_result_256_wr_addr   (result_256_wr_addr),

        // AXI GDDR6 interface
        .nap_axi                (axi_ddr_if.initiator),

        // Flow control
        .i_result_almost_full   (result_almost_full),

        // Status
        .o_engine_busy          (engine_busy),
        .o_mc_state             (mc_state),
        .o_mc_state_next        (mc_state_next),
        .o_dc_state             (dc_state),
        .o_ce_state             (ce_state),
        .o_last_opcode          (last_opcode),

        // Debug
        .o_bram_wr_count        (bram_wr_count),
        .o_result_count         (result_count),
        // Probe outputs (pipeline debugging)
        .o_probe_disp_data      (probe_disp_data),
        .o_probe_disp_valid     (probe_disp_valid),
        .o_probe_rowbram_data   (probe_rowbram_data),
        .o_probe_rowbram_valid  (probe_rowbram_valid),
        .o_probe_fp24_data      (probe_fp24_data),
        .o_probe_fp24_valid     (probe_fp24_valid),
        .o_probe_fp16_data      (probe_fp16_data),
        .o_probe_fp16_valid     (probe_fp16_valid)
    );

    // ===================================================================
    // Result BRAM Model - Direct 256-bit capture from MLP
    // ===================================================================
    // First 4 results (for quick checking)
    logic [15:0]  result_0, result_1, result_2, result_3;

    // BRAM model for results (512 lines × 256 bits = 8192 FP16 results)
    logic [255:0] result_bram_model [0:511];
    int           result_bram_lines_written;

    // BRAM Model - Captures 256-bit results directly from MLP
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            result_bram_lines_written <= 0;
            for (int i = 0; i < 512; i++) begin
                result_bram_model[i] <= 256'h0;
            end
        end else begin
            // MLP mode: Direct 256-bit writes from compute_engine_mlp
            if (result_256_valid) begin
                result_bram_model[result_256_wr_addr] <= result_256_data;
                result_bram_lines_written <= result_bram_lines_written + 1;
                $display("[TB_BRAM_MLP] @%0t WRITE: addr=%0d, data=0x%064x",
                         $time, result_256_wr_addr, result_256_data);
            end
        end
    end

    // Extract first 4 results for quick checking (from first BRAM line)
    assign result_0 = result_bram_model[0][15:0];
    assign result_1 = result_bram_model[0][31:16];
    assign result_2 = result_bram_model[0][47:32];
    assign result_3 = result_bram_model[0][63:48];

    // ===================================================================
    // Probe Capture Logic - Capture pipeline stages for debugging
    // ===================================================================
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            captured_probe_0 <= 16'd0;
            captured_probe_1 <= 16'd0;
            captured_probe_2 <= 24'd0;
            captured_probe_3 <= 16'd0;
        end else begin
            // Capture each probe on its valid signal
            if (probe_disp_valid) begin
                captured_probe_0 <= probe_disp_data;
                $display("[PROBE_0] @%0t DISP_BRAM: data=0x%04x", $time, probe_disp_data);
            end
            if (probe_rowbram_valid) begin
                captured_probe_1 <= probe_rowbram_data;
                $display("[PROBE_1] @%0t ROW_BRAM: data=0x%04x", $time, probe_rowbram_data);
            end
            if (probe_fp24_valid) begin
                captured_probe_2 <= probe_fp24_data;
                $display("[PROBE_2] @%0t FP24: data=0x%06x", $time, probe_fp24_data);
            end
            if (probe_fp16_valid) begin
                captured_probe_3 <= probe_fp16_data;
                $display("[PROBE_3] @%0t FP16: data=0x%04x", $time, probe_fp16_data);
            end
        end
    end

    // Backward compatibility signals (stubbed for MLP-only mode)
    // These were used by result_fifo_to_simple_bram packer
    logic [12:0]  result_rd_ptr = 13'b0;
    logic [12:0]  result_wr_ptr;
    logic [13:0]  result_used_entries;
    logic         result_empty;
    logic         result_bram_almost_full;
    logic [14:0]  result_fifo_count = 15'b0;

    // Compute from result_bram_lines_written (each line = 16 FP16 results)
    assign result_wr_ptr = result_bram_lines_written * 16;
    assign result_used_entries = result_bram_lines_written * 16;
    assign result_empty = (result_bram_lines_written == 0);
    assign result_bram_almost_full = (result_bram_lines_written >= 496);  // 512-16

    // ===================================================================
    // Memory Model Instantiation
    // ===================================================================
    logic [31:0] mem_outstanding_count;
    logic [31:0] mem_total_ar_received;
    logic [31:0] mem_total_r_issued;

    tb_memory_model_realistic #(
        .DATA_WIDTH         (TGT_DATA_WIDTH),
        .ADDR_WIDTH         (AXI_ADDR_WIDTH),
        .LINES_PER_BLOCK    (528),
        .NUM_BLOCKS         (2),
        .LATENCY_CYCLES     (`LATENCY_CYCLES),  // Configurable from Makefile (default: 0)
        .MAX_OUTSTANDING    (32),               // Support 32 outstanding ARs (realistic GDDR6)
        .VERBOSITY          (0)                 // Quiet mode for clean test output
    ) u_memory_model (
        .i_clk              (clk),
        .i_reset_n          (reset_n),

        // AXI interface
        .axi_mem_if         (axi_ddr_if.responder),

        // Debug/Statistics
        .o_outstanding_count  (mem_outstanding_count),
        .o_total_ar_received  (mem_total_ar_received),
        .o_total_r_issued     (mem_total_r_issued)
    );

    // ===================================================================
    // Test Control Variables
    // ===================================================================
    integer cmd_idx;
    integer result_idx;
    integer timeout_count;
    integer watchdog;
    
    // Test status
    integer total_tests = 0;
    integer passed_tests = 0;
    integer failed_tests = 0;

    // ===================================================================
    // Golden Reference Storage
    // ===================================================================
    logic [15:0] golden_results [0:16383];  // FP16 golden references
    integer golden_file;
    integer scan_result;
    string golden_filename;

    // ===================================================================
    // Test Configuration Array
    // ===================================================================
    typedef struct {
        int B;
        int C;
        int V;
        logic [23:0] col_en;  // Column enable mask (NEW: for multi-tile testing)
        string name;
    } test_config_t;

    // Test configurations: C > 16 tests (C must be divisible by 16)
    test_config_t test_configs[] = '{
        // Basic MLP tests (C = 16, baseline)
        '{B: 4,  C: 16,  V: 8, col_en: 24'h000001, name: "B4_C16_V8"},
        '{B: 8,  C: 16,  V: 4, col_en: 24'h000001, name: "B8_C16_V4"},
        '{B: 16, C: 16,  V: 8, col_en: 24'h000001, name: "B16_C16_V8"},

        // C > 16 tests (column group iteration)
        '{B: 4,  C: 32,  V: 4, col_en: 24'h000001, name: "B4_C32_V4"},
        '{B: 8,  C: 32,  V: 2, col_en: 24'h000001, name: "B8_C32_V2"},
        '{B: 8,  C: 64,  V: 2, col_en: 24'h000001, name: "B8_C64_V2"},
        '{B: 2,  C: 128, V: 1, col_en: 24'h000001, name: "B2_C128_V1"}
    };

    // ===================================================================
    // Main Test Sequence
    // ===================================================================
    initial begin
        $display("\n================================================================================");
        $display("TB: MS2.0 GEMM Engine Top Testbench - FIFO Interface");
        $display("================================================================================\n");

        // Initialize signals
        cmd_fifo_wdata = 32'h0;
        cmd_fifo_wen = 1'b0;
        // MLP mode: Results go directly to 256-bit output, no FIFO packer needed

        // Wait for reset to complete
        wait (reset_n == 1'b1);
        repeat (10) @(posedge clk);

        // Run all test configurations
        foreach (test_configs[i]) begin
            // Debug: Capture BRAM state before reset (for B4_C4_V4 analysis)
            if (i > 0 && i == 3) begin  // After test 3 (B4_C4_V4), before reset for test 4
                $display("[TB_DEBUG] @%0t BEFORE RESET: BRAM[0] = 0x%064x", $time, result_bram_model[0]);
                $display("[TB_DEBUG] @%0t BEFORE RESET: BRAM lines written counter = %0d", $time, result_bram_lines_written);
            end

            // Reset engine between tests to ensure clean state
            if (i > 0) begin
                reset_n = 1'b0;
                result_rd_ptr = 13'b0;  // Reset circular buffer read pointer
                repeat (10) @(posedge clk);
                reset_n = 1'b1;
                repeat (10) @(posedge clk);
                $display("[TB] Reset between tests completed at time %0t (rd_ptr reset to 0)", $time);
            end

            run_single_test(
                test_configs[i].B,
                test_configs[i].C,
                test_configs[i].V,
                test_configs[i].col_en,
                test_configs[i].name
            );
            repeat (100) @(posedge clk);  // Delay between tests
        end

        // Print summary
        $display("\n================================================================================");
        $display("TEST SUMMARY");
        $display("================================================================================");
        $display("Total Tests: %0d", total_tests);
        $display("Passed:      %0d", passed_tests);
        $display("Failed:      %0d", failed_tests);
        if (failed_tests == 0) begin
            $display("STATUS: ALL TESTS PASSED");
        end else begin
            $display("STATUS: %0d TESTS FAILED", failed_tests);
        end
        $display("================================================================================\n");

        $finish;
    end

    // ===================================================================
    // Task: Run Single Test
    // ===================================================================
    task automatic run_single_test(
        input int config_B,
        input int config_C,
        input int config_V,
        input logic [23:0] config_col_en,
        input string test_name
    );
        logic [31:0] cmd_sequence [0:511];
        integer num_commands;
        integer expected_results;
        integer expected_bram_lines;  // For MLP mode: ceil(expected_results / 16)
        integer results_seen;
        integer mismatches;
        integer idx;
        integer num_cols_enabled;    // For timing comparison

        // Timing measurements
        longint start_time, end_time;
        longint fetch_left_start, fetch_left_end, fetch_left_cycles;
        longint disp_left_start, disp_left_end, disp_left_cycles;
        longint fetch_right_start, fetch_right_end, fetch_right_cycles;
        longint disp_right_start, disp_right_end, disp_right_cycles;
        longint tile_start, tile_end, tile_cycles;
        longint total_cycles;

        total_tests++;

        $display("\n[TB] ====================================================================");
        $display("[TB] TEST %0d: Running configuration %s (B=%0d, C=%0d, V=%0d)",
                 total_tests, test_name, config_B, config_C, config_V);
        $display("[TB] ====================================================================");

        // Load golden reference (ALL tests validate against golden files)
        golden_filename = $sformatf("/home/dev/Dev/elastix_gemm/hex/golden_%s.hex", test_name);
        golden_file = $fopen(golden_filename, "r");
        if (golden_file == 0) begin
            $display("[TB] ERROR: Cannot open golden reference file: %s", golden_filename);
            failed_tests++;
            return;
        end

        // Load golden results
        idx = 0;
        while (!$feof(golden_file) && idx < 16384) begin
            scan_result = $fscanf(golden_file, "%h\n", golden_results[idx]);
            if (scan_result == 1) idx++;
        end
        $fclose(golden_file);
        $display("[TB] Loaded %0d golden results from %s (col_en=0x%06x)", idx, golden_filename, config_col_en);

        // Generate command sequence
        build_test_sequence(config_B, config_C, config_V, config_col_en, cmd_sequence, num_commands);
        $display("[TB] Generated %0d commands for col_en=0x%06x", num_commands, config_col_en);

        // Start overall timing
        start_time = $time;
        
        // Submit commands to FIFO with per-stage timing
        // Commands are organized as:
        // [0-3]: FETCH LEFT
        // [4-7]: DISPATCH LEFT
        // [8-11]: WAIT_DISPATCH LEFT
        // [12-15]: FETCH RIGHT
        // [16-19]: DISPATCH RIGHT
        // [20-23]: WAIT_DISPATCH RIGHT
        // [24-27]: TILE
        // [28-31]: WAIT_TILE
        
        // ========== FETCH LEFT (4 words) ==========
        fetch_left_start = $time;
        for (cmd_idx = 0; cmd_idx < 4; cmd_idx++) begin
            cmd_fifo_wdata = cmd_sequence[cmd_idx];
            cmd_fifo_wen = 1'b1;
            @(posedge clk);
        end
        cmd_fifo_wen = 1'b0;
        
        // ========== DISPATCH LEFT + WAIT (8 words) ==========
        disp_left_start = $time;
        for (cmd_idx = 4; cmd_idx < 12; cmd_idx++) begin
            cmd_fifo_wdata = cmd_sequence[cmd_idx];
            cmd_fifo_wen = 1'b1;
            @(posedge clk);
        end
        cmd_fifo_wen = 1'b0;
        
        // Wait for DISPATCH LEFT to complete (monitor engine_busy and packer draining)
        while (engine_busy || (result_used_entries > 0)) @(posedge clk);
        disp_left_end = $time;
        disp_left_cycles = (disp_left_end - disp_left_start) / CLK_PERIOD;
        fetch_left_end = disp_left_end;  // FETCH LEFT completes when DISPATCH LEFT completes
        fetch_left_cycles = (fetch_left_end - fetch_left_start) / CLK_PERIOD;
        
        // ========== FETCH RIGHT (4 words) ==========
        fetch_right_start = $time;
        for (cmd_idx = 12; cmd_idx < 16; cmd_idx++) begin
            cmd_fifo_wdata = cmd_sequence[cmd_idx];
            cmd_fifo_wen = 1'b1;
            @(posedge clk);
        end
        cmd_fifo_wen = 1'b0;
        
        // ========== DISPATCH RIGHT + WAIT (8 words) ==========
        disp_right_start = $time;
        for (cmd_idx = 16; cmd_idx < 24; cmd_idx++) begin
            cmd_fifo_wdata = cmd_sequence[cmd_idx];
            cmd_fifo_wen = 1'b1;
            @(posedge clk);
        end
        cmd_fifo_wen = 1'b0;
        
        // Wait for DISPATCH RIGHT to complete (monitor engine_busy and packer draining)
        while (engine_busy || (result_used_entries > 0)) @(posedge clk);
        disp_right_end = $time;
        disp_right_cycles = (disp_right_end - disp_right_start) / CLK_PERIOD;
        fetch_right_end = disp_right_end;  // FETCH RIGHT completes when DISPATCH RIGHT completes
        fetch_right_cycles = (fetch_right_end - fetch_right_start) / CLK_PERIOD;
        
        // ========== TILE + WAIT (8 words) ==========
        tile_start = $time;
        for (cmd_idx = 24; cmd_idx < 32; cmd_idx++) begin
            cmd_fifo_wdata = cmd_sequence[cmd_idx];
            cmd_fifo_wen = 1'b1;
            @(posedge clk);
        end
        cmd_fifo_wen = 1'b0;

        // ========== READOUT (4 words) ==========
        for (cmd_idx = 32; cmd_idx < 36; cmd_idx++) begin
            cmd_fifo_wdata = cmd_sequence[cmd_idx];
            cmd_fifo_wen = 1'b1;
            @(posedge clk);
        end
        cmd_fifo_wen = 1'b0;
        $display("[TB] All commands submitted to FIFO");

        // Continuously drain result FIFO as results become available
        // This prevents FIFO backpressure deadlock for large result sets
        expected_results = config_B * config_C;
        $display("[TB] Draining results as they arrive (expecting %0d results, B=%0d x C=%0d)...", 
                 expected_results, config_B, config_C);
        
        timeout_count = 0;
        watchdog = 100000;  // 1ms timeout
        results_seen = 0;
        mismatches = 0;

        // Wait for direct 256-bit writes to complete
        // Expected BRAM lines = ceil(expected_results / 16)
        expected_bram_lines = (expected_results + 15) / 16;
        $display("[TB] Waiting for %0d BRAM lines (= ceil(%0d/16))", expected_bram_lines, expected_results);

        while ((result_bram_lines_written < expected_bram_lines) && (timeout_count < watchdog)) begin
            @(posedge clk);
            timeout_count++;
        end

        if (timeout_count >= watchdog) begin
            $display("[TB] ERROR: Result timeout! Expected %0d lines, got %0d",
                     expected_bram_lines, result_bram_lines_written);
        end else begin
            $display("[TB] All results received after %0d cycles: %0d BRAM lines",
                     timeout_count, result_bram_lines_written);
        end

        // Wait for BRAM write to propagate (always_ff needs 1 cycle)
        @(posedge clk);
        @(posedge clk);  // Additional safety margin

        // Note: Partial BRAM line flush removed - no longer needed with simplified reset
        // The async reset (reset_n) now handles all buffer clearing
        // For tests with < 16 results, they remain in the packing buffer until next result or reset
        $display("[TB] BRAM lines written: %0d", result_bram_lines_written);

        // Read and verify packed results from BRAM model
        // NOTE: For C > 16, results need reordering:
        //   - Hardware outputs: Group 0 (all B batches × 16 cols), Group 1, ...
        //   - Golden file: Batch-major (batch 0 all cols, batch 1 all cols, ...)
        begin
            int num_col_groups;
            int hw_idx;
            int batch_idx, col_idx, group_idx, col_within_group, pulse_idx;
            logic [15:0] fp16_hw;
            logic [15:0] golden;
            int diff;
            int bram_line;
            int bram_pos;
            int tolerance_lsb;
            real golden_mag;
            logic is_golden_denormal;
            logic is_hw_zero;

            num_col_groups = (config_C + 15) / 16;  // Number of column groups

            for (int result_idx = 0; result_idx < expected_results; result_idx++) begin

                // For C > 16, we need to map golden index to hardware BRAM index
                // Golden order: result[batch * C + col] (batch-major)
                // HW order: For each group g, for each batch b: 16 results
                //   hw_idx = (group * B + batch) * 16 + col_within_group

                if (num_col_groups > 1) begin
                // Multi-group case: apply reordering
                batch_idx = result_idx / config_C;
                col_idx = result_idx % config_C;
                group_idx = col_idx / 16;
                col_within_group = col_idx % 16;
                pulse_idx = group_idx * config_B + batch_idx;
                hw_idx = pulse_idx * 16 + col_within_group;
            end else begin
                // Single group (C <= 16): no reordering needed
                hw_idx = result_idx;
            end

            // Calculate BRAM address from hw_idx
            bram_line = hw_idx / 16;
            bram_pos = hw_idx % 16;

            // Extract FP16 value from packed BRAM line
            fp16_hw = result_bram_model[bram_line][bram_pos*16 +: 16];
            golden = golden_results[result_idx];

            // Debug: Show what we read from BRAM for B4_C4_V4 test
            if (expected_results == 16 && result_idx < 4) begin
                $display("[TB_VERIFY] @%0t READ: result[%0d] from BRAM[%0d][%0d] = 0x%04x (full line = 0x%064x), golden = 0x%04x",
                        $time, result_idx, bram_line, bram_pos, fp16_hw, result_bram_model[bram_line], golden);
            end

            // Check for X/Z states (uninitialized values)
            if ($isunknown(fp16_hw)) begin
                $display("[TB] ERROR: hw=0x%04x contains X/Z (uninitialized) at result[%0d] (BRAM[%0d][%0d])",
                        fp16_hw, result_idx, bram_line, bram_pos);
                mismatches++;
            end else begin
                // Golden comparison: 5% relative tolerance or ±50 LSB minimum
                // Also handle denormal flush-to-zero: hardware outputs ±0 for denormals
                diff = (fp16_hw > golden) ? fp16_hw - golden : golden - fp16_hw;

                golden_mag = (golden & 16'h7FFF);  // Absolute value (ignore sign)
                tolerance_lsb = (golden_mag * 0.05 > 50) ? int'(golden_mag * 0.05) : 50;

                // Denormal golden values (exp=0, mantissa!=0) may flush to zero
                is_golden_denormal = (golden[14:10] == 5'b0) && (golden[9:0] != 10'b0);
                is_hw_zero = (fp16_hw == 16'h0000) || (fp16_hw == 16'h8000);

                if (is_golden_denormal && is_hw_zero) begin
                    // Flush-to-zero is acceptable for denormals
                    if (result_idx < 10 || (result_idx >= expected_results - 5)) begin
                        $display("[TB] MATCH[%0d]: hw=0x%04x golden=0x%04x (denormal flush-to-zero) (BRAM[%0d][%0d])",
                                result_idx, fp16_hw, golden, bram_line, bram_pos);
                    end
                end else if (diff > tolerance_lsb) begin
                    $display("[TB] MISMATCH[%0d]: hw=0x%04x golden=0x%04x diff=%0d tol=%0d (BRAM[%0d][%0d])",
                            result_idx, fp16_hw, golden, diff, tolerance_lsb, bram_line, bram_pos);
                    mismatches++;
                end else if (result_idx < 10 || (result_idx >= expected_results - 5)) begin
                    $display("[TB] MATCH[%0d]: hw=0x%04x golden=0x%04x diff=%0d (BRAM[%0d][%0d])",
                            result_idx, fp16_hw, golden, diff, bram_line, bram_pos);
                end
            end

                results_seen++;

                // Update rd_ptr every 16 results (one BRAM line consumed)
                if ((result_idx + 1) % 16 == 0) begin
                    result_rd_ptr = result_rd_ptr + 16;
                end
            end  // end for loop
        end  // end of begin block with variable declarations

        $display("[TB] Final circular buffer state: wr_ptr=%0d, rd_ptr=%0d, used_entries=%0d",
                 result_wr_ptr, result_rd_ptr, result_used_entries);
        
        // End timing for TILE stage (when all results collected)
        tile_end = $time;
        tile_cycles = (tile_end - tile_start) / CLK_PERIOD;
        end_time = $time;
        total_cycles = (end_time - start_time) / CLK_PERIOD;

        // Report timing for multi-column configurations
        num_cols_enabled = $countones(config_col_en[7:0]);
        $display("[TB_TIMING] Test %s: MATMUL completed in %0d cycles with %0d columns enabled (col_en=0x%06x)",
                 test_name, tile_cycles, num_cols_enabled, config_col_en);

        // Circular Buffer Status Monitoring
        $display("[TB] ====================================================================");
        $display("[TB] Circular Buffer Status:");
        $display("[TB]   wr_ptr: %0d", result_wr_ptr);
        $display("[TB]   rd_ptr: %0d", result_rd_ptr);
        $display("[TB]   used_entries: %0d / 8192 (%.1f%% full)",
                 result_used_entries, (result_used_entries * 100.0) / 8192.0);
        $display("[TB]   empty: %b", result_empty);
        $display("[TB]   almost_full: %b (threshold: 7936)", result_bram_almost_full);
        $display("[TB]   BRAM lines written: %0d", result_bram_lines_written);
        $display("[TB]   Results collected: %0d", results_seen);
        $display("[TB] ====================================================================");

        // MLP mode: Results written directly to BRAM via 256-bit interface
        $display("[TB] MLP Result Path:");
        $display("[TB]   Direct 256-bit writes: %0d lines", result_bram_lines_written);
        $display("[TB]   FP16 results captured: %0d", result_bram_lines_written * 16);
        
        // ===================================================================
        // TIMING REPORT
        // ===================================================================
        $display("\n[TB] ====================================================================");
        $display("[TB] TIMING BREAKDOWN FOR %s (B=%0d, C=%0d, V=%0d)", test_name, config_B, config_C, config_V);
        $display("[TB] ====================================================================");
        $display("[TB] FETCH LEFT:      %8d cycles (%6.2f%% of total)", 
                 fetch_left_cycles, (fetch_left_cycles * 100.0) / total_cycles);
        $display("[TB] DISPATCH LEFT:   %8d cycles (%6.2f%% of total)", 
                 disp_left_cycles, (disp_left_cycles * 100.0) / total_cycles);
        $display("[TB] FETCH RIGHT:     %8d cycles (%6.2f%% of total)", 
                 fetch_right_cycles, (fetch_right_cycles * 100.0) / total_cycles);
        $display("[TB] DISPATCH RIGHT:  %8d cycles (%6.2f%% of total)", 
                 disp_right_cycles, (disp_right_cycles * 100.0) / total_cycles);
        $display("[TB] TILE + RESULTS:  %8d cycles (%6.2f%% of total)", 
                 tile_cycles, (tile_cycles * 100.0) / total_cycles);
        $display("[TB] --------------------------------------------------------------------");
        $display("[TB] TOTAL:           %8d cycles (%.2f us @ 100MHz)", 
                 total_cycles, (total_cycles * CLK_PERIOD) / 1000.0);
        $display("[TB] ====================================================================\n");

        // Theck both count and golden match
        if (mismatches == 0 && results_seen == expected_results) begin
            $display("[TB] PASS: %s - All %0d results matched!", test_name, results_seen);
            passed_tests++;
        end else begin
            $display("[TB] FAIL: %s - %0d mismatches, %0d/%0d results",
                        test_name, mismatches, results_seen, expected_results);
            failed_tests++;
        end

    endtask

    // ===================================================================
    // Task: Build Test Sequence
    // ===================================================================
    task automatic build_test_sequence(
        input int B,
        input int C,
        input int V,
        input logic [23:0] col_en,
        output logic [31:0] cmd_seq [0:511],
        output integer num_cmds
    );
        logic [31:0] fetch_left_cmd [0:3];
        logic [31:0] fetch_right_cmd [0:3];
        logic [31:0] disp_cmd [0:3];
        logic [31:0] wait_disp_cmd [0:3];
        logic [31:0] tile_cmd [0:3];
        logic [31:0] wait_tile_cmd [0:3];
        logic [31:0] readout_cmd [0:3];

        integer idx = 0;
        integer num_enabled_tiles;
        integer dim_c_per_tile;

        // ===================================================================
        // LEFT MATRIX FETCH AND DISPATCH (disp_right=0)
        // ===================================================================
        // FETCH left matrix (start_addr = 0, fetch_right = 0)
        generate_fetch_command(0, 0, 528, 1'b0, fetch_left_cmd);
        $display("[TB] FETCH LEFT: cmd[0]=0x%08x, cmd[1]=0x%08x, cmd[2]=0x%08x, cmd[3]=0x%08x",
                 fetch_left_cmd[0], fetch_left_cmd[1], fetch_left_cmd[2], fetch_left_cmd[3]);
        cmd_seq[idx++] = fetch_left_cmd[0];
        cmd_seq[idx++] = fetch_left_cmd[1];
        cmd_seq[idx++] = fetch_left_cmd[2];
        cmd_seq[idx++] = fetch_left_cmd[3];

        // DISPATCH LEFT: dispatcher_bram (left) → tile_bram (left)
        // Multi-tile: Use BROADCAST mode for left matrix (activations replicated to all tiles)
        generate_disp_command(
            1,              // id
            B * V,          // man_nv_cnt: Total Native Vectors = B × V
            V,              // ugd_vec_size: NVs per UGD vector (matches test V parameter)
            16'd0,          // tile_addr: Start of tile BRAM
            1'b0,           // man_4b: 8-bit mantissa mode
            col_en,         // col_en: Column enable mask (parameterized)
            5'd0,           // col_start: Distribution starts at column 0
            1'b0,           // disp_right: LEFT dispatch (0=left)
            1'b1,           // broadcast: BROADCAST mode for left (activations)
            disp_cmd
        );
        $display("[TB] DISPATCH LEFT: man_nv_cnt=%0d (B×V=%0d×%0d), ugd_vec_size=%0d, broadcast=1, col_en=0x%06x", B*V, B, V, V, col_en);
        cmd_seq[idx++] = disp_cmd[0];
        cmd_seq[idx++] = disp_cmd[1];
        cmd_seq[idx++] = disp_cmd[2];
        cmd_seq[idx++] = disp_cmd[3];

        // WAIT_DISPATCH (wait for left dispatch to complete)
        generate_wait_disp_command(2, 1, wait_disp_cmd);
        cmd_seq[idx++] = wait_disp_cmd[0];
        cmd_seq[idx++] = wait_disp_cmd[1];
        cmd_seq[idx++] = wait_disp_cmd[2];
        cmd_seq[idx++] = wait_disp_cmd[3];

        // ===================================================================
        // RIGHT MATRIX FETCH AND DISPATCH (disp_right=1)
        // ===================================================================
        // FETCH right matrix (start_addr = 528, fetch_right = 1)
        generate_fetch_command(3, 528, 528, 1'b1, fetch_right_cmd);
        $display("[TB] FETCH RIGHT: cmd[0]=0x%08x, cmd[1]=0x%08x, cmd[2]=0x%08x, cmd[3]=0x%08x",
                 fetch_right_cmd[0], fetch_right_cmd[1], fetch_right_cmd[2], fetch_right_cmd[3]);
        cmd_seq[idx++] = fetch_right_cmd[0];
        cmd_seq[idx++] = fetch_right_cmd[1];
        cmd_seq[idx++] = fetch_right_cmd[2];
        cmd_seq[idx++] = fetch_right_cmd[3];

        // DISPATCH RIGHT: dispatcher_bram (right) → tile_bram (right)
        // Multi-tile: Use DISTRIBUTE mode for right matrix (weights sharded across tiles)
        generate_disp_command(
            4,              // id
            C * V,          // man_nv_cnt: Total Native Vectors = C × V
            V,              // ugd_vec_size: NVs per UGD vector (matches test V parameter)
            16'd0,          // tile_addr: Start of tile BRAM (same as left, different BRAM)
            1'b0,           // man_4b: 8-bit mantissa mode
            col_en,         // col_en: Column enable mask (parameterized)
            5'd0,           // col_start: Distribution starts at column 0
            1'b1,           // disp_right: RIGHT dispatch (1=right)
            1'b0,           // broadcast: DISTRIBUTE mode for right (weights)
            disp_cmd
        );
        $display("[TB] DISPATCH RIGHT: man_nv_cnt=%0d (C×V=%0d×%0d), ugd_vec_size=%0d, broadcast=0, col_en=0x%06x", C*V, C, V, V, col_en);
        cmd_seq[idx++] = disp_cmd[0];
        cmd_seq[idx++] = disp_cmd[1];
        cmd_seq[idx++] = disp_cmd[2];
        cmd_seq[idx++] = disp_cmd[3];

        // WAIT_DISPATCH (wait for right dispatch to complete)
        generate_wait_disp_command(5, 4, wait_disp_cmd);
        cmd_seq[idx++] = wait_disp_cmd[0];
        cmd_seq[idx++] = wait_disp_cmd[1];
        cmd_seq[idx++] = wait_disp_cmd[2];
        cmd_seq[idx++] = wait_disp_cmd[3];

        // ===================================================================
        // MATRIX MULTIPLY
        // ===================================================================
        // TILE (matrix multiply) - Both left and right matrices now in tile_bram
        // tile_bram structure: Separate address spaces (like dispatcher_bram)
        //   - man_left:  [0:511] × 256-bit
        //   - man_right: [0:511] × 256-bit
        //   - exp_left:  [0:511] × 8-bit
        //   - exp_right: [0:511] × 8-bit
        //
        // Multi-tile MATMUL: Pass GLOBAL C dimension to compute engines
        // Each compute engine calculates its per-tile column count internally based on:
        //   - Global C dimension
        //   - Number of enabled tiles (popcount of col_en)
        //   - Its TILE_ID
        // Distribution: First (C % num_tiles) tiles get ceil(C/num_tiles), rest get floor(C/num_tiles)

        // Count enabled tiles
        num_enabled_tiles = $countones(col_en);
        if (num_enabled_tiles == 0) num_enabled_tiles = 1;  // Safety: at least 1 tile

        $display("[TB] MATMUL: B=%0d, C_global=%0d, num_tiles=%0d, col_en=0x%06x",
                 B, C, num_enabled_tiles, col_en);
        $display("[TB]   Compute engines will calculate per-tile columns internally");

        generate_tile_command(
            6,              // id (updated from 4)
            0,              // left_addr: Start of left matrix (separate address space)
            0,              // right_addr: Start of right matrix (separate address space)
            B,              // dim_b: Batch dimension (rows)
            C,              // dim_c: GLOBAL Column dimension (not per-tile!)
            V,              // dim_v: Vector size (inner dimension)
            col_en,         // col_en: Use parameterized tile enable mask
            1'b0,           // left_4b: 8-bit mantissa
            1'b0,           // right_4b: 8-bit mantissa
            1'b0,           // main_loop_left: Main loop over right dimension
            tile_cmd
        );
        cmd_seq[idx++] = tile_cmd[0];
        cmd_seq[idx++] = tile_cmd[1];
        cmd_seq[idx++] = tile_cmd[2];
        cmd_seq[idx++] = tile_cmd[3];

        // WAIT_TILE
        generate_wait_tile_command(7, 6, wait_tile_cmd);
        cmd_seq[idx++] = wait_tile_cmd[0];
        cmd_seq[idx++] = wait_tile_cmd[1];
        cmd_seq[idx++] = wait_tile_cmd[2];
        cmd_seq[idx++] = wait_tile_cmd[3];

        // READOUT - Collect results from tiles (required for multi-tile operation)
        // rd_len = B × C (total FP16 results across all tiles)
        generate_readout_command(8, 8'd0, B * C, readout_cmd);  // start_col=0, rd_len=B×C
        $display("[TB] READOUT: start_col=0, rd_len=%0d (B×C=%0d×%0d)", B*C, B, C);
        cmd_seq[idx++] = readout_cmd[0];
        cmd_seq[idx++] = readout_cmd[1];
        cmd_seq[idx++] = readout_cmd[2];
        cmd_seq[idx++] = readout_cmd[3];

        num_cmds = idx;
    endtask

    // ===================================================================
    // Helper Tasks for Command Generation
    // ===================================================================
    task automatic generate_fetch_command(
        input logic [7:0] id,
        input logic [link_addr_width_gp-1:0] start_addr,
        input logic [link_len_width_gp-1:0] num_lines,
        input logic fetch_right,  // 0=left, 1=right
        output logic [31:0] cmd [0:3]
    );
        // SPEC-COMPLIANT FETCH command (SINGLE_ROW_REFERENCE.md)
        // Word 0: {reserved[7:0], len[7:0], id[7:0], opcode[7:0]}
        // Word 1: start_addr[31:0]
        // Word 2: {16'b0, len[15:0]}
        // Word 3: {31'b0, fetch_right}

        // Use bit shifts to avoid concatenation issues
        cmd[0] = (32'h00 << 24) | (32'd16 << 16) | ({24'h0, id} << 8) | {24'h0, e_cmd_op_fetch};
        cmd[1] = start_addr[31:0];                 // Word 1: Address
        cmd[2] = {16'b0, num_lines[15:0]};         // Word 2: Length only
        cmd[3] = {31'b0, fetch_right};             // Word 3: fetch_right in bit[0]
    endtask

    task automatic generate_disp_command(
        input logic [7:0] id,
        input logic [7:0] man_nv_cnt,      // Total NVs to dispatch
        input logic [7:0] ugd_vec_size,    // NVs per UGD vector
        input logic [15:0] tile_addr,      // Tile destination address
        input logic man_4b,                // Mantissa width (0=8-bit, 1=4-bit)
        input logic [23:0] col_en,         // UPDATED: Column enable mask (24 tiles max)
        input logic [4:0] col_start,       // UPDATED: Distribution start column (5 bits)
        input logic disp_right,            // NEW: Dispatch side (0=left, 1=right)
        input logic broadcast,             // Distribution mode (0=distribute, 1=broadcast)
        output logic [31:0] cmd [0:3]
    );
        // SPEC-COMPLIANT DISPATCH command (SINGLE_ROW_REFERENCE.md + gemm_pkg.sv cmd_disp_s)
        // Word 0: {reserved[7:0], len[7:0], id[7:0], opcode[7:0]}
        // Word 1: {8'b0, man_nv_cnt[7:0], 8'b0, ugd_vec_size[7:0]}
        // Word 2: {16'b0, tile_addr[15:0]}
        // Word 3: {col_en[23:0], col_start[4:0], disp_right, broadcast, man_4b}

        cmd[0] = (32'h00 << 24) | (32'd16 << 16) | ({24'h0, id} << 8) | {24'h0, e_cmd_op_disp};
        cmd[1] = {8'b0, man_nv_cnt[7:0], 8'b0, ugd_vec_size[7:0]};    // Word 1
        cmd[2] = {16'b0, tile_addr[15:0]};                             // Word 2
        cmd[3] = {col_en[23:0], col_start[4:0], disp_right, broadcast, man_4b};  // Word 3 - UPDATED
    endtask

    task automatic generate_wait_disp_command(
        input logic [7:0] id,
        input logic [7:0] wait_id,
        output logic [31:0] cmd [0:3]
    );
        // SPEC-COMPLIANT WAIT_DISPATCH command (SINGLE_ROW_REFERENCE.md)
        // All commands use 16-byte (4-word) format
        // Word 0: {reserved[7:0], len[7:0], id[7:0], opcode[7:0]}
        // Word 1: {24'b0, wait_id[7:0]}
        // Word 2-3: Reserved

        cmd[0] = (32'h00 << 24) | (32'd16 << 16) | ({24'h0, id} << 8) | {24'h0, e_cmd_op_wait_disp};
        cmd[1] = {24'd0, wait_id[7:0]};             // wait_id in bits [7:0]
        cmd[2] = 32'h00000000;                      // Reserved
        cmd[3] = 32'h00000000;                      // Reserved
    endtask

    task automatic generate_tile_command(
        input logic [7:0] id,
        input int left_addr,                 // FIXED: Use int for proper width handling
        input int right_addr,                // FIXED: Use int for proper width handling
        input int dim_b,
        input int dim_c,
        input int dim_v,
        input logic [23:0] col_en,           // UPDATED: Column enable mask (24 tiles max) - was 16 bits
        input logic left_4b,                 // Left mantissa width (0=8b, 1=4b)
        input logic right_4b,                // Right mantissa width (0=8b, 1=4b)
        input logic main_loop_left,          // Main loop dimension (0=right, 1=left)
        output logic [31:0] cmd [0:3]
    );
        // SPEC-COMPLIANT MATMUL command (SINGLE_ROW_REFERENCE.md + gemm_pkg.sv cmd_tile_s)
        // Uses updated cmd_tile_s structure from gemm_pkg.sv

        // Convert addresses to 16-bit (spec-compliant)
        logic [15:0] left_addr_16  = left_addr[15:0];
        logic [15:0] right_addr_16 = right_addr[15:0];

        // Convert dimensions to 8-bit UGD lengths
        logic [7:0] left_ugd_len  = dim_b[7:0];   // Batch dimension
        logic [7:0] right_ugd_len = dim_c[7:0];   // Column dimension
        logic [7:0] vec_len       = dim_v[7:0];   // Vector size (NVs per UGD vector)

        // Pack according to cmd_tile_s structure (gemm_pkg.sv):
        // Word 0: {reserved[7:0], len[7:0], id[7:0], opcode[7:0]}
        // Word 1: {left_addr[15:0], right_addr[15:0]}
        // Word 2: {reserved2[7:0], left_ugd_len[7:0], right_ugd_len[7:0], vec_len[7:0]}
        // Word 3: {col_en[23:0], reserved[4:0], left_4b, right_4b, main_loop_left} - UPDATED

        cmd[0] = (32'h00 << 24) | (32'd16 << 16) | ({24'h0, id} << 8) | {24'h0, e_cmd_op_tile};
        cmd[1] = {left_addr_16, right_addr_16};                                 // Addresses
        cmd[2] = {8'b0, left_ugd_len, right_ugd_len, vec_len};                 // Dimensions
        cmd[3] = {col_en, 5'b0, left_4b, right_4b, main_loop_left};           // Word 3 - UPDATED to 24-bit col_en + 5-bit reserved
    endtask

    task automatic generate_wait_tile_command(
        input logic [7:0] id,
        input logic [7:0] wait_id,
        output logic [31:0] cmd [0:3]
    );
        // SPEC-COMPLIANT WAIT_MATMUL command (SINGLE_ROW_REFERENCE.md)
        // All commands use 16-byte (4-word) format
        // Word 0: {reserved[7:0], len[7:0], id[7:0], opcode[7:0]}
        // Word 1: {24'b0, wait_id[7:0]}
        // Word 2-3: Reserved

        cmd[0] = (32'h00 << 24) | (32'd16 << 16) | ({24'h0, id} << 8) | {24'h0, e_cmd_op_wait_tile};
        cmd[1] = {24'd0, wait_id[7:0]};             // wait_id in bits [7:0]
        cmd[2] = 32'h00000000;                      // Reserved
        cmd[3] = 32'h00000000;                      // Reserved
    endtask

    task automatic generate_readout_command(
        input logic [7:0]  id,
        input logic [7:0]  start_col,           // Starting tile index (0-23)
        input logic [31:0] rd_len,              // Total FP16 results to read
        output logic [31:0] cmd [0:3]
    );
        // SPEC-COMPLIANT READOUT command (SINGLE_ROW_REFERENCE.md lines 950-961)
        // All commands use 16-byte (4-word) format
        // Word 0: {reserved[7:0], len[7:0], id[7:0], opcode[7:0]}
        // Word 1: {reserved[23:0], start_col[7:0]}
        // Word 2: {rd_len[31:0]}
        // Word 3: Reserved

        cmd[0] = (32'h00 << 24) | (32'd16 << 16) | ({24'h0, id} << 8) | {24'h0, e_cmd_op_readout};
        cmd[1] = {24'd0, start_col[7:0]};           // start_col in bits [7:0]
        cmd[2] = rd_len[31:0];                      // rd_len (total results)
        cmd[3] = 32'h00000000;                      // Reserved
    endtask

    // ===================================================================
    // Watchdog Timer
    // ===================================================================
    initial begin
        #10000000000;  // 10ms timeout (in ps)
        $display("\n[TB] ERROR: Watchdog timeout!");
        $display("[TB] Test did not complete in time");
        $finish;
    end

endmodule : tb_engine_top

