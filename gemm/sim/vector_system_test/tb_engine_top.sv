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

`timescale 1ns/1ps

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
    localparam CLK_PERIOD = 10;  // 10ns = 100MHz
    localparam TGT_DATA_WIDTH = 256;
    localparam AXI_ADDR_WIDTH = 42;  // 42-bit for GDDR6 NoC addressing
    localparam GDDR6_PAGE_ID = 9'd2;  // Channel 1 page ID


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

    // Line interface (from arbiter via engine_top)
    logic [255:0] line_data;
    logic [8:0]   line_addr;
    logic         line_valid;
    logic         overflow_error;
    logic         collection_done;

    // READOUT Command Interface (from master_control via engine_top)
    logic         readout_en;
    logic [7:0]   readout_start_col;
    logic [31:0]  readout_rd_len;
    logic         readout_done;

    // Status signals
    logic         engine_busy;
    logic [3:0]   mc_state;
    logic [3:0]   mc_state_next;
    logic [3:0]   dc_state;
    logic [3:0]   ce_state;
    logic [cmd_op_width_gp-1:0] last_opcode;
    logic [9:0]   bram_wr_count;
    logic [15:0]  result_count;

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
        .AXI_ADDR_WIDTH     (AXI_ADDR_WIDTH)
    ) u_dut (
        .i_clk                  (clk),
        .i_reset_n              (reset_n),

        // Command FIFO interface
        .i_cmd_fifo_wdata       (cmd_fifo_wdata),
        .i_cmd_fifo_wen         (cmd_fifo_wen),
        .o_cmd_fifo_full        (cmd_fifo_full),
        .o_cmd_fifo_afull       (cmd_fifo_afull),
        .o_cmd_fifo_count       (cmd_fifo_count),

        // Result Line Output Interface (NEW: 256-bit packed lines from arbiter)
        .o_line_data            (line_data),
        .o_line_addr            (line_addr),
        .o_line_valid           (line_valid),
        .o_overflow_error       (overflow_error),
        .o_collection_done      (collection_done),

        // READOUT Command Interface (NEW: master_control -> result_fifo_to_simple_bram bridge)
        .o_readout_en           (readout_en),
        .o_readout_start_col    (readout_start_col),
        .o_readout_rd_len       (readout_rd_len),
        .i_readout_done         (readout_done),

        // AXI GDDR6 interface
        .nap_axi                (axi_ddr_if.initiator),

        // Status
        .o_engine_busy          (engine_busy),
        .o_mc_state             (mc_state),
        .o_mc_state_next        (mc_state_next),
        .o_dc_state             (dc_state),
        .o_ce_state             (ce_state),
        .o_last_opcode          (last_opcode),

        // Debug
        .o_bram_wr_count        (bram_wr_count),
        .o_result_count         (result_count)
    );

    // ===================================================================
    // Result Packing Module - Circular Buffer Integration
    // ===================================================================
    // BRAM interface signals
    logic [8:0]   result_bram_wr_addr;
    logic [255:0] result_bram_wr_data;
    logic         result_bram_wr_en;
    logic [31:0]  result_bram_wr_strobe;

    // First 4 results (for quick checking)
    logic [15:0]  result_0, result_1, result_2, result_3;

    // Circular buffer interface
    logic [12:0]  result_rd_ptr;          // Read pointer (host-controlled)
    logic [12:0]  result_wr_ptr;          // Write pointer (hardware)
    logic [13:0]  result_used_entries;    // Used entries (0-8192)
    logic         result_empty;           // Empty flag
    logic         result_bram_almost_full; // Backpressure signal

    // BRAM model for packed results (512 lines × 256 bits)
    logic [255:0] result_bram_model [0:511];
    int           result_bram_lines_written;

    // Initialize result_rd_ptr
    initial begin
        result_rd_ptr = 13'b0;
    end

    result_fifo_to_simple_bram u_result_packer (
        .i_clk              (clk),
        .i_reset_n          (reset_n),

        // READOUT Command Interface (from master_control via engine_top)
        .i_readout_en       (readout_en),
        .o_readout_done     (readout_done),

        // Line interface (from result_arbiter via engine_top)
        .i_line_data        (line_data),
        .i_line_addr        (line_addr),
        .i_line_valid       (line_valid),
        .i_collection_done  (collection_done),

        // BRAM interface (to model)
        .o_bram_wr_addr     (result_bram_wr_addr),
        .o_bram_wr_data     (result_bram_wr_data),
        .o_bram_wr_en       (result_bram_wr_en),
        .o_bram_wr_strobe   (result_bram_wr_strobe),

        // First 4 results
        .o_result_0         (result_0),
        .o_result_1         (result_1),
        .o_result_2         (result_2),
        .o_result_3         (result_3),

        // Circular buffer interface
        .i_rd_ptr           (result_rd_ptr),
        .o_wr_ptr           (result_wr_ptr),
        .o_used_entries     (result_used_entries),
        .o_empty            (result_empty),
        .o_almost_full      (result_bram_almost_full)
    );

    // BRAM Model - Captures packed results
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            result_bram_lines_written <= 0;
            for (int i = 0; i < 512; i++) begin
                result_bram_model[i] <= 256'h0;
            end
        end else if (result_bram_wr_en) begin
            // Byte-granular write using byte strobes (each bit enables one byte)
            for (int byte_idx = 0; byte_idx < 32; byte_idx++) begin
                if (result_bram_wr_strobe[byte_idx]) begin
                    result_bram_model[result_bram_wr_addr][byte_idx*8 +: 8] <= result_bram_wr_data[byte_idx*8 +: 8];
                end
            end
            result_bram_lines_written <= result_bram_lines_written + 1;
            $display("[TB_BRAM] @%0t WRITE: addr=%0d, strobe=0x%08x, data=0x%064x",
                     $time, result_bram_wr_addr, result_bram_wr_strobe, result_bram_wr_data);
        end
    end

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
    integer total_expected_results;  // For batch mode testing

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

    // Test configurations matching test_gemm_full.cpp Stage 2 (circular buffer bug reproduction)
    // CONFIGURATION: 10-test sequence with NO RESET between tests (col_en=0x000001 single-tile)
    // MULTI-TILE TESTING: Change TILE_COUNT parameter below to test different configurations
    // Set TILE_COUNT to test: 1 (0x000001), 2 (0x000003), 4 (0x00000F), 8 (0x0000FF)
    parameter logic [23:0] TILE_COUNT = 24'h000001;  // Testing with n=1 tile (verify 2-cycle pipeline fix)

    // This reproduces the Stage 2 batch-then-read pattern that triggers the circular buffer bug
    test_config_t test_configs[] = '{
        // 10-test sequence with configurable tile count (matching SOFTWARE_REFERENCE_RESULTS.md)
        '{B: 1,   C: 1,   V: 1,   col_en: TILE_COUNT, name: "B1_C1_V1"},      // Test 1: 1 result, cumulative=1
        '{B: 2,   C: 2,   V: 2,   col_en: TILE_COUNT, name: "B2_C2_V2"},      // Test 2: 4 results, cumulative=5
        '{B: 4,   C: 4,   V: 4,   col_en: TILE_COUNT, name: "B4_C4_V4"},      // Test 3: 16 results, cumulative=21
        '{B: 2,   C: 2,   V: 64,  col_en: TILE_COUNT, name: "B2_C2_V64"},     // Test 4: 4 results, cumulative=25
        '{B: 4,   C: 4,   V: 32,  col_en: TILE_COUNT, name: "B4_C4_V32"},     // Test 5: 16 results, cumulative=41
        '{B: 8,   C: 8,   V: 16,  col_en: TILE_COUNT, name: "B8_C8_V16"},     // Test 6: 64 results, cumulative=105
        '{B: 16,  C: 16,  V: 8,   col_en: TILE_COUNT, name: "B16_C16_V8"},    // Test 7: 256 results, cumulative=361
        '{B: 1,   C: 128, V: 1,   col_en: TILE_COUNT, name: "B1_C128_V1"},    // Test 8: 128 results, cumulative=489
        '{B: 128, C: 1,   V: 1,   col_en: TILE_COUNT, name: "B128_C1_V1"},    // Test 9: 128 results, cumulative=617
        '{B: 1,   C: 1,   V: 128, col_en: TILE_COUNT, name: "B1_C1_V128"}     // Test 10: 1 result, cumulative=618

        // Multi-tile tests DISABLED for circular buffer bug reproduction
        // These will be re-enabled after bug is fixed to test multi-tile behavior
        '{B: 2, C: 2, V: 64,   col_en: 24'h000003, name: "B2_C2_V64"},
        '{B: 2, C: 2, V: 64,   col_en: 24'h00000F, name: "B2_C2_V64"},
        '{B: 2, C: 2, V: 64,   col_en: 24'h0000FF, name: "B2_C2_V64"},
        '{B: 4, C: 4, V: 32,  col_en: 24'h000003, name: "B4_C4_V32"},
        '{B: 4, C: 4, V: 32,  col_en: 24'h00000F, name: "B4_C4_V32"},
        '{B: 4, C: 4, V: 32,  col_en: 24'h0000FF, name: "B4_C4_V32"},
        '{B: 8, C: 8, V: 16,  col_en: 24'h000003, name: "B8_C8_V16"},
        '{B: 8, C: 8, V: 16,  col_en: 24'h00000F, name: "B8_C8_V16"},
        '{B: 8, C: 8, V: 16,  col_en: 24'h0000FF, name: "B8_C8_V16"},
        '{B: 16, C: 16, V: 8,  col_en: 24'h000003, name: "B16_C16_V8"},
        '{B: 16, C: 16, V: 8,  col_en: 24'h00000F, name: "B16_C16_V8"},
        '{B: 16, C: 16, V: 8,  col_en: 24'h0000FF, name: "B16_C16_V8"},
        '{B: 1, C: 128, V: 1,  col_en: 24'h000003, name: "B1_C128_V1"},
        '{B: 1, C: 128, V: 1,  col_en: 24'h00000F, name: "B1_C128_V1"},
        '{B: 1, C: 128, V: 1,  col_en: 24'h0000FF, name: "B1_C128_V1"}
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
        // result_fifo_ren is now driven by u_result_packer, not by testbench

        // Wait for reset to complete
        wait (reset_n == 1'b1);
        repeat (10) @(posedge clk);

        // STAGE 2 REPRODUCTION: Batch all commands for all tests FIRST
        // This matches test_gemm_full.cpp Stage 2: submit all commands, then wait for all results
        $display("\n[TB] ====================================================================");
        $display("[TB] MULTI-TILE CONFIGURATION: col_en=0x%06h (%0d tiles enabled)",
                 TILE_COUNT, $countones(TILE_COUNT));
        $display("[TB] STAGE 2 BATCH MODE: Submitting ALL commands for ALL %0d tests", test_configs.size());
        $display("[TB] ====================================================================\n");

        // Submit all commands for all tests
        foreach (test_configs[i]) begin
            $display("[TB] Submitting commands for Test %0d: %s (B=%0d, C=%0d, V=%0d)",
                     i+1, test_configs[i].name, test_configs[i].B, test_configs[i].C, test_configs[i].V);

            submit_test_commands(
                test_configs[i].B,
                test_configs[i].C,
                test_configs[i].V,
                test_configs[i].col_en,
                test_configs[i].name
            );
        end

        $display("\n[TB] All commands submitted! Waiting for all results to accumulate...\n");

        // Calculate total expected results for all tests
        total_expected_results = 0;
        foreach (test_configs[i]) begin
            total_expected_results += test_configs[i].B * test_configs[i].C;
        end
        $display("[TB] Expecting total of %0d results from %0d tests", total_expected_results, $size(test_configs));

        timeout_count = 0;
        watchdog = 50000000;  // 500ms timeout for all 25 tests (increased from 100ms)

        while ((result_wr_ptr < total_expected_results) && (timeout_count < watchdog)) begin
            @(posedge clk);
            timeout_count++;
        end

        if (timeout_count >= watchdog) begin
            $display("[TB] ERROR: Timeout waiting for all results! Expected wr_ptr=%0d, got %0d",
                     total_expected_results, result_wr_ptr);
            $display("[TB] Partial results collected. Proceeding with verification...");
        end else begin
            $display("[TB] SUCCESS: All %0d results collected in %0d cycles", result_wr_ptr, timeout_count);
        end

        // Wait for final BRAM writes to propagate
        repeat (10) @(posedge clk);

        // Check for circular buffer bug at position 1
        $display("\n[TB] ====================================================================");
        $display("[TB] CIRCULAR BUFFER BUG CHECK");
        $display("[TB] ====================================================================");
        $display("[TB] BRAM[0] pos[0]=0x%04x (Test 1 result)", result_bram_model[0][15:0]);
        $display("[TB] BRAM[0] pos[1]=0x%04x (Test 2 result 0 - CHECK FOR DUPLICATE!)", result_bram_model[0][31:16]);
        $display("[TB] BRAM[0] pos[2]=0x%04x (Test 2 result 1)", result_bram_model[0][47:32]);
        $display("[TB] BRAM[0] pos[3]=0x%04x (Test 2 result 2)", result_bram_model[0][63:48]);

        if (result_bram_model[0][31:16] == result_bram_model[0][15:0]) begin
            $display("[TB] *** BUG REPRODUCED! Position 1 is DUPLICATE of position 0 (0x%04x) ***",
                     result_bram_model[0][15:0]);
            $display("[TB] Expected pos[1]=0x22f7, got 0x%04x", result_bram_model[0][31:16]);
        end else begin
            $display("[TB] Position 1 OK: 0x%04x (no duplicate)", result_bram_model[0][31:16]);
        end
        $display("[TB] ====================================================================\n");

        // Now verify each test's results against golden files
        foreach (test_configs[i]) begin
            verify_test_results(
                i,
                test_configs[i].B,
                test_configs[i].C,
                test_configs[i].V,
                test_configs[i].col_en,
                test_configs[i].name
            );
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
        integer results_seen;
        integer mismatches;
        integer idx;
        integer num_cols_enabled;    // For timing comparison
        integer start_wr_ptr;         // Starting wr_ptr for cumulative tests
        integer target_wr_ptr;        // Target wr_ptr for cumulative tests

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
        // Multi-tile tests (col_en > 1) use "_multitile.hex" golden files
        if (config_col_en > 24'h000001) begin
            golden_filename = $sformatf("/home/dev/Dev/elastix_gemm/hex/golden_%s_multitile.hex", test_name);
        end else begin
            golden_filename = $sformatf("/home/dev/Dev/elastix_gemm/hex/golden_%s.hex", test_name);
        end
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

        // Circular Buffer Monitoring (CUMULATIVE across tests when reset is disabled)
        start_wr_ptr = result_wr_ptr;  // Capture starting wr_ptr for this test
        target_wr_ptr = start_wr_ptr + expected_results;  // Calculate target
        $display("[TB] Circular buffer monitoring enabled");
        $display("[TB] Start state: wr_ptr=%0d, rd_ptr=%0d, used_entries=%0d, empty=%b",
                 result_wr_ptr, result_rd_ptr, result_used_entries, result_empty);
        $display("[TB] Expecting wr_ptr to go from %0d to %0d (+%0d results)",
                 start_wr_ptr, target_wr_ptr, expected_results);

        // Wait for all results to be packed into BRAM (use cumulative wr_ptr with no-reset scenario)
        while ((result_wr_ptr < target_wr_ptr) && (timeout_count < watchdog)) begin
            @(posedge clk);
            timeout_count++;
        end

        if (timeout_count >= watchdog) begin
            $display("[TB] ERROR: Packing timeout! Expected wr_ptr=%0d, got %0d (started at %0d)",
                     target_wr_ptr, result_wr_ptr, start_wr_ptr);
        end else begin
            $display("[TB] All results packed after %0d cycles: wr_ptr=%0d (target=%0d), used_entries=%0d",
                     timeout_count, result_wr_ptr, target_wr_ptr, result_used_entries);
        end

        // Wait for BRAM write to propagate (always_ff needs 1 cycle)
        @(posedge clk);
        @(posedge clk);  // Additional safety margin

        // Note: Partial BRAM line flush removed - no longer needed with simplified reset
        // The async reset (reset_n) now handles all buffer clearing
        // For tests with < 16 results, they remain in the packing buffer until next result or reset
        $display("[TB] BRAM lines written: %0d", result_bram_lines_written);

        // Read and verify packed results from BRAM model
        // In no-reset scenario, results start at start_wr_ptr, not 0
        for (int result_idx = 0; result_idx < expected_results; result_idx++) begin
            logic [15:0] fp16_hw;
            logic [15:0] golden;
            int diff;
            int bram_line;
            int bram_pos;
            int cumulative_idx;  // Actual BRAM position (cumulative across tests)

            // Calculate cumulative index in BRAM (accounts for previous tests)
            cumulative_idx = start_wr_ptr + result_idx;

            // Calculate BRAM address: line = cumulative_idx / 16, position = cumulative_idx % 16
            bram_line = cumulative_idx / 16;
            bram_pos = cumulative_idx % 16;

            // Extract FP16 value from packed BRAM line
            fp16_hw = result_bram_model[bram_line][bram_pos*16 +: 16];
            golden = golden_results[result_idx];  // Golden is still indexed from 0 for THIS test

            // Debug: Show what we read from BRAM for B4_C4_V4 test
            if (expected_results == 16 && result_idx < 4) begin
                $display("[TB_VERIFY] @%0t READ: result[%0d] (cumulative=%0d) from BRAM[%0d][%0d] = 0x%04x (full line = 0x%064x), golden = 0x%04x",
                        $time, result_idx, cumulative_idx, bram_line, bram_pos, fp16_hw, result_bram_model[bram_line], golden);
            end

            // Check for X/Z states (uninitialized values)
            if ($isunknown(fp16_hw)) begin
                $display("[TB] ERROR: hw=0x%04x contains X/Z (uninitialized) at cumulative[%0d] (BRAM[%0d][%0d])",
                        fp16_hw, cumulative_idx, bram_line, bram_pos);
                mismatches++;
            end else begin
                // Only do golden comparison for single-tile tests
                diff = (fp16_hw > golden) ? fp16_hw - golden : golden - fp16_hw;

                if (diff > 5) begin
                    $display("[TB] MISMATCH[%0d]: hw=0x%04x golden=0x%04x diff=%0d (cumulative=%0d, BRAM[%0d][%0d])",
                            result_idx, fp16_hw, golden, diff, cumulative_idx, bram_line, bram_pos);
                    mismatches++;
                end else if (result_idx < 10 || (result_idx >= expected_results - 5)) begin
                    // Only print first 10 and last 5 matches to reduce log size
                    $display("[TB] MATCH[%0d]: hw=0x%04x golden=0x%04x diff=%0d (cumulative=%0d, BRAM[%0d][%0d])",
                            result_idx, fp16_hw, golden, diff, cumulative_idx, bram_line, bram_pos);
                end
            end

            results_seen++;

            // Update rd_ptr every 16 results (one BRAM line consumed) - use cumulative index
            if ((cumulative_idx + 1) % 16 == 0) begin
                result_rd_ptr = result_rd_ptr + 16;
            end
        end

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

        // Note: Result BRAM removed - arbiter now pushes directly to result_fifo_to_simple_bram
        $display("[TB] Result path: arbiter → result_fifo_to_simple_bram (direct PUSH)");

        // For packed result testing, a separate testbench for elastix_gemm_top
        // would be needed to verify the result_fifo_to_simple_bram functionality
        
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
    // Task: Submit Test Commands (Batch Mode - No Waiting)
    // ===================================================================
    task automatic submit_test_commands(
        input int config_B,
        input int config_C,
        input int config_V,
        input logic [23:0] config_col_en,
        input string test_name
    );
        logic [31:0] cmd_sequence [0:511];
        integer num_commands;
        integer cmd_idx;

        // Generate command sequence
        build_test_sequence(config_B, config_C, config_V, config_col_en, cmd_sequence, num_commands);

        // Submit all commands to FIFO without waiting
        for (cmd_idx = 0; cmd_idx < num_commands; cmd_idx++) begin
            cmd_fifo_wdata = cmd_sequence[cmd_idx];
            cmd_fifo_wen = 1'b1;
            @(posedge clk);
        end
        cmd_fifo_wen = 1'b0;

        $display("[TB]   Submitted %0d commands for %s", num_commands, test_name);
    endtask

    // ===================================================================
    // Task: Verify Test Results (From Accumulated BRAM)
    // ===================================================================
    task automatic verify_test_results(
        input int test_idx,
        input int config_B,
        input int config_C,
        input int config_V,
        input logic [23:0] config_col_en,
        input string test_name
    );
        integer expected_results;
        integer cumulative_start;  // Where this test's results start in BRAM
        integer result_idx;
        logic [15:0] fp16_hw;
        logic [15:0] golden;
        logic [15:0] golden_results [0:16383];
        integer golden_file;
        integer scan_result;
        integer idx;
        integer mismatches;
        string golden_filename;
        int diff;
        int bram_line;
        int bram_pos;
        int cumulative_idx;

        total_tests++;
        expected_results = config_B * config_C;

        // Calculate cumulative start position for this test
        cumulative_start = 0;
        for (int j = 0; j < test_idx; j++) begin
            cumulative_start += test_configs[j].B * test_configs[j].C;
        end

        $display("\n[TB] ====================================================================");
        $display("[TB] VERIFY TEST %0d: %s (B=%0d, C=%0d, V=%0d)", test_idx+1, test_name, config_B, config_C, config_V);
        $display("[TB] Results at BRAM positions [%0d:%0d] (count=%0d)",
                 cumulative_start, cumulative_start + expected_results - 1, expected_results);
        $display("[TB] ====================================================================");

        // Load golden reference
        // Multi-tile tests (col_en > 1) use "_multitile.hex" golden files
        if (config_col_en > 24'h000001) begin
            golden_filename = $sformatf("/home/dev/Dev/elastix_gemm/hex/golden_%s_multitile.hex", test_name);
        end else begin
            golden_filename = $sformatf("/home/dev/Dev/elastix_gemm/hex/golden_%s.hex", test_name);
        end
        golden_file = $fopen(golden_filename, "r");
        if (golden_file == 0) begin
            $display("[TB] ERROR: Cannot open golden reference file: %s", golden_filename);
            failed_tests++;
            return;
        end

        idx = 0;
        while (!$feof(golden_file) && idx < 16384) begin
            scan_result = $fscanf(golden_file, "%h\n", golden_results[idx]);
            if (scan_result == 1) idx++;
        end
        $fclose(golden_file);

        // Verify results
        mismatches = 0;
        for (result_idx = 0; result_idx < expected_results; result_idx++) begin
            cumulative_idx = cumulative_start + result_idx;
            bram_line = cumulative_idx / 16;
            bram_pos = cumulative_idx % 16;

            fp16_hw = result_bram_model[bram_line][bram_pos*16 +: 16];
            golden = golden_results[result_idx];

            if ($isunknown(fp16_hw)) begin
                $display("[TB] ERROR: X/Z at cumulative[%0d]", cumulative_idx);
                mismatches++;
            end else begin
                diff = (fp16_hw > golden) ? fp16_hw - golden : golden - fp16_hw;
                if (diff > 5) begin
                    $display("[TB] MISMATCH[%0d]: hw=0x%04x golden=0x%04x diff=%0d (cumulative=%0d)",
                            result_idx, fp16_hw, golden, diff, cumulative_idx);
                    mismatches++;
                end else if (result_idx < 5 || result_idx >= expected_results - 5) begin
                    $display("[TB] MATCH[%0d]: hw=0x%04x golden=0x%04x (cumulative=%0d)",
                            result_idx, fp16_hw, golden, cumulative_idx);
                end
            end
        end

        if (mismatches == 0) begin
            $display("[TB] PASS: %s - All %0d results matched!", test_name, expected_results);
            passed_tests++;
        end else begin
            $display("[TB] FAIL: %s - %0d/%0d mismatches", test_name, mismatches, expected_results);
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
        #10000000;  // 10ms timeout
        $display("\n[TB] ERROR: Watchdog timeout!");
        $display("[TB] Test did not complete in time");
        $finish;
    end

endmodule : tb_engine_top

