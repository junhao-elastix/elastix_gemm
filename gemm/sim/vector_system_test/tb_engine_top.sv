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

    // Result FIFO interface (FP16)
    logic [15:0]  result_fifo_rdata;
    logic         result_fifo_ren;
    logic         result_fifo_empty;
    logic [14:0]  result_fifo_count;

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
        .ADDR_WIDTH (AXI_ADDR_WIDTH)
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

        // Result FIFO interface
        .o_result_fifo_rdata    (result_fifo_rdata),
        .i_result_fifo_ren      (result_fifo_ren),
        .o_result_fifo_empty    (result_fifo_empty),
        .o_result_fifo_count    (result_fifo_count),

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
    // Memory Model Instantiation
    // ===================================================================
    logic [31:0] mem_read_count;
    logic [31:0] mem_last_addr;

    tb_memory_model #(
        .DATA_WIDTH         (TGT_DATA_WIDTH),
        .ADDR_WIDTH         (AXI_ADDR_WIDTH),
        .LINES_PER_BLOCK    (528),
        .NUM_BLOCKS         (2)
    ) u_memory_model (
        .i_clk              (clk),
        .i_reset_n          (reset_n),

        // AXI interface
        .axi_mem_if         (axi_ddr_if.responder),

        // Debug
        .o_read_count       (mem_read_count),
        .o_last_addr        (mem_last_addr)
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

    // Test configurations matching test_gemm.cpp
    // Single-tile tests (10 tests with col_en=0x000001)
    // Multi-tile tests (4 new tests with col_en=0x000003 for 2 tiles)
    test_config_t test_configs[] = '{
        // Single-tile regression tests (existing)
        '{B: 1, C: 1, V: 1,   col_en: 24'h000001, name: "B1_C1_V1"},
        '{B: 2, C: 2, V: 2,   col_en: 24'h000001, name: "B2_C2_V2"},
        '{B: 4, C: 4, V: 4,   col_en: 24'h000001, name: "B4_C4_V4"},
        '{B: 2, C: 2, V: 64,  col_en: 24'h000001, name: "B2_C2_V64"},
        '{B: 4, C: 4, V: 32,  col_en: 24'h000001, name: "B4_C4_V32"},
        '{B: 8, C: 8, V: 16,  col_en: 24'h000001, name: "B8_C8_V16"},
        '{B: 16, C: 16, V: 8, col_en: 24'h000001, name: "B16_C16_V8"},
        '{B: 1, C: 128, V: 1, col_en: 24'h000001, name: "B1_C128_V1"},
        '{B: 128, C: 1, V: 1, col_en: 24'h000001, name: "B128_C1_V1"},
        '{B: 1, C: 1, V: 128, col_en: 24'h000001, name: "B1_C1_V128"},

        // Multi-tile tests (NEW: 2-tile with col_en=0x000003)
        '{B: 2, C: 4, V: 16,  col_en: 24'h000003, name: "B2_C4_V16_2T"},
        '{B: 4, C: 8, V: 8,   col_en: 24'h000003, name: "B4_C8_V8_2T"},
        '{B: 8, C: 32, V: 2,  col_en: 24'h000003, name: "B8_C32_V2_2T"},
        '{B: 16, C: 16, V: 4, col_en: 24'h000003, name: "B16_C16_V4_2T"}
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
        result_fifo_ren = 1'b0;

        // Wait for reset to complete
        wait (reset_n == 1'b1);
        repeat (10) @(posedge clk);

        // Run all test configurations
        foreach (test_configs[i]) begin
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
        integer results_seen;
        integer mismatches;
        integer idx;
        
        total_tests++;
        
        $display("\n[TB] ====================================================================");
        $display("[TB] TEST %0d: Running configuration %s (B=%0d, C=%0d, V=%0d)",
                 total_tests, test_name, config_B, config_C, config_V);
        $display("[TB] ====================================================================");

        // Load golden reference
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
        $display("[TB] Loaded %0d golden results from %s", idx, golden_filename);

        // Generate command sequence
        build_test_sequence(config_B, config_C, config_V, config_col_en, cmd_sequence, num_commands);
        $display("[TB] Generated %0d commands for col_en=0x%06x", num_commands, config_col_en);

        // Submit commands to FIFO
        // Write all commands continuously (one word per cycle)
        for (cmd_idx = 0; cmd_idx < num_commands; cmd_idx++) begin
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
        
        // Continuously read results until expected count or timeout
        while (results_seen < expected_results && timeout_count < watchdog) begin
            @(posedge clk);
            timeout_count++;
            
            // Read result if FIFO has data
            if (!result_fifo_empty) begin
                logic [15:0] fp16_hw;
                logic [15:0] golden;
                int diff;
                
                result_fifo_ren = 1'b1;
                @(posedge clk);
                result_fifo_ren = 1'b0;
                @(posedge clk);  // Wait additional cycle for BRAM read latency
                fp16_hw = result_fifo_rdata;
                
                golden = golden_results[results_seen];
                
                // Check for X/Z states (uninitialized values)
                if ($isunknown(fp16_hw)) begin
                    $display("[TB] ERROR: hw=0x%04x contains X/Z (uninitialized) at result[%0d]", 
                            fp16_hw, results_seen);
                    mismatches++;
                end else begin
                    diff = (fp16_hw > golden) ? fp16_hw - golden : golden - fp16_hw;
                    
                    if (diff > 2) begin
                        $display("[TB] MISMATCH[%0d]: hw=0x%04x golden=0x%04x diff=%0d", 
                                results_seen, fp16_hw, golden, diff);
                        mismatches++;
                    end else begin
                        $display("[TB] MATCH[%0d]: hw=0x%04x golden=0x%04x diff=%0d", 
                                results_seen, fp16_hw, golden, diff);
                    end
                end
                
                results_seen++;
            end
        end

        if (timeout_count >= watchdog) begin
            $display("[TB] ERROR: Result wait timeout! Expected %0d, got %0d",
                     expected_results, results_seen);
        end else begin
            $display("[TB] Collected %0d results after %0d cycles", results_seen, timeout_count);
        end

        // Test verdict
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
        
        integer idx = 0;

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
            128,            // man_nv_cnt: Total NVs in dispatcher_bram (full capacity)
            V,              // ugd_vec_size: NVs per UGD vector (matches test V parameter)
            16'd0,          // tile_addr: Start of tile BRAM
            1'b0,           // man_4b: 8-bit mantissa mode
            col_en,         // col_en: Column enable mask (parameterized)
            5'd0,           // col_start: Distribution starts at column 0
            1'b0,           // disp_right: LEFT dispatch (0=left)
            1'b1,           // broadcast: BROADCAST mode for left (activations)
            disp_cmd
        );
        $display("[TB] DISPATCH LEFT: disp_right=0, broadcast=1, col_en=0x%06x", col_en);
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
            128,            // man_nv_cnt: Total NVs in dispatcher_bram (full capacity)
            V,              // ugd_vec_size: NVs per UGD vector (matches test V parameter)
            16'd0,          // tile_addr: Start of tile BRAM (same as left, different BRAM)
            1'b0,           // man_4b: 8-bit mantissa mode
            col_en,         // col_en: Column enable mask (parameterized)
            5'd0,           // col_start: Distribution starts at column 0
            1'b1,           // disp_right: RIGHT dispatch (1=right)
            1'b0,           // broadcast: DISTRIBUTE mode for right (weights)
            disp_cmd
        );
        $display("[TB] DISPATCH RIGHT: disp_right=1, broadcast=0, col_en=0x%06x", col_en);
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
        generate_tile_command(
            6,              // id (updated from 4)
            0,              // left_addr: Start of left matrix (separate address space)
            0,              // right_addr: Start of right matrix (separate address space)
            B,              // dim_b: Batch dimension
            C,              // dim_c: Column dimension
            V,              // dim_v: Vector size
            24'h000001,     // col_en: Single-tile mode (24-bit, only tile 0 enabled) - UPDATED
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
        $display("[GEN_FETCH_DEBUG] Generated cmd[0]=0x%08x (should be 0x00100%02xF0)", cmd[0], id);
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
        $display("[TB_CMD] DISP: id=%0d, cmd[3]=0x%08x (col_en=0x%06x, col_start=%0d, disp_right=%0b, broadcast=%0b, man_4b=%0b)",
                 id, cmd[3], col_en, col_start, disp_right, broadcast, man_4b);
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

