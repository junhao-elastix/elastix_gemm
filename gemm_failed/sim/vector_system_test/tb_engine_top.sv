// ------------------------------------------------------------------
// Testbench for Engine Top Module (MS2.0 FIFO Interface)
//
// Purpose: Complete testbench for engine_top with direct FIFO interface
// Features:
//  - Instantiates engine_top (DUT)
//  - Instantiates tb_memory_model (GDDR6 emulation)
//  - Uses tb_ucode_gen_pkg for command generation
//  - Test sequence: FETCH → FETCH → DISP → TILE → WAIT
//  - Result verification with FP16 output checking
//
// Test Flow:
//  1. Reset system
//  2. Load commands into cmd_fifo
//  3. Wait for commands to execute
//  4. Read results from result_fifo
//  5. Verify FP16 format and values
//
// Author: MS2.0 FIFO Architecture Integration
// Date: Sun Oct 12 2025
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

    // Test configuration parameters (can be overridden via +define)
    `ifdef TEST_B
        localparam int TEST_B = `TEST_B;
    `else
        localparam int TEST_B = 4;
    `endif

    `ifdef TEST_C
        localparam int TEST_C = `TEST_C;
    `else
        localparam int TEST_C = 4;
    `endif

    `ifdef TEST_V
        localparam int TEST_V = `TEST_V;
    `else
        localparam int TEST_V = 32;
    `endif

    // ===================================================================
    // Clock and Reset
    // ===================================================================
    logic clk;
    logic reset_n;

    initial begin
        clk = 1'b0;
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
    logic [3:0]   ce_state [0:15];  // Per-tile state array for NUM_TILES=16
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
    // DEBUG: Continuous State Monitoring
    // ===================================================================
    logic [3:0] mc_state_prev;
    logic [3:0] dc_state_prev;
    logic [3:0] ce_state_prev;

    initial mc_state_prev = 4'hF;
    initial dc_state_prev = 4'hF;
    initial ce_state_prev = 4'hF;

    always @(posedge clk) begin
        if (mc_state != mc_state_prev) begin
            $display("[STATE] @%0t MC: 0x%1h → 0x%1h (busy=%b, opcode=0x%02x)",
                     $time, mc_state_prev, mc_state, engine_busy, last_opcode);
            mc_state_prev <= mc_state;
        end

        if (dc_state != dc_state_prev) begin
            $display("[STATE] @%0t DC: 0x%1h → 0x%1h (wr_cnt=%0d)",
                     $time, dc_state_prev, dc_state, bram_wr_count);
            dc_state_prev <= dc_state;
        end

        if (ce_state[0] != ce_state_prev) begin
            $display("[STATE] @%0t CE[0]: 0x%1h → 0x%1h (result_cnt=%0d)",
                     $time, ce_state_prev, ce_state[0], result_count);
            ce_state_prev <= ce_state[0];
        end

        // Monitor result FIFO status
        if (result_fifo_count > 0) begin
            $display("[FIFO] @%0t Result FIFO: count=%0d (empty=%b)",
                     $time, result_fifo_count, result_fifo_empty);
        end
    end

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
    
    // Log file handle
    integer test_log_file;
    
    // ===================================================================
    // Logging Functions
    // ===================================================================
    function void log_message(string message);
        $display("%s", message);
        if (test_log_file != 0) begin
            $fdisplay(test_log_file, "%s", message);
        end
    endfunction

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
        string name;
    } test_config_t;

    test_config_t test_configs[] = '{
        // DEBUG: Focus on B4_C4_V32 only
        // '{B: 1, C: 1, V: 1,   name: "B1_C1_V1"},
        // '{B: 2, C: 2, V: 2,   name: "B2_C2_V2"},
        // '{B: 4, C: 4, V: 4,   name: "B4_C4_V4"},
        // '{B: 2, C: 2, V: 64,   name: "B2_C2_V64"},
        '{B: 4, C: 4, V: 32,  name: "B4_C4_V32"}
        // '{B: 8, C: 8, V: 16,  name: "B8_C8_V16"},
        // '{B: 1, C: 128, V: 1, name: "B1_C128_V1"},
        // '{B: 128, C: 1, V: 1, name: "B128_C1_V1"},
        // '{B: 1, C: 1, V: 128, name: "B1_C1_V128"}
    };

    // ===================================================================
    // Main Test Sequence
    // ===================================================================
    initial begin
        // Initialize log file
        test_log_file = $fopen("/home/dev/Dev/elastix_gemm/gemm/sim/vector_system_test/test_results.log", "w");
        if (test_log_file == 0) begin
            $display("[TB] WARNING: Could not open test log file");
        end else begin
            $fdisplay(test_log_file, "MS2.0 GEMM Engine Test Results Log");
            $fdisplay(test_log_file, "Generated: %t", $time);
            $fdisplay(test_log_file, "================================================================================\n");
        end
        
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
        
        // Close log file
        if (test_log_file != 0) begin
            $fdisplay(test_log_file, "\n================================================================================");
            $fdisplay(test_log_file, "TEST SUMMARY");
            $fdisplay(test_log_file, "================================================================================");
            $fdisplay(test_log_file, "Total Tests: %0d", total_tests);
            $fdisplay(test_log_file, "Passed:      %0d", passed_tests);
            $fdisplay(test_log_file, "Failed:      %0d", failed_tests);
            if (failed_tests == 0) begin
                $fdisplay(test_log_file, "STATUS: ALL TESTS PASSED");
            end else begin
                $fdisplay(test_log_file, "STATUS: %0d TESTS FAILED", failed_tests);
            end
            $fdisplay(test_log_file, "================================================================================");
            $fclose(test_log_file);
            $display("[TB] Test results logged to: test_results.log");
        end

        $finish;
    end

    // ===================================================================
    // Task: Run Single Test
    // ===================================================================
    task automatic run_single_test(
        input int config_B,
        input int config_C,
        input int config_V,
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
        log_message($sformatf("[TB] TEST %0d: Running configuration %s (B=%0d, C=%0d, V=%0d)",
                total_tests, test_name, config_B, config_C, config_V));
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
        build_test_sequence(config_B, config_C, config_V, cmd_sequence, num_commands);
        $display("[TB] Generated %0d commands", num_commands);

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
                    log_message($sformatf("[TB] ERROR: hw=0x%04x contains X/Z (uninitialized) at result[%0d]", 
                            fp16_hw, results_seen));
                    mismatches++;
                end else begin
                    diff = (fp16_hw > golden) ? fp16_hw - golden : golden - fp16_hw;
                    
                    if (diff > 2) begin
                        log_message($sformatf("[TB] MISMATCH[%0d]: hw=0x%04x golden=0x%04x diff=%0d", 
                                results_seen, fp16_hw, golden, diff));
                        mismatches++;
                    end else begin
                        // log_message($sformatf("[TB] MATCH[%0d]: hw=0x%04x golden=0x%04x diff=%0d", 
                        //         results_seen, fp16_hw, golden, diff));
                    end
                end
                
                results_seen++;
            end
        end

        if (timeout_count >= watchdog) begin
            log_message($sformatf("[TB] ERROR: Result wait timeout! Expected %0d, got %0d",
                     expected_results, results_seen));
        end else begin
            log_message($sformatf("[TB] Collected %0d results after %0d cycles", results_seen, timeout_count));
        end

        // Test verdict
        if (mismatches == 0 && results_seen == expected_results) begin
            log_message($sformatf("[TB] PASS: %s - All %0d results matched!", test_name, results_seen));
            passed_tests++;
        end else begin
            log_message($sformatf("[TB] FAIL: %s - %0d mismatches, %0d/%0d results /n",
                     test_name, mismatches, results_seen, expected_results));
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

        // FETCH left matrix (start_addr = 0, fetch_right = 0)
        generate_fetch_command(0, 0, 528, 1'b0, fetch_left_cmd);
        $display("[TB] FETCH LEFT: cmd[0]=0x%08x, cmd[1]=0x%08x, cmd[2]=0x%08x, cmd[3]=0x%08x",
                 fetch_left_cmd[0], fetch_left_cmd[1], fetch_left_cmd[2], fetch_left_cmd[3]);
        cmd_seq[idx++] = fetch_left_cmd[0];
        cmd_seq[idx++] = fetch_left_cmd[1];
        cmd_seq[idx++] = fetch_left_cmd[2];
        cmd_seq[idx++] = fetch_left_cmd[3];

        // FETCH right matrix (start_addr = 528, fetch_right = 1)
        generate_fetch_command(1, 528, 528, 1'b1, fetch_right_cmd);
        $display("[TB] FETCH RIGHT: cmd[0]=0x%08x, cmd[1]=0x%08x, cmd[2]=0x%08x, cmd[3]=0x%08x",
                 fetch_right_cmd[0], fetch_right_cmd[1], fetch_right_cmd[2], fetch_right_cmd[3]);
        cmd_seq[idx++] = fetch_right_cmd[0];
        cmd_seq[idx++] = fetch_right_cmd[1];
        cmd_seq[idx++] = fetch_right_cmd[2];
        cmd_seq[idx++] = fetch_right_cmd[3];

        // DISPATCH (Phase 1: Copy 512 lines from aligned buffers to tile[0])
        // Source: dispatcher_bram aligned buffers [0-511] (NOT packed 528-line block!)
        // Dest: tile_bram[0] starting at address 0
        generate_disp_command(2, 0, 512, 1'b0, disp_cmd);
        cmd_seq[idx++] = disp_cmd[0];
        cmd_seq[idx++] = disp_cmd[1];
        cmd_seq[idx++] = disp_cmd[2];
        cmd_seq[idx++] = disp_cmd[3];

        // WAIT_DISPATCH
        generate_wait_disp_command(2, wait_disp_cmd);  // Wait for DISPATCH ID=2
        cmd_seq[idx++] = wait_disp_cmd[0];
        cmd_seq[idx++] = wait_disp_cmd[1];
        cmd_seq[idx++] = wait_disp_cmd[2];
        cmd_seq[idx++] = wait_disp_cmd[3];

        // TILE (matrix multiply)
        // NEW: With two-BRAM organization, both left and right address spaces start at 0
        generate_tile_command(4, 0, 0, B, C, V, tile_cmd);
        cmd_seq[idx++] = tile_cmd[0];
        cmd_seq[idx++] = tile_cmd[1];
        cmd_seq[idx++] = tile_cmd[2];
        cmd_seq[idx++] = tile_cmd[3];

        // WAIT_TILE
        generate_wait_tile_command(5, 4, wait_tile_cmd);
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
        input logic fetch_right,  // NEW: 0=left, 1=right
        output logic [31:0] cmd [0:3]
    );
        cmd_fetch_s payload;
        
        // Pack using structure for correct bit alignment
        payload.start_addr = start_addr;
        payload.len = num_lines;
        payload.fetch_right = fetch_right;  // NEW: Set target
        payload.reserved = '0;
        
        // All commands are 4 words: header + 3 payload words (unused words are 0)
        cmd[0] = {16'd12, id, e_cmd_op_fetch};
        cmd[1] = payload[31:0];    // start_addr
        cmd[2] = payload[63:32];   // len in upper 16 bits, fetch_right bit, reserved
        cmd[3] = 32'h00000000;     // Unused payload word 3
    endtask

    task automatic generate_disp_command(
        input logic [7:0] id,
        input logic [tile_mem_addr_width_gp-1:0] disp_addr,
        input logic [tile_mem_addr_width_gp-1:0] disp_len,
        input logic man_4b,
        output logic [31:0] cmd [0:3]
    );
        // All commands are 4 words: header + 3 payload words (unused words are 0)
        cmd[0] = {16'd8, id, e_cmd_op_disp};
        cmd[1] = {man_4b, 10'b0, disp_len, disp_addr};
        cmd[2] = 32'h00000000;     // Unused payload word 2
        cmd[3] = 32'h00000000;     // Unused payload word 3
    endtask

    task automatic generate_wait_disp_command(
        input logic [7:0] wait_id,  // ID to wait for (goes in header ID field)
        output logic [31:0] cmd [0:3]
    );
        // WAIT_DISPATCH: wait_id goes in header bits [15:8] per MS2.0 spec
        // Header format: {len[31:16], wait_id[15:8], opcode[7:0]}
        cmd[0] = {16'd4, wait_id, e_cmd_op_wait_disp};
        cmd[1] = 32'h00000000;     // Unused payload word 1
        cmd[2] = 32'h00000000;     // Unused payload word 2
        cmd[3] = 32'h00000000;     // Unused payload word 3
    endtask

    task automatic generate_tile_command(
        input logic [7:0] id,
        input logic [tile_mem_addr_width_gp-1:0] left_addr,
        input logic [tile_mem_addr_width_gp-1:0] right_addr,
        input int dim_b,
        input int dim_c,
        input int dim_v,
        output logic [31:0] cmd [0:3]
    );
        cmd_header_s header;
        cmd_tile_s payload;
        
        // Pack header
        header.op       = e_cmd_op_tile;
        header.id       = id;
        header.len      = cmd_tile_len_gp;
        header.reserved = 8'h00;
        
        // Pack payload using structure (automatic bit width handling)
        payload.left_addr      = left_addr;
        payload.right_addr     = right_addr;
        payload.left_ugd_len   = 11'd1;      // Default: 1 unified group dot
        payload.right_ugd_len  = 11'd1;
        payload.vec_len        = dim_v[10:0];
        payload.dim_b          = dim_b[7:0];
        payload.dim_c          = dim_c[7:0];
        payload.dim_v          = dim_v[7:0];
        payload.flags.left_man_4b        = 1'b0;
        payload.flags.right_man_4b       = 1'b0;
        payload.flags.main_loop_over_left = 1'b0;
        payload.flags.reserved            = '0;
        
        // Output words (87 bits needs 3 words, padded to 96 bits)
        cmd[0] = header;
        cmd[1] = payload[31:0];              // Bits [31:0]
        cmd[2] = payload[63:32];             // Bits [63:32]
        cmd[3] = {9'b0, payload[86:64]};     // Bits [86:64], zero-padded
    endtask

    task automatic generate_wait_tile_command(
        input logic [7:0] id,
        input logic [7:0] wait_id,
        output logic [31:0] cmd [0:3]
    );
        // All commands are 4 words: header + 3 payload words (unused words are 0)
        cmd[0] = {wait_id, 8'd0, id, e_cmd_op_wait_tile};
        cmd[1] = 32'h00000000;     // Unused payload word 1
        cmd[2] = 32'h00000000;     // Unused payload word 2
        cmd[3] = 32'h00000000;     // Unused payload word 3
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

