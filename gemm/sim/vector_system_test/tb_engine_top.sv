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
// Refactored: Dec 18 2025
// ------------------------------------------------------------------

`timescale 1ps/1ps

`include "nap_interfaces.svh"

// Memory model latency configuration (from Makefile)
`ifndef LATENCY_CYCLES
    `define LATENCY_CYCLES 0  // Default: 0 for fast simulation
`endif

module tb_engine_top;

    import gemm_pkg::*;

    // ===================================================================
    // Constants
    // ===================================================================
    localparam string HEX_PATH = "/home/dev/Dev/elastix_gemm/hex/";

    // ===================================================================
    // Testbench Parameters
    // ===================================================================
    localparam CLK_PERIOD = 10000;  // 10000ps = 10ns = 100MHz
    localparam TGT_DATA_WIDTH = 256;
    localparam AXI_ADDR_WIDTH = 42;  // 42-bit for GDDR6 NoC addressing
    localparam GDDR6_PAGE_ID = 9'd0;  // Match ACX_GDDR6_SPACE for DMA compatibility
    localparam NUM_TILES = 8;
    localparam DEFAULT_TIMEOUT = 100000;  // Default watchdog cycles

    // ===================================================================
    // Test Configuration
    // ===================================================================
    typedef enum {
        TEST_SINGLE,           // Standard single FETCH+DISPATCH pair per side
        TEST_16_DISPATCH,      // 16 consecutive right dispatches
        TEST_MULTI_DISPATCH,   // Multiple right dispatches with different C values
        TEST_OFFSET            // col_start and tile_addr offset testing
    } test_type_e;

    typedef struct {
        int B;
        int C;
        int V;
        logic [23:0] col_en;  // Column enable mask
        string name;
        test_type_e test_type;
    } test_config_t;

    // Test configurations
    test_config_t test_configs[] = '{
        // Basic MLP tests (C = 16, baseline)
        '{B: 4,  C: 16,  V: 8, col_en: 24'h000001, name: "B4_C16_V8", test_type: TEST_SINGLE},
        '{B: 8,  C: 16,  V: 4, col_en: 24'h000001, name: "B8_C16_V4", test_type: TEST_SINGLE},
        '{B: 16, C: 16,  V: 8, col_en: 24'h000001, name: "B16_C16_V8", test_type: TEST_SINGLE},

        // C < 16 tests
        '{B: 4,  C: 8,   V: 8, col_en: 24'h000001, name: "B4_C8_V8", test_type: TEST_SINGLE},
        '{B: 8,  C: 14,  V: 4, col_en: 24'h000001, name: "B8_C14_V4", test_type: TEST_SINGLE},
        '{B: 2,  C: 4,   V: 16, col_en: 24'h000001, name: "B2_C4_V16", test_type: TEST_SINGLE},

        // C > 16 tests (column group iteration)
        '{B: 4,  C: 32,  V: 4, col_en: 24'h000001, name: "B4_C32_V4", test_type: TEST_SINGLE},
        '{B: 8,  C: 32,  V: 2, col_en: 24'h000001, name: "B8_C32_V2", test_type: TEST_SINGLE},
        '{B: 8,  C: 64,  V: 2, col_en: 24'h000001, name: "B8_C64_V2", test_type: TEST_SINGLE},
        '{B: 2,  C: 128, V: 1, col_en: 24'h000001, name: "B2_C128_V1", test_type: TEST_SINGLE},
        '{B: 1,  C: 128, V: 1, col_en: 24'h000001, name: "B1_C128_V1", test_type: TEST_SINGLE},

        // Single-dispatch tests (used for golden reference generation)
        '{B: 4,  C: 4,  V: 4, col_en: 24'hFFFFFF, name: "B4_C4_V4", test_type: TEST_SINGLE},
        '{B: 4,  C: 8,  V: 4, col_en: 24'hFFFFFF, name: "B4_C8_V4", test_type: TEST_SINGLE},
        '{B: 4,  C: 14,  V: 4, col_en: 24'hFFFFFF, name: "B4_C14_V4", test_type: TEST_SINGLE},
        '{B: 4,  C: 32,  V: 4, col_en: 24'hFFFFFF, name: "B4_C32_V4_single_dispatch", test_type: TEST_SINGLE}
    };

    // ===================================================================
    // Clock and Reset
    // ===================================================================
    logic clk;
    logic reset_n;

    initial begin
        clk = 1'b0;
        $display("========================================");
        $display("TB_ENGINE_TOP: REFACTORED VERSION");
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

    // Flow control
    logic         result_almost_full;
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

    // ===================================================================
    // AXI Interface
    // ===================================================================
    t_AXI4 #(
        .DATA_WIDTH (TGT_DATA_WIDTH),
        .ADDR_WIDTH (AXI_ADDR_WIDTH),
        .LEN_WIDTH  (8),
        .ID_WIDTH   (8)
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

        // 256-bit Result interface
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
    logic [255:0] result_bram_model [0:511];
    int           result_bram_lines_written;

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            result_bram_lines_written <= 0;
            for (int i = 0; i < 512; i++) begin
                result_bram_model[i] <= 256'h0;
            end
        end else begin
            if (result_256_valid) begin
                result_bram_model[result_256_wr_addr] <= result_256_data;
                result_bram_lines_written <= result_bram_lines_written + 1;
                $display("[TB_BRAM_MLP] @%0t WRITE: addr=%0d, data=0x%064x",
                         $time, result_256_wr_addr, result_256_data);
            end
        end
    end

    // Backward compatibility signals
    logic [12:0]  result_rd_ptr = 13'b0;
    logic [12:0]  result_wr_ptr;
    logic [13:0]  result_used_entries;
    logic         result_empty;

    assign result_wr_ptr = result_bram_lines_written * 16;
    assign result_used_entries = result_bram_lines_written * 16;
    assign result_empty = (result_bram_lines_written == 0);

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
        .NUM_BLOCKS         (20),  // 1 left + up to 16 right for 16-dispatch test
        .LATENCY_CYCLES     (`LATENCY_CYCLES),
        .MAX_OUTSTANDING    (32),
        .VERBOSITY          (0)
    ) u_memory_model (
        .i_clk              (clk),
        .i_reset_n          (reset_n),
        .axi_mem_if         (axi_ddr_if.responder),
        .o_outstanding_count  (mem_outstanding_count),
        .o_total_ar_received  (mem_total_ar_received),
        .o_total_r_issued     (mem_total_r_issued)
    );

    // ===================================================================
    // Test Control Variables
    // ===================================================================
    integer total_tests = 0;
    integer passed_tests = 0;
    integer failed_tests = 0;

    // Golden Reference Storage
    logic [15:0] golden_results [0:16383];

    // ===================================================================
    // Core Helper Tasks
    // ===================================================================

    // Task: Submit a 4-word command to FIFO
    task automatic submit_cmd(input logic [31:0] cmd [0:3]);
        for (int i = 0; i < 4; i++) begin
            cmd_fifo_wdata = cmd[i];
            cmd_fifo_wen = 1'b1;
            @(posedge clk);
        end
        cmd_fifo_wen = 1'b0;
    endtask

    // Task: Submit a sequence of commands from array
    task automatic submit_cmd_range(
        ref logic [31:0] cmd_seq [0:511],
        input int start_idx,
        input int end_idx
    );
        for (int i = start_idx; i < end_idx; i++) begin
            cmd_fifo_wdata = cmd_seq[i];
            cmd_fifo_wen = 1'b1;
            @(posedge clk);
        end
        cmd_fifo_wen = 1'b0;
    endtask

    // Task: Wait for engine to become idle
    task automatic wait_engine_idle();
        while (engine_busy) @(posedge clk);
    endtask

    // Task: Wait for results with timeout
    task automatic wait_for_results(
        input int expected_lines,
        input int timeout,
        output logic success
    );
        int count;
        count = 0;
        while ((result_bram_lines_written < expected_lines) && (count < timeout)) begin
            @(posedge clk);
            count++;
        end
        success = (count < timeout);
        if (!success) begin
            $display("[TB] ERROR: Timeout waiting for results! Expected %0d lines, got %0d",
                     expected_lines, result_bram_lines_written);
        end else begin
            $display("[TB] Results received after %0d cycles: %0d BRAM lines",
                     count, result_bram_lines_written);
        end
    endtask

    // Task: Load golden reference file
    task automatic load_golden_file(
        input string filename,
        ref logic [15:0] storage [0:16383],
        output int count
    );
        int fd;
        int scan_result;

        fd = $fopen(filename, "r");
        if (fd == 0) begin
            $display("[TB] ERROR: Cannot open golden file: %s", filename);
            count = -1;
            return;
        end

        count = 0;
        while (!$feof(fd) && count < 16384) begin
            scan_result = $fscanf(fd, "%h\n", storage[count]);
            if (scan_result == 1) count++;
        end
        $fclose(fd);
        $display("[TB] Loaded %0d golden results from %s", count, filename);
    endtask

    // Task: Validate results against golden reference
    task automatic validate_results(
        input int B,
        input int C,
        input int expected_results,
        ref logic [15:0] golden [0:16383],
        output int mismatches,
        output int results_seen
    );
        int num_col_groups;
        int batch_idx, col_idx, group_idx, col_within_group;
        int bram_line, bram_pos;
        logic [15:0] fp16_hw, golden_val;
        int diff, tolerance_lsb;
        real golden_mag;
        logic is_golden_denormal, is_hw_zero;

        num_col_groups = (C + 15) / 16;
        mismatches = 0;
        results_seen = 0;

        for (int result_idx = 0; result_idx < expected_results; result_idx++) begin
            batch_idx = result_idx / C;
            col_idx   = result_idx % C;

            if (num_col_groups > 1) begin
                group_idx        = col_idx / 16;
                col_within_group = col_idx % 16;
                bram_line        = batch_idx * num_col_groups + group_idx;
                bram_pos         = col_within_group;
            end else begin
                bram_line = batch_idx;
                bram_pos  = col_idx;
            end

            fp16_hw = result_bram_model[bram_line][bram_pos*16 +: 16];
            golden_val = golden[result_idx];

            // Check for X/Z states
            if ($isunknown(fp16_hw)) begin
                $display("[TB] ERROR: hw=0x%04x contains X/Z at result[%0d]",
                        fp16_hw, result_idx);
                mismatches++;
            end else begin
                diff = (fp16_hw > golden_val) ? fp16_hw - golden_val : golden_val - fp16_hw;
                golden_mag = (golden_val & 16'h7FFF);
                tolerance_lsb = (golden_mag * 0.05 > 50) ? int'(golden_mag * 0.05) : 50;

                is_golden_denormal = (golden_val[14:10] == 5'b0) && (golden_val[9:0] != 10'b0);
                is_hw_zero = (fp16_hw == 16'h0000) || (fp16_hw == 16'h8000);

                if (is_golden_denormal && is_hw_zero) begin
                    // Flush-to-zero acceptable
                    if (result_idx < 10 || (result_idx >= expected_results - 5)) begin
                        $display("[TB] MATCH[%0d]: hw=0x%04x golden=0x%04x (denormal flush-to-zero)",
                                result_idx, fp16_hw, golden_val);
                    end
                end else if (diff > tolerance_lsb) begin
                    $display("[TB] MISMATCH[%0d]: hw=0x%04x golden=0x%04x diff=%0d tol=%0d",
                            result_idx, fp16_hw, golden_val, diff, tolerance_lsb);
                    mismatches++;
                end else if (result_idx < 10 || (result_idx >= expected_results - 5)) begin
                    $display("[TB] MATCH[%0d]: hw=0x%04x golden=0x%04x diff=%0d",
                            result_idx, fp16_hw, golden_val, diff);
                end
            end
            results_seen++;
        end
    endtask

    // Task: Reset between tests
    task automatic reset_between_tests();
        reset_n = 1'b0;
        result_rd_ptr = 13'b0;
        repeat (10) @(posedge clk);
        reset_n = 1'b1;
        repeat (10) @(posedge clk);
        $display("[TB] Reset between tests completed at time %0t", $time);
    endtask

    // ===================================================================
    // Command Generation Tasks
    // ===================================================================

    task automatic generate_fetch_command(
        input logic [7:0] id,
        input logic [link_addr_width_gp-1:0] start_addr,
        input logic [link_len_width_gp-1:0] num_lines,
        input logic fetch_right,
        output logic [31:0] cmd [0:3]
    );
        cmd[0] = (32'h00 << 24) | (32'd16 << 16) | ({24'h0, id} << 8) | {24'h0, e_cmd_op_fetch};
        cmd[1] = start_addr[31:0];
        cmd[2] = {16'b0, num_lines[15:0]};
        cmd[3] = {31'b0, fetch_right};
    endtask

    task automatic generate_disp_command(
        input logic [7:0] id,
        input logic [7:0] man_nv_cnt,
        input logic [7:0] ugd_vec_size,
        input logic [15:0] tile_addr,
        input logic man_4b,
        input logic [23:0] col_en,
        input logic [4:0] col_start,
        input logic disp_right,
        input logic broadcast,
        output logic [31:0] cmd [0:3]
    );
        cmd[0] = (32'h00 << 24) | (32'd16 << 16) | ({24'h0, id} << 8) | {24'h0, e_cmd_op_disp};
        cmd[1] = {8'b0, man_nv_cnt[7:0], 8'b0, ugd_vec_size[7:0]};
        cmd[2] = {16'b0, tile_addr[15:0]};
        cmd[3] = {col_en[23:0], col_start[4:0], disp_right, broadcast, man_4b};
    endtask

    task automatic generate_wait_disp_command(
        input logic [7:0] id,
        input logic [7:0] wait_id,
        output logic [31:0] cmd [0:3]
    );
        cmd[0] = (32'h00 << 24) | (32'd16 << 16) | ({24'h0, id} << 8) | {24'h0, e_cmd_op_wait_disp};
        cmd[1] = {24'd0, wait_id[7:0]};
        cmd[2] = 32'h00000000;
        cmd[3] = 32'h00000000;
    endtask

    task automatic generate_tile_command(
        input logic [7:0] id,
        input int left_addr,
        input int right_addr,
        input int dim_b,
        input int dim_c,
        input int dim_v,
        input logic [23:0] col_en,
        input logic left_4b,
        input logic right_4b,
        input logic main_loop_left,
        output logic [31:0] cmd [0:3]
    );
        logic [15:0] left_addr_16  = left_addr[15:0];
        logic [15:0] right_addr_16 = right_addr[15:0];
        logic [7:0] left_ugd_len  = dim_b[7:0];
        logic [7:0] right_ugd_len = dim_c[7:0];
        logic [7:0] vec_len       = dim_v[7:0];

        cmd[0] = (32'h00 << 24) | (32'd16 << 16) | ({24'h0, id} << 8) | {24'h0, e_cmd_op_tile};
        cmd[1] = {left_addr_16, right_addr_16};
        cmd[2] = {8'b0, left_ugd_len, right_ugd_len, vec_len};
        cmd[3] = {col_en, 5'b0, left_4b, right_4b, main_loop_left};
    endtask

    task automatic generate_wait_tile_command(
        input logic [7:0] id,
        input logic [7:0] wait_id,
        output logic [31:0] cmd [0:3]
    );
        cmd[0] = (32'h00 << 24) | (32'd16 << 16) | ({24'h0, id} << 8) | {24'h0, e_cmd_op_wait_tile};
        cmd[1] = {24'd0, wait_id[7:0]};
        cmd[2] = 32'h00000000;
        cmd[3] = 32'h00000000;
    endtask

    task automatic generate_readout_command(
        input logic [7:0]  id,
        input logic [7:0]  start_col,
        input logic [31:0] rd_len,
        output logic [31:0] cmd [0:3]
    );
        cmd[0] = (32'h00 << 24) | (32'd16 << 16) | ({24'h0, id} << 8) | {24'h0, e_cmd_op_readout};
        cmd[1] = {24'd0, start_col[7:0]};
        cmd[2] = rd_len[31:0];
        cmd[3] = 32'h00000000;
    endtask

    // ===================================================================
    // Compound Command Tasks
    // ===================================================================

    // Task: Execute FETCH + DISPATCH + WAIT_DISPATCH for LEFT matrix
    task automatic fetch_dispatch_left(
        ref int cmd_id,
        input int B,
        input int V,
        input logic [23:0] col_en,
        input int fetch_addr,
        input int fetch_len,
        input int tile_addr
    );
        logic [31:0] cmd [0:3];

        // FETCH LEFT
        generate_fetch_command(cmd_id, fetch_addr, fetch_len, 1'b0, cmd);
        submit_cmd(cmd);
        cmd_id++;

        // DISPATCH LEFT (broadcast)
        generate_disp_command(cmd_id, B*V, V, tile_addr[15:0], 1'b0, col_en, 5'd0, 1'b0, 1'b1, cmd);
        submit_cmd(cmd);
        cmd_id++;

        // WAIT_DISPATCH LEFT
        generate_wait_disp_command(cmd_id, cmd_id-1, cmd);
        submit_cmd(cmd);
        cmd_id++;

        wait_engine_idle();
        $display("[TB] LEFT dispatch complete at time %0t", $time);
    endtask

    // Task: Execute FETCH + DISPATCH + WAIT_DISPATCH for RIGHT matrix
    task automatic fetch_dispatch_right(
        ref int cmd_id,
        input int C,
        input int V,
        input logic [23:0] col_en,
        input int fetch_addr,
        input int fetch_len,
        input int tile_addr,
        input int col_start
    );
        logic [31:0] cmd [0:3];

        // FETCH RIGHT
        generate_fetch_command(cmd_id, fetch_addr, fetch_len, 1'b1, cmd);
        submit_cmd(cmd);
        cmd_id++;

        // DISPATCH RIGHT (distribute)
        generate_disp_command(cmd_id, C*V, V, tile_addr[15:0], 1'b0, col_en, col_start[4:0], 1'b1, 1'b0, cmd);
        submit_cmd(cmd);
        cmd_id++;

        // WAIT_DISPATCH RIGHT
        generate_wait_disp_command(cmd_id, cmd_id-1, cmd);
        submit_cmd(cmd);
        cmd_id++;

        wait_engine_idle();
        $display("[TB] RIGHT dispatch complete at time %0t", $time);
    endtask

    // Task: Execute TILE + WAIT_TILE + READOUT
    task automatic tile_and_readout(
        ref int cmd_id,
        input int B,
        input int C,
        input int V,
        input logic [23:0] col_en,
        input int left_addr,
        input int right_addr
    );
        logic [31:0] cmd [0:3];
        int num_col_groups;
        int rd_len_padded;

        num_col_groups = (C + 15) / 16;
        rd_len_padded = B * num_col_groups * 16;

        // TILE
        generate_tile_command(cmd_id, left_addr, right_addr, B, C, V, col_en, 1'b0, 1'b0, 1'b0, cmd);
        submit_cmd(cmd);
        cmd_id++;

        // WAIT_TILE
        generate_wait_tile_command(cmd_id, cmd_id-1, cmd);
        submit_cmd(cmd);
        cmd_id++;

        // READOUT
        generate_readout_command(cmd_id, 8'd0, rd_len_padded, cmd);
        submit_cmd(cmd);
        cmd_id++;

        $display("[TB] TILE+READOUT commands submitted (B=%0d, C=%0d, V=%0d)", B, C, V);
    endtask

    // ===================================================================
    // Test Execution Tasks
    // ===================================================================

    // Task: Run a single standard test
    task automatic run_single_test(
        input int config_B,
        input int config_C,
        input int config_V,
        input logic [23:0] config_col_en,
        input string test_name
    );
        int cmd_id;
        int expected_results, expected_results_padded, expected_bram_lines;
        int mismatches, results_seen;
        int golden_count;
        string golden_filename;
        logic success;
        longint start_time, end_time;

        total_tests++;
        $display("\n[TB] ====================================================================");
        $display("[TB] TEST %0d: %s (B=%0d, C=%0d, V=%0d)", total_tests, test_name, config_B, config_C, config_V);
        $display("[TB] ====================================================================");

        // Load golden reference
        golden_filename = $sformatf("%sgolden_%s.hex", HEX_PATH, test_name);
        load_golden_file(golden_filename, golden_results, golden_count);
        if (golden_count < 0) begin
            failed_tests++;
            return;
        end

        start_time = $time;
        cmd_id = 0;

        // LEFT: FETCH + DISPATCH
        fetch_dispatch_left(cmd_id, config_B, config_V, config_col_en, 0, 528, 0);

        // RIGHT: FETCH + DISPATCH
        fetch_dispatch_right(cmd_id, config_C, config_V, config_col_en, 528, 528, 0, 0);

        // TILE + READOUT
        tile_and_readout(cmd_id, config_B, config_C, config_V, config_col_en, 0, 0);

        // Wait for results
        expected_results = config_B * config_C;
        expected_results_padded = config_B * ((config_C + 15) / 16) * 16;
        expected_bram_lines = expected_results_padded / 16;

        wait_for_results(expected_bram_lines, DEFAULT_TIMEOUT, success);
        if (!success) begin
            failed_tests++;
            return;
        end

        // Wait for BRAM write to propagate
        repeat (2) @(posedge clk);

        // Validate results
        validate_results(config_B, config_C, expected_results, golden_results, mismatches, results_seen);

        end_time = $time;
        $display("[TB] Test completed in %0d cycles", (end_time - start_time) / CLK_PERIOD);

        if (mismatches == 0 && results_seen == expected_results) begin
            $display("[TB] PASS: %s - All %0d results matched!", test_name, results_seen);
            passed_tests++;
        end else begin
            $display("[TB] FAIL: %s - %0d mismatches, %0d/%0d results",
                     test_name, mismatches, results_seen, expected_results);
            failed_tests++;
        end
    endtask

    // Task: Run 16-dispatch test
    task automatic run_16_dispatch_test();
        localparam int B = 4;
        localparam int V = 32;
        localparam int C_PER_DISPATCH = 4;
        localparam int NUM_DISPATCHES = 16;
        localparam int C_TOTAL = C_PER_DISPATCH * NUM_DISPATCHES;  // 64
        localparam int NUM_COL_GROUPS = (C_TOTAL + 15) / 16;  // 4

        int cmd_id;
        int expected_results, expected_bram_lines;
        int mismatches, results_seen;
        logic success;
        logic [31:0] cmd [0:3];

        // Variables for golden loading
        int file_seg, scan_seg;
        string golden_seg_file;
        logic [15:0] file_val;
        logic load_ok;

        total_tests++;
        $display("\n[TB] ====================================================================");
        $display("[TB] 16-DISPATCH TEST: B=%0d, C_total=%0d (16 × C=%0d), V=%0d",
                 B, C_TOTAL, C_PER_DISPATCH, V);
        $display("[TB] ====================================================================");

        // Load 16 individual golden files
        load_ok = 1;
        for (int disp_idx = 0; disp_idx < NUM_DISPATCHES && load_ok; disp_idx++) begin
            golden_seg_file = $sformatf("%sgolden_B4_C4_V32_%0d.hex", HEX_PATH, disp_idx);
            file_seg = $fopen(golden_seg_file, "r");
            if (file_seg == 0) begin
                $display("[TB] ERROR: Cannot open %s", golden_seg_file);
                failed_tests++;
                load_ok = 0;
            end else begin
                for (int b = 0; b < B; b++) begin
                    for (int c = 0; c < 4; c++) begin
                        scan_seg = $fscanf(file_seg, "%h\n", file_val);
                        if (scan_seg == 1) begin
                            golden_results[b * C_TOTAL + disp_idx * 4 + c] = file_val;
                        end
                    end
                end
                $fclose(file_seg);
            end
        end
        if (!load_ok) return;
        $display("[TB] Loaded 16 golden files for B4_C64_V32");

        cmd_id = 0;

        // LEFT: FETCH + DISPATCH (528 lines: 16 exp + 512 man)
        fetch_dispatch_left(cmd_id, B, V, 24'hFFFFFF, 0, 528, 0);

        // Load ALL 16 right matrices into memory model FIRST
        // NOTE: Hex files have 528 lines: 16 exponent lines + 512 mantissa lines
        $display("[TB] === Loading 16 right matrices into memory model ===");
        for (int disp_idx = 0; disp_idx < NUM_DISPATCHES; disp_idx++) begin
            string right_hex_file;
            int fetch_addr;
            fetch_addr = 528 + disp_idx * 528;
            right_hex_file = $sformatf("%sright_%0d.hex", HEX_PATH, disp_idx);
            u_memory_model.load_hex_file(right_hex_file, fetch_addr, 528);  // Full hex file: 16 exp + 512 man
        end
        $display("[TB] All 16 right matrices loaded into memory model");

        // Now dispatch all 16 right matrices
        $display("[TB] === Dispatching 16 right matrices ===");
        for (int disp_idx = 0; disp_idx < NUM_DISPATCHES; disp_idx++) begin
            int fetch_addr;
            int group_idx, col_start_val, tile_addr_val;

            fetch_addr = 528 + disp_idx * 528;
            group_idx = disp_idx / 4;
            col_start_val = (disp_idx % 4) * 4;
            tile_addr_val = group_idx * V * 8;

            $display("[TB] Dispatch %0d: col_start=%0d, tile_addr=%0d, fetch_addr=%0d",
                     disp_idx + 1, col_start_val, tile_addr_val, fetch_addr);

            // FETCH 528 lines: 16 exponent + 512 mantissa (full hex file format)
            fetch_dispatch_right(cmd_id, C_PER_DISPATCH, V, 24'hFFFFFF,
                                fetch_addr, 528, tile_addr_val, col_start_val);
        end

        // TILE + READOUT
        tile_and_readout(cmd_id, B, C_TOTAL, V, 24'hFFFFFF, 0, 0);

        // Wait for results
        expected_results = B * C_TOTAL;
        expected_bram_lines = (expected_results + 15) / 16;

        wait_for_results(expected_bram_lines, 200000, success);
        if (!success) begin
            failed_tests++;
            return;
        end

        repeat (10) @(posedge clk);

        // Validate with custom 16-dispatch logic
        mismatches = 0;
        results_seen = 0;

        for (int batch_idx = 0; batch_idx < B; batch_idx++) begin
            for (int col_idx = 0; col_idx < C_TOTAL; col_idx++) begin
                int group_idx, col_within_group, pulse_idx, hw_idx;
                int bram_line, bram_pos;
                logic [15:0] hw_result, golden_val;
                int diff, tolerance;

                group_idx = col_idx / 16;
                col_within_group = col_idx % 16;
                pulse_idx = batch_idx * NUM_COL_GROUPS + group_idx;
                hw_idx = pulse_idx * 16 + col_within_group;

                bram_line = hw_idx / 16;
                bram_pos = hw_idx % 16;
                hw_result = result_bram_model[bram_line][bram_pos*16 +: 16];
                golden_val = golden_results[batch_idx * C_TOTAL + col_idx];

                diff = (hw_result > golden_val) ? (hw_result - golden_val) : (golden_val - hw_result);
                tolerance = (golden_val[14:10] > 5'd15) ? (1 << (golden_val[14:10] - 15)) : 1;
                tolerance = (tolerance < 32) ? 32 : tolerance;

                if (diff > tolerance) begin
                    $display("[TB] MISMATCH[%0d]: batch=%0d, col=%0d, hw=0x%04x, golden=0x%04x, diff=%0d",
                             results_seen, batch_idx, col_idx, hw_result, golden_val, diff);
                    mismatches++;
                end
                results_seen++;
            end
        end

        if (mismatches > 0) begin
            $display("[TB] 16-DISPATCH TEST FAILED: %0d/%0d mismatches", mismatches, results_seen);
            failed_tests++;
        end else begin
            $display("[TB] 16-DISPATCH TEST PASSED: All %0d results matched!", results_seen);
            passed_tests++;
        end
    endtask

    // ===================================================================
    // Main Test Sequence
    // ===================================================================
    initial begin
        $display("\n================================================================================");
        $display("TB: MS2.0 GEMM Engine Top Testbench - FIFO Interface (Refactored)");
        $display("================================================================================\n");

        // Initialize signals
        cmd_fifo_wdata = 32'h0;
        cmd_fifo_wen = 1'b0;

        // Wait for reset to complete
        wait (reset_n == 1'b1);
        repeat (10) @(posedge clk);

        // Run all test configurations
        foreach (test_configs[i]) begin
            if (i > 0) reset_between_tests();

            case (test_configs[i].test_type)
                TEST_SINGLE: begin
                    run_single_test(
                        test_configs[i].B,
                        test_configs[i].C,
                        test_configs[i].V,
                        test_configs[i].col_en,
                        test_configs[i].name
                    );
                end
                default: begin
                    // Other test types handled separately
                end
            endcase
            repeat (100) @(posedge clk);
        end

        // Run 16-dispatch test
        reset_between_tests();
        run_16_dispatch_test();
        repeat (100) @(posedge clk);

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
    // Watchdog Timer
    // ===================================================================
    initial begin
        #10000000000;  // 10ms timeout (in ps)
        $display("\n[TB] ERROR: Watchdog timeout!");
        $display("[TB] Test did not complete in time");
        $finish;
    end

endmodule : tb_engine_top
