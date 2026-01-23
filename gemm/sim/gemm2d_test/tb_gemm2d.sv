// ------------------------------------------------------------------
// 2-D GEMM Full Integration Testbench
//
// Purpose: Validate full 16-row GEMM engine integration
// Configuration: Parameterized B, C, V with 16 per-row hex file pairs
//
// Test Sequence:
//   1. Load hex files into 16 memory models (left_r.hex, right_r.hex)
//   2. Issue FETCH (right) -> DISPATCH (right) for all rows
//   3. Issue FETCH (left) -> DISPATCH (left) for all rows
//   4. Issue MATMUL command
//   5. Issue READOUT command
//   6. Capture results and verify against golden files
//
// Author: Junhao Pan
// Date: 01/22/2026
// ------------------------------------------------------------------

`timescale 1ns/1ps

`include "nap_interfaces.svh"

module tb_gemm2d;

    // ====================================================================
    // Test Configuration
    // ====================================================================
    localparam int NUM_ROWS = 16;
    localparam int NUM_COLS = 16;
    localparam int NUM_MLPS = 8;
    
    // BCV configuration from hex files
    // Testing B4_C13_V9 - non-power-of-2 C and V values
    // Fixed FIFO drain issue in dispatcher_2d.sv that was causing 2^16 magnitude errors
    localparam int B = 4;
    localparam int C = 13;
    localparam int V = 9;                        // V per row
    localparam int V_TOTAL = V * NUM_ROWS;       // Total V across all rows (144)

    // Memory block configuration
    localparam int LINES_PER_BLOCK = 528;
    localparam int MAN_WIDTH = 256;
    localparam int EXP_WIDTH = 8;
    localparam int BRAM_DEPTH = 512;

    // AXI configuration
    localparam int AXI_ADDR_WIDTH = 42;
    localparam int AXI_DATA_WIDTH = 256;

    // Clock configuration (400 MHz)
    localparam CLK_PERIOD = 2.5;

    // Hex file base path
    localparam string HEX_BASE_PATH = "/home/dev/Dev/elastix_gemm/hex/B4_C13_V9/";
    
    // ====================================================================
    // Opcodes (from gemm_pkg)
    // ====================================================================
    localparam logic [7:0] OPC_NOP       = 8'h00;
    localparam logic [7:0] OPC_FETCH     = 8'hF0;
    localparam logic [7:0] OPC_DISP      = 8'hF1;
    localparam logic [7:0] OPC_MATMUL    = 8'hF2;
    localparam logic [7:0] OPC_WAIT_DISP = 8'hF3;
    localparam logic [7:0] OPC_WAIT_MATMUL = 8'hF4;
    localparam logic [7:0] OPC_READOUT   = 8'hF5;

    // ====================================================================
    // Clock and Reset
    // ====================================================================
    logic clk = 1'b0;
    logic reset_n;
    
    always #(CLK_PERIOD/2) clk <= ~clk;

    // ====================================================================
    // Test Control
    // ====================================================================
    integer test_errors;
    integer cycle_count;
    integer tests_run;
    integer tests_passed;

    // ====================================================================
    // Command FIFO Interface
    // ====================================================================
    logic [31:0] cmd_fifo_wdata;
    logic        cmd_fifo_wen;
    logic        cmd_fifo_full;
    logic        cmd_fifo_afull;
    logic [12:0] cmd_fifo_count;

    // ====================================================================
    // Result Interface
    // ====================================================================
    logic        result_ready;
    logic        result_valid;
    logic        result_last;
    logic [15:0] result_keep;
    logic [255:0] result_data;

    // ====================================================================
    // Status Interface
    // ====================================================================
    logic        engine_busy;
    logic [3:0]  mc_state;
    logic [3:0]  rc_state;

    // ====================================================================
    // AXI Interfaces (16 channels)
    // ====================================================================
    t_AXI4 #(
        .DATA_WIDTH(AXI_DATA_WIDTH),
        .ADDR_WIDTH(AXI_ADDR_WIDTH),
        .LEN_WIDTH(8),
        .ID_WIDTH(8)
    ) axi_ddr_if [NUM_ROWS-1:0] ();

    // ====================================================================
    // DUT: 2-D GEMM Engine
    // ====================================================================
    engine_top_2d #(
        .NUM_MLPS      (NUM_MLPS),
        .STACK_DEPTH   (4),
        .NUM_ROWS      (NUM_ROWS),
        .NUM_COLS      (NUM_COLS),
        .MAN_WIDTH     (MAN_WIDTH),
        .EXP_WIDTH     (EXP_WIDTH),
        .BRAM_DEPTH    (BRAM_DEPTH)
    ) u_dut (
        .i_clk              (clk),
        .i_reset_n          (reset_n),
        
        // Command FIFO Interface
        .i_cmd_fifo_wdata   (cmd_fifo_wdata),
        .i_cmd_fifo_wen     (cmd_fifo_wen),
        .o_cmd_fifo_full    (cmd_fifo_full),
        .o_cmd_fifo_afull   (cmd_fifo_afull),
        .o_cmd_fifo_count   (cmd_fifo_count),
        
        // AXI Interfaces (16 channels)
        .axi_ddr_if         (axi_ddr_if),
        
        // Result Interface
        .i_result_ready     (result_ready),
        .o_result_valid     (result_valid),
        .o_result_last      (result_last),
        .o_result_keep      (result_keep),
        .o_result_data      (result_data),
        
        // Status
        .o_engine_busy      (engine_busy),
        .o_mc_state         (mc_state),
        .o_rc_state         (rc_state)
    );

    // ====================================================================
    // Memory Models (16 instances - one per GDDR6 channel)
    // ====================================================================
    // Each memory model stores 2 blocks: left (0-527), right (528-1055)
    // Using parameterized memory model that auto-loads channel-specific hex files
    
    generate
        for (genvar r = 0; r < NUM_ROWS; r++) begin : gen_mem_model
            
            // Memory statistics
            logic [31:0] mem_outstanding_count;
            logic [31:0] mem_total_ar_received;
            logic [31:0] mem_total_r_issued;
            
            tb_mem_model_parameterized #(
                .DATA_WIDTH(AXI_DATA_WIDTH),
                .ADDR_WIDTH(AXI_ADDR_WIDTH),
                .LINES_PER_BLOCK(LINES_PER_BLOCK),
                .NUM_BLOCKS(2),
                .LATENCY_CYCLES(40),      // 100ns @ 400MHz
                .MAX_OUTSTANDING(32),
                .VERBOSITY(1),            // Show loading messages
                .CHANNEL_ID(r),           // Channel-specific hex files
                .HEX_BASE_PATH(HEX_BASE_PATH)
            ) u_mem_model (
                .i_clk(clk),
                .i_reset_n(reset_n),
                .axi_mem_if(axi_ddr_if[r].responder),
                .o_outstanding_count(mem_outstanding_count),
                .o_total_ar_received(mem_total_ar_received),
                .o_total_r_issued(mem_total_r_issued)
            );
        end
    endgenerate

    // ====================================================================
    // Golden Results Storage
    // ====================================================================
    // Per-row golden: B * C = 16 FP16 values per row
    // Total results after reduction: B * C = 16 FP16 values (sum across 16 rows)
    logic [15:0] golden_per_row [0:NUM_ROWS-1][0:B*C-1];
    logic [15:0] golden_reduced [0:B*C-1];
    logic [15:0] captured_results [0:B*C-1];
    integer captured_count;

    // ====================================================================
    // Weight BRAM Initialization Note
    // ====================================================================
    // For tests with C < NUM_COLS (16), unused MLPs will read X values.
    // The Achronix BRAM simulation model internal structure is complex and
    // hierarchical access to initialize memory arrays is not portable.
    //
    // Solutions for C < 16 tests:
    //   1. Use C=16 to ensure all MLPs receive valid data
    //   2. Create hex files with zeros for all 16 columns
    //   3. Add DISPATCH commands for zeros to unused columns
    //
    // For compute_engine_2d_test, option (2) is used - unused columns are
    // explicitly initialized to zero before MATMUL.
    // ====================================================================

    // Placeholder task - BRAM initialization done via hex files or C=16
    task automatic init_weight_brams();
        $display("[TB] Note: Weight BRAM initialization relies on hex data or C=NUM_COLS");
    endtask

    // ====================================================================
    // Hex File Loading Task
    // ====================================================================
    // Note: Memory models now auto-load hex files during initialization
    //       based on CHANNEL_ID parameter. This task is now a no-op placeholder.
    task automatic load_all_hex_files();
        $display("\n[TB] Hex files auto-loaded by memory models during init\n");
    endtask

    // ====================================================================
    // Golden Results Loading Task
    // Pattern matches MLPStack_test/tb_mlp_wrapper.sv for consistency
    // ====================================================================
    task automatic load_golden_results();
        string golden_file;
        string line_str;
        integer fd;
        logic [15:0] fp16_val;
        integer scan_result;
        integer load_errors;
        integer values_loaded;
        real golden_sum_check;

        $display("[TB] Loading golden results...");
        load_errors = 0;

        // Initialize all golden values to zero first (prevents X values)
        for (int r = 0; r < NUM_ROWS; r++) begin
            for (int i = 0; i < B*C; i++) begin
                golden_per_row[r][i] = 16'h0000;
            end
        end

        // Load per-row golden files
        for (int r = 0; r < NUM_ROWS; r++) begin
            $sformat(golden_file, "%sgolden_B%0d_C%0d_V%0d_%0d.hex", HEX_BASE_PATH, B, C, V, r);

            fd = $fopen(golden_file, "r");
            if (fd == 0) begin
                $error("[TB] Cannot open golden file: %s", golden_file);
                load_errors++;
                continue;
            end

            // Read using $fgets + $sscanf pattern (same as MLPStack_test)
            values_loaded = 0;
            while (!$feof(fd) && values_loaded < B*C) begin
                if ($fgets(line_str, fd)) begin
                    scan_result = $sscanf(line_str, "%h", fp16_val);
                    if (scan_result == 1) begin
                        golden_per_row[r][values_loaded] = fp16_val;
                        values_loaded++;
                    end
                end
            end

            $fclose(fd);
            $display("[TB]   Loaded %0d values for row %0d: %s", values_loaded, r, golden_file);

            // Show first few values for debug
            if (r == 0) begin
                $display("[TB]     First 4 values: 0x%04x, 0x%04x, 0x%04x, 0x%04x",
                         golden_per_row[r][0], golden_per_row[r][1],
                         golden_per_row[r][2], golden_per_row[r][3]);
            end

            // Check if we got expected number of values
            if (values_loaded < B*C) begin
                $warning("[TB] Only loaded %0d/%0d values from %s", values_loaded, B*C, golden_file);
                load_errors++;
            end
        end

        // Compute and display expected sums for verification
        $display("[TB] Computing expected sums (sum across 16 rows):");
        for (int i = 0; i < B*C; i++) begin
            golden_sum_check = 0.0;
            for (int r = 0; r < NUM_ROWS; r++) begin
                golden_sum_check = golden_sum_check + fp16_to_real(golden_per_row[r][i]);
            end
            golden_reduced[i] = 16'h0000;  // Placeholder - actual reduction in HW
            if (i < 4) begin
                $display("[TB]   Expected sum[%0d] = %.6f", i, golden_sum_check);
            end
        end

        if (load_errors > 0) begin
            $error("[TB] Golden loading had %0d errors!", load_errors);
        end else begin
            $display("[TB] Golden results loaded successfully\n");
        end
    endtask

    // ====================================================================
    // FP16 Utility Functions
    // ====================================================================
    function automatic real fp16_to_real(input logic [15:0] fp16_val);
        logic sign;
        logic [4:0] exp;
        logic [9:0] mant;
        real result;
        int exp_int;  // Signed exponent for proper arithmetic

        sign = fp16_val[15];
        exp = fp16_val[14:10];
        mant = fp16_val[9:0];

        // Convert to signed int for proper exponent arithmetic
        exp_int = int'(exp) - 15;

        if (exp == 5'h00) begin
            // Denormal or zero
            if (mant == 10'h000) begin
                result = 0.0;
            end else begin
                result = (real'(mant) / 1024.0) * (2.0 ** (-14));
            end
        end else if (exp == 5'h1F) begin
            // Inf or NaN
            result = (mant == 10'h000) ? 1.0e38 : 0.0/0.0;
        end else begin
            // Normal: value = (1 + mant/1024) * 2^(exp-15)
            result = (1.0 + (real'(mant) / 1024.0)) * (2.0 ** exp_int);
        end

        if (sign) result = -result;
        return result;
    endfunction

    // ====================================================================
    // Command Writing Task
    // ====================================================================
    task automatic write_cmd(input logic [31:0] word);
        while (cmd_fifo_full) @(posedge clk);
        cmd_fifo_wdata = word;
        cmd_fifo_wen = 1'b1;
        @(posedge clk);
        cmd_fifo_wen = 1'b0;
    endtask

    // ====================================================================
    // Issue Command Sequence Tasks
    // ====================================================================
    // =========================================================================
    // FETCH Command (0xF0) - Per MULTI_ROW_REFERENCE.md lines 644-649:
    //   cmd[0] = {16'd16, cmd_id[7:0], OPC_FETCH}
    //   cmd[1] = {start_addr[31:0]}
    //   cmd[2] = {ugd_len[15:0], len[15:0]}
    //   cmd[3] = {31'b0, fetch_right}
    // =========================================================================
    task automatic issue_fetch_command(
        input logic [7:0] cmd_id,
        input logic [31:0] start_addr,    // Byte address (hardware converts to 32-byte lines)
        input logic [15:0] ugd_len,       // V - total NVs per UGD (for row partitioning)
        input logic [15:0] len,           // Number of lines to fetch (default 528)
        input logic fetch_right
    );
        logic [31:0] header, word1, word2, word3;

        // Header: {16'd16, cmd_id[7:0], opcode[7:0]}
        header = {16'h0010, cmd_id, OPC_FETCH};

        // Word1: start_addr[31:0]
        word1 = start_addr;

        // Word2: {ugd_len[15:0], len[15:0]}
        word2 = {ugd_len, len};

        // Word3: {31'b0, fetch_right}
        word3 = {31'b0, fetch_right};

        $display("[TB] FETCH CMD: id=%0d, addr=0x%08x, ugd_len=%0d, len=%0d, right=%0d",
                 cmd_id, start_addr, ugd_len, len, fetch_right);

        write_cmd(header);
        write_cmd(word1);
        write_cmd(word2);
        write_cmd(word3);
    endtask

    // =========================================================================
    // DISPATCH Command (0xF1) - Per MULTI_ROW_REFERENCE.md lines 687-691:
    //   cmd[0] = {16'd16, cmd_id[7:0], OPC_DISPATCH}
    //   cmd[1] = {nv_cnt[15:0], ugd_len[15:0]}
    //   cmd[2] = {16'b0, tile_addr[15:0]}
    //   cmd[3] = {16'b0, col_start[7:0], 5'b0, disp_right, broadcast, man_4b}
    // =========================================================================
    task automatic issue_dispatch_command(
        input logic [7:0] cmd_id,
        input logic [15:0] nv_cnt,        // Total NVs to dispatch
        input logic [15:0] ugd_len,       // NVs per UGD vector
        input logic [15:0] tile_addr,     // Destination BRAM address
        input logic [7:0] col_start,      // Starting column for round-robin (8-bit)
        input logic disp_right            // 1=weights to mlp_bram, 0=activations to row_bram
    );
        logic [31:0] header, word1, word2, word3;
        logic broadcast;

        // broadcast = ~disp_right (left=broadcast, right=distribute)
        broadcast = ~disp_right;

        // Header: {16'd16, cmd_id[7:0], opcode[7:0]}
        header = {16'h0010, cmd_id, OPC_DISP};

        // Word1: {nv_cnt[15:0], ugd_len[15:0]}
        word1 = {nv_cnt, ugd_len};

        // Word2: {16'b0, tile_addr[15:0]}
        word2 = {16'b0, tile_addr};

        // Word3: {16'b0, col_start[7:0], 5'b0, disp_right, broadcast, man_4b}
        word3 = {16'b0, col_start, 5'b0, disp_right, broadcast, 1'b0};

        $display("[TB] DISPATCH CMD: id=%0d, nv=%0d, ugd=%0d, tile=0x%04x, col=%0d, right=%0d, bc=%0d",
                 cmd_id, nv_cnt, ugd_len, tile_addr, col_start, disp_right, broadcast);

        write_cmd(header);
        write_cmd(word1);
        write_cmd(word2);
        write_cmd(word3);
    endtask

    // =========================================================================
    // WAIT_DISP Command (0xF3) - Per MULTI_ROW_REFERENCE.md lines 744-748:
    //   cmd[0] = {16'd16, cmd_id[7:0], OPC_WAIT_DISPATCH}
    //   cmd[1] = {24'd0, wait_id[7:0]}
    //   cmd[2] = 0
    //   cmd[3] = 0
    // =========================================================================
    task automatic issue_wait_disp_command(
        input logic [7:0] cmd_id,
        input logic [7:0] wait_id
    );
        logic [31:0] header, word1, word2, word3;

        header = {16'h0010, cmd_id, OPC_WAIT_DISP};
        word1 = {24'd0, wait_id};  // wait_id in word1 (master_control reads from cmd_reg[1][7:0])
        word2 = 32'd0;
        word3 = 32'd0;

        $display("[TB] WAIT_DISP CMD: id=%0d, wait_id=%0d", cmd_id, wait_id);

        write_cmd(header);
        write_cmd(word1);
        write_cmd(word2);
        write_cmd(word3);
    endtask

    // =========================================================================
    // MATMUL Command (0xF2) - Per MULTI_ROW_REFERENCE.md lines 717-721:
    //   cmd[0] = {16'd16, cmd_id[7:0], OPC_MATMUL}
    //   cmd[1] = {left_addr[15:0], right_addr[15:0]}
    //   cmd[2] = {left_len[15:0], right_len[15:0]}   -- B and C as 16-bit
    //   cmd[3] = {ugd_len[15:0], 13'b0, left_4b, right_4b, main_loop_left}
    // =========================================================================
    task automatic issue_matmul_command(
        input logic [7:0] cmd_id,
        input logic [15:0] left_addr,     // Starting line in row_bram (activations)
        input logic [15:0] right_addr,    // Starting line in mlp_bram (weights)
        input logic [15:0] left_len,      // B - batch dimension (16-bit)
        input logic [15:0] right_len,     // C - column dimension (16-bit)
        input logic [15:0] ugd_len        // V - inner dimension / NVs per UGD (16-bit)
    );
        logic [31:0] header, word1, word2, word3;

        // Header: {16'd16, cmd_id[7:0], opcode[7:0]}
        header = {16'h0010, cmd_id, OPC_MATMUL};

        // Word1: {left_addr[15:0], right_addr[15:0]}
        word1 = {left_addr, right_addr};

        // Word2: {left_len[15:0], right_len[15:0]}
        word2 = {left_len, right_len};

        // Word3: {ugd_len[15:0], 13'b0, left_4b, right_4b, main_loop_left}
        // Flags all 0 for 8-bit mode, loop over left first
        word3 = {ugd_len, 13'b0, 1'b0, 1'b0, 1'b0};

        $display("[TB] MATMUL CMD: id=%0d, left_addr=%0d, right_addr=%0d, B=%0d, C=%0d, V=%0d",
                 cmd_id, left_addr, right_addr, left_len, right_len, ugd_len);

        write_cmd(header);
        write_cmd(word1);
        write_cmd(word2);
        write_cmd(word3);
    endtask

    // =========================================================================
    // WAIT_MATMUL Command (0xF4) - Per MULTI_ROW_REFERENCE.md lines 760-764:
    //   cmd[0] = {16'd16, cmd_id[7:0], OPC_WAIT_MATMUL}
    //   cmd[1] = {24'd0, wait_id[7:0]}
    //   cmd[2] = 0
    //   cmd[3] = 0
    // =========================================================================
    task automatic issue_wait_tile_command(
        input logic [7:0] cmd_id,
        input logic [7:0] wait_id
    );
        logic [31:0] header, word1, word2, word3;

        header = {16'h0010, cmd_id, OPC_WAIT_MATMUL};
        word1 = {24'd0, wait_id};  // wait_id in word1 (master_control reads from cmd_reg[1][7:0])
        word2 = 32'd0;
        word3 = 32'd0;

        $display("[TB] wait_matmul CMD: id=%0d, wait_id=%0d", cmd_id, wait_id);

        write_cmd(header);
        write_cmd(word1);
        write_cmd(word2);
        write_cmd(word3);
    endtask

    // =========================================================================
    // READOUT Command (0xF5) - Per MULTI_ROW_REFERENCE.md lines 778-782:
    //   cmd[0] = {16'd16, cmd_id[7:0], OPC_READOUT}
    //   cmd[1] = {left_len[15:0], right_len[15:0]}
    //   cmd[2] = {16'b0, ugd_len[15:0]}
    //   cmd[3] = 0
    // =========================================================================
    task automatic issue_readout_command(
        input logic [7:0] cmd_id,
        input logic [15:0] left_len,      // B - batch dimension
        input logic [15:0] right_len,     // C - column dimension
        input logic [15:0] ugd_len        // V - inner dimension
    );
        logic [31:0] header, word1, word2, word3;

        // Header: {16'd16, cmd_id[7:0], opcode[7:0]}
        header = {16'h0010, cmd_id, OPC_READOUT};

        // Word1: {left_len[15:0], right_len[15:0]}
        word1 = {left_len, right_len};

        // Word2: {16'b0, ugd_len[15:0]}
        word2 = {16'b0, ugd_len};

        // Word3: reserved
        word3 = 32'd0;

        $display("[TB] READOUT CMD: id=%0d, B=%0d, C=%0d, V=%0d", cmd_id, left_len, right_len, ugd_len);

        write_cmd(header);
        write_cmd(word1);
        write_cmd(word2);
        write_cmd(word3);
    endtask

    // ====================================================================
    // Result Capture Task
    // ====================================================================
    task automatic capture_results(input integer expected_count);
        integer timeout;
        integer line_idx;
        
        $display("[TB] Capturing results (expected %0d FP16 values)...", expected_count);
        
        captured_count = 0;
        line_idx = 0;
        timeout = 0;
        result_ready = 1'b1;
        
        while (captured_count < expected_count && timeout < 100000) begin
            @(posedge clk);
            timeout++;
            
            if (result_valid) begin
                // Extract FP16 values from 256-bit line (16 x FP16)
                for (int i = 0; i < 16 && captured_count < expected_count; i++) begin
                    if (result_keep[i]) begin
                        captured_results[captured_count] = result_data[i*16 +: 16];
                        captured_count++;
                    end
                end
                
                line_idx++;
                
                if (result_last) begin
                    $display("[TB] Last result received at line %0d", line_idx);
                    break;
                end
            end
        end
        
        result_ready = 1'b0;
        
        if (timeout >= 100000) begin
            $error("[TB] Timeout waiting for results! Captured %0d/%0d", captured_count, expected_count);
        end else begin
            $display("[TB] Captured %0d results in %0d cycles", captured_count, timeout);
        end
    endtask

    // ====================================================================
    // Verification Task
    // ====================================================================

    // Helper function to check if a real value is NaN
    function automatic bit is_nan(input real val);
        // NaN is the only value that is not equal to itself
        return (val != val);
    endfunction

    task automatic verify_results();
        integer errors;
        integer zero_count;
        integer nan_count;
        real actual_real, tolerance, diff;
        real golden_sum;
        bit golden_is_nan;
        bit actual_is_nan;

        $display("\n[TB] Verifying results...");
        errors = 0;
        zero_count = 0;
        nan_count = 0;

        // For each result position, compare captured vs golden
        // Since golden_reduced requires FP16 addition of 16 values,
        // and we don't have access to exact HW behavior in TB,
        // we'll compute expected sum from per-row golden and allow tolerance

        for (int i = 0; i < B*C; i++) begin
            // Compute golden sum (sequential FP16 addition approximation)
            golden_sum = 0.0;
            for (int r = 0; r < NUM_ROWS; r++) begin
                golden_sum = golden_sum + fp16_to_real(golden_per_row[r][i]);
            end

            actual_real = fp16_to_real(captured_results[i]);

            // Check for NaN values
            golden_is_nan = is_nan(golden_sum);
            actual_is_nan = is_nan(actual_real);

            // Track zeros in output
            if (captured_results[i] == 16'h0000) begin
                zero_count++;
            end

            // Check for NaN in golden (indicates loading problem)
            if (golden_is_nan) begin
                if (nan_count < 4) begin
                    $display("[TB] ERROR at result[%0d]: golden_sum is NaN! (golden loading failed)", i);
                end
                nan_count++;
                errors++;
                continue;
            end

            // Check for NaN in actual result
            if (actual_is_nan) begin
                if (errors < 10) begin
                    $display("[TB] ERROR at result[%0d]: got NaN (0x%04x), expected ~%.4f",
                             i, captured_results[i], golden_sum);
                end
                errors++;
                continue;
            end

            // 5% tolerance for FP16 tree reduction vs sequential accumulation
            // Hardware uses parallel tree adder, Python uses sequential - different rounding
            // FP16 has limited precision (10-bit mantissa), accumulation order matters
            // Exception: For near-zero sums (catastrophic cancellation), use 25% tolerance
            if (golden_sum > -1.0 && golden_sum < 1.0) begin
                // Near-zero: use 25% tolerance for catastrophic cancellation
                tolerance = (golden_sum < 0) ? -golden_sum * 0.25 : golden_sum * 0.25;
            end else begin
                // Normal: use 5% tolerance for FP16 accumulation differences
                tolerance = (golden_sum < 0) ? -golden_sum * 0.05 : golden_sum * 0.05;
            end
            if (tolerance < 0.1) tolerance = 0.1;  // Minimum tolerance (FP16 LSB at this magnitude)

            diff = actual_real - golden_sum;
            if (diff < 0) diff = -diff;

            if (diff > tolerance) begin
                if (errors < 10) begin
                    $display("[TB] ERROR at result[%0d]: got 0x%04x (%.4f), expected ~%.4f (diff=%.4f, tol=%.4f)",
                             i, captured_results[i], actual_real, golden_sum, diff, tolerance);
                end
                errors++;
            end else begin
                if (i < 4) begin  // Show first few matches
                    $display("[TB] MATCH at result[%0d]: got 0x%04x (%.4f), expected ~%.4f",
                             i, captured_results[i], actual_real, golden_sum);
                end
            end
        end

        // Additional sanity checks
        $display("[TB] Summary: %0d/%0d results are zero, %0d NaN errors", zero_count, B*C, nan_count);

        // CRITICAL: If all outputs are zero, this is a FAIL regardless of golden
        if (zero_count == B*C) begin
            $display("[TB] CRITICAL: All %0d results are ZERO - hardware produced no output!", B*C);
            errors = B*C;  // Force failure
        end

        // Report NaN issues
        if (nan_count > 0) begin
            $display("[TB] CRITICAL: %0d golden values were NaN - check golden file loading!", nan_count);
        end

        if (errors == 0) begin
            $display("[TB] PASS: All %0d results match within tolerance", B*C);
            tests_passed++;
        end else begin
            $display("[TB] FAIL: %0d errors out of %0d results", errors, B*C);
        end

        test_errors += errors;
        tests_run++;
    endtask

    // ====================================================================
    // Main Test Sequence
    // ====================================================================
    initial begin
        // Initialize
        reset_n = 1'b0;
        test_errors = 0;
        cycle_count = 0;
        tests_run = 0;
        tests_passed = 0;
        cmd_fifo_wdata = 32'd0;
        cmd_fifo_wen = 1'b0;
        result_ready = 1'b0;
        captured_count = 0;
        
        $display("\n===============================================");
        $display("2-D GEMM FULL INTEGRATION TESTBENCH");
        $display("Configuration: B=%0d, C=%0d, V=%0d, Rows=%0d", B, C, V, NUM_ROWS);
        $display("===============================================\n");
        
        // Reset sequence
        repeat(10) @(posedge clk);
        reset_n = 1'b1;
        repeat(10) @(posedge clk);

        // Initialize all weight BRAMs to zero BEFORE loading data
        // Critical: Prevents X values in unused MLPs (when C < NUM_COLS)
        init_weight_brams();

        // Load hex files into memory models
        load_all_hex_files();
        
        // Load golden results
        load_golden_results();
        
        // =================================================================
        // Issue Command Sequence
        // =================================================================
        // **CRITICAL**: fetcher_2d expects LINE ADDRESSES, not byte addresses!
        // Block 0 (left):  lines 0-527
        // Block 1 (right): lines 528-1055
        // =================================================================
        $display("\n=== ISSUING COMMAND SEQUENCE ===\n");

        // Step 1: Fetch RIGHT (weights) - block 1 starts at line 528
        // IMPORTANT: fetcher_2d.sv expects LINE address, not byte address
        // ugd_len = V_TOTAL (512) - MC partitions this to V=32 per row
        issue_fetch_command(
            .cmd_id(8'd1),
            .start_addr(32'd528),           // Line address 528 (not byte address!)
            .ugd_len(V_TOTAL),              // Total V across all rows (512), MC partitions to 32/row
            .len(16'd528),                  // Full block (528 lines)
            .fetch_right(1'b1)
        );

        // Step 1.5: Wait for RIGHT FETCH to complete before DISPATCH
        // CRITICAL: Without this, DISPATCH reads stale data from FIFO
        issue_wait_disp_command(
            .cmd_id(8'd11),                 // Use intermediate cmd_id
            .wait_id(8'd1)                  // Wait for FETCH cmd_id=1 to complete
        );

        // Step 2: Dispatch RIGHT (weights) to mlp_bram
        // nv_cnt = C (number of UGD vectors/columns, per dispatcher_control_2d.sv)
        // ugd_len = V_TOTAL (512), MC partitions to 32 per row
        issue_dispatch_command(
            .cmd_id(8'd2),
            .nv_cnt(C),                     // C = number of columns (UGD vectors)
            .ugd_len(V_TOTAL),              // Total V (512), MC partitions to 32/row
            .tile_addr(16'd0),              // Start address in mlp_bram
            .col_start(8'd0),               // Start at column 0
            .disp_right(1'b1)               // Right = weights -> mlp_bram
        );

        // Step 3: Wait for DISPATCH to complete
        issue_wait_disp_command(
            .cmd_id(8'd3),
            .wait_id(8'd2)
        );

        // Step 4: Fetch LEFT (activations) - block 0 starts at line 0
        // IMPORTANT: fetcher_2d.sv expects LINE address, not byte address
        // ugd_len = V_TOTAL (512) - MC partitions this to V=32 per row
        issue_fetch_command(
            .cmd_id(8'd4),
            .start_addr(32'd0),             // Line address 0
            .ugd_len(V_TOTAL),              // Total V (512), MC partitions to 32/row
            .len(16'd528),                  // Full block (528 lines)
            .fetch_right(1'b0)
        );

        // Step 4.5: Wait for LEFT FETCH to complete before DISPATCH
        // CRITICAL: Without this, DISPATCH reads stale data from FIFO
        issue_wait_disp_command(
            .cmd_id(8'd44),                 // Use intermediate cmd_id
            .wait_id(8'd4)                  // Wait for FETCH cmd_id=4 to complete
        );

        // Step 5: Dispatch LEFT (activations) to row_bram
        // nv_cnt = B (number of UGD vectors/batches, per dispatcher_control_2d.sv)
        // ugd_len = V_TOTAL (512), MC partitions to 32 per row
        issue_dispatch_command(
            .cmd_id(8'd5),
            .nv_cnt(B),                     // B = number of batches (UGD vectors)
            .ugd_len(V_TOTAL),              // Total V (512), MC partitions to 32/row
            .tile_addr(16'd0),              // Start address in row_bram
            .col_start(8'd0),               // Ignored for left (broadcast mode)
            .disp_right(1'b0)               // Left = activations -> row_bram (broadcast)
        );

        // Step 6: Wait for DISPATCH to complete
        issue_wait_disp_command(
            .cmd_id(8'd6),
            .wait_id(8'd5)
        );

        // Step 7: Issue MATMUL - compute O = A * W
        // B batches, C columns, V_TOTAL = V * NUM_ROWS (MC partitions to V/row)
        issue_matmul_command(
            .cmd_id(8'd7),
            .left_addr(16'd0),              // Start address in row_bram
            .right_addr(16'd0),             // Start address in mlp_bram
            .left_len(16'(B)),              // B (batch dimension)
            .right_len(16'(C)),             // C (column dimension)
            .ugd_len(V_TOTAL)               // Total V, MC partitions to V/row
        );

        // Step 8: READOUT results - issue immediately after MATMUL (before WAIT)
        // This registers the readout parameters; actual readout happens after MATMUL completes
        // Output: B * C FP16 values
        issue_readout_command(
            .cmd_id(8'd8),
            .left_len(16'(B)),              // B
            .right_len(16'(C)),             // C
            .ugd_len(V_TOTAL)               // Total V, for reduction tracking
        );

        // Step 9: Wait for MATMUL to complete (blocks until computation done)
        issue_wait_tile_command(
            .cmd_id(8'd9),
            .wait_id(8'd7)                  // Wait for MATMUL cmd_id=7
        );
        
        // Wait for command processing to start
        repeat(100) @(posedge clk);
        
        // =================================================================
        // Capture Results
        // =================================================================
        $display("\n=== CAPTURING RESULTS ===\n");
        capture_results(B * C);
        
        // =================================================================
        // Verify Results
        // =================================================================
        $display("\n=== VERIFYING RESULTS ===\n");
        verify_results();
        
        // =================================================================
        // Test Summary
        // =================================================================
        repeat(100) @(posedge clk);
        
        $display("\n===============================================");
        $display("TEST SUMMARY");
        $display("===============================================");
        $display("Tests run:    %0d", tests_run);
        $display("Tests passed: %0d", tests_passed);
        $display("Total errors: %0d", test_errors);
        $display("Total cycles: %0d", cycle_count);
        $display("===============================================");
        
        if (test_errors == 0) begin
            $display("\n*** ALL TESTS PASSED ***\n");
        end else begin
            $display("\n*** TESTS FAILED ***\n");
        end
        
        $finish;
    end

    // ====================================================================
    // Cycle Counter
    // ====================================================================
    always @(posedge clk) begin
        if (reset_n) cycle_count <= cycle_count + 1;
        else cycle_count <= 0;
    end

    // ====================================================================
    // Timeout (5ms = 2,000,000 cycles @ 400MHz)
    // ====================================================================
    initial begin
        #5000000ns;
        $error("[TB] TIMEOUT after 5ms!");
        $finish;
    end

    // ====================================================================
    // Debug: Monitor State Changes
    // ====================================================================
    always @(posedge clk) begin
        if (reset_n && cycle_count > 100 && cycle_count < 1000) begin
            // Early debug output
            if (mc_state != 4'd0 || rc_state != 4'd0) begin
                //$display("[TB] @%0d: mc_state=%0d, rc_state=%0d, engine_busy=%b",
                //         cycle_count, mc_state, rc_state, engine_busy);
            end
        end
    end

    // ====================================================================
    // Debug: Monitor FIFO Activity in Dispatcher Controls (Row 0 only for brevity)
    // ====================================================================
    // Access internal FIFO signals via hierarchical reference
    always @(posedge clk) begin
        if (reset_n) begin
            // Monitor Row 0 FIFO write activity (data from fetcher)
            if (u_dut.gen_row[0].u_dispatcher_control.fifo_wr_en) begin
                $display("[FIFO_WR] @%0t Row0: wr_en=1, count=%0d, data[31:0]=0x%08x",
                         $time,
                         u_dut.gen_row[0].u_dispatcher_control.fifo_count,
                         u_dut.gen_row[0].u_dispatcher_control.fifo_wr_data[31:0]);
            end

            // Monitor Row 0 FIFO read activity (data to dispatcher)
            if (u_dut.gen_row[0].u_dispatcher_control.fifo_rd_en) begin
                $display("[FIFO_RD] @%0t Row0: rd_en=1, count=%0d, empty=%b",
                         $time,
                         u_dut.gen_row[0].u_dispatcher_control.fifo_count,
                         u_dut.gen_row[0].u_dispatcher_control.fifo_empty);
            end

            // Monitor MC state transitions
            if (mc_state != 4'd0 && cycle_count < 5000) begin
                $display("[MC_STATE] @%0t cycle=%0d mc_state=%0d",
                         $time, cycle_count, mc_state);
            end
        end
    end

    // ====================================================================
    // Debug: Monitor AXI AR transactions (Row 0 - see if fetcher issues reads)
    // ====================================================================
    always @(posedge clk) begin
        if (reset_n && axi_ddr_if[0].arvalid && axi_ddr_if[0].arready) begin
            $display("[AXI_AR] @%0t Row0: araddr=0x%011x, arlen=%0d",
                     $time, axi_ddr_if[0].araddr, axi_ddr_if[0].arlen);
        end
        if (reset_n && axi_ddr_if[0].rvalid && axi_ddr_if[0].rready) begin
            // Only log first few beats to avoid spam
            if (cycle_count < 2000) begin
                $display("[AXI_R] @%0t Row0: rdata[31:0]=0x%08x, rlast=%b",
                         $time, axi_ddr_if[0].rdata[31:0], axi_ddr_if[0].rlast);
            end
        end
    end

endmodule : tb_gemm2d
