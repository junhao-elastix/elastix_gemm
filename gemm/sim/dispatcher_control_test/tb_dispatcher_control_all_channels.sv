// ------------------------------------------------------------------
// Testbench for dispatcher_control_2d.sv - All 16 GDDR6 Channels
//
// Purpose: Comprehensive test with 16 DUT instances (one per Ctrl ID)
//
// Architecture:
//   - 16 dispatcher_control_2d instances (gen_row[0..15])
//   - 16 AXI interfaces to single multi-channel memory model
//   - 16 comp_row_bram instances for LEFT verification
//   - 16 sets of mock column BRAMs for RIGHT verification
//
// Controller ID Mapping (from engine_top_2d.sv):
//   Row 0:  0xC    Row 1:  0xD    Row 2:  0x4    Row 3:  0x5
//   Row 4:  0x0    Row 5:  0x1    Row 6:  0x8    Row 7:  0x9
//   Row 8:  0xF    Row 9:  0xE    Row 10: 0x7    Row 11: 0x6
//   Row 12: 0x3    Row 13: 0x2    Row 14: 0xB    Row 15: 0xA
//
// Author: Junhao Pan
// Date: Jan 2026
// ------------------------------------------------------------------

`timescale 1ns/1ps

`include "nap_interfaces.svh"

module tb_dispatcher_control_all_channels;

    // =========================================================================
    // Parameters
    // =========================================================================
    localparam CLK_PERIOD       = 2.5;
    localparam TIMEOUT_NS       = 10000000;     // 10ms timeout
    localparam DATA_WIDTH       = 256;
    localparam MAN_WIDTH        = 256;
    localparam EXP_WIDTH        = 8;
    localparam BRAM_DEPTH       = 512;
    localparam FIFO_DEPTH       = 1024;
    localparam NUM_COLS         = 16;
    localparam NUM_ROWS         = 16;
    localparam ADDR_WIDTH       = $clog2(BRAM_DEPTH);
    localparam AXI_ADDR_WIDTH   = 42;
    localparam LINES_PER_BLOCK  = 528;
    localparam EXP_LINES        = 16;
    localparam LINES_PER_NV     = 4;

    // =========================================================================
    // GDDR6 Controller ID Mapping (from engine_top_2d.sv)
    // =========================================================================
    localparam [8:0] GDDR6_CTRL_ID [0:NUM_ROWS-1] = '{
        9'hC, 9'hD,   // Controller 0: Ch0, Ch1
        9'h4, 9'h5,   // Controller 1: Ch0, Ch1
        9'h0, 9'h1,   // Controller 2: Ch0, Ch1
        9'h8, 9'h9,   // Controller 3: Ch0, Ch1
        9'hF, 9'hE,   // Controller 4: Ch0, Ch1 (East)
        9'h7, 9'h6,   // Controller 5: Ch0, Ch1 (East)
        9'h3, 9'h2,   // Controller 6: Ch0, Ch1 (East)
        9'hB, 9'hA    // Controller 7: Ch0, Ch1 (East)
    };

    // =========================================================================
    // Clock and Reset
    // =========================================================================
    logic clk = 1'b0;
    logic rstn;

    always #(CLK_PERIOD/2) clk = ~clk;

    // =========================================================================
    // Per-Row Signals (directly declared, no generate for signals)
    // =========================================================================

    // Command interface (directly in testbench)
    logic [7:0]  mc_cmd_op   [NUM_ROWS-1:0];
    logic [7:0]  mc_cmd_id   [NUM_ROWS-1:0];
    logic [31:0] cmd_word1   [NUM_ROWS-1:0];
    logic [31:0] cmd_word2   [NUM_ROWS-1:0];
    logic [31:0] cmd_word3   [NUM_ROWS-1:0];

    // ACK and status
    logic        dc_ack_fetch [NUM_ROWS-1:0];
    logic        dc_ack_disp  [NUM_ROWS-1:0];
    logic [7:0]  dc_id        [NUM_ROWS-1:0];
    logic [3:0]  dc_state     [NUM_ROWS-1:0];
    logic [3:0]  fetcher_state[NUM_ROWS-1:0];
    logic [3:0]  disp_state   [NUM_ROWS-1:0];
    logic [15:0] lines_rcvd   [NUM_ROWS-1:0];
    logic [15:0] lines_proc   [NUM_ROWS-1:0];

    // LEFT path outputs
    logic [ADDR_WIDTH-1:0] left_man_wr_addr [NUM_ROWS-1:0];
    logic                  left_man_wr_en   [NUM_ROWS-1:0];
    logic [MAN_WIDTH-1:0]  left_man_wr_data [NUM_ROWS-1:0];
    logic [ADDR_WIDTH-1:0] left_exp_wr_addr [NUM_ROWS-1:0];
    logic                  left_exp_wr_en   [NUM_ROWS-1:0];
    logic [EXP_WIDTH-1:0]  left_exp_wr_data [NUM_ROWS-1:0];

    // RIGHT path outputs
    logic [ADDR_WIDTH-1:0] right_wr_addr    [NUM_ROWS-1:0];
    logic [NUM_COLS-1:0]   right_wr_en      [NUM_ROWS-1:0];
    logic [MAN_WIDTH-1:0]  right_man_wr_data[NUM_ROWS-1:0];
    logic [EXP_WIDTH-1:0]  right_exp_wr_data[NUM_ROWS-1:0];

    // Opcode constants
    localparam logic [7:0] CMD_FETCH = 8'hF0;
    localparam logic [7:0] CMD_DISP  = 8'hF1;
    localparam logic [7:0] CMD_NOP   = 8'h00;

    // =========================================================================
    // AXI Interfaces (one per row)
    // =========================================================================
    t_AXI4 #(.DATA_WIDTH(256), .ADDR_WIDTH(42), .LEN_WIDTH(8), .ID_WIDTH(8)) axi_if [NUM_ROWS-1:0] ();

    // =========================================================================
    // Multi-Channel Memory Model
    // =========================================================================
    logic [31:0] mem_outstanding [NUM_ROWS-1:0];
    logic [31:0] mem_ar_count    [NUM_ROWS-1:0];
    logic [31:0] mem_r_count     [NUM_ROWS-1:0];

    // Generate 16 memory model instances (one per row/channel)
    genvar mem_idx;
    generate
        for (mem_idx = 0; mem_idx < NUM_ROWS; mem_idx++) begin : gen_mem
            tb_memory_model_multi_channel #(
                .DATA_WIDTH(256),
                .ADDR_WIDTH(42),
                .LINES_PER_BLOCK(LINES_PER_BLOCK),
                .NUM_CTRL_IDS(16),
                .LATENCY_CYCLES(40),
                .MAX_OUTSTANDING(32),
                .VERBOSITY(0)
            ) u_mem (
                .i_clk(clk),
                .i_reset_n(rstn),
                .axi_mem_if(axi_if[mem_idx].responder),
                .i_ctrl_id_filter(GDDR6_CTRL_ID[mem_idx]),  // Filter to this row's Ctrl ID
                .o_outstanding_count(mem_outstanding[mem_idx]),
                .o_total_ar_received(mem_ar_count[mem_idx]),
                .o_total_r_issued(mem_r_count[mem_idx])
            );
        end
    endgenerate

    // =========================================================================
    // Generate 16 DUT Instances
    // =========================================================================
    genvar row;
    generate
        for (row = 0; row < NUM_ROWS; row++) begin : gen_row
            dispatcher_control_2d #(
                .MAN_WIDTH      (MAN_WIDTH),
                .EXP_WIDTH      (EXP_WIDTH),
                .BRAM_DEPTH     (BRAM_DEPTH),
                .FIFO_DEPTH     (FIFO_DEPTH),
                .NUM_COLS       (NUM_COLS),
                .AXI_ADDR_WIDTH (AXI_ADDR_WIDTH),
                .GDDR6_CTRL_ID  (GDDR6_CTRL_ID[row])
            ) u_dut (
                .i_clk              (clk),
                .i_reset_n          (rstn),
                .i_mc_cmd_op        (mc_cmd_op[row]),
                .i_mc_cmd_id        (mc_cmd_id[row]),
                .i_cmd_payload_word1(cmd_word1[row]),
                .i_cmd_payload_word2(cmd_word2[row]),
                .i_cmd_payload_word3(cmd_word3[row]),
                .o_dc_ack_fetch     (dc_ack_fetch[row]),
                .o_dc_ack_disp      (dc_ack_disp[row]),
                .o_dc_id            (dc_id[row]),
                .o_left_man_wr_addr (left_man_wr_addr[row]),
                .o_left_man_wr_en   (left_man_wr_en[row]),
                .o_left_man_wr_data (left_man_wr_data[row]),
                .o_left_exp_wr_addr (left_exp_wr_addr[row]),
                .o_left_exp_wr_en   (left_exp_wr_en[row]),
                .o_left_exp_wr_data (left_exp_wr_data[row]),
                .o_right_wr_addr    (right_wr_addr[row]),
                .o_right_wr_en      (right_wr_en[row]),
                .o_right_man_wr_data(right_man_wr_data[row]),
                .o_right_exp_wr_data(right_exp_wr_data[row]),
                .axi_ddr_if         (axi_if[row].initiator),
                .o_dc_state               (dc_state[row]),
                .o_fetcher_state          (fetcher_state[row]),
                .o_dispatcher_state       (disp_state[row]),
                .o_fetcher_lines_received (lines_rcvd[row]),
                .o_dispatcher_lines_processed(lines_proc[row]),
                .o_fifo_count             ()
            );
        end
    endgenerate

    // =========================================================================
    // Generate 16 comp_row_bram Instances (LEFT verification)
    // =========================================================================
    logic [6:0]           row_bram_rd_idx [NUM_ROWS-1:0];
    logic [31:0]          row_bram_exp    [NUM_ROWS-1:0];
    logic [MAN_WIDTH-1:0] row_bram_man    [NUM_ROWS-1:0][0:3];

    generate
        for (row = 0; row < NUM_ROWS; row++) begin : gen_row_bram
            comp_row_bram #(
                .MAN_WIDTH  (MAN_WIDTH),
                .EXP_WIDTH  (EXP_WIDTH),
                .BRAM_DEPTH (BRAM_DEPTH),
                .ADDR_WIDTH (ADDR_WIDTH)
            ) u_row_bram (
                .i_clk             (clk),
                .i_reset_n         (rstn),
                .i_man_left_wr_addr(left_man_wr_addr[row]),
                .i_man_left_wr_en  (left_man_wr_en[row]),
                .i_man_left_wr_data(left_man_wr_data[row]),
                .i_exp_left_wr_addr(left_exp_wr_addr[row]),
                .i_exp_left_wr_en  (left_exp_wr_en[row]),
                .i_exp_left_wr_data(left_exp_wr_data[row]),
                .i_nv_left_rd_idx  (row_bram_rd_idx[row]),
                .o_nv_left_exp     (row_bram_exp[row]),
                .o_nv_left_man     (row_bram_man[row])
            );
        end
    endgenerate

    // =========================================================================
    // Mock Column BRAMs (RIGHT verification) - Per Row
    // =========================================================================
    logic [MAN_WIDTH-1:0] col_man_mem [NUM_ROWS-1:0][NUM_COLS-1:0][BRAM_DEPTH-1:0];
    logic [EXP_WIDTH-1:0] col_exp_mem [NUM_ROWS-1:0][NUM_COLS-1:0][BRAM_DEPTH-1:0];
    int col_wr_cnt [NUM_ROWS-1:0][NUM_COLS-1:0];

    always_ff @(posedge clk) begin
        for (int r = 0; r < NUM_ROWS; r++) begin
            for (int c = 0; c < NUM_COLS; c++) begin
                if (right_wr_en[r][c]) begin
                    col_man_mem[r][c][right_wr_addr[r]] <= right_man_wr_data[r];
                    col_exp_mem[r][c][right_wr_addr[r]] <= right_exp_wr_data[r];
                    col_wr_cnt[r][c] <= col_wr_cnt[r][c] + 1;
                end
            end
        end
    end

    // =========================================================================
    // Golden Reference Storage (per Ctrl ID)
    // =========================================================================
    logic [DATA_WIDTH-1:0] golden_data [0:15][0:LINES_PER_BLOCK-1];

    // =========================================================================
    // Test Status
    // =========================================================================
    int tests_run, tests_passed;
    int rows_tested, rows_passed;
    logic current_test_ok;
    int cycle_count;

    always @(posedge clk) begin
        if (rstn) cycle_count <= cycle_count + 1;
        else cycle_count <= 0;
    end

    // =========================================================================
    // Hex File Loading
    // =========================================================================
    task automatic load_hex_file(
        input [3:0] ctrl_id,
        input string filename
    );
        integer fd, line_idx, byte_idx, scan_result;
        logic [7:0] bytes [0:31];
        logic [DATA_WIDTH-1:0] packed_line;

        fd = $fopen(filename, "r");
        if (fd == 0) begin
            $display("[TB] WARNING: Cannot open %s", filename);
            return;
        end

        line_idx = 0;
        while (!$feof(fd) && line_idx < LINES_PER_BLOCK) begin
            scan_result = $fscanf(fd, "%h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h\n",
                bytes[0],  bytes[1],  bytes[2],  bytes[3],  bytes[4],  bytes[5],  bytes[6],  bytes[7],
                bytes[8],  bytes[9],  bytes[10], bytes[11], bytes[12], bytes[13], bytes[14], bytes[15],
                bytes[16], bytes[17], bytes[18], bytes[19], bytes[20], bytes[21], bytes[22], bytes[23],
                bytes[24], bytes[25], bytes[26], bytes[27], bytes[28], bytes[29], bytes[30], bytes[31]);

            if (scan_result == 32) begin
                packed_line = '0;
                for (byte_idx = 0; byte_idx < 32; byte_idx++) begin
                    packed_line[byte_idx*8 +: 8] = bytes[byte_idx];
                end
                golden_data[ctrl_id][line_idx] = packed_line;
                line_idx++;
            end
        end
        $fclose(fd);
    endtask

    // =========================================================================
    // Reset All Rows
    // =========================================================================
    task automatic reset_all();
        rstn = 0;
        for (int r = 0; r < NUM_ROWS; r++) begin
            mc_cmd_op[r] = CMD_NOP;
            mc_cmd_id[r] = 8'd0;
            cmd_word1[r] = 32'd0;
            cmd_word2[r] = 32'd0;
            cmd_word3[r] = 32'd0;
            row_bram_rd_idx[r] = 0;
        end
        repeat (10) @(posedge clk);

        // Clear column BRAMs
        for (int r = 0; r < NUM_ROWS; r++) begin
            for (int c = 0; c < NUM_COLS; c++) begin
                col_wr_cnt[r][c] = 0;
                for (int a = 0; a < BRAM_DEPTH; a++) begin
                    col_man_mem[r][c][a] = '0;
                    col_exp_mem[r][c][a] = '0;
                end
            end
        end

        rstn = 1;
        repeat (10) @(posedge clk);
    endtask

    // =========================================================================
    // Issue FETCH to Specific Row
    // =========================================================================
    task automatic issue_fetch_row(
        input int row_idx,
        input logic [25:0] addr,
        input logic [15:0] len,
        input logic [7:0] cmd_id
    );
        int start_cycle;
        start_cycle = cycle_count;

        @(posedge clk);
        cmd_word1[row_idx] = {6'b0, addr};
        cmd_word2[row_idx] = {16'd1, len};
        cmd_word3[row_idx] = 32'd0;
        mc_cmd_id[row_idx] = cmd_id;
        mc_cmd_op[row_idx] = CMD_FETCH;

        @(posedge clk);
        #1;
        if (!dc_ack_fetch[row_idx]) begin
            $display("[TB] Row %0d: ERROR - FETCH ACK not received", row_idx);
            current_test_ok = 0;
        end

        mc_cmd_op[row_idx] = CMD_NOP;
        repeat (3) @(posedge clk);

        while (fetcher_state[row_idx] != 0) @(posedge clk);

        $display("[TB] Row %0d: FETCH done in %0d cycles, %0d lines",
                 row_idx, cycle_count - start_cycle, lines_rcvd[row_idx]);
        repeat (5) @(posedge clk);
    endtask

    // =========================================================================
    // Issue DISPATCH to Specific Row
    // =========================================================================
    task automatic issue_dispatch_row(
        input int row_idx,
        input logic [15:0] nv_cnt,
        input logic [15:0] ugd_len,
        input logic [3:0] col_start,
        input logic is_right,
        input logic [ADDR_WIDTH-1:0] tile_addr,
        input logic [7:0] cmd_id
    );
        int start_cycle;
        start_cycle = cycle_count;

        @(posedge clk);
        cmd_word1[row_idx] = {nv_cnt, ugd_len};
        cmd_word2[row_idx] = {16'b0, {7'b0, tile_addr}};
        cmd_word3[row_idx] = {16'b0, {4'b0, col_start}, 5'b0, is_right, 1'b0, 1'b0};
        mc_cmd_id[row_idx] = cmd_id;
        mc_cmd_op[row_idx] = CMD_DISP;

        @(posedge clk);
        #1;
        if (!dc_ack_disp[row_idx]) begin
            $display("[TB] Row %0d: ERROR - DISPATCH ACK not received", row_idx);
            current_test_ok = 0;
        end

        mc_cmd_op[row_idx] = CMD_NOP;
        repeat (3) @(posedge clk);

        while (disp_state[row_idx] != 0) @(posedge clk);

        $display("[TB] Row %0d: DISPATCH done in %0d cycles, %0d lines",
                 row_idx, cycle_count - start_cycle, lines_proc[row_idx]);
        repeat (5) @(posedge clk);
    endtask

    // =========================================================================
    // Verify LEFT Data for Specific Row
    // =========================================================================
    task automatic verify_left_row(input int row_idx, input int nv_cnt, input int ugd_len);
        int errors;
        int total_nvs;
        logic [3:0] ctrl_id;

        errors = 0;
        total_nvs = nv_cnt * ugd_len;
        ctrl_id = GDDR6_CTRL_ID[row_idx][3:0];

        for (int nv = 0; nv < total_nvs; nv++) begin
            row_bram_rd_idx[row_idx] = nv;
            @(posedge clk); @(posedge clk);

            for (int g = 0; g < LINES_PER_NV; g++) begin
                int man_idx = EXP_LINES + nv * LINES_PER_NV + g;
                if (row_bram_man[row_idx][g] !== golden_data[ctrl_id][man_idx]) begin
                    errors++;
                end
            end
        end

        if (errors == 0) begin
            $display("[TB] Row %0d LEFT: PASS (%0d NVs verified)", row_idx, total_nvs);
        end else begin
            $display("[TB] Row %0d LEFT: FAIL (%0d errors)", row_idx, errors);
            current_test_ok = 0;
        end
    endtask

    // =========================================================================
    // Verify RIGHT Data for Specific Row
    // =========================================================================
    task automatic verify_right_row(input int row_idx, input int nv_cnt, input int ugd_len);
        int errors;
        int expected_writes;
        logic [3:0] ctrl_id;

        errors = 0;
        expected_writes = ugd_len * LINES_PER_NV;
        ctrl_id = GDDR6_CTRL_ID[row_idx][3:0];

        // Check write counts
        for (int c = 0; c < nv_cnt && c < NUM_COLS; c++) begin
            if (col_wr_cnt[row_idx][c] != expected_writes) begin
                errors++;
            end
        end

        // Check data content
        for (int c = 0; c < nv_cnt && c < NUM_COLS; c++) begin
            for (int v = 0; v < ugd_len; v++) begin
                for (int l = 0; l < LINES_PER_NV; l++) begin
                    int addr = v * LINES_PER_NV + l;
                    int man_idx = EXP_LINES + c * ugd_len * LINES_PER_NV + v * LINES_PER_NV + l;
                    if (col_man_mem[row_idx][c][addr] !== golden_data[ctrl_id][man_idx]) begin
                        errors++;
                    end
                end
            end
        end

        if (errors == 0) begin
            $display("[TB] Row %0d RIGHT: PASS (%0d cols verified)", row_idx, nv_cnt);
        end else begin
            $display("[TB] Row %0d RIGHT: FAIL (%0d errors)", row_idx, errors);
            current_test_ok = 0;
        end
    endtask

    // =========================================================================
    // Reset DUT (pulses rstn to clear all state including FIFO)
    // =========================================================================
    task automatic reset_dut();
        rstn = 0;
        // Clear all command signals during reset
        for (int r = 0; r < NUM_ROWS; r++) begin
            mc_cmd_op[r] = CMD_NOP;
            mc_cmd_id[r] = '0;
            cmd_word1[r] = '0;
            cmd_word2[r] = '0;
            cmd_word3[r] = '0;
        end
        repeat (5) @(posedge clk);
        rstn = 1;
        repeat (10) @(posedge clk);
    endtask

    // =========================================================================
    // Test Single Row
    // =========================================================================
    task automatic test_row(input int row_idx);
        logic [3:0] ctrl_id;
        string hex_file;
        int B, V;

        ctrl_id = GDDR6_CTRL_ID[row_idx][3:0];
        hex_file = (row_idx % 2 == 0) ? "/home/dev/Dev/elastix_gemm/hex/left.hex"
                                      : "/home/dev/Dev/elastix_gemm/hex/right.hex";
        B = 4;
        V = 2;

        $display("\n--- Row %0d: Ctrl ID 0x%01X ---", row_idx, ctrl_id);

        // Reset DUT to clear FIFO state
        reset_dut();

        current_test_ok = 1;

        // Clear this row's column BRAMs
        for (int c = 0; c < NUM_COLS; c++) begin
            col_wr_cnt[row_idx][c] = 0;
            for (int a = 0; a < BRAM_DEPTH; a++) begin
                col_man_mem[row_idx][c][a] = '0;
                col_exp_mem[row_idx][c][a] = '0;
            end
        end

        // FETCH + LEFT DISPATCH
        issue_fetch_row(row_idx, 26'd0, 16'd528, 8'd1);
        issue_dispatch_row(row_idx, B, V, 0, 0, 0, 8'd2);
        verify_left_row(row_idx, B, V);
        tests_run++;
        if (current_test_ok) tests_passed++;

        // Reset DUT between tests to clear FIFO
        reset_dut();

        // Clear for RIGHT test
        current_test_ok = 1;
        for (int c = 0; c < NUM_COLS; c++) begin
            col_wr_cnt[row_idx][c] = 0;
        end

        // FETCH + RIGHT DISPATCH
        issue_fetch_row(row_idx, 26'd0, 16'd528, 8'd3);
        issue_dispatch_row(row_idx, B, V, 0, 1, 0, 8'd4);
        verify_right_row(row_idx, B, V);
        tests_run++;
        if (current_test_ok) tests_passed++;

        rows_tested++;
        if (current_test_ok) rows_passed++;

        $display("[TB] Row %0d (Ctrl ID 0x%01X): %s", row_idx, ctrl_id, current_test_ok ? "PASS" : "FAIL");
    endtask

    // =========================================================================
    // Main Test Sequence
    // =========================================================================
    initial begin
        tests_run = 0;
        tests_passed = 0;
        rows_tested = 0;
        rows_passed = 0;
        cycle_count = 0;

        $display("\n===============================================");
        $display("DISPATCHER_CONTROL_2D - ALL 16 CHANNELS TEST");
        $display("===============================================");
        $display("Testing 16 DUT instances with unique Ctrl IDs");
        $display("===============================================\n");

        // Load golden data for all Ctrl IDs
        $display("[TB] Loading golden reference files...");
        for (int r = 0; r < NUM_ROWS; r++) begin
            string hex_file;
            hex_file = (r % 2 == 0) ? "/home/dev/Dev/elastix_gemm/hex/left.hex"
                                    : "/home/dev/Dev/elastix_gemm/hex/right.hex";
            load_hex_file(GDDR6_CTRL_ID[r][3:0], hex_file);
        end
        $display("[TB] Golden data loaded for all 16 Ctrl IDs\n");

        // Reset
        reset_all();

        // Test all 16 rows
        for (int r = 0; r < NUM_ROWS; r++) begin
            test_row(r);
        end

        // Final Summary
        $display("\n===============================================");
        $display("FINAL SUMMARY");
        $display("===============================================");
        $display("Rows tested:  %0d / %0d", rows_tested, NUM_ROWS);
        $display("Rows passed:  %0d / %0d", rows_passed, NUM_ROWS);
        $display("Tests passed: %0d / %0d", tests_passed, tests_run);

        if (rows_passed == NUM_ROWS) begin
            $display("\n*** ALL 16 CHANNELS PASSED ***\n");
        end else begin
            $display("\n*** %0d CHANNEL(S) FAILED ***\n", NUM_ROWS - rows_passed);
        end
        $display("===============================================\n");

        $finish;
    end

    // =========================================================================
    // Timeout
    // =========================================================================
    initial begin
        #TIMEOUT_NS;
        $error("[TB] TIMEOUT!");
        $finish;
    end

endmodule
