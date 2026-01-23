// ------------------------------------------------------------------
// Testbench for dispatcher_control_2d.sv
//
// Purpose: End-to-end test of FETCH + DISPATCH data flow
// 
// Test Architecture:
//  - tb_memory_model_realistic: AXI memory model (like fetcher_test)
//  - dispatcher_control_2d: DUT (fetcher_2d + flex_fifo + dispatcher_2d)
//  - comp_row_bram: LEFT path verification
//  - Mock column BRAMs: RIGHT path verification
//
// Test Cases:
//  1. FETCH block 0, LEFT DISPATCH - verify data in row_bram
//  2. FETCH block 1, RIGHT DISPATCH - verify data in 16 col_brams
//  3. ACK timing - verify immediate ACK on command decode
//  4. cmd_id tracking - verify o_dc_id updates on completion
//
// Author: Junhao Pan
// Date: Jan 2026
// ------------------------------------------------------------------

`timescale 1ns/1ps

`include "nap_interfaces.svh"

module tb_dispatcher_control;

    // =========================================================================
    // Parameters
    // =========================================================================
    localparam CLK_PERIOD       = 2.5;          // 400MHz
    localparam TIMEOUT_NS       = 500000;       // 500us timeout
    localparam DATA_WIDTH       = 256;
    localparam MAN_WIDTH        = 256;
    localparam EXP_WIDTH        = 8;
    localparam BRAM_DEPTH       = 512;
    localparam FIFO_DEPTH       = 1024;
    localparam NUM_COLS         = 16;
    localparam ADDR_WIDTH       = $clog2(BRAM_DEPTH);
    localparam AXI_ADDR_WIDTH   = 42;
    localparam [8:0] GDDR6_CTRL_ID = 9'd2;
    localparam LINES_PER_BLOCK  = 528;
    localparam EXP_LINES        = 16;
    localparam LINES_PER_NV     = 4;

    // =========================================================================
    // Clock and Reset
    // =========================================================================
    logic clk = 1'b0;
    logic rstn;

    always #(CLK_PERIOD/2) clk = ~clk;

    // =========================================================================
    // AXI Interface (NAP to GDDR6)
    // =========================================================================
    t_AXI4 #(
        .DATA_WIDTH(256),
        .ADDR_WIDTH(42),
        .LEN_WIDTH(8),
        .ID_WIDTH(8)
    ) axi_nap();

    // =========================================================================
    // GDDR6 Memory Model (Realistic - 32 Outstanding Limit)
    // =========================================================================
    logic [31:0] mem_outstanding_count;
    logic [31:0] mem_total_ar_received;
    logic [31:0] mem_total_r_issued;

    tb_memory_model_realistic #(
        .DATA_WIDTH(256),
        .ADDR_WIDTH(42),
        .LINES_PER_BLOCK(528),
        .NUM_BLOCKS(2),
        .LATENCY_CYCLES(40),      // 100ns @ 400MHz = realistic GDDR6
        .MAX_OUTSTANDING(32),     // Achronix GDDR6 NoC limit
        .VERBOSITY(1)             // 0=quiet, 1=summary, 2=detailed
    ) u_gddr6_model (
        .i_clk(clk),
        .i_reset_n(rstn),
        .axi_mem_if(axi_nap.responder),
        .o_outstanding_count(mem_outstanding_count),
        .o_total_ar_received(mem_total_ar_received),
        .o_total_r_issued(mem_total_r_issued)
    );

    // =========================================================================
    // DUT Command Interface - Packed Payload (matches master_control_2d output)
    // =========================================================================
    logic [7:0]             mc_cmd_op;           // Opcode
    logic [7:0]             mc_cmd_id;           // Command ID
    logic [31:0]            cmd_payload_word1;   // Per-row payload word 1
    logic [31:0]            cmd_payload_word2;   // Per-row payload word 2
    logic [31:0]            cmd_payload_word3;   // Per-row payload word 3
    logic                   dc_ack_fetch;        // FETCH ACK (immediate)
    logic                   dc_ack_disp;         // DISPATCH ACK (immediate)

    // Opcode constants
    localparam logic [7:0] CMD_FETCH = 8'hF0;
    localparam logic [7:0] CMD_DISP  = 8'hF1;
    localparam logic [7:0] CMD_NOP   = 8'h00;

    // =========================================================================
    // DUT Output Signals - cmd_id Tracking
    // =========================================================================
    logic [7:0]             dc_id;

    // =========================================================================
    // DUT Output Signals - LEFT Path
    // =========================================================================
    logic [ADDR_WIDTH-1:0]  left_man_wr_addr;
    logic                   left_man_wr_en;
    logic [MAN_WIDTH-1:0]   left_man_wr_data;
    logic [ADDR_WIDTH-1:0]  left_exp_wr_addr;
    logic                   left_exp_wr_en;
    logic [EXP_WIDTH-1:0]   left_exp_wr_data;

    // =========================================================================
    // DUT Output Signals - RIGHT Path
    // =========================================================================
    logic [ADDR_WIDTH-1:0]  right_wr_addr;
    logic [NUM_COLS-1:0]    right_wr_en;
    logic [MAN_WIDTH-1:0]   right_man_wr_data;
    logic [EXP_WIDTH-1:0]   right_exp_wr_data;

    // =========================================================================
    // Debug Signals
    // =========================================================================
    logic [3:0]             dc_state;
    logic [3:0]             fetcher_state;
    logic [3:0]             dispatcher_state;
    logic [15:0]            fetcher_lines_received;
    logic [15:0]            dispatcher_lines_processed;
    logic [$clog2(FIFO_DEPTH):0] fifo_count;

    // =========================================================================
    // DUT: dispatcher_control_2d
    // =========================================================================
    dispatcher_control_2d #(
        .MAN_WIDTH      (MAN_WIDTH),
        .EXP_WIDTH      (EXP_WIDTH),
        .BRAM_DEPTH     (BRAM_DEPTH),
        .FIFO_DEPTH     (FIFO_DEPTH),
        .NUM_COLS       (NUM_COLS),
        .AXI_ADDR_WIDTH (AXI_ADDR_WIDTH),
        .GDDR6_CTRL_ID  (GDDR6_CTRL_ID)
    ) u_dut (
        .i_clk              (clk),
        .i_reset_n          (rstn),
        
        // Master Control Command Interface (Packed Payload)
        .i_mc_cmd_op        (mc_cmd_op),
        .i_mc_cmd_id        (mc_cmd_id),
        .i_cmd_payload_word1(cmd_payload_word1),
        .i_cmd_payload_word2(cmd_payload_word2),
        .i_cmd_payload_word3(cmd_payload_word3),
        .o_dc_ack_fetch     (dc_ack_fetch),
        .o_dc_ack_disp      (dc_ack_disp),
        
        // cmd_id tracking
        .o_dc_id            (dc_id),
        
        // LEFT path outputs
        .o_left_man_wr_addr (left_man_wr_addr),
        .o_left_man_wr_en   (left_man_wr_en),
        .o_left_man_wr_data (left_man_wr_data),
        .o_left_exp_wr_addr (left_exp_wr_addr),
        .o_left_exp_wr_en   (left_exp_wr_en),
        .o_left_exp_wr_data (left_exp_wr_data),
        
        // RIGHT path outputs
        .o_right_wr_addr    (right_wr_addr),
        .o_right_wr_en      (right_wr_en),
        .o_right_man_wr_data(right_man_wr_data),
        .o_right_exp_wr_data(right_exp_wr_data),
        
        // AXI interface
        .axi_ddr_if         (axi_nap.initiator),
        
        // Debug outputs
        .o_dc_state               (dc_state),
        .o_fetcher_state          (fetcher_state),
        .o_dispatcher_state       (dispatcher_state),
        .o_fetcher_lines_received (fetcher_lines_received),
        .o_dispatcher_lines_processed(dispatcher_lines_processed),
        .o_fifo_count             (fifo_count)
    );

    // =========================================================================
    // comp_row_bram (for LEFT path verification)
    // =========================================================================
    logic [6:0]              row_bram_rd_idx;
    logic [31:0]             row_bram_exp;
    logic [MAN_WIDTH-1:0]    row_bram_man [0:3];

    comp_row_bram #(
        .MAN_WIDTH  (MAN_WIDTH),
        .EXP_WIDTH  (EXP_WIDTH),
        .BRAM_DEPTH (BRAM_DEPTH),
        .ADDR_WIDTH (ADDR_WIDTH)
    ) u_row_bram (
        .i_clk             (clk),
        .i_reset_n         (rstn),
        // Write interface
        .i_man_left_wr_addr(left_man_wr_addr),
        .i_man_left_wr_en  (left_man_wr_en),
        .i_man_left_wr_data(left_man_wr_data),
        .i_exp_left_wr_addr(left_exp_wr_addr),
        .i_exp_left_wr_en  (left_exp_wr_en),
        .i_exp_left_wr_data(left_exp_wr_data),
        // Read interface
        .i_nv_left_rd_idx  (row_bram_rd_idx),
        .o_nv_left_exp     (row_bram_exp),
        .o_nv_left_man     (row_bram_man)
    );

    // =========================================================================
    // Mock Column BRAMs (for RIGHT path verification)
    // =========================================================================
    logic [MAN_WIDTH-1:0] col_man_mem [NUM_COLS-1:0][BRAM_DEPTH-1:0];
    logic [EXP_WIDTH-1:0] col_exp_mem [NUM_COLS-1:0][BRAM_DEPTH-1:0];
    int col_write_counts [NUM_COLS-1:0];
    logic clear_col_brams;  // Signal to clear mock BRAMs

    always_ff @(posedge clk) begin
        if (clear_col_brams) begin
            // Clear write counts on reset/clear request
            for (int c = 0; c < NUM_COLS; c++) begin
                col_write_counts[c] <= 0;
            end
        end else begin
            for (int c = 0; c < NUM_COLS; c++) begin
                if (right_wr_en[c]) begin
                    col_man_mem[c][right_wr_addr] <= right_man_wr_data;
                    col_exp_mem[c][right_wr_addr] <= right_exp_wr_data;
                    col_write_counts[c] <= col_write_counts[c] + 1;
                end
            end
        end
    end

    // =========================================================================
    // Golden Reference Storage (loaded from hex files)
    // =========================================================================
    logic [DATA_WIDTH-1:0] golden_left  [0:LINES_PER_BLOCK-1];
    logic [DATA_WIDTH-1:0] golden_right [0:LINES_PER_BLOCK-1];

    // =========================================================================
    // Test Status
    // =========================================================================
    int     tests_run;
    int     tests_passed;
    logic   current_test_ok;
    int     cycle_count;

    // =========================================================================
    // Cycle Counter
    // =========================================================================
    always @(posedge clk) begin
        if (rstn) cycle_count <= cycle_count + 1;
        else cycle_count <= 0;
    end

    // =========================================================================
    // Hex File Loading Task
    // =========================================================================
    task automatic load_hex_file(
        input string filename,
        ref logic [DATA_WIDTH-1:0] storage [0:LINES_PER_BLOCK-1]
    );
        integer fd, line_idx, byte_idx, scan_result;
        logic [7:0] bytes [0:31];
        logic [DATA_WIDTH-1:0] packed_line;

        fd = $fopen(filename, "r");
        if (fd == 0) begin
            $error("[HEX] Failed to open file: %s", filename);
            return;
        end

        $display("[HEX] Loading %s...", filename);
        line_idx = 0;

        while (!$feof(fd) && line_idx < LINES_PER_BLOCK) begin
            // Read 32 space-separated hex bytes per line
            scan_result = $fscanf(fd, "%h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h\n",
                bytes[0],  bytes[1],  bytes[2],  bytes[3],  bytes[4],  bytes[5],  bytes[6],  bytes[7],
                bytes[8],  bytes[9],  bytes[10], bytes[11], bytes[12], bytes[13], bytes[14], bytes[15],
                bytes[16], bytes[17], bytes[18], bytes[19], bytes[20], bytes[21], bytes[22], bytes[23],
                bytes[24], bytes[25], bytes[26], bytes[27], bytes[28], bytes[29], bytes[30], bytes[31]);

            if (scan_result == 32) begin
                // Pack bytes into 256-bit line (bytes[0] is LSB)
                packed_line = '0;
                for (byte_idx = 0; byte_idx < 32; byte_idx++) begin
                    packed_line[byte_idx*8 +: 8] = bytes[byte_idx];
                end
                storage[line_idx] = packed_line;
                line_idx++;
            end
        end

        $fclose(fd);
        $display("[HEX] Loaded %0d lines from %s", line_idx, filename);
    endtask

    // =========================================================================
    // Task: Reset DUT
    // =========================================================================
    task automatic reset_dut();
        rstn = 0;
        mc_cmd_op = CMD_NOP;
        mc_cmd_id = 8'd0;
        cmd_payload_word1 = 32'd0;
        cmd_payload_word2 = 32'd0;
        cmd_payload_word3 = 32'd0;
        row_bram_rd_idx = 0;
        
        // Clear mock column BRAMs via signal (will be handled by always_ff)
        clear_col_brams = 1;
        repeat (10) @(posedge clk);
        clear_col_brams = 0;
        
        // Clear BRAM memory (can be done directly as it's not in always_ff)
        for (int c = 0; c < NUM_COLS; c++) begin
            for (int a = 0; a < BRAM_DEPTH; a++) begin
                col_man_mem[c][a] = '0;
                col_exp_mem[c][a] = '0;
            end
        end
        
        rstn = 1;
        repeat (10) @(posedge clk);
    endtask

    // =========================================================================
    // Task: Issue FETCH Command (Packed Payload Interface)
    // Payload format:
    //   word1 = start_addr[31:0]
    //   word2 = {v_count[15:0], len[15:0]}
    //   word3 = {31'b0, fetch_right}
    // =========================================================================
    task automatic issue_fetch(
        input logic [25:0] addr,
        input logic [15:0] len,
        input logic [7:0]  cmd_id
    );
        int start_cycle;
        
        $display("[TB] FETCH: addr=0x%06x, len=%0d, cmd_id=%0d", addr, len, cmd_id);
        
        start_cycle = cycle_count;
        
        @(posedge clk);
        // Pack command payload
        cmd_payload_word1 = {6'b0, addr};                  // start_addr[31:0]
        cmd_payload_word2 = {16'd1, len};                  // {v_count, len} - v_count=1 for this test
        cmd_payload_word3 = 32'd0;                         // fetch_right=0 (unused)
        mc_cmd_id = cmd_id;
        mc_cmd_op = CMD_FETCH;                             // Assert FETCH opcode
        
        // Wait for rising edge to be detected and ACK to be registered
        @(posedge clk);
        #1;  // Small delay to let NBA settle, check before next edge
        
        // Verify ACK (should be high after the edge where rising edge was detected)
        if (!dc_ack_fetch) begin
            $display("[TB] ERROR: dc_ack_fetch not asserted on decode!");
            current_test_ok = 0;
        end else begin
            $display("[TB] FETCH ACK received (correct behavior)");
        end
        
        // Clear opcode (return to NOP)
        mc_cmd_op = CMD_NOP;
        
        // Wait for fetcher to actually start (state machine needs clock edge to transition)
        repeat (3) @(posedge clk);
        
        // Wait for fetcher to complete (internal)
        while (fetcher_state != 0) begin
            @(posedge clk);
        end
        
        $display("[TB] FETCH complete in %0d cycles, lines_received=%0d",
                 cycle_count - start_cycle, fetcher_lines_received);
        
        repeat (10) @(posedge clk);
    endtask

    // =========================================================================
    // Task: Issue DISPATCH Command (Packed Payload Interface)
    // Payload format (per master_control_2d):
    //   word1 = {nv_cnt[15:0], v_count[15:0]}
    //   word2 = {16'b0, tile_addr[15:0]}
    //   word3 = {16'b0, col_start[7:0], 5'b0, disp_right, broadcast, man_4b}
    // =========================================================================
    task automatic issue_dispatch(
        input logic [15:0]            nv_cnt,
        input logic [15:0]            ugd_len,
        input logic [3:0]             col_start,
        input logic                   is_right,
        input logic [ADDR_WIDTH-1:0]  tile_addr,
        input logic [7:0]             cmd_id
    );
        int start_cycle;
        
        $display("[TB] DISPATCH: right=%0d, nv_cnt=%0d, ugd_len=%0d, col_start=%0d, cmd_id=%0d",
                 is_right, nv_cnt, ugd_len, col_start, cmd_id);
        
        start_cycle = cycle_count;
        
        @(posedge clk);
        // Pack command payload per master_control_2d format:
        // word1[31:16] = nv_cnt, word1[15:0] = v_count (ugd_len)
        // word2[15:0] = tile_addr
        // word3[15:8] = col_start (8-bit field, we use lower 4 bits), word3[2] = disp_right
        cmd_payload_word1 = {nv_cnt, ugd_len};                              // {nv_cnt, v_count}
        cmd_payload_word2 = {16'b0, {7'b0, tile_addr}};                     // {reserved, tile_addr}
        cmd_payload_word3 = {16'b0, {4'b0, col_start}, 5'b0, is_right, 1'b0, 1'b0};  // {reserved, col_start[7:0], reserved, disp_right, broadcast, man_4b}
        mc_cmd_id = cmd_id;
        mc_cmd_op = CMD_DISP;                                               // Assert DISP opcode
        
        // Wait for rising edge to be detected and ACK to be registered
        @(posedge clk);
        #1;  // Small delay to let NBA settle, check before next edge
        
        // Verify ACK
        if (!dc_ack_disp) begin
            $display("[TB] ERROR: dc_ack_disp not asserted on decode!");
            current_test_ok = 0;
        end else begin
            $display("[TB] DISPATCH ACK received (correct behavior)");
        end
        
        // Clear opcode (return to NOP)
        mc_cmd_op = CMD_NOP;
        
        // Wait for dispatcher to start (may take 1-2 cycles for pulse to propagate)
        repeat (3) @(posedge clk);
        
        // Now wait for dispatcher to complete (state returns to IDLE)
        while (dispatcher_state != 0) begin
            @(posedge clk);
        end
        
        $display("[TB] DISPATCH complete in %0d cycles, lines_processed=%0d",
                 cycle_count - start_cycle, dispatcher_lines_processed);
        
        // Wait a couple cycles for dc_id to be updated (triggered by dispatcher_done_internal)
        repeat (3) @(posedge clk);
        
        // Verify cmd_id updated
        if (dc_id == cmd_id) begin
            $display("[TB] dc_id updated correctly to %0d", cmd_id);
        end else begin
            $display("[TB] ERROR: dc_id is %0d, expected %0d", dc_id, cmd_id);
            current_test_ok = 0;
        end
        
        repeat (10) @(posedge clk);
    endtask

    // =========================================================================
    // Task: Verify LEFT Path Data
    // =========================================================================
    // Reference: MULTI_ROW_REFERENCE.md - "Exponent Indexing" section
    // Exponent index = b_idx * ugd_len * 4 + v_idx * 4 + l
    // Memory block format: lines 0-15 = exponents (512 bytes), lines 16+ = mantissa
    task automatic verify_left_data(
        input int nv_cnt,      // B count (number of UGDs)
        input int ugd_len      // V count (NVs per UGD)
    );
        int man_errors;
        int exp_errors;
        int total_nvs;
        int mantissa_idx;
        int exp_idx;
        int exp_line;
        int exp_byte_pos;
        int b_idx;
        int v_idx;
        logic [DATA_WIDTH-1:0] expected_man_line;
        logic [7:0] expected_exp;
        logic [7:0] actual_exp;
        
        man_errors = 0;
        exp_errors = 0;
        total_nvs = nv_cnt * ugd_len;
        
        $display("[TB] Verifying LEFT path data: B=%0d, V=%0d (%0d NVs total)", nv_cnt, ugd_len, total_nvs);
        
        for (int nv = 0; nv < total_nvs; nv++) begin
            row_bram_rd_idx = nv;
            @(posedge clk);
            @(posedge clk);  // Allow combinational read
            
            // Calculate b_idx and v_idx from flat nv index
            b_idx = nv / ugd_len;  // Which UGD (batch)
            v_idx = nv % ugd_len;  // V within UGD
            
            // Verify mantissa data (4 groups per NV)
            for (int g = 0; g < LINES_PER_NV; g++) begin
                mantissa_idx = EXP_LINES + nv * LINES_PER_NV + g;
                expected_man_line = golden_left[mantissa_idx];
                
                if (row_bram_man[g] !== expected_man_line) begin
                    if (man_errors < 10) begin
                        $display("[TB] ERROR: NV %0d (B=%0d,V=%0d) group %0d mantissa mismatch", nv, b_idx, v_idx, g);
                        $display("[TB]   Expected: 0x%064x", expected_man_line);
                        $display("[TB]   Got:      0x%064x", row_bram_man[g]);
                    end
                    man_errors++;
                end
                
                // Verify exponent data
                // Exponent index = b_idx * ugd_len * 4 + v_idx * 4 + g
                // This is the CORRECTED formula matching MULTI_ROW_REFERENCE.md
                exp_idx = b_idx * ugd_len * LINES_PER_NV + v_idx * LINES_PER_NV + g;
                exp_line = exp_idx / 32;         // Which of 16 exp lines
                exp_byte_pos = exp_idx % 32;     // Which byte within line
                expected_exp = golden_left[exp_line][exp_byte_pos * 8 +: 8];
                actual_exp = row_bram_exp[g * 8 +: 8];
                
                if (actual_exp !== expected_exp) begin
                    if (exp_errors < 10) begin
                        $display("[TB] ERROR: NV %0d (B=%0d,V=%0d) exp[%0d]: expected 0x%02x (idx=%0d), got 0x%02x",
                                 nv, b_idx, v_idx, g, expected_exp, exp_idx, actual_exp);
                    end
                    exp_errors++;
                end
            end
            
            if (nv < 2 || nv >= total_nvs - 2) begin
                $display("[TB]   NV %0d (B=%0d,V=%0d): man[0][31:0]=0x%08x, exp=0x%08x",
                         nv, b_idx, v_idx, row_bram_man[0][31:0], row_bram_exp);
            end
        end
        
        if (man_errors == 0 && exp_errors == 0) begin
            $display("[TB] LEFT path verification: PASS (%0d NVs, mantissa: OK, exponents: OK)", total_nvs);
        end else begin
            $display("[TB] LEFT path verification: FAIL (mantissa errors: %0d, exponent errors: %0d)", man_errors, exp_errors);
            current_test_ok = 0;
        end
    endtask

    // =========================================================================
    // Task: Verify RIGHT Path Data
    // =========================================================================
    // Reference: MULTI_ROW_REFERENCE.md - "Exponent Indexing" section
    // Exponent index = c_idx * ugd_len * 4 + v_idx * 4 + l
    // Memory block format: lines 0-15 = exponents (512 bytes), lines 16+ = mantissa
    task automatic verify_right_data(
        input int nv_cnt,      // C count (number of UGDs/columns)
        input int ugd_len,     // V count (NVs per UGD)
        input int col_start
    );
        int man_errors;
        int exp_errors;
        int count_errors;
        int total_writes;
        int mantissa_idx;
        int exp_idx;
        int exp_line;
        int exp_byte_pos;
        int col_idx;
        int addr_offset;
        int wraddr_start;
        logic [DATA_WIDTH-1:0] expected_man_line;
        logic [7:0] expected_exp;
        logic [7:0] actual_exp;
        
        man_errors = 0;
        exp_errors = 0;
        count_errors = 0;
        total_writes = nv_cnt * ugd_len * LINES_PER_NV;
        
        $display("[TB] Verifying RIGHT path data: C=%0d, V=%0d (%0d lines across %0d columns)",
                 nv_cnt, ugd_len, total_writes, nv_cnt);
        
        // Verify total writes per column
        begin
            automatic int expected_writes = ugd_len * LINES_PER_NV;
            for (int c = 0; c < nv_cnt && c < NUM_COLS; c++) begin
                col_idx = (col_start + c) % NUM_COLS;
                
                if (col_write_counts[col_idx] != expected_writes) begin
                    $display("[TB] ERROR: Col %0d write count: expected %0d, got %0d",
                             col_idx, expected_writes, col_write_counts[col_idx]);
                    count_errors++;
                end
                
                $display("[TB]   Col %0d: %0d writes", col_idx, col_write_counts[col_idx]);
            end
        end
        
        // Verify data content for all columns
        wraddr_start = 0;
        
        for (int c = 0; c < nv_cnt && c < NUM_COLS; c++) begin
            col_idx = (col_start + c) % NUM_COLS;
            
            // Check if this is a wrap point
            if (c > 0 && ((col_start + c) % NUM_COLS) == 0) begin
                wraddr_start = wraddr_start + ugd_len * LINES_PER_NV;
            end
            
            for (int v = 0; v < ugd_len; v++) begin
                for (int l = 0; l < LINES_PER_NV; l++) begin
                    addr_offset = wraddr_start + v * LINES_PER_NV + l;
                    
                    // Mantissa index in golden data: for column c, the mantissa line is at
                    // golden_right[EXP_LINES + c * ugd_len * 4 + v * 4 + l]
                    mantissa_idx = EXP_LINES + c * ugd_len * LINES_PER_NV + v * LINES_PER_NV + l;
                    expected_man_line = golden_right[mantissa_idx];
                    
                    if (col_man_mem[col_idx][addr_offset] !== expected_man_line) begin
                        if (man_errors < 10) begin
                            $display("[TB] ERROR: Col %0d (C=%0d) addr %0d mantissa mismatch", col_idx, c, addr_offset);
                            $display("[TB]   Expected: 0x%064x", expected_man_line);
                            $display("[TB]   Got:      0x%064x", col_man_mem[col_idx][addr_offset]);
                        end
                        man_errors++;
                    end
                    
                    // Verify exponent data
                    // Exponent index = c * ugd_len * 4 + v * 4 + l
                    // This is the CORRECTED formula matching MULTI_ROW_REFERENCE.md
                    exp_idx = c * ugd_len * LINES_PER_NV + v * LINES_PER_NV + l;
                    exp_line = exp_idx / 32;         // Which of 16 exp lines
                    exp_byte_pos = exp_idx % 32;     // Which byte within line
                    expected_exp = golden_right[exp_line][exp_byte_pos * 8 +: 8];
                    actual_exp = col_exp_mem[col_idx][addr_offset];
                    
                    if (actual_exp !== expected_exp) begin
                        if (exp_errors < 10) begin
                            $display("[TB] ERROR: Col %0d (C=%0d) addr %0d exp: expected 0x%02x (idx=%0d), got 0x%02x",
                                     col_idx, c, addr_offset, expected_exp, exp_idx, actual_exp);
                        end
                        exp_errors++;
                    end
                end
            end
        end
        
        if (man_errors == 0 && exp_errors == 0 && count_errors == 0) begin
            $display("[TB] RIGHT path verification: PASS (mantissa: OK, exponents: OK, counts: OK)");
        end else begin
            $display("[TB] RIGHT path verification: FAIL (mantissa errors: %0d, exponent errors: %0d, count errors: %0d)",
                     man_errors, exp_errors, count_errors);
            current_test_ok = 0;
        end
    endtask

    // =========================================================================
    // Test 1: FETCH + LEFT DISPATCH
    // =========================================================================
    task automatic test_fetch_left_dispatch();
        int B = 4;   // Number of batches
        int V = 2;   // NVs per batch
        
        $display("\n========================================");
        $display("TEST 1: FETCH Block 0 + LEFT DISPATCH");
        $display("  B=%0d, V=%0d (%0d mantissa lines)", B, V, B*V*LINES_PER_NV);
        $display("========================================");
        
        current_test_ok = 1;
        reset_dut();
        
        // FETCH block 0 (left data)
        issue_fetch(26'd0, 16'd528, 8'd1);
        
        // LEFT DISPATCH
        issue_dispatch(B, V, 0, 0, 0, 8'd2);  // right=0 for LEFT
        
        // Verify results
        verify_left_data(B, V);
        
        tests_run++;
        if (current_test_ok) tests_passed++;
    endtask

    // =========================================================================
    // Test 2: FETCH + RIGHT DISPATCH
    // =========================================================================
    task automatic test_fetch_right_dispatch();
        int C = 4;   // Number of columns
        int V = 2;   // NVs per column
        
        $display("\n========================================");
        $display("TEST 2: FETCH Block 1 + RIGHT DISPATCH");
        $display("  C=%0d, V=%0d (%0d mantissa lines)", C, V, C*V*LINES_PER_NV);
        $display("========================================");
        
        current_test_ok = 1;
        reset_dut();
        
        // FETCH block 1 (right data)
        issue_fetch(26'd528, 16'd528, 8'd3);
        
        // RIGHT DISPATCH
        issue_dispatch(C, V, 0, 1, 0, 8'd4);  // right=1 for RIGHT
        
        // Verify results
        verify_right_data(C, V, 0);
        
        tests_run++;
        if (current_test_ok) tests_passed++;
    endtask

    // =========================================================================
    // Test 3: ACK Timing Verification
    // =========================================================================
    task automatic test_ack_timing();
        $display("\n========================================");
        $display("TEST 3: ACK Timing Verification");
        $display("========================================");
        
        current_test_ok = 1;
        reset_dut();
        
        // Issue FETCH and check ACK (using packed interface)
        @(posedge clk);
        cmd_payload_word1 = {6'b0, 26'd0};   // start_addr
        cmd_payload_word2 = {16'd1, 16'd16}; // {v_count, len}
        cmd_payload_word3 = 32'd0;            // fetch_right=0
        mc_cmd_id = 8'd5;
        mc_cmd_op = CMD_FETCH;
        
        @(posedge clk);
        #1;  // Let NBA settle
        if (dc_ack_fetch) begin
            $display("[TB] FETCH ACK: PASS - received");
        end else begin
            $display("[TB] FETCH ACK: FAIL - not received");
            current_test_ok = 0;
        end
        mc_cmd_op = CMD_NOP;
        
        // Wait for internal completion
        repeat (200) @(posedge clk);
        
        // Issue DISPATCH and check ACK (using packed interface)
        @(posedge clk);
        cmd_payload_word1 = {16'd1, 16'd1};               // {nv_cnt, v_count}
        cmd_payload_word2 = {16'b0, 16'd0};               // tile_addr
        cmd_payload_word3 = {16'b0, 8'd0, 5'b0, 1'b0, 1'b0, 1'b0};  // col_start=0, disp_right=0
        mc_cmd_id = 8'd6;
        mc_cmd_op = CMD_DISP;
        
        @(posedge clk);
        #1;  // Let NBA settle
        if (dc_ack_disp) begin
            $display("[TB] DISPATCH ACK: PASS - received");
        end else begin
            $display("[TB] DISPATCH ACK: FAIL - not received");
            current_test_ok = 0;
        end
        mc_cmd_op = CMD_NOP;
        
        // Wait for internal completion
        repeat (200) @(posedge clk);
        
        tests_run++;
        if (current_test_ok) tests_passed++;
    endtask

    // =========================================================================
    // Test 4: cmd_id Tracking
    // =========================================================================
    task automatic test_cmd_id_tracking();
        $display("\n========================================");
        $display("TEST 4: cmd_id Tracking");
        $display("========================================");
        
        current_test_ok = 1;
        reset_dut();
        
        // Initial dc_id should be 0
        if (dc_id != 0) begin
            $display("[TB] ERROR: Initial dc_id is %0d, expected 0", dc_id);
            current_test_ok = 0;
        end
        
        // Issue FETCH with cmd_id=7
        issue_fetch(26'd0, 16'd32, 8'd7);
        
        // After FETCH completion, dc_id should be 7
        if (dc_id == 8'd7) begin
            $display("[TB] dc_id after FETCH: PASS (dc_id=%0d)", dc_id);
        end else begin
            $display("[TB] dc_id after FETCH: FAIL (dc_id=%0d, expected 7)", dc_id);
            current_test_ok = 0;
        end
        
        // Issue DISPATCH with cmd_id=8
        issue_dispatch(1, 1, 0, 0, 0, 8'd8);
        
        // After DISPATCH completion, dc_id should be 8
        if (dc_id == 8'd8) begin
            $display("[TB] dc_id after DISPATCH: PASS (dc_id=%0d)", dc_id);
        end else begin
            $display("[TB] dc_id after DISPATCH: FAIL (dc_id=%0d, expected 8)", dc_id);
            current_test_ok = 0;
        end
        
        tests_run++;
        if (current_test_ok) tests_passed++;
    endtask

    // =========================================================================
    // Main Test Sequence
    // =========================================================================
    initial begin
        tests_run = 0;
        tests_passed = 0;
        cycle_count = 0;
        clear_col_brams = 0;

        $display("\n===============================================");
        $display("DISPATCHER_CONTROL_2D TESTBENCH");
        $display("End-to-End FETCH + DISPATCH Verification");
        $display("===============================================\n");

        // Load hex files into golden storage
        load_hex_file("/home/dev/Dev/elastix_gemm/hex/left.hex", golden_left);
        load_hex_file("/home/dev/Dev/elastix_gemm/hex/right.hex", golden_right);

        // Reset sequence
        repeat(10) @(posedge clk);
        rstn = 1'b0;
        clear_col_brams = 1;
        repeat(10) @(posedge clk);
        clear_col_brams = 0;
        rstn = 1'b1;
        repeat(10) @(posedge clk);

        // Run tests
        test_fetch_left_dispatch();
        test_fetch_right_dispatch();
        test_ack_timing();
        test_cmd_id_tracking();

        // Summary
        $display("\n===============================================");
        $display("TEST SUMMARY");
        $display("===============================================");
        $display("Tests run:    %0d", tests_run);
        $display("Tests passed: %0d", tests_passed);
        $display("Total AR received: %0d", mem_total_ar_received);
        $display("Total R issued:    %0d", mem_total_r_issued);
        
        if (tests_passed == tests_run) begin
            $display("\n*** ALL TESTS PASSED ***\n");
        end else begin
            $display("\n*** %0d TEST(S) FAILED ***\n", tests_run - tests_passed);
        end
        $display("===============================================\n");

        $finish;
    end

    // =========================================================================
    // Timeout Watchdog
    // =========================================================================
    initial begin
        #TIMEOUT_NS;
        $error("[TB] Timeout!");
        $finish;
    end

endmodule
