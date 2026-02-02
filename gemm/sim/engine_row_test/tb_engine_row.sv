// ------------------------------------------------------------------
// Engine Row Testbench - Dispatcher Control + Compute Engine Integration
//
// Purpose: Test one complete row of the GEMM engine:
//   - dispatcher_control_2d: Fetches data from memory, dispatches to CE
//   - compute_engine_2d: Computes matrix multiplication
//   - Address conversion layer (from engine_top_2d)
//
// This tests the integration between dispatcher and compute engine
// with the same interface as the full gemm2d system, but isolated to
// one row for debugging.
//
// Input: Memory model loaded with left/right hex files (like dispatcher_control_test)
// Output: Golden comparison (like compute_engine_2d_test)
//
// Author: Junhao Pan
// Date: Jan 2026
// ------------------------------------------------------------------

`timescale 1ns/1ps

`include "nap_interfaces.svh"

module tb_engine_row;

    // =========================================================================
    // Parameters
    // =========================================================================
    localparam CLK_PERIOD       = 2.5;          // 400MHz
    localparam TIMEOUT_NS       = 5000000;      // 5ms timeout
    localparam DATA_WIDTH       = 256;
    localparam MAN_WIDTH        = 256;
    localparam EXP_WIDTH        = 8;
    localparam BRAM_DEPTH       = 512;
    localparam FIFO_DEPTH       = 1024;
    localparam ADDR_WIDTH       = $clog2(BRAM_DEPTH);
    localparam AXI_ADDR_WIDTH   = 42;
    localparam [8:0] GDDR6_CTRL_ID = 9'd2;
    localparam LINES_PER_BLOCK  = 528;
    localparam EXP_LINES        = 16;
    localparam LINES_PER_NV     = 4;

    // Configurable NUM_MLPS
    `ifndef NUM_MLPS
    `define NUM_MLPS 2
    `endif
    localparam int NUM_MLPS = `NUM_MLPS;
    localparam int NUM_COLS = 2 * NUM_MLPS;
    localparam int COL_IDX_WIDTH = $clog2(NUM_COLS);
    localparam int MLP_SEL_WIDTH = $clog2(NUM_MLPS);

    // Hex file path
    localparam string HEX_PATH = "/home/dev/Dev/elastix_gemm/hex/";

    // =========================================================================
    // Test Configuration
    // =========================================================================
    typedef struct {
        int         C;
        int         V;
        int         B;
        string      name;
    } test_config_t;

    // Test suite - tests column grouping (C > NUM_COLS handled via wraddr_start)
    test_config_t test_suite[] = '{
        '{C: 4,  V: 4,  B: 4,   name: "golden_B4_C4_V4"},     // No column grouping (C=NUM_COLS)
        '{C: 64, V: 2,  B: 1,   name: "golden_B1_C64_V2"},    // Column grouping (C=64 > NUM_COLS=4)
        '{C: 64, V: 2,  B: 8,   name: "golden_B8_C64_V2"}     // Column grouping with multiple batches
    };

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
    // GDDR6 Memory Model
    // =========================================================================
    logic [31:0] mem_outstanding_count;
    logic [31:0] mem_total_ar_received;
    logic [31:0] mem_total_r_issued;

    tb_memory_model_realistic #(
        .DATA_WIDTH(256),
        .ADDR_WIDTH(42),
        .LINES_PER_BLOCK(528),
        .NUM_BLOCKS(2),
        .LATENCY_CYCLES(40),
        .MAX_OUTSTANDING(32),
        .VERBOSITY(1)
    ) u_gddr6_model (
        .i_clk(clk),
        .i_reset_n(rstn),
        .axi_mem_if(axi_nap.responder),
        .o_outstanding_count(mem_outstanding_count),
        .o_total_ar_received(mem_total_ar_received),
        .o_total_r_issued(mem_total_r_issued)
    );

    // =========================================================================
    // Command Interface (Packed Payload)
    // =========================================================================
    logic [7:0]   mc_cmd_op;
    logic [7:0]   mc_cmd_id;
    logic [31:0]  cmd_payload_word1;
    logic [31:0]  cmd_payload_word2;
    logic [31:0]  cmd_payload_word3;

    // Opcode constants
    localparam logic [7:0] CMD_NOP    = 8'h00;
    localparam logic [7:0] CMD_FETCH  = 8'hF0;
    localparam logic [7:0] CMD_DISP   = 8'hF1;
    localparam logic [7:0] CMD_MATMUL = 8'hF2;

    // =========================================================================
    // Dispatcher Control Outputs
    // =========================================================================
    logic                   dc_ack_fetch;
    logic                   dc_ack_disp;
    logic [7:0]             dc_id;

    // LEFT path outputs (activations -> row_bram)
    logic [ADDR_WIDTH-1:0]  left_man_wr_addr;
    logic                   left_man_wr_en;
    logic [MAN_WIDTH-1:0]   left_man_wr_data;
    logic [ADDR_WIDTH-1:0]  left_exp_wr_addr;
    logic                   left_exp_wr_en;
    logic [EXP_WIDTH-1:0]   left_exp_wr_data;

    // RIGHT path outputs (weights -> column BRAMs)
    logic [ADDR_WIDTH-1:0]  right_wr_addr;
    logic [NUM_COLS-1:0]    right_wr_en;
    logic [MAN_WIDTH-1:0]   right_man_wr_data;
    logic [EXP_WIDTH-1:0]   right_exp_wr_data;

    // Debug signals
    logic [3:0]             dc_state;
    logic [3:0]             fetcher_state;
    logic [3:0]             dispatcher_state;
    logic [15:0]            fetcher_lines_received;
    logic [15:0]            dispatcher_lines_processed;
    logic [$clog2(FIFO_DEPTH):0] fifo_count;
    logic                   fifo_afull;

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
    ) u_dispatcher_control (
        .i_clk              (clk),
        .i_reset_n          (rstn),
        
        // Command Interface
        .i_mc_cmd_op        (mc_cmd_op),
        .i_mc_cmd_id        (mc_cmd_id),
        .i_cmd_payload_word1(cmd_payload_word1),
        .i_cmd_payload_word2(cmd_payload_word2),
        .i_cmd_payload_word3(cmd_payload_word3),
        .o_dc_ack_fetch     (dc_ack_fetch),
        .o_dc_ack_disp      (dc_ack_disp),
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
        .o_fifo_count             (fifo_count),
        .o_fifo_afull             (fifo_afull)
    );

    // =========================================================================
    // Weight Interface Adapter: DC RIGHT -> CE Weight
    // (Same logic as engine_top_2d)
    // =========================================================================
    logic                          wt_wr_en;
    logic [MLP_SEL_WIDTH-1:0]      wt_mlp_sel;
    logic [9:0]                    wt_nv_idx;
    logic [COL_IDX_WIDTH-1:0]      col_idx;

    // One-hot to binary decoder for column index
    always_comb begin
        col_idx = '0;
        for (int c = 0; c < NUM_COLS; c++) begin
            if (right_wr_en[c])
                col_idx = COL_IDX_WIDTH'(c);
        end
    end

    // Weight write enable is OR of all column enables
    assign wt_wr_en = |right_wr_en;

    // MLP selection: column / 2
    assign wt_mlp_sel = col_idx[COL_IDX_WIDTH-1:1];

    // NV index: addr * 2 + bank (where bank = col % 2)
    assign wt_nv_idx = {right_wr_addr, 1'b0} + {9'b0, col_idx[0]};

    // Debug: weight address calculation
    always @(posedge clk) begin
        if (wt_wr_en) begin
            $display("[WT_ADDR] @%0t dc_addr=%0d col_idx=%0d mlp_sel=%0d nv_idx=%0d",
                     $time, right_wr_addr, col_idx, wt_mlp_sel, wt_nv_idx);
        end
    end

    // =========================================================================
    // Compute Engine Signals
    // =========================================================================
    logic         ce_ack_matmul;
    logic [7:0]   ce_id;
    logic         matmul_done;
    logic [3:0]   ce_state;
    logic [15:0]  result_count;
    logic         read_empty_sticky;
    logic         results_ready;

    // Result FIFO Interface
    logic [15:0]  result_data [NUM_COLS-1:0];
    logic         result_rd_en [NUM_COLS-1:0];
    logic         result_empty [NUM_COLS-1:0];
    logic         result_afull;

    // =========================================================================
    // DUT: compute_engine_2d
    // =========================================================================
    compute_engine_2d #(
        .MATMUL_ID          (0),
        .MAN_WIDTH          (MAN_WIDTH),
        .EXP_WIDTH          (EXP_WIDTH),
        .BRAM_DEPTH         (BRAM_DEPTH),
        .ADDR_WIDTH         (ADDR_WIDTH),
        .NUM_MLPS           (NUM_MLPS),
        .NUM_COLS           (NUM_COLS),
        .RESULT_FIFO_DEPTH  (1024)
    ) u_compute_engine (
        .i_clk              (clk),
        .i_reset_n          (rstn),

        // MATMUL Command Interface
        .i_mc_cmd_op        (mc_cmd_op),
        .i_cmd_id           (mc_cmd_id),
        .i_cmd_payload_word1(cmd_payload_word1),
        .i_cmd_payload_word2(cmd_payload_word2),
        .i_cmd_payload_word3(cmd_payload_word3),
        .o_ce_ack_matmul    (ce_ack_matmul),
        .o_ce_id            (ce_id),
        .o_matmul_done      (matmul_done),

        // row_bram Write Interface (from DC left path)
        .i_man_left_wr_addr (left_man_wr_addr),
        .i_man_left_wr_en   (left_man_wr_en),
        .i_man_left_wr_data (left_man_wr_data),
        .i_exp_left_wr_addr (left_exp_wr_addr),
        .i_exp_left_wr_en   (left_exp_wr_en),
        .i_exp_left_wr_data (left_exp_wr_data),

        // MLP Weight Write Interface (adapted from DC right path)
        .i_wt_wr_en         (wt_wr_en),
        .o_wt_wr_ready      (),
        .i_wt_wr_man        (right_man_wr_data),
        .i_wt_wr_exp        (right_exp_wr_data),
        .i_wt_mlp_sel       (wt_mlp_sel),
        .i_wt_nv_idx        (wt_nv_idx),

        // Result FIFO Interface
        .o_result_data      (result_data),
        .i_result_rd_en     (result_rd_en),
        .o_result_empty     (result_empty),
        .o_result_afull     (result_afull),

        // Debug Interface
        .o_ce_state         (ce_state),
        .o_result_count     (result_count),
        .o_read_empty_sticky(read_empty_sticky),
        .o_results_ready    (results_ready)
    );

    // =========================================================================
    // Test Status
    // =========================================================================
    int     tests_run;
    int     tests_passed;
    logic   current_test_ok;
    int     cycle_count;

    always @(posedge clk) begin
        if (rstn) cycle_count <= cycle_count + 1;
        else cycle_count <= 0;
    end

    // =========================================================================
    // Result Collection Storage
    // =========================================================================
    logic [15:0] collected_results [0:4095];
    int num_results_collected;

    // =========================================================================
    // Golden Reference Storage
    // =========================================================================
    logic [15:0] golden_results [0:4095];
    int golden_count;

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
        for (int i = 0; i < NUM_COLS; i++) result_rd_en[i] = 1'b0;
        
        repeat (20) @(posedge clk);
        rstn = 1;
        repeat (10) @(posedge clk);
        
        $display("[TB] Reset complete");
    endtask

    // =========================================================================
    // Task: Issue FETCH Command
    // word1 = start_addr[31:0]
    // word2 = {v_count[15:0], len[15:0]}
    // word3 = {31'b0, fetch_right}
    // =========================================================================
    task automatic issue_fetch(
        input logic [31:0] addr,
        input logic [15:0] len,
        input logic [15:0] v_count,
        input logic        fetch_right,
        input logic [7:0]  cmd_id_in
    );
        int start_cycle;
        
        $display("[TB] FETCH: addr=0x%08x, len=%0d, v=%0d, right=%0d, cmd_id=%0d",
                 addr, len, v_count, fetch_right, cmd_id_in);
        
        start_cycle = cycle_count;
        
        @(posedge clk);
        cmd_payload_word1 = addr;
        cmd_payload_word2 = {v_count, len};
        cmd_payload_word3 = {31'b0, fetch_right};
        mc_cmd_id = cmd_id_in;
        mc_cmd_op = CMD_FETCH;
        
        @(posedge clk);
        #1;
        
        if (!dc_ack_fetch) begin
            $display("[TB] WARNING: dc_ack_fetch not asserted");
        end
        
        mc_cmd_op = CMD_NOP;
        
        // Wait for fetcher to complete
        repeat (3) @(posedge clk);
        while (fetcher_state != 0) begin
            @(posedge clk);
            if (cycle_count - start_cycle > 50000) begin
                $display("[TB] ERROR: FETCH timeout");
                break;
            end
        end
        
        $display("[TB] FETCH complete in %0d cycles", cycle_count - start_cycle);
        repeat (5) @(posedge clk);
    endtask

    // =========================================================================
    // Task: Issue DISPATCH Command
    // word1 = {nv_cnt[15:0], v_count[15:0]}
    // word2 = {16'b0, tile_addr[15:0]}
    // word3 = {16'b0, col_start[7:0], 5'b0, disp_right, broadcast, man_4b}
    // =========================================================================
    task automatic issue_dispatch(
        input logic [15:0] nv_cnt,
        input logic [15:0] v_count,
        input logic [15:0] tile_addr,
        input logic [7:0]  col_start,
        input logic        disp_right,
        input logic        broadcast,
        input logic [7:0]  cmd_id_in
    );
        int start_cycle;
        
        $display("[TB] DISPATCH: nv_cnt=%0d, v=%0d, tile_addr=0x%04x, col_start=%0d, right=%0d, bc=%0d, cmd_id=%0d",
                 nv_cnt, v_count, tile_addr, col_start, disp_right, broadcast, cmd_id_in);
        
        start_cycle = cycle_count;
        
        @(posedge clk);
        cmd_payload_word1 = {nv_cnt, v_count};
        cmd_payload_word2 = {16'b0, tile_addr};
        cmd_payload_word3 = {16'b0, col_start, 5'b0, disp_right, broadcast, 1'b0};
        mc_cmd_id = cmd_id_in;
        mc_cmd_op = CMD_DISP;
        
        @(posedge clk);
        #1;
        
        if (!dc_ack_disp) begin
            $display("[TB] WARNING: dc_ack_disp not asserted");
        end
        
        mc_cmd_op = CMD_NOP;
        
        // Wait for dispatcher to complete
        repeat (3) @(posedge clk);
        while (dispatcher_state != 0) begin
            @(posedge clk);
            if (cycle_count - start_cycle > 50000) begin
                $display("[TB] ERROR: DISPATCH timeout");
                break;
            end
        end
        
        $display("[TB] DISPATCH complete in %0d cycles, lines=%0d",
                 cycle_count - start_cycle, dispatcher_lines_processed);
        repeat (5) @(posedge clk);
    endtask

    // =========================================================================
    // Task: Issue MATMUL Command
    // word1 = {left_addr[15:0], right_addr[15:0]}
    // word2 = {B[15:0], C[15:0]}
    // word3 = {V[15:0], flags[15:0]}
    // =========================================================================
    task automatic issue_matmul(
        input logic [15:0] left_addr,
        input logic [15:0] right_addr,
        input logic [15:0] B,
        input logic [15:0] C,
        input logic [15:0] V,
        input logic [7:0]  cmd_id_in
    );
        int start_cycle;
        
        $display("[TB] MATMUL: left_addr=%0d, right_addr=%0d, B=%0d, C=%0d, V=%0d, cmd_id=%0d",
                 left_addr, right_addr, B, C, V, cmd_id_in);
        
        start_cycle = cycle_count;
        
        @(posedge clk);
        cmd_payload_word1 = {left_addr, right_addr};
        cmd_payload_word2 = {B, C};
        cmd_payload_word3 = {V, 16'b0};
        mc_cmd_id = cmd_id_in;
        mc_cmd_op = CMD_MATMUL;
        
        @(posedge clk);
        #1;
        
        if (!ce_ack_matmul) begin
            $display("[TB] WARNING: ce_ack_matmul not asserted");
        end
        
        mc_cmd_op = CMD_NOP;
        
        // Wait for MATMUL to complete
        repeat (3) @(posedge clk);
        while (!matmul_done) begin
            @(posedge clk);
            if (cycle_count - start_cycle > 500000) begin
                $display("[TB] ERROR: MATMUL timeout");
                break;
            end
        end
        
        $display("[TB] MATMUL complete in %0d cycles", cycle_count - start_cycle);
        repeat (10) @(posedge clk);
    endtask

    // =========================================================================
    // Task: Collect Results from FIFOs
    // Column Grouping: For C > NUM_COLS, the compute engine produces results
    // in column groups. Each column group produces NUM_COLS results which are
    // read from the physical FIFOs [0:NUM_COLS-1].
    // Result order: [b0_cg0_c0, b0_cg0_c1, ..., b0_cg1_c0, ..., b(B-1)_cgN_cM]
    // =========================================================================
    task automatic collect_results(int B, int C, int expected_count);
        int collected;
        int timeout_cnt;
        int batch, cg, logical_col;
        int num_col_groups;
        int active_cols;
        logic any_available;

        num_col_groups = (C + NUM_COLS - 1) / NUM_COLS;  // Ceiling division
        $display("[TB] Collecting %0d results (B=%0d, C=%0d, col_groups=%0d)", 
                 expected_count, B, C, num_col_groups);
        collected = 0;
        timeout_cnt = 0;
        
        for (int i = 0; i < NUM_COLS; i++) result_rd_en[i] = 1'b0;

        // For each batch
        for (batch = 0; batch < B && timeout_cnt < 100000; batch++) begin
            // For each column group within the batch
            for (cg = 0; cg < num_col_groups && timeout_cnt < 100000; cg++) begin
                // Calculate how many columns are active in this group
                // Last group may have fewer columns if C % NUM_COLS != 0
                if (cg == num_col_groups - 1 && (C % NUM_COLS) != 0) begin
                    active_cols = C % NUM_COLS;
                end else begin
                    active_cols = NUM_COLS;
                end

                // Wait for data available in FIFO 0
                any_available = 0;
                while (!any_available && timeout_cnt < 100000) begin
                    if (!result_empty[0]) begin
                        any_available = 1;
                    end else begin
                        @(posedge clk);
                        timeout_cnt++;
                    end
                end

                if (!any_available) break;

                // Pop ALL NUM_COLS FIFOs (including garbage for partial groups)
                for (int f = 0; f < NUM_COLS; f++) begin
                    result_rd_en[f] = 1'b1;
                end

                @(posedge clk);  // FIFO latches rd_en
                
                for (int f = 0; f < NUM_COLS; f++) begin
                    result_rd_en[f] = 1'b0;
                end
                
                @(posedge clk);  // Data now stable on outputs

                // Capture only valid results from this column group
                for (int f = 0; f < active_cols && collected < expected_count; f++) begin
                    logical_col = cg * NUM_COLS + f;
                    collected_results[collected] = result_data[f];
                    collected++;
                end
                timeout_cnt++;
            end
        end

        num_results_collected = collected;
        $display("[TB] Collected %0d results", collected);
    endtask

    // =========================================================================
    // FP16 to Real Conversion
    // =========================================================================
    function automatic real fp16_to_real(logic [15:0] fp16);
        logic        sign;
        logic [4:0]  exp;
        logic [9:0]  mant;
        real         result;
        int          exp_val;

        sign = fp16[15];
        exp  = fp16[14:10];
        mant = fp16[9:0];

        if (exp == 0) begin
            if (mant == 0) result = 0.0;
            else result = $itor(mant) / 1024.0 * $pow(2.0, -14);
        end else if (exp == 31) begin
            if (mant == 0) result = sign ? -1.0/0.0 : 1.0/0.0;
            else result = 0.0/0.0;
        end else begin
            exp_val = exp - 15;
            result = (1.0 + $itor(mant) / 1024.0) * $pow(2.0, exp_val);
        end

        if (sign) result = -result;
        return result;
    endfunction

    // =========================================================================
    // Load Golden File
    // =========================================================================
    task automatic load_golden_file(string filename);
        integer fd;
        string line_str;
        logic [15:0] value;
        int idx;

        fd = $fopen(filename, "r");
        if (fd == 0) begin
            $display("[TB] ERROR: Cannot open golden file %s", filename);
            golden_count = 0;
            return;
        end

        idx = 0;
        while (!$feof(fd) && idx < 4096) begin
            if ($fgets(line_str, fd)) begin
                if ($sscanf(line_str, "%h", value) == 1) begin
                    golden_results[idx] = value;
                    idx++;
                end
            end
        end
        $fclose(fd);
        golden_count = idx;
        $display("[TB] Loaded %0d golden values from %s", golden_count, filename);
    endtask

    // =========================================================================
    // Compare Results
    // =========================================================================
    task automatic compare_results(int expected_count, output logic pass);
        real actual_val, golden_val, diff, rel_error;
        int mismatches;

        mismatches = 0;
        pass = 1'b1;

        for (int i = 0; i < expected_count; i++) begin
            actual_val = fp16_to_real(collected_results[i]);
            golden_val = fp16_to_real(golden_results[i]);

            diff = actual_val - golden_val;
            if (diff < 0) diff = -diff;

            if (golden_val != 0.0) begin
                rel_error = diff / (golden_val < 0 ? -golden_val : golden_val);
            end else begin
                rel_error = (actual_val == 0.0) ? 0.0 : 1.0;
            end

            // 5% relative OR 0.001 absolute tolerance
            if (rel_error > 0.05 && diff > 0.001) begin
                if (mismatches < 10) begin
                    $display("[TB] MISMATCH [%0d]: actual=0x%04x (%.6f) vs golden=0x%04x (%.6f), diff=%.6f, rel=%.2f%%",
                             i, collected_results[i], actual_val,
                             golden_results[i], golden_val, diff, rel_error*100);
                end
                mismatches++;
                pass = 1'b0;
            end
        end

        if (mismatches > 0) begin
            $display("[TB] Total mismatches: %0d / %0d", mismatches, expected_count);
        end else begin
            $display("[TB] All %0d results match!", expected_count);
        end
    endtask

    // =========================================================================
    // Run Single Test
    // =========================================================================
    task automatic run_test(test_config_t cfg);
        string golden_file;
        string left_file;
        string right_file;
        int expected_results;
        logic pass;

        $display("");
        $display("======================================================================");
        $display("  Test: %s (B=%0d, C=%0d, V=%0d)", cfg.name, cfg.B, cfg.C, cfg.V);
        $display("======================================================================");

        expected_results = cfg.B * cfg.C;
        $display("[TB] Expected results: %0d", expected_results);

        // Reset
        reset_dut();
        num_results_collected = 0;

        // Load golden file
        golden_file = {HEX_PATH, cfg.name, ".hex"};
        load_golden_file(golden_file);

        if (golden_count == 0) begin
            $display("[TB] SKIP: No golden file");
            return;
        end

        // Load memory model with left and right hex files
        // Memory model is pre-loaded in the initial block
        // We just need to issue FETCH commands

        // FETCH and DISPATCH RIGHT (weights)
        // Block 1: line address 528 (not byte address!)
        issue_fetch(
            .addr(32'd528),             // Line address (block 1 starts at line 528)
            .len(16'd528),
            .v_count(cfg.V),
            .fetch_right(1'b1),
            .cmd_id_in(8'd1)
        );

        issue_dispatch(
            .nv_cnt(cfg.C),             // Number of columns
            .v_count(cfg.V),            // V per column
            .tile_addr(16'd0),
            .col_start(8'd0),
            .disp_right(1'b1),
            .broadcast(1'b0),
            .cmd_id_in(8'd2)
        );

        // FETCH and DISPATCH LEFT (activations)
        // Block 0: line address 0
        issue_fetch(
            .addr(32'd0),               // Line address (block 0 starts at line 0)
            .len(16'd528),
            .v_count(cfg.V),
            .fetch_right(1'b0),
            .cmd_id_in(8'd3)
        );

        issue_dispatch(
            .nv_cnt(cfg.B),             // Number of batches
            .v_count(cfg.V),            // V per batch
            .tile_addr(16'd0),
            .col_start(8'd0),
            .disp_right(1'b0),
            .broadcast(1'b1),
            .cmd_id_in(8'd4)
        );

        // Issue MATMUL
        issue_matmul(
            .left_addr(16'd0),
            .right_addr(16'd0),
            .B(cfg.B),
            .C(cfg.C),
            .V(cfg.V),
            .cmd_id_in(8'd5)
        );

        // Collect results
        collect_results(cfg.B, cfg.C, expected_results);

        // Compare with golden
        compare_results(expected_results, pass);

        tests_run++;
        if (pass) begin
            tests_passed++;
            $display("[TB] TEST PASSED: %s", cfg.name);
        end else begin
            $display("[TB] TEST FAILED: %s", cfg.name);
        end
    endtask

    // =========================================================================
    // Main Test Sequence
    // =========================================================================
    initial begin
        $display("");
        $display("======================================================================");
        $display("  Engine Row Testbench");
        $display("  NUM_MLPS=%0d, NUM_COLS=%0d", NUM_MLPS, NUM_COLS);
        $display("======================================================================");

        tests_run = 0;
        tests_passed = 0;

        // Reset
        rstn = 0;
        mc_cmd_op = CMD_NOP;
        mc_cmd_id = 8'd0;
        cmd_payload_word1 = 32'd0;
        cmd_payload_word2 = 32'd0;
        cmd_payload_word3 = 32'd0;
        for (int i = 0; i < NUM_COLS; i++) result_rd_en[i] = 1'b0;
        
        repeat (50) @(posedge clk);
        rstn = 1;
        repeat (20) @(posedge clk);

        // Run tests
        foreach (test_suite[i]) begin
            run_test(test_suite[i]);
        end

        // Summary
        $display("");
        $display("======================================================================");
        $display("  TEST SUMMARY");
        $display("======================================================================");
        $display("  Tests Run:    %0d", tests_run);
        $display("  Tests Passed: %0d", tests_passed);
        $display("  Tests Failed: %0d", tests_run - tests_passed);
        
        if (tests_passed == tests_run && tests_run > 0) begin
            $display("  ALL TESTS PASSED!");
        end else begin
            $display("  *** TESTS FAILED ***");
        end
        $display("======================================================================");

        $finish;
    end

    // =========================================================================
    // Timeout Watchdog
    // =========================================================================
    initial begin
        #TIMEOUT_NS;
        $display("[TB] ERROR: Simulation timeout!");
        $finish;
    end

endmodule
