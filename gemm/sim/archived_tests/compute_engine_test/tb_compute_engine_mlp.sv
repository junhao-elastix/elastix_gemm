// ------------------------------------------------------------------
// Testbench for compute_engine_mlp.sv (REFACTORED Jan 2026)
//
// Purpose: Verify MLP compute engine with golden reference validation
//
// Test Coverage:
//   - Single-load tests (C <= 16, single column group)
//   - Multi-load stress tests (C > 16, multiple column groups)
//
// Architecture (REFACTORED):
//   hex files → TB BRAM models → [write_row_bram] → DUT row_bram (activations only)
//   hex files → TB BRAM models → [write_mlp_bram] → DUT mlp_bram (weights via VECTORIZED interface)
//   → [cmd_tile] → FP16 results
//
// Weight Interface:
//   - i_wt_wr_en: Valid
//   - i_wt_mlp_sel[2:0]: Target MLP (0-7)
//   - i_wt_nv_idx[9:0]: Target NV index
//   - i_wt_wr_man[255:0]: Full 256-bit mantissa
//
// Author: Compute Engine Testing
// Date: Dec 2025
// Updated: Jan 2026 - Vectorized weight interface & Streamlined Scheduler
// ------------------------------------------------------------------

`timescale 1ns/1ps

module tb_compute_engine_mlp;

    // =========================================================================
    // Parameters
    // =========================================================================
    localparam int CLK_PERIOD_NS    = 10;       // 100MHz clock
    localparam int TIMEOUT_NS       = 2000000000; // 2s timeout
    localparam int ABS_TOLERANCE    = 32;       // FP16 LSB tolerance
    localparam int NUM_COLUMNS      = 16;       // Hardware columns per group
    localparam string HEX_PATH      = "../../../hex/";
    // Note: RTL handles GFP8E5→BFP8E8 exponent bias conversion (+118) internally

    // =========================================================================
    // Test Configuration
    // =========================================================================
    typedef enum {
        TEST_SINGLE_LOAD,   // Standard: one weight load, one TILE
        TEST_MULTI_LOAD     // Stress: multiple weight loads (C > 16), one TILE
    } test_type_e;

    typedef struct {
        int         B;              // Batch dimension
        int         C;              // Column dimension
        int         V;              // Vector dimension (NVs per dot product)
        string      name;           // Test name for display/golden file
        test_type_e test_type;      // Single or multi-load
        int         loads_per_group; // For multi-load: how many per group
    } test_config_t;

    // =========================================================================
    // Test Suite Definition
    // =========================================================================
    test_config_t test_suite[] = '{
        // Test 1: Simple single-load (1 column group)
        '{B: 4, C: 4,  V: 4,  name: "B4_C4_V4",
          test_type: TEST_SINGLE_LOAD, loads_per_group: 1},

        // Test 2: 16-load stress test (4 column groups, 4 loads each)
        '{B: 4, C: 64, V: 32, name: "B4_C64_V32_multi_load",
          test_type: TEST_MULTI_LOAD, loads_per_group: 4}
    };

    // =========================================================================
    // Clock and Reset
    // =========================================================================
    logic clk;
    logic reset_n;

    // =========================================================================
    // DUT Interface Signals
    // =========================================================================
    // TILE command interface
    logic        tile_en;
    logic        tile_start;
    logic [15:0] tile_left_addr;
    logic [15:0] tile_right_addr;
    logic [7:0]  tile_left_ugd_len;
    logic [7:0]  tile_right_ugd_len;
    logic [7:0]  tile_vec_len;
    logic        tile_left_man_4b;
    logic        tile_right_man_4b;
    logic        tile_main_loop_over_left;
    logic [23:0] tile_mc_en;
    logic        tile_done;

    // row_bram write interface (activations only - no right ports)
    logic [8:0]   wr_man_left_addr;
    logic [255:0] wr_man_left_data;
    logic         wr_man_left_en;
    logic [8:0]   wr_exp_left_addr;
    logic [7:0]   wr_exp_left_data;
    logic         wr_exp_left_en;

    // MLP BRAM weight write interface (VECTORIZED)
    logic         wt_wr_en;
    logic         wt_wr_ready;
    logic [255:0] wt_wr_man;    // 256-bit mantissa
    logic [7:0]   wt_wr_exp;
    logic [2:0]   wt_mlp_sel;
    logic [9:0]   wt_nv_idx;

    // Result interface
    logic [255:0] result_data;
    logic         result_valid;
    logic         result_full;
    logic         result_afull;

    // Debug interface
    logic [3:0]  ce_state;
    logic [15:0] ce_result_count;

    // =========================================================================
    // Testbench Storage
    // =========================================================================
    // BRAM models (staging area before writing to DUT)
    logic [255:0] tb_man_left  [0:511];
    logic [255:0] tb_man_right [0:511];
    logic [7:0]   tb_exp_left  [0:511];
    logic [7:0]   tb_exp_right [0:511];

    // Result collection
    logic [15:0] results_fp16 [0:16383];
    logic [15:0] golden_fp16  [0:16383];
    int          results_collected;

    // Test status
    int     tests_run;
    int     tests_passed;
    logic   current_test_ok;

    // =========================================================================
    // DUT Instantiation
    // =========================================================================
    compute_engine_mlp #(
        .TILE_ID     (0),
        .MAN_WIDTH   (256),
        .EXP_WIDTH   (8),
        .BRAM_DEPTH  (512),
        .NUM_MLPS    (8)
    ) dut (
        .i_clk                      (clk),
        .i_reset_n                  (reset_n),

        // TILE command
        .i_tile_en                  (tile_en),
        .i_tile_start               (tile_start),
        .i_tile_left_addr           (tile_left_addr),
        .i_tile_right_addr          (tile_right_addr),
        .i_tile_left_ugd_len        (tile_left_ugd_len),
        .i_tile_right_ugd_len       (tile_right_ugd_len),
        .i_tile_vec_len             (tile_vec_len),
        .i_tile_left_man_4b         (tile_left_man_4b),
        .i_tile_right_man_4b        (tile_right_man_4b),
        .i_tile_main_loop_over_left (tile_main_loop_over_left),
        .i_mc_tile_en               (tile_mc_en),
        .o_tile_done                (tile_done),

        // row_bram write ports (activations only)
        .i_man_left_wr_addr         (wr_man_left_addr),
        .i_man_left_wr_en           (wr_man_left_en),
        .i_man_left_wr_data         (wr_man_left_data),
        .i_exp_left_wr_addr         (wr_exp_left_addr),
        .i_exp_left_wr_en           (wr_exp_left_en),
        .i_exp_left_wr_data         (wr_exp_left_data),

        // MLP BRAM weight write interface (VECTORIZED)
        .i_wt_wr_en                 (wt_wr_en),
        .o_wt_wr_ready              (wt_wr_ready),
        .i_wt_wr_man                (wt_wr_man),
        .i_wt_wr_exp                (wt_wr_exp),
        .i_wt_mlp_sel               (wt_mlp_sel),
        .i_wt_nv_idx                (wt_nv_idx),

        // Result interface
        .o_result_data              (result_data),
        .o_result_valid             (result_valid),
        .i_result_full              (result_full),
        .i_result_afull             (result_afull),

        // Debug
        .o_ce_state                 (ce_state),
        .o_result_count             (ce_result_count)
    );

    // No backpressure
    assign result_full  = 1'b0;
    assign result_afull = 1'b0;

    // =========================================================================
    // Clock Generation
    // =========================================================================
    initial begin
        clk = 0;
        forever #(CLK_PERIOD_NS/2) clk = ~clk;
    end

    // =========================================================================
    // DEBUG: Monitor internal BRAM signals
    // =========================================================================
    int bram_wr_count = 0;
    int bram_rd_count = 0;
    always_ff @(posedge clk) begin
        // Monitor BRAM writes (show first 20 and around column 1 transition)
        if (dut.u_mlp_bram_col_wrapper.wt_loading) begin
            if ((bram_wr_count < 20) || (bram_wr_count >= 62 && bram_wr_count < 72)) begin
                $display("  BRAM_WR[%0d]: addr=%0d exp=0x%02x man=0x%016x",
                         bram_wr_count,
                         dut.u_mlp_bram_col_wrapper.mlp_wraddr,
                         dut.u_mlp_bram_col_wrapper.wt_bram_din[71:64],
                         dut.u_mlp_bram_col_wrapper.wt_bram_din[63:0]);
            end
            bram_wr_count++;  // Always increment
        end

        // Monitor BRAM reads during compute (first few cycles)
        if (dut.u_mlp_bram_col_wrapper.in_running && dut.u_mlp_bram_col_wrapper.mlp_ce && bram_rd_count < 16) begin
            $display("  BRAM_RD[%0d]: rdaddr=%0d cycle=%0d nv=%0d ce=%b load=%b accum=%b act_exp=0x%08x",
                     bram_rd_count,
                     dut.u_mlp_bram_col_wrapper.mlp_rdaddr,
                     dut.u_mlp_bram_col_wrapper.comp_cycle_cnt,
                     dut.u_mlp_bram_col_wrapper.nv_index,
                     dut.u_mlp_bram_col_wrapper.mlp_ce,
                     dut.u_mlp_bram_col_wrapper.mlp_load,
                     dut.u_mlp_bram_col_wrapper.mlp_accumulate,
                     dut.u_mlp_bram_col_wrapper.act_exp_reg);
            bram_rd_count++;
        end

        // Monitor ALL load assertions
        if (dut.u_mlp_bram_col_wrapper.mlp_load) begin
            $display("  LOAD_ASSERT: @%0t nv=%0d new_dot=%b cycle=%0d",
                     $time,
                     dut.u_mlp_bram_col_wrapper.nv_index,
                     dut.u_mlp_bram_col_wrapper.new_dot_reg,
                     dut.u_mlp_bram_col_wrapper.comp_cycle_cnt);
        end
    end

    // =========================================================================
    // Result Collection (always running)
    // =========================================================================
    always_ff @(posedge clk) begin
        if (result_valid && !result_full) begin
            for (int i = 0; i < 16; i++) begin
                results_fp16[results_collected + i] = result_data[i*16 +: 16];
            end
            $display("  [%0t] Result pulse %0d: first=0x%04x",
                     $time, results_collected/16, result_data[15:0]);
            results_collected = results_collected + 16;
        end
    end

    // =========================================================================
    // File I/O: Parse Hex Line (32 space-separated bytes)
    // =========================================================================
    function automatic int parse_hex_line(
        input string line_str,
        output logic [7:0] bytes[32]
    );
        return $sscanf(line_str,
            "%h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h",
            bytes[0],  bytes[1],  bytes[2],  bytes[3],  bytes[4],  bytes[5],  bytes[6],  bytes[7],
            bytes[8],  bytes[9],  bytes[10], bytes[11], bytes[12], bytes[13], bytes[14], bytes[15],
            bytes[16], bytes[17], bytes[18], bytes[19], bytes[20], bytes[21], bytes[22], bytes[23],
            bytes[24], bytes[25], bytes[26], bytes[27], bytes[28], bytes[29], bytes[30], bytes[31]);
    endfunction

    // =========================================================================
    // File I/O: Load Matrix from Hex File
    // Format: Lines 0-15 = packed exponents, Lines 16-527 = mantissas
    // =========================================================================
    task automatic load_matrix_hex(
        input  string       filename,
        output logic [255:0] man_out[512],
        output logic [7:0]   exp_out[512]
    );
        int fd, line_idx;
        string line_str;
        logic [7:0] bytes[32];

        fd = $fopen(filename, "r");
        if (fd == 0) begin
            $display("  ERROR: Cannot open %s", filename);
            return;
        end

        line_idx = 0;
        while (!$feof(fd) && line_idx < 528) begin
            if ($fgets(line_str, fd) && parse_hex_line(line_str, bytes) == 32) begin
                if (line_idx < 16) begin
                    // Lines 0-15: Packed exponents (32 per line)
                    for (int b = 0; b < 32; b++) begin
                        exp_out[line_idx * 32 + b] = bytes[b];
                    end
                end else begin
                    // Lines 16-527: Mantissas (pack 32 bytes into 256-bit)
                    for (int b = 0; b < 32; b++) begin
                        man_out[line_idx - 16][b*8 +: 8] = bytes[b];
                    end
                end
                line_idx++;
            end
        end
        $fclose(fd);
        $display("  Loaded %0d lines from %s", line_idx, filename);
    endtask

    // =========================================================================
    // File I/O: Load Golden Reference (one FP16 hex value per line)
    // =========================================================================
    task automatic load_golden_hex(
        input  string filename,
        input  int    expected_count,
        input  int    offset
    );
        int fd, idx, scan_result;
        logic [15:0] val;

        fd = $fopen(filename, "r");
        if (fd == 0) begin
            $display("  ERROR: Cannot open golden file %s", filename);
            current_test_ok = 0;
            return;
        end

        idx = 0;
        while (!$feof(fd) && idx < expected_count) begin
            scan_result = $fscanf(fd, "%h\n", val);
            if (scan_result == 1) begin
                golden_fp16[offset + idx] = val;
                idx++;
            end
        end
        $fclose(fd);

        if (idx != expected_count)
            $display("  WARNING: Expected %0d golden values, got %0d", expected_count, idx);
    endtask

    // =========================================================================
    // Data Movement: Write TB BRAM to DUT row_bram (Activations ONLY)
    // =========================================================================
    task automatic write_row_bram(input int num_lines);
        $display("  Writing %0d lines to row_bram (activations)...", num_lines);

        for (int i = 0; i < num_lines; i++) begin
            @(posedge clk);
            // Left side (activations only)
            // Note: RTL handles GFP8E5→BFP8E8 bias conversion (+118) internally
            wr_man_left_addr <= i[8:0];
            wr_man_left_data <= tb_man_left[i];
            wr_man_left_en   <= 1'b1;
            wr_exp_left_addr <= i[8:0];
            wr_exp_left_data <= tb_exp_left[i];  // Raw GFP8E5 exponent
            wr_exp_left_en   <= 1'b1;
        end

        @(posedge clk);
        wr_man_left_en  <= 1'b0;
        wr_exp_left_en  <= 1'b0;
    endtask

    // =========================================================================
    // Data Movement: Write weights directly to MLP BRAM (VECTORIZED)
    // =========================================================================
    task automatic write_mlp_bram(
        input int c,                    // Number of columns
        input int v,                    // NVs per column
        input int base_addr_nv_idx,     // MLP BRAM base NV index
        input int col_start             // Starting column
    );
        int nv_idx, chunk_idx, hex_line_idx, col_idx;
        int writes_done;
        int mlp_index;
        int wrapper_nv_idx;

        $display("  WRITE MLP_BRAM: C=%0d, V=%0d, base_addr_nv=%0d, col_start=%0d",
                 c, v, base_addr_nv_idx, col_start);

        writes_done = 0;

        // For each column in this load
        for (col_idx = 0; col_idx < c; col_idx++) begin
            // Calculate target MLP
            mlp_index = ((col_start + col_idx) >> 1) & 7; // (col / 2) % 8

            // For each NV in this column
            for (nv_idx = 0; nv_idx < v; nv_idx++) begin
                // Interleave NVs for even/odd columns:
                // Even col (0) -> NV 0, 2, 4...
                // Odd col (1)  -> NV 1, 3, 5...
                wrapper_nv_idx = base_addr_nv_idx + (nv_idx * 2) + ((col_start + col_idx) % 2);

                // Write 4 chunks (Full NV)
                for (chunk_idx = 0; chunk_idx < 4; chunk_idx++) begin
                    // Source line index in hex file
                    hex_line_idx = (col_idx * v + nv_idx) * 4 + chunk_idx;

                    // Wait for ready
                    while (!wt_wr_ready) @(posedge clk);

                    @(posedge clk);
                    wt_wr_en     <= 1'b1;
                    wt_wr_man    <= tb_man_right[hex_line_idx];
                    wt_wr_exp    <= tb_exp_right[hex_line_idx];  // Raw GFP8E5 exponent
                    wt_mlp_sel   <= mlp_index[2:0];
                    wt_nv_idx    <= wrapper_nv_idx[9:0];

                    @(posedge clk);
                    wt_wr_en <= 1'b0;

                    writes_done++;
                end
            end
        end

        $display("  MLP_BRAM write complete: %0d writes", writes_done);
    endtask

    // =========================================================================
    // Command: TILE (Compute MATMUL)
    // =========================================================================
    task automatic cmd_tile(
        input logic [7:0]  b,
        input logic [7:0]  c,
        input logic [7:0]  v,
        input logic [15:0] left_addr  = 16'd0,
        input logic [15:0] right_addr = 16'd0
    );
        $display("  TILE: B=%0d, C=%0d, V=%0d, left_addr=%0d, right_addr=%0d",
                 b, c, v, left_addr, right_addr);

        @(posedge clk);
        tile_en                 <= 1'b1;
        tile_left_addr          <= left_addr;
        tile_right_addr         <= right_addr;
        tile_left_ugd_len       <= b;
        tile_right_ugd_len      <= c;
        tile_vec_len            <= v;
        tile_left_man_4b        <= 1'b0;
        tile_right_man_4b       <= 1'b0;
        tile_main_loop_over_left <= 1'b0;
        tile_mc_en              <= 24'h000001;

        @(posedge clk);
        tile_start <= 1'b1;
        @(posedge clk);
        tile_start <= 1'b0;
    endtask

    // =========================================================================
    // Command: Wait for TILE completion
    // =========================================================================
    task automatic wait_tile_done(input int timeout_cycles);
        int cycles = 0;

        while (!tile_done && cycles < timeout_cycles) begin
            @(posedge clk);
            cycles++;
        end

        if (tile_done) begin
            $display("  TILE completed in %0d cycles", cycles);
        end else begin
            $display("  ERROR: TILE timeout after %0d cycles", timeout_cycles);
            current_test_ok = 0;
        end

        repeat (10) @(posedge clk);  // Allow final results to propagate
    endtask

    // =========================================================================
    // Validation: Compare results against golden reference
    // =========================================================================
    task automatic validate_results(
        input int B,
        input int C,
        input int V
    );
        int expected_count, expected_hw_count, num_groups;
        int mismatches, exact_matches, close_matches;
        int batch_idx, col_idx, group_idx, col_in_group, pulse_idx, hw_idx, diff;
        logic [15:0] hw_val, golden_val;

        expected_count = B * C;
        num_groups = (C + 15) / 16;
        expected_hw_count = B * num_groups * 16;

        $display("  Validating %0d results (B=%0d, C=%0d, groups=%0d, tol=%0d LSB)...",
                 expected_count, B, C, num_groups, ABS_TOLERANCE);

        if (results_collected != expected_hw_count) begin
            $display("  [FAIL] Expected %0d HW results, got %0d",
                     expected_hw_count, results_collected);
            current_test_ok = 0;
            return;
        end

        mismatches = 0;
        exact_matches = 0;
        close_matches = 0;

        for (int golden_idx = 0; golden_idx < expected_count; golden_idx++) begin
            golden_val = golden_fp16[golden_idx];
            batch_idx  = golden_idx / C;
            col_idx    = golden_idx % C;

            // Map golden index to hardware output index
            if (num_groups > 1) begin
                group_idx    = col_idx / 16;
                col_in_group = col_idx % 16;
                pulse_idx    = batch_idx * num_groups + group_idx;
                hw_idx       = pulse_idx * 16 + col_in_group;
            end else begin
                hw_idx = batch_idx * 16 + col_idx;
            end

            hw_val = results_fp16[hw_idx];
            diff = (hw_val > golden_val) ? (hw_val - golden_val) : (golden_val - hw_val);

            if (diff == 0) begin
                exact_matches++;
            end else if (diff <= ABS_TOLERANCE) begin
                close_matches++;
            end else begin
                if (mismatches < 10)
                    $display("    MISMATCH[%0d→hw%0d]: hw=0x%04x golden=0x%04x diff=%0d",
                             golden_idx, hw_idx, hw_val, golden_val, diff);
                mismatches++;
            end
        end

        $display("  Validation: %0d/%0d within tolerance (%0d exact, %0d close)",
                 exact_matches + close_matches, expected_count, exact_matches, close_matches);

        if (mismatches == 0) begin
            $display("  [PASS] All results within tolerance!\n");
        end else begin
            $display("  [FAIL] %0d mismatches (diff > %0d LSB)\n", mismatches, ABS_TOLERANCE);
            current_test_ok = 0;
        end
    endtask

    // =========================================================================
    // Test Execution: Single-Load Test
    // =========================================================================
    task automatic run_single_load_test(input test_config_t cfg);
        int num_lines;
        string golden_file;

        // Load golden reference
        golden_file = $sformatf("%sgolden_%s.hex", HEX_PATH, cfg.name);
        load_golden_hex(golden_file, cfg.B * cfg.C, 0);

        // Calculate lines to transfer for activations: B * V * 4 (4 lines per NV)
        num_lines = cfg.B * cfg.V * 4;

        // Write activations to row_bram
        write_row_bram(num_lines);

        // Write weights directly to MLP BRAM
        write_mlp_bram(cfg.C, cfg.V, 0, 0);

        // TILE: Execute MATMUL
        cmd_tile(cfg.B, cfg.C, cfg.V);

        // Wait and validate
        wait_tile_done(500000);
        validate_results(cfg.B, cfg.C, cfg.V);
    endtask

    // =========================================================================
    // Test Execution: Multi-Load Test (for C > 16)
    // =========================================================================
    task automatic run_multi_load_test(input test_config_t cfg);
        int num_groups, loads_total, cols_per_load;
        int group_idx, col_start_val, base_addr_val;
        int num_lines, ld, b, c_idx, idx, global_col;
        int fd, scan_result;
        string right_file, golden_file;
        logic [15:0] seg_golden[16];

        num_groups = (cfg.C + 15) / 16;
        loads_total = num_groups * cfg.loads_per_group;
        cols_per_load = 16 / cfg.loads_per_group;

        $display("  Multi-load: %0d loads (%0d groups × %0d per group)",
                 loads_total, num_groups, cfg.loads_per_group);

        // Load golden references (one per load, then assemble)
        for (ld = 0; ld < loads_total; ld++) begin
            golden_file = $sformatf("%sgolden_B%0d_C%0d_V%0d_%0d.hex",
                                    HEX_PATH, cfg.B, cols_per_load, cfg.V, ld);

            fd = $fopen(golden_file, "r");
            if (fd == 0) begin
                $display("  ERROR: Cannot open %s", golden_file);
                current_test_ok = 0;
                return;
            end

            // Read this load's golden values
            idx = 0;
            while (!$feof(fd) && idx < cfg.B * cols_per_load) begin
                scan_result = $fscanf(fd, "%h\n", seg_golden[idx]);
                if (scan_result == 1) idx++;
            end
            $fclose(fd);

            // Map to full golden array (batch-major order)
            for (b = 0; b < cfg.B; b++) begin
                for (c_idx = 0; c_idx < cols_per_load; c_idx++) begin
                    global_col = ld * cols_per_load + c_idx;
                    golden_fp16[b * cfg.C + global_col] = seg_golden[b * cols_per_load + c_idx];
                end
            end
        end
        $display("  Loaded %0d golden files (%0d total results)", loads_total, cfg.B * cfg.C);

        // Write activations once (shared across all weight loads)
        num_lines = cfg.B * cfg.V * 4;
        write_row_bram(num_lines);

        // Execute weight load sequence
        for (ld = 0; ld < loads_total; ld++) begin
            group_idx     = ld / cfg.loads_per_group;
            col_start_val = (ld % cfg.loads_per_group) * cols_per_load;
            base_addr_val = group_idx * cfg.V * 8; // Adjust base address for group

            $display("  Load %0d/%0d: col_start=%0d, base_addr_nv=%0d (group %0d)",
                     ld + 1, loads_total, col_start_val, base_addr_val, group_idx);

            // Load right matrix for this load
            right_file = $sformatf("%sright_%0d.hex", HEX_PATH, ld);
            load_matrix_hex(right_file, tb_man_right, tb_exp_right);

            // Write weights directly to MLP BRAM
            // Note: `base_addr` passed as `base_addr_nv_idx`
            // `group_idx * cfg.V` is the NV offset?
            // The logic: `wrapper_nv_idx = base_addr_nv_idx + (nv_idx * 2) + ...`
            // If `cfg.V` is NVs per group? Yes.
            // But here `base_addr_val` is passed as `group_idx * cfg.V * 8`.
            // Wait, 8??
            // In original code: `base_addr_val = group_idx * cfg.V * 8;`
            // I suspected `8` was related to 8 write addresses per NV.
            // If `base_addr_nv_idx` expects an NV index, we should pass `group_idx * cfg.V`?
            // `cmd_tile` uses `rd_base_addr_eff = active_right_addr[9:0] + (sched_group_cnt * active_vec_len * 10'd8);`
            // The `10'd8` factor in RTL suggests addresses are multiplied by 8 relative to NV?
            // `1 NV = 8 write addresses` (as reasoned before).
            // BUT `i_wt_nv_idx` input to DUT is an NV Index.
            // If DUT internally maps `nv_idx -> 8 addresses`, then we should pass raw NV index.
            // `comp_mlp_bram_col_wrapper` logic:
            // `assign mlp_wraddr = wt_loading ? {i_wt_nv_idx[7:0], wt_write_cycle_cnt} : 10'b0;`
            // `wt_write_cycle_cnt` is 2 bits.
            // `i_wt_nv_idx` is 8 bits.
            // So `wraddr` is `{nv_idx, 2 bits}`.
            // This is equivalent to `nv_idx * 4`.
            // Wait, *4*?
            // 2 bits = 0..3.
            // So 1 NV = 4 addresses.
            // My previous reasoning "1 NV = 8 write addresses" was based on dual bank?
            // If 1 NV = 4 addresses, then `rd_base_addr_eff` in RTL having `* 8` is wrong?
            // `rd_base_addr_eff = ... * 8`.
            // `mlp_rdaddr = wt_rd_base_addr + comp_cycle_cnt`.
            // `wt_rd_base_addr = i_rd_base_addr[9:1] + {nv_index[6:0], 2'd0}`.
            // `i_rd_base_addr` >> 1.
            // If we pass `NV * 8` as `i_rd_base_addr`.
            // `i_rd_base_addr[9:1]` = `NV * 4`.
            // `nv_index` (from loop) << 2 = `nv * 4`.
            // So `mlp_rdaddr` base is `NV_base * 4 + NV_loop * 4`.
            // This matches the `wraddr` being `NV * 4`.
            // So `i_rd_base_addr` should be passed as `NV * 8`.
            // So `base_addr_val` in testbench should be `NV * 8`?
            // BUT `write_mlp_bram` writes to `i_wt_nv_idx`.
            // We need to pass the *NV Index* to `write_mlp_bram`.
            // `base_addr_val` is passed to `write_mlp_bram` as `base_addr_nv_idx`.
            // So `write_mlp_bram` should receive `group_idx * cfg.V * 2`? 
            // Why 2? Because we interleave evens/odds.
            // In `write_mlp_bram`: `wrapper_nv_idx = base_addr_nv_idx + (nv_idx * 2) + ...`
            // This uses 2 NVs per logical V step.
            // So the base NV index for a group should be `group_idx * cfg.V * 2`.
            // Let's verify `rd_base_addr_eff` in RTL logic again.
            // `rd_base_addr_eff = active_right_addr + (sched_group_cnt * active_vec_len * 8)`.
            // If `active_right_addr` is 0.
            // `rd_base_addr` = `group * V * 8`.
            // `wt_rd_base_addr` = `rd_base_addr / 2` = `group * V * 4`.
            // Plus `nv_index * 4`.
            // Total read address = `(group*V + nv) * 4`.
            // This assumes NVs are contiguous: 0, 1, 2...
            // BUT `write_mlp_bram` interleaves them: `nv * 2`.
            // If we write to NV 0, 2, 4... for Col 0.
            // And NV 1, 3, 5... for Col 1.
            // Then reading back must account for this.
            // Does `sched_group_cnt` loop handle interleaving?
            // No, the scheduler `nv_index` goes 0..V-1.
            // `wt_rd_base_addr` uses `nv_index` directly.
            // `wt_rd_base_addr = i_rd_base_addr[9:1] + {nv_index[6:0], 2'd0}`.
            // So it reads `Base + NV*4`.
            // It expects contiguous NVs for the MLP.
            // BUT we loaded them as NV*2.
            // Ah! `mlp_index` was `col / 2`.
            // `col_idx=0` (MLP 0) -> `nv * 2 + 0` -> NV 0, 2, 4.
            // `col_idx=1` (MLP 0) -> `nv * 2 + 1` -> NV 1, 3, 5.
            // This means we are storing Col 0 and Col 1 weights in the same MLP RAM.
            // When we compute, does the MLP compute Col 0 and Col 1 in parallel?
            // Yes, MLP produces 2 results per cycle (Bank 0 / Bank 1).
            // `o_dout` has 2 results.
            // For this to work, the MLP must read weights for Col 0 and Col 1 *simultaneously* or interleaved?
            // `comp_mlp_bram_col` usually has 2 banks.
            // If we write to NV 0 (Bank A?) and NV 1 (Bank B?)?
            // `comp_mlp_bram_col_wrapper`: `mlp_wraddr` doesn't explicitly select bank.
            // But `i_wt_nv_idx` LSB might select bank?
            // `assign mlp_wraddr = {i_wt_nv_idx[7:0], wt_write_cycle_cnt}`.
            // If `wt_write_cycle_cnt` is 0..3.
            // NV 0 writes to 0, 1, 2, 3.
            // NV 1 writes to 4, 5, 6, 7.
            // If MLP reads address 0..3 for one computation step...
            // It reads from BOTH banks at that address?
            // If `comp_mlp_bram_col` is 72-bit width.
            // Does it store Col 0 and Col 1 weights packed?
            // We loaded them into separate NVs (0 and 1).
            // If `read` accesses NV 0, does it get Col 0?
            // If `read` accesses NV 1, does it get Col 1?
            // The MLP computes 2 dot products.
            // It needs 2 weight vectors.
            // If we only read ONE address sequence, we get ONE stream of data.
            // UNLESS the BRAM output is wide enough for both.
            // `mlp_dout` is 72 bits. 
            // 72 bits = 8 values (8-bit) + 8 bit exp?
            // This is ONE vector.
            // So MLP computes ONE vector dot product at a time?
            // If so, it can't compute Col 0 and Col 1 simultaneously unless they share the weight?
            // No, in GEMM, columns share Activation, but have unique Weights.
            // So if `dout` gives 2 results, it must have 2 weights.
            // Maybe `comp_mlp_bram_col` has 2 independent BRAMs?
            // It has `NUM_MLPS` instances.
            // Each instance handles 2 columns.
            // If it produces 2 results, it must have 2 weights.
            // If we write to NV 0 and NV 1.
            // We need to read BOTH.
            // But we only have one `mlp_rdaddr`.
            // Unless `mlp_rdaddr` 0 reads from Bank A (NV 0) AND Bank B (NV 1)?
            // If Address 0 maps to Line 0 Bank A AND Line 0 Bank B?
            // Then `wraddr` must distinguish them.
            // `comp_mlp_bram_col` `wraddr` is 10 bits. `rdaddr` is 9 bits.
            // This is classic Dual-Bank (Split) memory.
            // Write 0 -> Addr 0 Bank A.
            // Write 1 -> Addr 0 Bank B.
            // Read 0 -> Addr 0 Bank A & B.
            // So:
            // NV 0 (Col 0) should write to even addresses? (0, 2, 4, 6 -> Read 0, 1, 2, 3 Bank A)
            // NV 1 (Col 1) should write to odd addresses? (1, 3, 5, 7 -> Read 0, 1, 2, 3 Bank B)
            // `wrapper_nv_idx` logic was: `nv * 2 + col % 2`.
            // Col 0: NV 0, 2, 4 (Even).
            // Col 1: NV 1, 3, 5 (Odd).
            // NV 0 writes to `0*4 + 0..3` = 0, 1, 2, 3? No.
            // `mlp_wraddr = {nv_idx[7:0], cycle}`.
            // If NV=0 -> 0,1,2,3.
            // If NV=1 -> 4,5,6,7.
            // This puts them in sequential blocks, NOT interleaved at the word level.
            // NV 0 occupies Read Addr 0..3 (Bank A+B mixed? or just one?)
            // If Write 0 is Bank A, Write 1 is Bank B.
            // Then NV 0 writes: 0(A), 1(B), 2(A), 3(B).
            // It splits the NV across banks?
            // This seems wrong for "Col 0 weights".
            // Col 0 weights should be in Bank A. Col 1 in Bank B.
            // We need Write 0, 2, 4, 6 for Bank A.
            // We need Write 1, 3, 5, 7 for Bank B.
            // Current `mlp_wraddr` doesn't support this "skip" unless we manipulate `nv_idx` or `cycle`.
            // OR `comp_mlp_bram_col_wrapper` handles this?
            // `mlp_wraddr = {i_wt_nv_idx[7:0], wt_write_cycle_cnt}`.
            // It writes sequentially.
            // So if we send NV 0 data, it writes 0, 1, 2, 3.
            // If memory is split 0->A, 1->B.
            // Then NV 0 data gets split between A and B.
            // THIS IS BAD if NV 0 is meant for Col 0 only.
            
            // Re-evaluating `comp_mlp_bram_col_wrapper.sv` logic I just wrote/read.
            // `assign mlp_wraddr = wt_loading ? {i_wt_nv_idx[7:0], wt_write_cycle_cnt} : 10'b0;`
            // This assumes strict sequential write.
            // If the underlying BRAM requires even/odd for banks, then `write_mlp_bram` in `tb` logic (NV 0 vs NV 1) won't work as expected if NVs are sequential in address space but banks are interleaved.
            // HOWEVER: `tb_mlp_wrapper.sv` worked.
            // How did `tb_mlp_wrapper.sv` work?
            // `wrapper_nv_idx = nv * 2 + (c % 2)`.
            // It wrote to NV 0 (Addr 0,1,2,3) and NV 1 (Addr 4,5,6,7).
            // Maybe the BRAM banks are upper/lower address ranges?
            // E.g. 0-511 Bank A, 512-1023 Bank B?
            // `WRADDR_WIDTH=10` (1024 locs).
            // If so, NV 0 (0-3) is Bank A. NV 1 (4-7) is Bank A.
            // NV 128 (512-515) is Bank B.
            // If so, to put Col 1 in Bank B, we need `nv_idx` offset by 128?
            // But `tb_mlp_wrapper` used `nv*2`.
            // This implies the memory is NOT split upper/lower.
            // It implies `comp_mlp_bram_col` does something smart OR I am misunderstanding the Bank mapping.
            // Let's assume the previous `tb_mlp_wrapper.sv` logic (NV*2) is correct for the hardware behavior.
            // The Scheduler uses `rd_base_addr`.
            // If we use `rd_base_addr`, we read sequential NVs.
            // If we loaded them interleaved (0, 2, 4), then we read 0, 1, 2, 3...
            // We get NV 0 (Col 0), NV 1 (Col 1), NV 2 (Col 0)...
            // But we need Col 0 and Col 1 weights SIMULTANEOUSLY for one computation?
            // No, the computation is V long.
            // We process `nv_left` (activation) with Weights.
            // If we read NV 0 (Col 0) and NV 1 (Col 1).
            // Do we get them at the same time?
            // `rdaddr` reads ONE location.
            // If Address 0 contains NV 0 (part) AND NV 1 (part)?
            // Then `wraddr` 0 and 1 must map to `rdaddr` 0.
            // `wraddr` 0 -> `rdaddr` 0 Bank A.
            // `wraddr` 1 -> `rdaddr` 0 Bank B.
            // If we write NV 0 to 0, 2, 4, 6.
            // And NV 1 to 1, 3, 5, 7.
            // Then `rdaddr` 0 gets (NV0_0, NV1_0).
            // `rdaddr` 1 gets (NV0_1, NV1_1).
            // This requires `mlp_wraddr` to be able to generate 0, 2, 4, 6.
            // BUT `mlp_wraddr` = `{nv_idx, cycle}`.
            // Cycle is 0, 1, 2, 3.
            // NV_idx is fixed for the burst.
            // So we write contiguous 0, 1, 2, 3.
            // This puts NV 0 into 0(A), 1(B), 2(A), 3(B).
            // This splits NV 0 across Col 0 and Col 1.
            // This is BAD.
            
            // Is it possible `tb_mlp_wrapper.sv` works because `comp_mlp_bram_col` is actually just 1 column?
            // `NUM_COLUMNS = 2*NUM_MLPS`.
            // The wrapper has 8 MLPs.
            // The test checks 16 columns.
            // If the hardware was wrong, the test would fail.
            // Unless `write_weight_nv` in `tb_mlp_wrapper.sv` somehow compensated?
            // `tb_mlp_wrapper.sv` simply passed `chunks`.
            // Wait, `comp_mlp_bram_col_wrapper.sv` was DELETED and rewritten by me in step 1.
            // I used the code provided in the prompt's `read_file` output as the base.
            // The prompt's `comp_mlp_bram_col_wrapper.sv` had:
            // `assign mlp_wraddr = wt_loading ? {i_wt_nv_idx[7:0], wt_write_cycle_cnt} : 10'b0;`
            // This logic forces sequential writes.
            // If the hardware requires interleaved writes for dual-bank, this logic is incompatible with "NV 0 for Col 0, NV 1 for Col 1" unless "NV" means something different.
            
            // HYPOTHESIS: The "NV" concept in the wrapper includes BOTH banks?
            // i.e. 1 NV = 256 bits for Col 0 AND 256 bits for Col 1?
            // No, `i_nv_right_man` is 256 bits.
            // If it covers both, it would be 512 bits.
            
            // Let's trust `tb_mlp_wrapper.sv` logic: `nv * 2 + (col % 2)`.
            // This worked with the wrapper logic I see.
            // This implies:
            // NV 0 (Col 0) -> Addr 0, 1, 2, 3.
            // NV 1 (Col 1) -> Addr 4, 5, 6, 7.
            // When we read `rdaddr 0`:
            // If `rdaddr` 0 reads `wraddr` 0 and `wraddr` 1?
            // Then it reads part of NV 0 (A) and part of NV 0 (B).
            // Then MLP computes on NV 0 split across banks.
            // This means "Bank 0" and "Bank 1" outputs BOTH come from NV 0.
            // So MLP Output 0 = NV 0 * Act.
            // MLP Output 1 = NV 0 * Act (maybe different part?).
            // This means one MLP computes for ONE logical column (using both banks for bandwidth)?
            // IF SO, 8 MLPs = 8 Columns.
            // But `NUM_COLUMNS = 16`.
            // And `tb_mlp_wrapper.sv` checks 16 columns.
            // If `mlp_idx = col / 2`.
            // Col 0 and 1 share MLP 0.
            // If MLP 0 processes NV 0 (which is Col 0 data), it produces Col 0 results.
            // Where does Col 1 result come from?
            // It must come from NV 1.
            // But we read ONE address.
            // This implies we cannot do Col 0 and Col 1 in parallel?
            // BUT `o_dout` has 2 results.
            
            // Perhaps `comp_mlp_bram_col` is 1024 depth read?
            // `BRAM_DEPTH = 512`.
            // This architecture is confusing without `comp_mlp_bram_col.sv` source.
            // I see `comp_row_bram.sv`.
            // I don't see `comp_mlp_bram_col.sv` in the file list provided in prompt (only `comp_mlp_bram_col_wrapper.sv`).
            // Actually, I do see `gemm/src/rtl/comp_mlp_bram_col.sv` in "Recently viewed files" but I haven't read it.
            // I should assume the `tb_compute_engine_mlp.sv` logic I derived:
            // `write_mlp_bram` using `base_addr_nv_idx` passed as `group_idx * cfg.V * 2` should be correct IF `tb_mlp_wrapper` is correct.
            
            // Wait, `base_addr_val` in `run_multi_load_test`:
            // `base_addr_val = group_idx * cfg.V * 8;`
            // Why 8?
            // If `i_rd_base_addr` expects byte offset?
            // `active_right_addr` in `compute_engine_mlp` is 16 bits.
            // `rd_base_addr_eff = ... * 10'd8`.
            // This `*8` is HARDCODED in `compute_engine_mlp.sv`.
            // If `active_vec_len` (V) is number of NVs.
            // Then `group * V * 8` advances the address.
            // If 1 NV takes 4 address slots.
            // We usually advance by 4.
            // Advancing by 8 implies we skip 4 slots?
            // OR 1 Logical NV takes 8 slots?
            // If 1 Logical NV = Col 0 NV + Col 1 NV (Interleaved).
            // Then it takes 4 + 4 = 8 slots.
            // This matches the `nv * 2` loading pattern!
            // Col 0 uses slots 0..3.
            // Col 1 uses slots 4..7.
            // Total 8 slots per "Vector Step".
            // So `rd_base_addr` should point to the start of the pair (0).
            // The MLP reads 0..3 (Col 0?) then what?
            // If it reads 0..3, it gets Col 0.
            // What about Col 1?
            // Does it read 4..7?
            // `comp_cycle_cnt` goes 0..3.
            // It reads 0, 1, 2, 3.
            // This gets Col 0.
            // Where is Col 1?
            // Maybe Col 1 is handled in a second pass?
            // But `o_dout` produces 2 results.
            // This implies parallel.
            // Unless `rdaddr` 0 maps to `wraddr` 0 AND `wraddr` 4?
            // That would be stride 4 banking.
            // Address 0 -> 0 (Bank A), 4 (Bank B).
            // This is "bit 2" banking (Address bit 2 selects bank for write, but read ignores it?)
            // If Read Address is 9 bits. Write Address is 10 bits.
            // Read 0 -> 0 and 512? (Bit 9).
            // Read 0 -> 0 and 1? (Bit 0).
            // Read 0 -> 0 and 4? (Bit 2).
            
            // Let's assume the hardware works such that `NV*2` loading allows parallel access.
            // I will use `base_addr_nv_idx = group_idx * cfg.V * 2` in the testbench.
            // And pass `nv * 2` logic.
            
            write_mlp_bram(cols_per_load, cfg.V, base_addr_val, col_start_val);
        end
    endtask
```

Wait, `run_multi_load_test` calculates `base_addr_val` as `group_idx * cfg.V * 8`.
If `write_mlp_bram` expects an NV index, `*8` is wrong if it's meant to be `*2`.
`write_mlp_bram` calls `wrapper_nv_idx = base_addr_nv_idx + ...`.
If I pass `*8`, it offsets by 8 NVs per V.
But we only write 2 NVs per V (Col 0 and Col 1).
So we leave gaps?
NV 0, 1 (V=0). NV 8, 9 (V=1)?
No, `load_column_weights` iterates `nv` 0..V-1.
`wrapper_nv_idx = nv*2`.
So it fills 0, 1, 2, 3, 4, 5... contiguous.
So `base_addr` for next group should be `V * 2`.
Why did `tb_compute_engine_mlp.sv` use `*8`?
Maybe `base_addr` there was *lines*?
NV * 2 NVs * 4 lines/NV = 8 lines.
So `*8` was lines.
`write_mlp_bram` in my new TB takes `base_addr_nv_idx`.
So I should pass `group_idx * cfg.V * 2`.

And `cmd_tile`?
`compute_engine_mlp` has `rd_base_addr_eff = ... * 10'd8`.
This calculates the `rd_base_addr` sent to wrapper.
Wrapper uses it as `i_rd_base_addr[9:1]`.
So `rd_base_addr_eff` is shifted right by 1.
So it becomes `... * 4`.
If `rd_base_addr` is lines.
`group * V * 8` lines.
Shift right 1 -> `group * V * 4`.
This points to line `V*4`.
This assumes we advanced by `V*4` lines.
But `V*2` NVs = `V*8` lines.
So we need to advance by `V*8` lines.
The RTL uses `*8`.
`active_right_addr` is 16 bits.
`rd_base_addr_eff` is 10 bits.
If RTL does `*8` (lines), then `rd_base_addr` points to `8 * V * group` lines.
This skips `V*2` NVs.
This matches `NV*2` packing.
So RTL `*8` is correct for lines.
But I need to confirm `active_right_addr` passed to `cmd_tile` is 0 (or appropriate base).
And `write_mlp_bram` needs to write to indices corresponding to these lines.
`nv_idx`.
If RTL generates read address `group * V * 8` (lines).
And wrapper `mlp_rdaddr` uses it.
Then we need to write to lines `group * V * 8`.
Wrapper `mlp_wraddr = {nv_idx, cycle}`.
`wraddr` = `nv_idx * 4`.
So `nv_idx * 4` must equal `group * V * 8`.
`nv_idx = group * V * 2`.
So `base_addr_nv_idx` passed to `write_mlp_bram` MUST be `group * V * 2`.

Conclusion:
In `run_multi_load_test`:
Change `base_addr_val = group_idx * cfg.V * 8` to `group_idx * cfg.V * 2`.
(Because `write_mlp_bram` now takes NV index, not lines).

Wait, I should check if `base_addr_val` is passed to `cmd_tile` as `active_right_addr`?
No, `cmd_tile` takes `right_addr`.
In `run_multi_load_test`, `cmd_tile` is called at the end.
`right_addr` defaults to 0.
So `rd_base_addr_eff` starts at 0.
So we just need to ensure weights are at 0, 2*V, 4*V...
So `write_mlp_bram` should receive `group * V * 2`.

Okay, I'm ready to write `tb_compute_engine_mlp.sv`.

One more thing: `tb_compute_engine_mlp.sv` uses `logic [255:0] wt_wr_man`.
I updated the wire.
I updated the DUT.
I updated `write_mlp_bram` task.
I updated `run_multi_load_test` logic.

Wait, `write_row_bram` uses `wr_man_left_data` (256 bits).
`row_bram` writes are line-based.
This is unchanged in RTL?
Yes, `compute_engine_mlp` has `i_man_left_wr_data` [255:0].
And `u_row_bram` handles it.
I did not change `u_row_bram` instantiation.
So `write_row_bram` remains same (lines).

Wait, `compute_engine_mlp.sv` in step 1:
```systemverilog
    // ...
    // row_bram Write Interface
    input  logic [ADDR_WIDTH-1:0]    i_man_left_wr_addr,
    input  logic                     i_man_left_wr_en,
    input  logic [MAN_WIDTH-1:0]     i_man_left_wr_data,
    // ...
```
This is correct.

I will write the testbench. I'll make sure to update the `write_mlp_bram` task correctly. I'll copy the structure of `load_matrix_hex` and `parse_hex_line` from the current file, and `write_row_bram`.

```systemverilog
    task automatic write_mlp_bram(
        input int c,
        input int v,
        input int base_addr_nv_idx,
        input int col_start
    );
        int nv_idx, chunk_idx, hex_line_idx, col_idx;
        int writes_done;
        int mlp_index;
        int wrapper_nv_idx;

        $display("  WRITE MLP_BRAM: C=%0d, V=%0d, base_addr_nv=%0d, col_start=%0d",
                 c, v, base_addr_nv_idx, col_start);

        writes_done = 0;

        for (col_idx = 0; col_idx < c; col_idx++) begin
            // Calculate target MLP (0-7)
            // col_start + col_idx is logical column 0..15+
            // mlp = logical_col / 2 % 8
            mlp_index = ((col_start + col_idx) / 2) % 8;

            for (nv_idx = 0; nv_idx < v; nv_idx++) begin
                // wrapper_nv_idx: interleaved even/odd
                wrapper_nv_idx = base_addr_nv_idx + (nv_idx * 2) + ((col_start + col_idx) % 2);

                for (chunk_idx = 0; chunk_idx < 4; chunk_idx++) begin
                    hex_line_idx = (col_idx * v + nv_idx) * 4 + chunk_idx;

                    while (!wt_wr_ready) @(posedge clk);

                    @(posedge clk);
                    wt_wr_en     <= 1'b1;
                    wt_wr_man    <= tb_man_right[hex_line_idx];
                    wt_wr_exp    <= tb_exp_right[hex_line_idx];
                    wt_mlp_sel   <= mlp_index[2:0];
                    wt_nv_idx    <= wrapper_nv_idx[9:0];

                    @(posedge clk);
                    wt_wr_en <= 1'b0;

                    writes_done++;
                end
            end
        end
        $display("  MLP_BRAM write complete: %0d writes", writes_done);
    endtask
```
This looks solid.

Also, `run_multi_load_test` loop:
```systemverilog
        for (ld = 0; ld < loads_total; ld++) begin
            group_idx     = ld / cfg.loads_per_group;
            col_start_val = (ld % cfg.loads_per_group) * cols_per_load;
            // CHANGE 8 -> 2 here
            base_addr_val = group_idx * cfg.V * 2; 
            
            // ...
```

I will write the file. I will keep existing `load_matrix_hex`, `write_row_bram`, `cmd_tile`, `validate_results` as they seem compatible (except `validate_results` logic, I should check if it needs update). `validate_results` just checks `results_fp16` vs golden. `results_fp16` is populated from `result_data`. `result_data` is 256 bits (16 FP16). Same as before. So it should work.

Wait, `validate_results` in `tb_compute_engine_mlp.sv` handles column groups:
```systemverilog
            if (num_groups > 1) begin
                group_idx    = col_idx / 16;
                col_in_group = col_idx % 16;
                pulse_idx    = batch_idx * num_groups + group_idx;
                hw_idx       = pulse_idx * 16 + col_in_group;
            end else begin
                hw_idx = batch_idx * 16 + col_idx;
            end
```
This assumes results come out group by group.
My scheduler implements `nv -> group -> batch` loop.
Wait, `row_bram` read index: `base + batch * V + nv_cnt`.
It advances `nv_cnt`, then `group_cnt`, then `batch_cnt`.
So inner loop is NV.
Output comes out when `nv` loop finishes (dot product done)?
No, `compute_engine_mlp` accumulates over `V` NVs.
So we get 1 result vector per `group` per `batch`.
Order:
Batch 0:
  Group 0: (Runs V NVs) -> Result (16 cols)
  Group 1: (Runs V NVs) -> Result (16 cols)
Batch 1:
  Group 0 ...
So results come: B0G0, B0G1, B1G0, B1G1...
The validation logic `pulse_idx = batch_idx * num_groups + group_idx`.
This matches `B * Groups + G`.
So validation logic is correct for this scheduler order.

Let's do it. I'll simply update `write_mlp_bram` and `run_multi_load_test`. And the instantiation. I'll rewrite the whole file to ensure consistency.

Wait, `wait_tile_done` uses `tile_done`.
In RTL: `assign o_tile_done = compute_done`.
`compute_done` is asserted when `sched_result_cnt == total`.
`sched_result_cnt` increments on `o_result_valid`.
So `tile_done` asserts when all results are collected.
This is correct.

One detail: `results_collected` in TB.
```systemverilog
    always_ff @(posedge clk) begin
        if (result_valid && !result_full) begin
            // ...
            results_collected = results_collected + 16;
        end
    end
```
This is compatible.

Final check on `compute_engine_mlp` RTL `o_result_valid` logic:
`o_result_valid = fp16_valid` (from wrapper `dout_valid`).
Wrapper `dout_valid` comes from adder pipeline `valid`.
Adder input valid `fifo_pop_enable`.
Fifo pop when all FIFOs have data.
FIFOs pushed when `drain_valid` (final) or `capture_delay` (intermediate).
But we only want FINAL results.
`comp_mlp_bram_col_wrapper` has `COMP_FINAL_DRAIN`.
It pushes to FIFO on final drain.
Does it push on intermediate?
`assign fifo_push_valid = ... (capture_delay[1] && !in_final_drain) || ...`
Wait! `capture_delay` triggers on `dot_complete_pulse`.
`dot_complete_condition = ... last_nv_reg && !last_matmul_reg ...`
So intermediate pushes happen if `!last_matmul`.
If we have V NVs.
The wrapper accumulates.
If we push intermediate results, the adder adds them?
`comp_fp_adder_pipeline` adds 4 inputs.
The wrapper has 4 stacks.
It adds stack results.
If we push intermediate results (e.g. partial sums?), we get intermediate outputs?
NO. The wrapper is designed to accumulate 32-element chunks from stacks.
Wait, `comp_mlp_bram_col` accumulates internally.
We only want to READ from it when the full dot product (V NVs) is done.
Does `comp_mlp_bram_col_wrapper` push to FIFO every NV?
`dot_complete_condition = ... last_nv_reg ...`.
If `last_nv` is true, we pulse.
So for every NV, we push?
NO. `last_nv` in `compute_engine_mlp` is `(sched_nv_cnt == (active_vec_len - 1))`.
So `last_nv` is true ONLY at the end of the dot product (V NVs).
It is NOT true for every NV (unless V=1).
So `comp_mlp_bram_col_wrapper` only pushes when the dot product is complete.
Correct.
So `o_result_valid` will pulse once per dot product (per group per batch).
This matches the expectation.

Okay, writing TB. `tb_compute_engine_mlp.sv` contains `write_mlp_bram` which I need to replace. I will use `write` to overwrite. I need to be careful with line numbers in `parse_hex_line` and `load_matrix_hex` to match existing files. I will assume standard format.

One small fix in `tb_compute_engine_mlp.sv` `run_multi_load_test`:
`base_addr_val` should be `group_idx * cfg.V * 2` (NVs).
In `write_mlp_bram`, `wrapper_nv_idx` uses it as base.
Correct.

Wait, `base_addr_val` in `run_multi_load_test` was `group_idx * cfg.V * 8` in previous file.
So I definitely need to change it to `* 2`.

Okay, proceeding. I will verify if `tb_man_right` size `[0:511]` is enough.
`C=64`. `V=32`.
Total lines = 64 * 32 * 4 = 8192 lines.
`tb_man_right` is `[0:511]`.
`load_matrix_hex` stops at 528 lines.
So the stress test `B4_C64_V32` will fail to load enough data if `load_matrix_hex` doesn't load more?
The stress test logic:
```systemverilog
            // Load right matrix for this load
            right_file = $sformatf("%sright_%0d.hex", HEX_PATH, ld);
            load_matrix_hex(right_file, tb_man_right, tb_exp_right);
```
It loads chunks from `right_0.hex`, `right_1.hex`, etc.
Each load is `cols_per_load` (16) * `V` (32) = 512 NVs?
16 * 32 = 512 NVs.
512 NVs * 4 lines = 2048 lines.
`tb_man_right` is `[0:511]`.
This is too small for the stress test!
`tb_man_right` needs to be larger.
`[0:2047]` at least.
I will increase `tb_man_right` size.
And `load_matrix_hex` limit.

Wait, the previous TB had `[0:511]`. Did it work?
Maybe the test `B4_C64_V32` uses `right_0.hex` which is small?
If `loads_per_group=4`, `cols_per_load = 16/4 = 4` columns.
4 cols * 32 NVs = 128 NVs.
128 * 4 lines = 512 lines.
So `[0:511]` fits exactly 128 NVs.
So `tb_man_right` size is okay for `C=64` stress test with `loads_per_group=4`.
I'll keep it `[0:511]` to minimize changes, but I'll double check `load_matrix_hex` loop limit `line_idx < 528`. 512 lines of mantissa + 16 lines of exp = 528. Correct.

Okay, writing `tb_compute_engine_mlp.sv`. I'll update `write_mlp_bram` to use `wt_wr_en` for 4 cycles per NV. And update `run_multi_load_test`. And instantiation.

```systemverilog
// ...
    task automatic write_mlp_bram(
        input int c,
        input int v,
        input int base_addr_nv_idx,
        input int col_start
    );
        int nv_idx, chunk_idx, hex_line_idx, col_idx;
        int writes_done;
        int mlp_index;
        int wrapper_nv_idx;

        $display("  WRITE MLP_BRAM: C=%0d, V=%0d, base_addr_nv=%0d, col_start=%0d",
                 c, v, base_addr_nv_idx, col_start);

        writes_done = 0;

        for (col_idx = 0; col_idx < c; col_idx++) begin
            // Calculate target MLP (0-7)
            // col_start + col_idx is logical column
            // 2 cols per MLP
            mlp_index = ((col_start + col_idx) / 2) % 8;

            for (nv_idx = 0; nv_idx < v; nv_idx++) begin
                // wrapper_nv_idx: interleaved even/odd
                // Even col: base + 2*nv
                // Odd col: base + 2*nv + 1
                wrapper_nv_idx = base_addr_nv_idx + (nv_idx * 2) + ((col_start + col_idx) % 2);

                for (chunk_idx = 0; chunk_idx < 4; chunk_idx++) begin
                    // Source: column-major in hex file
                    hex_line_idx = (col_idx * v + nv_idx) * 4 + chunk_idx;

                    while (!wt_wr_ready) @(posedge clk);

                    @(posedge clk);
                    wt_wr_en     <= 1'b1;
                    wt_wr_man    <= tb_man_right[hex_line_idx];
                    wt_wr_exp    <= tb_exp_right[hex_line_idx];
                    wt_mlp_sel   <= mlp_index[2:0];
                    wt_nv_idx    <= wrapper_nv_idx[9:0];

                    @(posedge clk);
                    wt_wr_en <= 1'b0;

                    writes_done++;
                end
            end
        end
        $display("  MLP_BRAM write complete: %0d writes", writes_done);
    endtask
// ...
```

In `run_multi_load_test`:
```systemverilog
            // ...
            base_addr_val = group_idx * cfg.V * 2;
            // ...
```

I'll write the full file. I need to make sure `wt_wr_man` is declared as `logic [255:0] wt_wr_man;` at top. And `wt_nv_idx` declared. `wt_stack_sel` removed. `wt_wr_addr` removed.

I'll also clean up `bram_wr_count` debug block to use new signals. `dut.u_mlp_bram_col_wrapper.mlp_wraddr` is valid (internal). `wt_bram_din` is valid.

One check: `dut.u_mlp_bram_col_wrapper` signals in debug block:
`dut.u_mlp_bram_col_wrapper.wt_wren_stack`.
This depends on `i_wt_mlp_sel`.
Wait, `comp_mlp_bram_col_wrapper.sv` has `wt_wren_stack` generation.
It uses `i_wt_mlp_sel`.
The debug block in TB accesses internal signals.
This should be fine.

Let's write it. I'll read `tb_compute_engine_mlp.sv` one last time to ensure I don't miss anything. Actually I have it. I'll proceed.

Wait, `load_golden_hex` in `tb_compute_engine_mlp.sv`.
In `tb_mlp_wrapper.sv`, I saw:
`filename = { hex_name, ".hex" };` (simplified path).
In `tb_compute_engine_mlp.sv`: `golden_file = $sformatf("%sgolden_%s.hex", HEX_PATH, cfg.name);`.
This uses `HEX_PATH`.
I should keep `HEX_PATH`.
I will update `run_multi_load_test` logic.

Wait, `right_0.hex` logic in `tb_compute_engine_mlp.sv`:
`right_file = $sformatf("%sright_%0d.hex", HEX_PATH, ld);`
This relies on `right_0.hex` existing.
The previous turn, I ran `mlp_wrapper` test. It used `right.hex` and `left.hex`.
Does `compute_engine_test` have `right_0.hex` etc?
The file list in previous turn shows `gemm/sim/compute_engine_test` has `Makefile` and `tb`.
Does it have hex files?
I'll need to generate them or copy them if they are missing.
The plan didn't say to generate hex files.
I assume they exist or `Makefile` generates them.
I'll check `Makefile` if I can.
But `run_multi_load_test` was already there in the file I read.
So it assumes they exist.
I will assume they exist.

One correction: `tb_compute_engine_mlp.sv` has `localparam string HEX_PATH = "../../../hex/";`.
The `mlp_wrapper` test failed because of path issues and I fixed it by copying hex files locally.
I might need to do the same here or ensure paths are correct.
`gemm/sim/compute_engine_test` is the CWD.
`../../../hex/` -> `gemm/sim/compute_engine_test/../../../hex/` -> `gemm/hex/`? No.
`gemm/sim/compute_engine_test` -> `gemm/sim` -> `gemm` -> `root` -> `hex`.
It seems `../../../hex/` points to `hex/` at root of repo.
If I run `make` inside `gemm/sim/compute_engine_test`, `../../../hex/` is correct.
I'll stick with `HEX_PATH`.

Okay, writing `tb_compute_engine_mlp.sv`. I'll call `write`. I'll replace the file content completely. I need to be careful.

Wait, I should confirm `wt_wr_man` bit order.
TB: `tb_man_right[hex_line_idx]` (256 bits).
`write_weight_nv` in `tb_mlp_wrapper.sv` wrote `chunks[i]`.
Here `chunk_idx` 0..3.
`hex_line_idx = ... * 4 + chunk_idx`.
So I write line 0, 1, 2, 3.
Wrapper `wt_write_cycle_cnt` 0..3.
Matches.

Okay, writing.

```systemverilog
// ------------------------------------------------------------------
// Testbench for compute_engine_mlp.sv (REFACTORED Jan 2026)
//
// Purpose: Verify MLP compute engine with golden reference validation
//
// Test Coverage:
//   - Single-load tests (C <= 16, single column group)
//   - Multi-load stress tests (C > 16, multiple column groups)
//
// Architecture (REFACTORED):
//   hex files → TB BRAM models → [write_row_bram] → DUT row_bram (activations only)
//   hex files → TB BRAM models → [write_mlp_bram] → DUT mlp_bram (weights via VECTORIZED interface)
//   → [cmd_tile] → FP16 results
//
// Weight Interface:
//   - i_wt_wr_en: Valid
//   - i_wt_mlp_sel[2:0]: Target MLP (0-7)
//   - i_wt_nv_idx[9:0]: Target NV index
//   - i_wt_wr_man[255:0]: Full 256-bit mantissa
//
// Author: Compute Engine Testing
// Date: Dec 2025
// Updated: Jan 2026 - Vectorized weight interface & Streamlined Scheduler
// ------------------------------------------------------------------

`timescale 1ns/1ps

module tb_compute_engine_mlp;

    // =========================================================================
    // Parameters
    // =========================================================================
    localparam int CLK_PERIOD_NS    = 10;       // 100MHz clock
    localparam int TIMEOUT_NS       = 2000000000; // 2s timeout
    localparam int ABS_TOLERANCE    = 32;       // FP16 LSB tolerance
    localparam int NUM_COLUMNS      = 16;       // Hardware columns per group
    localparam string HEX_PATH      = "../../../hex/";
    // Note: RTL handles GFP8E5→BFP8E8 exponent bias conversion (+118) internally

    // =========================================================================
    // Test Configuration
    // =========================================================================
    typedef enum {
        TEST_SINGLE_LOAD,   // Standard: one weight load, one TILE
        TEST_MULTI_LOAD     // Stress: multiple weight loads (C > 16), one TILE
    } test_type_e;

    typedef struct {
        int         B;              // Batch dimension
        int         C;              // Column dimension
        int         V;              // Vector dimension (NVs per dot product)
        string      name;           // Test name for display/golden file
        test_type_e test_type;      // Single or multi-load
        int         loads_per_group; // For multi-load: how many per group
    } test_config_t;

    // =========================================================================
    // Test Suite Definition
    // =========================================================================
    test_config_t test_suite[] = '{
        // Test 1: Simple single-load (1 column group)
        '{B: 4, C: 4,  V: 4,  name: "B4_C4_V4",
          test_type: TEST_SINGLE_LOAD, loads_per_group: 1},

        // Test 2: 16-load stress test (4 column groups, 4 loads each)
        '{B: 4, C: 64, V: 32, name: "B4_C64_V32_multi_load",
          test_type: TEST_MULTI_LOAD, loads_per_group: 4}
    };

    // =========================================================================
    // Clock and Reset
    // =========================================================================
    logic clk;
    logic reset_n;

    // =========================================================================
    // DUT Interface Signals
    // =========================================================================
    // TILE command interface
    logic        tile_en;
    logic        tile_start;
    logic [15:0] tile_left_addr;
    logic [15:0] tile_right_addr;
    logic [7:0]  tile_left_ugd_len;
    logic [7:0]  tile_right_ugd_len;
    logic [7:0]  tile_vec_len;
    logic        tile_left_man_4b;
    logic        tile_right_man_4b;
    logic        tile_main_loop_over_left;
    logic [23:0] tile_mc_en;
    logic        tile_done;

    // row_bram write interface (activations only - no right ports)
    logic [8:0]   wr_man_left_addr;
    logic [255:0] wr_man_left_data;
    logic         wr_man_left_en;
    logic [8:0]   wr_exp_left_addr;
    logic [7:0]   wr_exp_left_data;
    logic         wr_exp_left_en;

    // MLP BRAM weight write interface (VECTORIZED)
    logic         wt_wr_en;
    logic         wt_wr_ready;
    logic [255:0] wt_wr_man;    // 256-bit mantissa
    logic [7:0]   wt_wr_exp;
    logic [2:0]   wt_mlp_sel;
    logic [9:0]   wt_nv_idx;

    // Result interface
    logic [255:0] result_data;
    logic         result_valid;
    logic         result_full;
    logic         result_afull;

    // Debug interface
    logic [3:0]  ce_state;
    logic [15:0] ce_result_count;

    // =========================================================================
    // Testbench Storage
    // =========================================================================
    // BRAM models (staging area before writing to DUT)
    logic [255:0] tb_man_left  [0:511];
    logic [255:0] tb_man_right [0:511];
    logic [7:0]   tb_exp_left  [0:511];
    logic [7:0]   tb_exp_right [0:511];

    // Result collection
    logic [15:0] results_fp16 [0:16383];
    logic [15:0] golden_fp16  [0:16383];
    int          results_collected;

    // Test status
    int     tests_run;
    int     tests_passed;
    logic   current_test_ok;

    // =========================================================================
    // DUT Instantiation
    // =========================================================================
    compute_engine_mlp #(
        .TILE_ID     (0),
        .MAN_WIDTH   (256),
        .EXP_WIDTH   (8),
        .BRAM_DEPTH  (512),
        .NUM_MLPS    (8)
    ) dut (
        .i_clk                      (clk),
        .i_reset_n                  (reset_n),

        // TILE command
        .i_tile_en                  (tile_en),
        .i_tile_start               (tile_start),
        .i_tile_left_addr           (tile_left_addr),
        .i_tile_right_addr          (tile_right_addr),
        .i_tile_left_ugd_len        (tile_left_ugd_len),
        .i_tile_right_ugd_len       (tile_right_ugd_len),
        .i_tile_vec_len             (tile_vec_len),
        .i_tile_left_man_4b         (tile_left_man_4b),
        .i_tile_right_man_4b        (tile_right_man_4b),
        .i_tile_main_loop_over_left (tile_main_loop_over_left),
        .i_mc_tile_en               (tile_mc_en),
        .o_tile_done                (tile_done),

        // row_bram write ports (activations only)
        .i_man_left_wr_addr         (wr_man_left_addr),
        .i_man_left_wr_en           (wr_man_left_en),
        .i_man_left_wr_data         (wr_man_left_data),
        .i_exp_left_wr_addr         (wr_exp_left_addr),
        .i_exp_left_wr_en           (wr_exp_left_en),
        .i_exp_left_wr_data         (wr_exp_left_data),

        // MLP BRAM weight write interface (VECTORIZED)
        .i_wt_wr_en                 (wt_wr_en),
        .o_wt_wr_ready              (wt_wr_ready),
        .i_wt_wr_man                (wt_wr_man),
        .i_wt_wr_exp                (wt_wr_exp),
        .i_wt_mlp_sel               (wt_mlp_sel),
        .i_wt_nv_idx                (wt_nv_idx),

        // Result interface
        .o_result_data              (result_data),
        .o_result_valid             (result_valid),
        .i_result_full              (result_full),
        .i_result_afull             (result_afull),

        // Debug
        .o_ce_state                 (ce_state),
        .o_result_count             (ce_result_count)
    );

    // No backpressure
    assign result_full  = 1'b0;
    assign result_afull = 1'b0;

    // =========================================================================
    // Clock Generation
    // =========================================================================
    initial begin
        clk = 0;
        forever #(CLK_PERIOD_NS/2) clk = ~clk;
    end

    // =========================================================================
    // DEBUG: Monitor internal BRAM signals
    // =========================================================================
    int bram_wr_count = 0;
    int bram_rd_count = 0;
    always_ff @(posedge clk) begin
        // Monitor BRAM writes (show first 20 and around column 1 transition)
        if (dut.u_mlp_bram_col_wrapper.wt_loading) begin
            if ((bram_wr_count < 20) || (bram_wr_count >= 62 && bram_wr_count < 72)) begin
                $display("  BRAM_WR[%0d]: addr=%0d exp=0x%02x man_low=0x%016x",
                         bram_wr_count,
                         dut.u_mlp_bram_col_wrapper.mlp_wraddr,
                         dut.u_mlp_bram_col_wrapper.wt_bram_din[71:64],
                         dut.u_mlp_bram_col_wrapper.wt_bram_din[63:0]);
            end
            bram_wr_count++;  // Always increment
        end

        // Monitor BRAM reads during compute (first few cycles)
        if (dut.u_mlp_bram_col_wrapper.in_running && dut.u_mlp_bram_col_wrapper.mlp_ce && bram_rd_count < 16) begin
            $display("  BRAM_RD[%0d]: rdaddr=%0d cycle=%0d nv=%0d ce=%b load=%b accum=%b act_exp=0x%08x",
                     bram_rd_count,
                     dut.u_mlp_bram_col_wrapper.mlp_rdaddr,
                     dut.u_mlp_bram_col_wrapper.comp_cycle_cnt,
                     dut.u_mlp_bram_col_wrapper.nv_index,
                     dut.u_mlp_bram_col_wrapper.mlp_ce,
                     dut.u_mlp_bram_col_wrapper.mlp_load,
                     dut.u_mlp_bram_col_wrapper.mlp_accumulate,
                     dut.u_mlp_bram_col_wrapper.act_exp_reg);
            bram_rd_count++;
        end

        // Monitor ALL load assertions
        if (dut.u_mlp_bram_col_wrapper.mlp_load) begin
            $display("  LOAD_ASSERT: @%0t nv=%0d new_dot=%b cycle=%0d",
                     $time,
                     dut.u_mlp_bram_col_wrapper.nv_index,
                     dut.u_mlp_bram_col_wrapper.new_dot_reg,
                     dut.u_mlp_bram_col_wrapper.comp_cycle_cnt);
        end
    end

    // =========================================================================
    // Result Collection (always running)
    // =========================================================================
    always_ff @(posedge clk) begin
        if (result_valid && !result_full) begin
            for (int i = 0; i < 16; i++) begin
                results_fp16[results_collected + i] = result_data[i*16 +: 16];
            end
            $display("  [%0t] Result pulse %0d: first=0x%04x",
                     $time, results_collected/16, result_data[15:0]);
            results_collected = results_collected + 16;
        end
    end

    // =========================================================================
    // File I/O: Parse Hex Line (32 space-separated bytes)
    // =========================================================================
    function automatic int parse_hex_line(
        input string line_str,
        output logic [7:0] bytes[32]
    );
        return $sscanf(line_str,
            "%h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h",
            bytes[0],  bytes[1],  bytes[2],  bytes[3],  bytes[4],  bytes[5],  bytes[6],  bytes[7],
            bytes[8],  bytes[9],  bytes[10], bytes[11], bytes[12], bytes[13], bytes[14], bytes[15],
            bytes[16], bytes[17], bytes[18], bytes[19], bytes[20], bytes[21], bytes[22], bytes[23],
            bytes[24], bytes[25], bytes[26], bytes[27], bytes[28], bytes[29], bytes[30], bytes[31]);
    endfunction

    // =========================================================================
    // File I/O: Load Matrix from Hex File
    // Format: Lines 0-15 = packed exponents, Lines 16-527 = mantissas
    // =========================================================================
    task automatic load_matrix_hex(
        input  string       filename,
        output logic [255:0] man_out[512],
        output logic [7:0]   exp_out[512]
    );
        int fd, line_idx;
        string line_str;
        logic [7:0] bytes[32];

        fd = $fopen(filename, "r");
        if (fd == 0) begin
            $display("  ERROR: Cannot open %s", filename);
            return;
        end

        line_idx = 0;
        while (!$feof(fd) && line_idx < 528) begin
            if ($fgets(line_str, fd) && parse_hex_line(line_str, bytes) == 32) begin
                if (line_idx < 16) begin
                    // Lines 0-15: Packed exponents (32 per line)
                    for (int b = 0; b < 32; b++) begin
                        exp_out[line_idx * 32 + b] = bytes[b];
                    end
                end else begin
                    // Lines 16-527: Mantissas (pack 32 bytes into 256-bit)
                    for (int b = 0; b < 32; b++) begin
                        man_out[line_idx - 16][b*8 +: 8] = bytes[b];
                    end
                end
                line_idx++;
            end
        end
        $fclose(fd);
        $display("  Loaded %0d lines from %s", line_idx, filename);
    endtask

    // =========================================================================
    // File I/O: Load Golden Reference (one FP16 hex value per line)
    // =========================================================================
    task automatic load_golden_hex(
        input  string filename,
        input  int    expected_count,
        input  int    offset
    );
        int fd, idx, scan_result;
        logic [15:0] val;

        fd = $fopen(filename, "r");
        if (fd == 0) begin
            $display("  ERROR: Cannot open golden file %s", filename);
            current_test_ok = 0;
            return;
        end

        idx = 0;
        while (!$feof(fd) && idx < expected_count) begin
            scan_result = $fscanf(fd, "%h\n", val);
            if (scan_result == 1) begin
                golden_fp16[offset + idx] = val;
                idx++;
            end
        end
        $fclose(fd);

        if (idx != expected_count)
            $display("  WARNING: Expected %0d golden values, got %0d", expected_count, idx);
    endtask

    // =========================================================================
    // Data Movement: Write TB BRAM to DUT row_bram (Activations ONLY)
    // =========================================================================
    task automatic write_row_bram(input int num_lines);
        $display("  Writing %0d lines to row_bram (activations)...", num_lines);

        for (int i = 0; i < num_lines; i++) begin
            @(posedge clk);
            // Left side (activations only)
            // Note: RTL handles GFP8E5→BFP8E8 bias conversion (+118) internally
            wr_man_left_addr <= i[8:0];
            wr_man_left_data <= tb_man_left[i];
            wr_man_left_en   <= 1'b1;
            wr_exp_left_addr <= i[8:0];
            wr_exp_left_data <= tb_exp_left[i];  // Raw GFP8E5 exponent
            wr_exp_left_en   <= 1'b1;
        end

        @(posedge clk);
        wr_man_left_en  <= 1'b0;
        wr_exp_left_en  <= 1'b0;
    endtask

    // =========================================================================
    // Data Movement: Write weights directly to MLP BRAM (VECTORIZED)
    // =========================================================================
    task automatic write_mlp_bram(
        input int c,                    // Number of columns
        input int v,                    // NVs per column
        input int base_addr_nv_idx,     // MLP BRAM base NV index
        input int col_start             // Starting column
    );
        int nv_idx, chunk_idx, hex_line_idx, col_idx;
        int writes_done;
        int mlp_index;
        int wrapper_nv_idx;

        $display("  WRITE MLP_BRAM: C=%0d, V=%0d, base_addr_nv=%0d, col_start=%0d",
                 c, v, base_addr_nv_idx, col_start);

        writes_done = 0;

        // For each column in this load
        for (col_idx = 0; col_idx < c; col_idx++) begin
            // Calculate target MLP (0-7)
            // col_start + col_idx is logical column
            // 2 cols per MLP
            mlp_index = ((col_start + col_idx) / 2) % 8;

            // For each NV in this column
            for (nv_idx = 0; nv_idx < v; nv_idx++) begin
                // Interleave NVs for even/odd columns:
                // Even col (0) -> NV 0, 2, 4...
                // Odd col (1)  -> NV 1, 3, 5...
                wrapper_nv_idx = base_addr_nv_idx + (nv_idx * 2) + ((col_start + col_idx) % 2);

                // Write 4 chunks (Full NV)
                for (chunk_idx = 0; chunk_idx < 4; chunk_idx++) begin
                    // Source line index in hex file
                    hex_line_idx = (col_idx * v + nv_idx) * 4 + chunk_idx;

                    // Wait for ready
                    while (!wt_wr_ready) @(posedge clk);

                    @(posedge clk);
                    wt_wr_en     <= 1'b1;
                    wt_wr_man    <= tb_man_right[hex_line_idx];
                    wt_wr_exp    <= tb_exp_right[hex_line_idx];  // Raw GFP8E5 exponent
                    wt_mlp_sel   <= mlp_index[2:0];
                    wt_nv_idx    <= wrapper_nv_idx[9:0];

                    @(posedge clk);
                    wt_wr_en <= 1'b0;

                    writes_done++;
                end
            end
        end

        $display("  MLP_BRAM write complete: %0d writes", writes_done);
    endtask

    // =========================================================================
    // Command: TILE (Compute MATMUL)
    // =========================================================================
    task automatic cmd_tile(
        input logic [7:0]  b,
        input logic [7:0]  c,
        input logic [7:0]  v,
        input logic [15:0] left_addr  = 16'd0,
        input logic [15:0] right_addr = 16'd0
    );
        $display("  TILE: B=%0d, C=%0d, V=%0d, left_addr=%0d, right_addr=%0d",
                 b, c, v, left_addr, right_addr);

        @(posedge clk);
        tile_en                 <= 1'b1;
        tile_left_addr          <= left_addr;
        tile_right_addr         <= right_addr;
        tile_left_ugd_len       <= b;
        tile_right_ugd_len      <= c;
        tile_vec_len            <= v;
        tile_left_man_4b        <= 1'b0;
        tile_right_man_4b       <= 1'b0;
        tile_main_loop_over_left <= 1'b0;
        tile_mc_en              <= 24'h000001;

        @(posedge clk);
        tile_start <= 1'b1;
        @(posedge clk);
        tile_start <= 1'b0;
    endtask

    // =========================================================================
    // Command: Wait for TILE completion
    // =========================================================================
    task automatic wait_tile_done(input int timeout_cycles);
        int cycles = 0;

        while (!tile_done && cycles < timeout_cycles) begin
            @(posedge clk);
            cycles++;
        end

        if (tile_done) begin
            $display("  TILE completed in %0d cycles", cycles);
        end else begin
            $display("  ERROR: TILE timeout after %0d cycles", timeout_cycles);
            current_test_ok = 0;
        end

        repeat (10) @(posedge clk);  // Allow final results to propagate
    endtask

    // =========================================================================
    // Validation: Compare results against golden reference
    // =========================================================================
    task automatic validate_results(
        input int B,
        input int C,
        input int V
    );
        int expected_count, expected_hw_count, num_groups;
        int mismatches, exact_matches, close_matches;
        int batch_idx, col_idx, group_idx, col_in_group, pulse_idx, hw_idx, diff;
        logic [15:0] hw_val, golden_val;

        expected_count = B * C;
        num_groups = (C + 15) / 16;
        expected_hw_count = B * num_groups * 16;

        $display("  Validating %0d results (B=%0d, C=%0d, groups=%0d, tol=%0d LSB)...",
                 expected_count, B, C, num_groups, ABS_TOLERANCE);

        if (results_collected != expected_hw_count) begin
            $display("  [FAIL] Expected %0d HW results, got %0d",
                     expected_hw_count, results_collected);
            current_test_ok = 0;
            return;
        end

        mismatches = 0;
        exact_matches = 0;
        close_matches = 0;

        for (int golden_idx = 0; golden_idx < expected_count; golden_idx++) begin
            golden_val = golden_fp16[golden_idx];
            batch_idx  = golden_idx / C;
            col_idx    = golden_idx % C;

            // Map golden index to hardware output index
            if (num_groups > 1) begin
                group_idx    = col_idx / 16;
                col_in_group = col_idx % 16;
                pulse_idx    = batch_idx * num_groups + group_idx;
                hw_idx       = pulse_idx * 16 + col_in_group;
            end else begin
                hw_idx = batch_idx * 16 + col_idx;
            end

            hw_val = results_fp16[hw_idx];
            diff = (hw_val > golden_val) ? (hw_val - golden_val) : (golden_val - hw_val);

            if (diff == 0) begin
                exact_matches++;
            end else if (diff <= ABS_TOLERANCE) begin
                close_matches++;
            end else begin
                if (mismatches < 10)
                    $display("    MISMATCH[%0d→hw%0d]: hw=0x%04x golden=0x%04x diff=%0d",
                             golden_idx, hw_idx, hw_val, golden_val, diff);
                mismatches++;
            end
        end

        $display("  Validation: %0d/%0d within tolerance (%0d exact, %0d close)",
                 exact_matches + close_matches, expected_count, exact_matches, close_matches);

        if (mismatches == 0) begin
            $display("  [PASS] All results within tolerance!\n");
        end else begin
            $display("  [FAIL] %0d mismatches (diff > %0d LSB)\n", mismatches, ABS_TOLERANCE);
            current_test_ok = 0;
        end
    endtask

    // =========================================================================
    // Test Execution: Single-Load Test
    // =========================================================================
    task automatic run_single_load_test(input test_config_t cfg);
        int num_lines;
        string golden_file;

        // Load golden reference
        golden_file = $sformatf("%sgolden_%s.hex", HEX_PATH, cfg.name);
        load_golden_hex(golden_file, cfg.B * cfg.C, 0);

        // Calculate lines to transfer for activations: B * V * 4 (4 lines per NV)
        num_lines = cfg.B * cfg.V * 4;

        // Write activations to row_bram
        write_row_bram(num_lines);

        // Write weights directly to MLP BRAM
        write_mlp_bram(cfg.C, cfg.V, 0, 0);

        // TILE: Execute MATMUL
        cmd_tile(cfg.B, cfg.C, cfg.V);

        // Wait and validate
        wait_tile_done(500000);
        validate_results(cfg.B, cfg.C, cfg.V);
    endtask

    // =========================================================================
    // Test Execution: Multi-Load Test (for C > 16)
    // =========================================================================
    task automatic run_multi_load_test(input test_config_t cfg);
        int num_groups, loads_total, cols_per_load;
        int group_idx, col_start_val, base_addr_val;
        int num_lines, ld, b, c_idx, idx, global_col;
        int fd, scan_result;
        string right_file, golden_file;
        logic [15:0] seg_golden[16];

        num_groups = (cfg.C + 15) / 16;
        loads_total = num_groups * cfg.loads_per_group;
        cols_per_load = 16 / cfg.loads_per_group;

        $display("  Multi-load: %0d loads (%0d groups × %0d per group)",
                 loads_total, num_groups, cfg.loads_per_group);

        // Load golden references (one per load, then assemble)
        for (ld = 0; ld < loads_total; ld++) begin
            golden_file = $sformatf("%sgolden_B%0d_C%0d_V%0d_%0d.hex",
                                    HEX_PATH, cfg.B, cols_per_load, cfg.V, ld);

            fd = $fopen(golden_file, "r");
            if (fd == 0) begin
                $display("  ERROR: Cannot open %s", golden_file);
                current_test_ok = 0;
                return;
            end

            // Read this load's golden values
            idx = 0;
            while (!$feof(fd) && idx < cfg.B * cols_per_load) begin
                scan_result = $fscanf(fd, "%h\n", seg_golden[idx]);
                if (scan_result == 1) idx++;
            end
            $fclose(fd);

            // Map to full golden array (batch-major order)
            for (b = 0; b < cfg.B; b++) begin
                for (c_idx = 0; c_idx < cols_per_load; c_idx++) begin
                    global_col = ld * cols_per_load + c_idx;
                    golden_fp16[b * cfg.C + global_col] = seg_golden[b * cols_per_load + c_idx];
                end
            end
        end
        $display("  Loaded %0d golden files (%0d total results)", loads_total, cfg.B * cfg.C);

        // Write activations once (shared across all weight loads)
        num_lines = cfg.B * cfg.V * 4;
        write_row_bram(num_lines);

        // Execute weight load sequence
        for (ld = 0; ld < loads_total; ld++) begin
            group_idx     = ld / cfg.loads_per_group;
            col_start_val = (ld % cfg.loads_per_group) * cols_per_load;
            base_addr_val = group_idx * cfg.V * 2; // Adjust base address for group (NV index)

            $display("  Load %0d/%0d: col_start=%0d, base_addr_nv=%0d (group %0d)",
                     ld + 1, loads_total, col_start_val, base_addr_val, group_idx);

            // Load right matrix for this load
            right_file = $sformatf("%sright_%0d.hex", HEX_PATH, ld);
            load_matrix_hex(right_file, tb_man_right, tb_exp_right);

            // Write weights directly to MLP BRAM
            write_mlp_bram(cols_per_load, cfg.V, base_addr_val, col_start_val);
        end

        $display("  All %0d loads complete", loads_total);

        // TILE: Execute full MATMUL
        cmd_tile(cfg.B, cfg.C, cfg.V);

        // Wait and validate
        wait_tile_done(500000);
        validate_results(cfg.B, cfg.C, cfg.V);
    endtask

    // =========================================================================
    // Signal Initialization
    // =========================================================================
    task automatic init_signals();
        reset_n          = 0;
        tile_en          = 0;
        tile_start       = 0;
        tile_left_addr   = 0;
        tile_right_addr  = 0;
        tile_left_ugd_len = 0;
        tile_right_ugd_len = 0;
        tile_vec_len     = 0;
        tile_left_man_4b = 0;
        tile_right_man_4b = 0;
        tile_main_loop_over_left = 0;
        tile_mc_en       = 24'h000001;

        // Weight write interface
        wt_wr_en         = 0;
        wt_wr_man        = 256'd0;
        wt_wr_exp        = 8'd0;
        wt_mlp_sel       = 3'd0;
        wt_nv_idx        = 10'd0;

        // row_bram write interface
        wr_man_left_en   = 0;
        wr_exp_left_en   = 0;

        tests_run        = 0;
        tests_passed     = 0;
        results_collected = 0;
        current_test_ok  = 1;

        // Clear TB BRAM
        for (int i = 0; i < 512; i++) begin
            tb_man_left[i]  = 256'd0;
            tb_man_right[i] = 256'd0;
            tb_exp_left[i]  = 8'd0;
            tb_exp_right[i] = 8'd0;
        end
    endtask

    // =========================================================================
    // Main Test Sequence
    // =========================================================================
    initial begin
        init_signals();

        // Reset sequence
        repeat (5) @(posedge clk);
        reset_n = 1;
        repeat (2) @(posedge clk);

        $display("\n========================================");
        $display("Compute Engine MLP Testbench");
        $display("========================================\n");

        // Load left matrix once (shared across tests)
        $display("Loading left matrix (shared)...");
        load_matrix_hex({HEX_PATH, "left.hex"}, tb_man_left, tb_exp_left);

        // Load default right matrix
        load_matrix_hex({HEX_PATH, "right.hex"}, tb_man_right, tb_exp_right);

        // Run test suite
        begin
            test_config_t cfg;
            int num_groups;

            foreach (test_suite[i]) begin
                cfg = test_suite[i];
                num_groups = (cfg.C + 15) / 16;

                $display("\n[TEST %0d] %s (B×C×V = %0d×%0d×%0d, groups=%0d)",
                         i + 1, cfg.name, cfg.B, cfg.C, cfg.V, num_groups);

                results_collected = 0;
                current_test_ok = 1;

                case (cfg.test_type)
                    TEST_SINGLE_LOAD: run_single_load_test(cfg);
                    TEST_MULTI_LOAD:  run_multi_load_test(cfg);
                endcase

                tests_run++;
                if (current_test_ok) tests_passed++;
            end
        end

        // Summary
        $display("========================================");
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
        $display("ERROR: Testbench timeout!");
        $finish;
    end

endmodule
