// ------------------------------------------------------------------
// Testbench for Compute Engine -> Result Collector -> Result to DMA
//
// Purpose: Test the complete compute-to-output data path:
//   - 16 compute_engine_2d instances (one per row)
//   - result_collector_2d (reduces 16 rows -> 1 FP16 per column)
//   - result_to_dma (circular buffer to BRAM)
//   - Mock result BRAM captures final output
//
// Auto-Drain Behavior:
//   - CEs compute and produce results into oFIFOs
//   - Result collector auto-drains when all rows have data for a column
//   - result_to_dma always accepts data (o_ready=1)
//   - No ce_results_ready signal needed for full output lines
//
// Test Configuration: B=1, C=64, V=2 (4 column groups)
//
// Author: Junhao Pan
// Date: Jan 29, 2026
// ------------------------------------------------------------------

`timescale 1ns/1ps

module tb_comp_readout;

    // =========================================================================
    // Parameters
    // =========================================================================
    localparam int CLK_PERIOD_NS    = 2;             // 500MHz
    localparam int TIMEOUT_NS       = 10000000;      // 10ms timeout

    // CE parameters
    localparam int NUM_ROWS         = 16;
    localparam int NUM_MLPS         = 2;
    localparam int NUM_COLS         = 2 * NUM_MLPS;  // 16 columns per CE
    localparam int MAN_WIDTH        = 256;
    localparam int EXP_WIDTH        = 8;
    localparam int BRAM_DEPTH       = 512;
    localparam int ADDR_WIDTH       = $clog2(BRAM_DEPTH);
    localparam int MLP_SEL_WIDTH    = $clog2(NUM_MLPS);
    localparam int RESULT_FIFO_DEPTH = 1024;

    // Result collector/DMA parameters
    localparam int OUTPUT_FIFO_DEPTH = 1024;
    localparam int RESULT_ADDR_WIDTH = 9;
    localparam int RESULT_BUFFER_DEPTH = 512;

    // Memory file constants
    localparam int EXP_LINES        = 16;
    localparam int MAN_LINE_START   = 16;
    localparam int TOTAL_LINES      = 528;

    // Hex file path
    localparam string HEX_PATH = "/home/dev/Dev/elastix_gemm/hex/B1_C64_V2/";

    // =========================================================================
    // Clock and Reset
    // =========================================================================
    logic clk = 1'b0;
    logic rstn;

    always #(CLK_PERIOD_NS/2.0) clk = ~clk;

    // =========================================================================
    // Opcode Constants
    // =========================================================================
    localparam logic [7:0] OPC_NOP    = 8'h00;
    localparam logic [7:0] OPC_MATMUL = 8'hF2;

    // =========================================================================
    // Command Interface (shared across all CEs)
    // =========================================================================
    logic [7:0]   mc_cmd_op;
    logic [7:0]   mc_cmd_id;
    logic [31:0]  cmd_payload_word1;
    logic [31:0]  cmd_payload_word2;
    logic [31:0]  cmd_payload_word3;

    // =========================================================================
    // Per-Row CE Signals
    // =========================================================================
    // Activation write interface (per row)
    logic [ADDR_WIDTH-1:0]  man_left_wr_addr  [NUM_ROWS-1:0];
    logic                   man_left_wr_en    [NUM_ROWS-1:0];
    logic [MAN_WIDTH-1:0]   man_left_wr_data  [NUM_ROWS-1:0];
    logic [ADDR_WIDTH-1:0]  exp_left_wr_addr  [NUM_ROWS-1:0];
    logic                   exp_left_wr_en    [NUM_ROWS-1:0];
    logic [EXP_WIDTH-1:0]   exp_left_wr_data  [NUM_ROWS-1:0];

    // Weight write interface (per row)
    logic                   wt_wr_en    [NUM_ROWS-1:0];
    logic                   wt_wr_ready [NUM_ROWS-1:0];
    logic [255:0]           wt_wr_man   [NUM_ROWS-1:0];
    logic [EXP_WIDTH-1:0]   wt_wr_exp   [NUM_ROWS-1:0];
    logic [MLP_SEL_WIDTH-1:0] wt_mlp_sel [NUM_ROWS-1:0];
    logic [9:0]             wt_nv_idx   [NUM_ROWS-1:0];

    // CE status (per row)
    logic                   ce_ack_matmul [NUM_ROWS-1:0];
    logic [7:0]             ce_id         [NUM_ROWS-1:0];
    logic                   ce_matmul_done[NUM_ROWS-1:0];
    logic [3:0]             ce_state      [NUM_ROWS-1:0];
    logic                   ce_results_ready [NUM_ROWS-1:0];

    // =========================================================================
    // CE oFIFO -> Result Collector Interface
    // =========================================================================
    logic [15:0] ce_result_data  [NUM_ROWS-1:0][NUM_COLS-1:0];
    logic        ce_result_empty [NUM_ROWS-1:0][NUM_COLS-1:0];
    logic        rc_result_rd_en [NUM_ROWS-1:0][NUM_COLS-1:0];

    // =========================================================================
    // Result Collector -> result_to_dma Interface
    // =========================================================================
    logic        rc_output_valid;
    logic        rc_output_last;
    logic [15:0] rc_output_keep;
    logic [255:0] rc_output_data;
    logic        r2d_ready;

    // Result collector status
    logic [3:0]  rc_state;
    logic        rc_busy;
    logic        rc_output_fifo_afull;

    // =========================================================================
    // result_to_dma -> BRAM Interface
    // =========================================================================
    logic                           bram_wr_en;
    logic [RESULT_ADDR_WIDTH-1:0]   bram_wr_addr;
    logic [255:0]                   bram_wr_data;
    logic [31:0]                    bram_wr_strobe;

    // Circular buffer control/status
    logic [RESULT_ADDR_WIDTH-1:0]   rd_ptr;
    logic [RESULT_ADDR_WIDTH-1:0]   wr_ptr;
    logic [RESULT_ADDR_WIDTH:0]     used_entries;
    logic                           almost_full;
    logic                           buffer_empty;

    // =========================================================================
    // Mock Result BRAM
    // =========================================================================
    logic [255:0] result_bram [0:RESULT_BUFFER_DEPTH-1];
    int           total_bram_writes;

    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            total_bram_writes <= 0;
        end else if (bram_wr_en) begin
            for (int i = 0; i < 32; i++) begin
                if (bram_wr_strobe[i]) begin
                    result_bram[bram_wr_addr][i*8 +: 8] <= bram_wr_data[i*8 +: 8];
                end
            end
            total_bram_writes <= total_bram_writes + 1;
        end
    end

    // =========================================================================
    // 16 Compute Engine Instances
    // =========================================================================
    generate
        for (genvar row = 0; row < NUM_ROWS; row++) begin : gen_ce
            compute_engine_2d #(
                .MATMUL_ID        (row),
                .MAN_WIDTH        (MAN_WIDTH),
                .EXP_WIDTH        (EXP_WIDTH),
                .BRAM_DEPTH       (BRAM_DEPTH),
                .NUM_MLPS         (NUM_MLPS),
                .RESULT_FIFO_DEPTH(RESULT_FIFO_DEPTH)
            ) u_ce (
                .i_clk              (clk),
                .i_reset_n          (rstn),

                // Command Interface (shared opcode, per-row response)
                .i_mc_cmd_op        (mc_cmd_op),
                .i_cmd_id           (mc_cmd_id),
                .i_cmd_payload_word1(cmd_payload_word1),
                .i_cmd_payload_word2(cmd_payload_word2),
                .i_cmd_payload_word3(cmd_payload_word3),
                .o_ce_ack_matmul    (ce_ack_matmul[row]),
                .o_ce_id            (ce_id[row]),
                .o_matmul_done      (ce_matmul_done[row]),

                // Activation write interface
                .i_man_left_wr_addr (man_left_wr_addr[row]),
                .i_man_left_wr_en   (man_left_wr_en[row]),
                .i_man_left_wr_data (man_left_wr_data[row]),
                .i_exp_left_wr_addr (exp_left_wr_addr[row]),
                .i_exp_left_wr_en   (exp_left_wr_en[row]),
                .i_exp_left_wr_data (exp_left_wr_data[row]),

                // Weight write interface
                .i_wt_wr_en         (wt_wr_en[row]),
                .o_wt_wr_ready      (wt_wr_ready[row]),
                .i_wt_wr_man        (wt_wr_man[row]),
                .i_wt_wr_exp        (wt_wr_exp[row]),
                .i_wt_mlp_sel       (wt_mlp_sel[row]),
                .i_wt_nv_idx        (wt_nv_idx[row]),

                // Result FIFO Interface -> Result Collector
                .o_result_data      (ce_result_data[row]),
                .i_result_rd_en     (rc_result_rd_en[row]),
                .o_result_empty     (ce_result_empty[row]),
                .o_result_afull     (),

                // Debug
                .o_ce_state         (ce_state[row]),
                .o_result_count     (),
                .o_read_empty_sticky(),
                .o_results_ready    (ce_results_ready[row])
            );
        end
    endgenerate

    // =========================================================================
    // Result Collector 2D
    // =========================================================================
    // OR all ce_results_ready for completion detection
    logic all_ce_results_ready;
    always_comb begin
        all_ce_results_ready = 1'b1;
        for (int r = 0; r < NUM_ROWS; r++) begin
            all_ce_results_ready = all_ce_results_ready && ce_results_ready[r];
        end
    end

    result_collector_2d #(
        .NUM_ROWS          (NUM_ROWS),
        .NUM_COLS          (NUM_COLS),
        .ADDER_SEG_LEN     (2),
        .OUTPUT_FIFO_DEPTH (OUTPUT_FIFO_DEPTH)
    ) u_result_collector (
        .i_clk              (clk),
        .i_reset_n          (rstn),

        // CE completion signal (for partial line flush)
        .i_ce_results_ready (all_ce_results_ready),

        // Command interface (not used in auto-drain mode)
        .i_mc_cmd_op        (8'h00),
        .i_mc_cmd_id        (8'h00),
        .i_cmd_payload_word1(32'h0),
        .i_cmd_payload_word2(32'h0),
        .i_cmd_payload_word3(32'h0),
        .o_rc_ack_readout   (),

        // CE FIFO Interface
        .i_ce_result_data   (ce_result_data),
        .i_ce_result_empty  (ce_result_empty),
        .o_ce_result_rd_en  (rc_result_rd_en),

        // Output Interface -> result_to_dma
        .i_output_ready     (r2d_ready),
        .o_output_valid     (rc_output_valid),
        .o_output_last      (rc_output_last),
        .o_output_keep      (rc_output_keep),
        .o_output_data      (rc_output_data),

        // Status
        .o_rc_state         (rc_state),
        .o_rc_busy          (rc_busy),
        .o_rc_cmd_id        (),
        .o_output_fifo_afull(rc_output_fifo_afull)
    );

    // =========================================================================
    // Result to DMA (Always-Drain Circular Buffer)
    // =========================================================================
    result_to_dma #(
        .DATA_WIDTH         (256),
        .ADDR_WIDTH         (RESULT_ADDR_WIDTH),
        .ALMOST_FULL_MARGIN (16)
    ) u_result_to_dma (
        .i_clk              (clk),
        .i_reset_n          (rstn),

        // From result_collector
        .i_data             (rc_output_data),
        .i_keep             (rc_output_keep),
        .i_last             (rc_output_last),
        .i_valid            (rc_output_valid),
        .o_ready            (r2d_ready),

        // Circular buffer control
        .i_rd_ptr           (rd_ptr),
        .o_wr_ptr           (wr_ptr),
        .o_used_entries     (used_entries),
        .o_almost_full      (almost_full),
        .o_empty            (buffer_empty),

        // BRAM write
        .o_bram_wr_en       (bram_wr_en),
        .o_bram_wr_addr     (bram_wr_addr),
        .o_bram_wr_data     (bram_wr_data),
        .o_bram_wr_strobe   (bram_wr_strobe)
    );

    // =========================================================================
    // Hex Data Storage (per-row for activations, per-row-per-cg for weights)
    // =========================================================================
    // Per-row activation data: left_{row}.hex
    logic [7:0] left_exp_data  [NUM_ROWS-1:0][0:EXP_LINES-1][0:31];
    logic [7:0] left_man_data  [NUM_ROWS-1:0][0:511][0:31];
    int left_lines_loaded [NUM_ROWS-1:0];

    // Per-row-per-column-group weight data: right_{row}_{cg}.hex
    localparam int MAX_COL_GROUPS = 4;
    logic [7:0] right_exp_data [NUM_ROWS-1:0][MAX_COL_GROUPS-1:0][0:EXP_LINES-1][0:31];
    logic [7:0] right_man_data [NUM_ROWS-1:0][MAX_COL_GROUPS-1:0][0:511][0:31];
    int right_lines_loaded [NUM_ROWS-1:0][MAX_COL_GROUPS-1:0];

    // =========================================================================
    // Exponent Conversion Functions (per-row variants)
    // =========================================================================
    localparam int GFP5_BIAS = 15;
    localparam int BFP8E8_BIAS = 133;
    localparam int ACX_BFP_BIAS_OFFSET = BFP8E8_BIAS - GFP5_BIAS;

    // Get raw exponent from per-row activation data
    function automatic logic [7:0] get_left_exponent(
        input int row,
        input int nv_idx,
        input int chunk_idx
    );
        int exp_idx, exp_line, exp_byte;
        exp_idx = nv_idx * 4 + chunk_idx;
        exp_line = exp_idx / 32;
        exp_byte = exp_idx % 32;
        return left_exp_data[row][exp_line][exp_byte];
    endfunction

    // Get mantissa chunk from per-row activation data
    function automatic logic [255:0] get_left_mantissa(
        input int row,
        input int nv_idx,
        input int chunk_idx
    );
        int man_line;
        logic [255:0] chunk;
        man_line = nv_idx * 4 + chunk_idx;
        chunk = '0;
        for (int i = 0; i < 32; i++) begin
            chunk[i*8 +: 8] = left_man_data[row][man_line][i];
        end
        return chunk;
    endfunction

    // Get raw exponent from per-row-per-cg weight data
    function automatic logic [7:0] get_right_exponent(
        input int row,
        input int cg,
        input int nv_idx,
        input int chunk_idx
    );
        int exp_idx, exp_line, exp_byte;
        exp_idx = nv_idx * 4 + chunk_idx;
        exp_line = exp_idx / 32;
        exp_byte = exp_idx % 32;
        return right_exp_data[row][cg][exp_line][exp_byte];
    endfunction

    // Get mantissa chunk from per-row-per-cg weight data
    function automatic logic [255:0] get_right_mantissa(
        input int row,
        input int cg,
        input int nv_idx,
        input int chunk_idx
    );
        int man_line;
        logic [255:0] chunk;
        man_line = nv_idx * 4 + chunk_idx;
        chunk = '0;
        for (int i = 0; i < 32; i++) begin
            chunk[i*8 +: 8] = right_man_data[row][cg][man_line][i];
        end
        return chunk;
    endfunction

    // =========================================================================
    // Load Hex File Tasks
    // =========================================================================
    // Load activation file for a specific row
    task automatic load_left_hex_file(
        input string filename,
        input int row
    );
        integer fd;
        string line_str;
        logic [7:0] hex_bytes[0:31];
        integer scan_result;
        int line_idx;

        fd = $fopen(filename, "r");
        if (fd == 0) begin
            $display("[TB] ERROR: Cannot open %s", filename);
            left_lines_loaded[row] = 0;
            return;
        end

        line_idx = 0;
        while (!$feof(fd) && line_idx < TOTAL_LINES) begin
            if ($fgets(line_str, fd)) begin
                scan_result = $sscanf(line_str,
                    "%h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h",
                    hex_bytes[0], hex_bytes[1], hex_bytes[2], hex_bytes[3],
                    hex_bytes[4], hex_bytes[5], hex_bytes[6], hex_bytes[7],
                    hex_bytes[8], hex_bytes[9], hex_bytes[10], hex_bytes[11],
                    hex_bytes[12], hex_bytes[13], hex_bytes[14], hex_bytes[15],
                    hex_bytes[16], hex_bytes[17], hex_bytes[18], hex_bytes[19],
                    hex_bytes[20], hex_bytes[21], hex_bytes[22], hex_bytes[23],
                    hex_bytes[24], hex_bytes[25], hex_bytes[26], hex_bytes[27],
                    hex_bytes[28], hex_bytes[29], hex_bytes[30], hex_bytes[31]);

                if (scan_result == 32) begin
                    if (line_idx < EXP_LINES) begin
                        for (int i = 0; i < 32; i++) left_exp_data[row][line_idx][i] = hex_bytes[i];
                    end else begin
                        int man_idx = line_idx - MAN_LINE_START;
                        for (int i = 0; i < 32; i++) left_man_data[row][man_idx][i] = hex_bytes[i];
                    end
                    line_idx++;
                end
            end
        end
        $fclose(fd);
        left_lines_loaded[row] = line_idx;
    endtask

    // Load weight file for a specific row and column group
    task automatic load_right_hex_file(
        input string filename,
        input int row,
        input int cg
    );
        integer fd;
        string line_str;
        logic [7:0] hex_bytes[0:31];
        integer scan_result;
        int line_idx;

        fd = $fopen(filename, "r");
        if (fd == 0) begin
            $display("[TB] ERROR: Cannot open %s", filename);
            right_lines_loaded[row][cg] = 0;
            return;
        end

        line_idx = 0;
        while (!$feof(fd) && line_idx < TOTAL_LINES) begin
            if ($fgets(line_str, fd)) begin
                scan_result = $sscanf(line_str,
                    "%h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h",
                    hex_bytes[0], hex_bytes[1], hex_bytes[2], hex_bytes[3],
                    hex_bytes[4], hex_bytes[5], hex_bytes[6], hex_bytes[7],
                    hex_bytes[8], hex_bytes[9], hex_bytes[10], hex_bytes[11],
                    hex_bytes[12], hex_bytes[13], hex_bytes[14], hex_bytes[15],
                    hex_bytes[16], hex_bytes[17], hex_bytes[18], hex_bytes[19],
                    hex_bytes[20], hex_bytes[21], hex_bytes[22], hex_bytes[23],
                    hex_bytes[24], hex_bytes[25], hex_bytes[26], hex_bytes[27],
                    hex_bytes[28], hex_bytes[29], hex_bytes[30], hex_bytes[31]);

                if (scan_result == 32) begin
                    if (line_idx < EXP_LINES) begin
                        for (int i = 0; i < 32; i++) right_exp_data[row][cg][line_idx][i] = hex_bytes[i];
                    end else begin
                        int man_idx = line_idx - MAN_LINE_START;
                        for (int i = 0; i < 32; i++) right_man_data[row][cg][man_idx][i] = hex_bytes[i];
                    end
                    line_idx++;
                end
            end
        end
        $fclose(fd);
        right_lines_loaded[row][cg] = line_idx;
    endtask

    // Load all hex files for all rows and column groups
    task automatic load_all_hex_files(int num_col_groups);
        string filename;
        $display("[TB] Loading hex files from %s", HEX_PATH);
        $display("[TB]   Loading %0d left files (activations)", NUM_ROWS);
        for (int row = 0; row < NUM_ROWS; row++) begin
            $sformat(filename, "%sleft_%0d.hex", HEX_PATH, row);
            load_left_hex_file(filename, row);
        end

        $display("[TB]   Loading %0d x %0d right files (weights)", NUM_ROWS, num_col_groups);
        for (int row = 0; row < NUM_ROWS; row++) begin
            for (int cg = 0; cg < num_col_groups; cg++) begin
                $sformat(filename, "%sright_%0d_%0d.hex", HEX_PATH, row, cg);
                load_right_hex_file(filename, row, cg);
            end
        end
        $display("[TB] Hex file loading complete");
    endtask

    // =========================================================================
    // Write Activations to All CEs (per-row data)
    // =========================================================================
    task automatic write_activations_all_rows(int B, int V);
        $display("[TB] Writing activations to all %0d rows: B=%0d, V=%0d", NUM_ROWS, B, V);

        for (int nv = 0; nv < B * V; nv++) begin
            // Write mantissa chunks
            for (int chunk = 0; chunk < 4; chunk++) begin
                for (int row = 0; row < NUM_ROWS; row++) begin
                    man_left_wr_addr[row] = nv * 4 + chunk;
                    man_left_wr_data[row] = get_left_mantissa(row, nv, chunk);
                    man_left_wr_en[row] = 1'b1;
                end
                @(posedge clk);
                for (int row = 0; row < NUM_ROWS; row++) man_left_wr_en[row] = 1'b0;
            end
            // Write exponent chunks
            for (int chunk = 0; chunk < 4; chunk++) begin
                for (int row = 0; row < NUM_ROWS; row++) begin
                    exp_left_wr_addr[row] = nv * 4 + chunk;
                    exp_left_wr_data[row] = get_left_exponent(row, nv, chunk);
                    exp_left_wr_en[row] = 1'b1;
                end
                @(posedge clk);
                for (int row = 0; row < NUM_ROWS; row++) exp_left_wr_en[row] = 1'b0;
            end
        end
        $display("[TB] Activation write complete");
    endtask

    // =========================================================================
    // Write Weights to All CEs (load all 4 blocks into weight BRAMs)
    // =========================================================================
    // Each hex block fills 1/4 of the weight BRAM (128 lines per block)
    // Block 0 → addresses 0-127, Block 1 → 128-255, etc.
    // Each column's weight BRAM holds C*V/4 = 128 NVs for B1_C64_V2
    task automatic write_weights_all_rows(int C, int V);
        int block;
        int nv_in_block;
        int chunk;
        int mlp_idx;
        int bank;
        int nv_addr;
        int base_addr;
        int nvs_per_block;

        // Calculate NVs per block: total NVs divided by 4 blocks
        nvs_per_block = (C * V) / 4;  // 128/4 = 32 for B1_C64_V2

        $display("[TB] Writing weights to all %0d rows: C=%0d, V=%0d", NUM_ROWS, C, V);
        $display("[TB]   Loading 4 blocks, %0d NVs per block, into weight BRAMs", nvs_per_block);

        // Load all 4 blocks into weight BRAMs
        for (block = 0; block < 4; block++) begin
            base_addr = block * (512 / 4);  // 0, 128, 256, 384

            for (nv_in_block = 0; nv_in_block < nvs_per_block; nv_in_block++) begin
                // Write to all columns in this CE
                for (int col = 0; col < NUM_COLS; col++) begin
                    mlp_idx = col / 2;
                    bank = col % 2;

                    for (chunk = 0; chunk < 4; chunk++) begin
                        // Address within this block's range
                        nv_addr = base_addr + nv_in_block * 8 + chunk * 2 + bank;

                        for (int row = 0; row < NUM_ROWS; row++) begin
                            wt_mlp_sel[row] = mlp_idx[MLP_SEL_WIDTH-1:0];
                            wt_nv_idx[row] = nv_addr;
                            // Use per-row weight data from this block
                            wt_wr_man[row] = get_right_mantissa(row, block, nv_in_block, chunk);
                            wt_wr_exp[row] = get_right_exponent(row, block, nv_in_block, chunk);
                            wt_wr_en[row] = 1'b1;
                        end
                        @(posedge clk);
                        for (int row = 0; row < NUM_ROWS; row++) wt_wr_en[row] = 1'b0;
                        @(posedge clk);
                    end
                end
            end
            $display("[TB]   Block %0d loaded (addresses %0d-%0d)", block, base_addr, base_addr + 127);
        end
        $display("[TB] Weight write complete");
    endtask

    // =========================================================================
    // Issue MATMUL Command to All CEs
    // =========================================================================
    task automatic issue_matmul_all(int B, int C, int V);
        $display("[TB] Issuing MATMUL to all CEs: B=%0d, C=%0d, V=%0d", B, C, V);

        cmd_payload_word1 = {16'd0, 16'd0};
        cmd_payload_word2 = {B[15:0], C[15:0]};
        cmd_payload_word3 = {V[15:0], 16'd0};
        mc_cmd_id = 8'd1;

        @(posedge clk);
        mc_cmd_op = OPC_MATMUL;

        // Wait for all ACKs
        @(posedge clk);
        @(posedge clk);
        for (int row = 0; row < NUM_ROWS; row++) begin
            if (ce_ack_matmul[row])
                $display("[TB] CE[%0d] acknowledged MATMUL", row);
        end

        @(posedge clk);
        mc_cmd_op = OPC_NOP;
    endtask

    // =========================================================================
    // Wait for Results (monitor wr_ptr)
    // =========================================================================
    task automatic wait_for_results(int expected_lines, int timeout_cycles);
        int cycle_cnt = 0;
        int prev_wr_ptr = 0;
        int idle_cycles = 0;

        $display("[TB] Waiting for %0d result lines (timeout=%0d cycles)...", expected_lines, timeout_cycles);

        while (cycle_cnt < timeout_cycles) begin
            @(posedge clk);
            cycle_cnt++;

            if (wr_ptr != prev_wr_ptr) begin
                $display("[TB] @cycle %0d: wr_ptr=%0d, used_entries=%0d, bram_writes=%0d",
                         cycle_cnt, wr_ptr, used_entries, total_bram_writes);
                prev_wr_ptr = wr_ptr;
                idle_cycles = 0;
            end else begin
                idle_cycles++;
            end

            if (total_bram_writes >= expected_lines && idle_cycles > 100) begin
                $display("[TB] All %0d lines received", expected_lines);
                return;
            end

            if (cycle_cnt % 5000 == 0) begin
                $display("[TB] @cycle %0d: rc_state=%0d, rc_busy=%b, wr_ptr=%0d, writes=%0d",
                         cycle_cnt, rc_state, rc_busy, wr_ptr, total_bram_writes);
            end
        end

        $display("[TB] TIMEOUT waiting for results after %0d cycles", timeout_cycles);
        $display("[TB]   wr_ptr=%0d, expected=%0d, bram_writes=%0d", wr_ptr, expected_lines, total_bram_writes);
    endtask

    // =========================================================================
    // Load Golden and Verify (per-row, per-cg golden files)
    // =========================================================================
    // Golden results: [row][cg][col_in_cg]
    logic [15:0] golden_results [NUM_ROWS-1:0][MAX_COL_GROUPS-1:0][0:NUM_COLS-1];
    int golden_count [NUM_ROWS-1:0][MAX_COL_GROUPS-1:0];

    task automatic load_golden_file(string filename, int row, int cg);
        integer fd;
        string line_str;
        logic [15:0] hex_val;
        int idx;

        fd = $fopen(filename, "r");
        if (fd == 0) begin
            $display("[TB] WARNING: Cannot open golden file %s", filename);
            golden_count[row][cg] = 0;
            return;
        end

        idx = 0;
        while (!$feof(fd) && idx < NUM_COLS) begin
            if ($fgets(line_str, fd)) begin
                if ($sscanf(line_str, "%h", hex_val) == 1) begin
                    golden_results[row][cg][idx] = hex_val;
                    idx++;
                end
            end
        end
        $fclose(fd);
        golden_count[row][cg] = idx;
    endtask

    // Load all golden files
    task automatic load_all_golden_files(int num_col_groups);
        string filename;
        int total_loaded = 0;
        $display("[TB] Loading golden files...");
        for (int row = 0; row < NUM_ROWS; row++) begin
            for (int cg = 0; cg < num_col_groups; cg++) begin
                $sformat(filename, "%sgolden_B1_C64_V2_%0d_%0d.hex", HEX_PATH, row, cg);
                load_golden_file(filename, row, cg);
                total_loaded += golden_count[row][cg];
            end
        end
        $display("[TB] Loaded %0d total golden values", total_loaded);
    endtask

    // =========================================================================
    // Main Test Sequence
    // =========================================================================
    int B, C, V;
    int col_groups;
    int expected_results;
    int expected_lines;

    initial begin
        $display("");
        $display("======================================================================");
        $display("  Compute -> Result Collector -> Result to DMA Testbench");
        $display("======================================================================");
        $display("  Configuration: %0d CEs x %0d columns (NUM_MLPS=%0d)", NUM_ROWS, NUM_COLS, NUM_MLPS);
        $display("  Test: B=1, C=256, V=2 (256 results -> 16 output lines)");
        $display("======================================================================");
        $display("");

        // Initialize
        rstn = 0;
        mc_cmd_op = OPC_NOP;
        mc_cmd_id = 8'd0;
        cmd_payload_word1 = 32'h0;
        cmd_payload_word2 = 32'h0;
        cmd_payload_word3 = 32'h0;
        rd_ptr = 0;

        for (int row = 0; row < NUM_ROWS; row++) begin
            man_left_wr_en[row] = 0;
            exp_left_wr_en[row] = 0;
            wt_wr_en[row] = 0;
        end

        for (int i = 0; i < RESULT_BUFFER_DEPTH; i++) begin
            result_bram[i] = 256'h0;
        end

        repeat (20) @(posedge clk);
        rstn = 1;
        repeat (10) @(posedge clk);

        // Test configuration
        // With NUM_COLS=4 and 4 hex blocks loaded, use C=256 to utilize all weight data
        // C=256 / NUM_COLS=4 = 64 column groups × 8 addr/group = 512 addresses (full BRAM)
        B = 1;
        C = 256;
        V = 2;
        col_groups = (C + NUM_COLS - 1) / NUM_COLS;  // 4 for C=64
        expected_results = B * C;  // 64 (summed across 16 rows)
        expected_lines = (expected_results + 15) / 16;  // 4

        // Load all hex files (per-row activations, all 4 weight blocks per row)
        // Note: 4 blocks fill the weight BRAMs regardless of NUM_COLS
        load_all_hex_files(MAX_COL_GROUPS);  // Always load all 4 blocks

        // Load golden files (optional, for verification)
        load_all_golden_files(MAX_COL_GROUPS);

        // Write activations to all CEs
        write_activations_all_rows(B, V);

        // Write weights to all CEs
        write_weights_all_rows(C, V);

        // Issue MATMUL to all CEs
        issue_matmul_all(B, C, V);

        // Wait for results (auto-drain should produce output)
        wait_for_results(expected_lines, 100000);

        // Report results
        $display("");
        $display("======================================================================");
        $display("  RESULTS");
        $display("======================================================================");
        $display("  Expected lines: %0d", expected_lines);
        $display("  BRAM writes:    %0d", total_bram_writes);
        $display("  wr_ptr:         %0d", wr_ptr);
        $display("  used_entries:   %0d", used_entries);

        if (total_bram_writes == expected_lines) begin
            $display("  STATUS: PASS - All output lines received");
        end else begin
            $display("  STATUS: FAIL - Missing output lines");
        end

        // Display all output lines from BRAM
        $display("");
        $display("  Output BRAM contents (%0d lines):", total_bram_writes);
        for (int line = 0; line < total_bram_writes && line < 8; line++) begin
            $display("  Line %0d:", line);
            for (int i = 0; i < 16; i++) begin
                $display("    [%0d] = 0x%04x", i, result_bram[line][i*16 +: 16]);
            end
        end

        $display("======================================================================");
        $display("");

        #1000;
        $finish;
    end

endmodule
