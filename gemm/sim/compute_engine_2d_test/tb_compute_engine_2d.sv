// ------------------------------------------------------------------
// Testbench for compute_engine_2d.sv
//
// Purpose: Validate the compute engine with:
//   - comp_row_bram for activations
//   - comp_MLPStack for computation
//   - comp_MLPStack_oFIFO for result buffering
//
// Test Flow:
//   1. Load left.hex (activations) and right.hex (weights)
//   2. For each test configuration (B, C, V):
//      a. Write activations to row_bram
//      b. Write weights to MLPStack
//      c. Issue MATMUL command (packed payload)
//      d. Read results from 16 output FIFOs
//      e. Compare against golden file
//
// Memory Layout (528 lines per hex file):
//   Lines 0-15:   Exponent data (16 lines x 32 bytes = 512 exponents)
//   Lines 16-527: Mantissa data (512 lines x 32 bytes = 128 NVs x 4 chunks)
//
// Command Interface (raw opcode from master_control_2d):
//   - i_mc_cmd_op: Raw opcode (CE detects MATMUL=0xF2 internally)
//   - i_cmd_id: Command ID
//   - i_cmd_payload_word1: {left_addr[15:0], right_addr[15:0]}
//   - i_cmd_payload_word2: {B[15:0], C[15:0]}
//   - i_cmd_payload_word3: {V[15:0], flags[15:0]}
//
// Validation Tolerance:
//   - Combined tolerance: 5% relative OR 0.001 absolute
//
// Author: Compute Engine 2D Testing
// Date: Jan 22, 2026 - Updated for packed command interface
// ------------------------------------------------------------------

`timescale 1ns/1ps

module tb_compute_engine_2d;

    // =========================================================================
    // Parameters - Configurable via Makefile defines
    // =========================================================================
    localparam int CLK_PERIOD_NS    = 10;        // 100MHz clock
    localparam int TIMEOUT_NS       = 100000000; // 100ms timeout

    // Configurable NUM_MLPS - override via Makefile +define+NUM_MLPS=N
    `ifndef NUM_MLPS
    `define NUM_MLPS 2
    `define NUM_MLPS 2
    `endif
    localparam int NUM_MLPS         = `NUM_MLPS;
    localparam int NUM_COLS         = 2 * NUM_MLPS;  // 2 columns per MLP

    localparam int MAN_WIDTH        = 256;
    localparam int EXP_WIDTH        = 8;
    localparam int BRAM_DEPTH       = 512;
    localparam int ADDR_WIDTH       = 9;

    // Memory block constants
    localparam int EXP_LINES     = 16;           // Lines 0-15
    localparam int MAN_LINE_START = 16;          // Mantissa starts at line 16
    localparam int TOTAL_LINES   = 528;
    localparam int MAX_NVS       = 128;

    // =========================================================================
    // Hex File Paths
    // =========================================================================
    localparam string HEX_PATH = "/home/workstation/elastix_gemm/hex/";

    // =========================================================================
    // Test Configuration
    // =========================================================================
    typedef struct {
        int         C;              // Number of columns (weight NVs)
        int         V;              // NVs per column (V-loop depth for accumulation)
        int         B;              // Number of batches (activation NVs per dot product)
        string      name;           // Test directory name and golden file prefix
        bit         multi_file;     // 1=load from subdirectory with multiple files
        int         row_id;         // Row ID for multi-file tests (0-15)
    } test_config_t;

    // Test suite - uses available golden files
    test_config_t test_suite[] = '{
        // '{C: 1,  V: 1,  B: 1,   name: "golden_B1_C1_V1"},      // Minimal smoke test
        // '{C: 2,  V: 2,  B: 2,   name: "golden_B2_C2_V2"},      // Multi-batch, multi-column
        // '{C: 4,  V: 4,  B: 4,   name: "golden_B4_C4_V4"},      // 4x4 test
        '{C: 8,  V: 8,  B: 4,   name: "golden_B4_C8_V8"},      // 8 columns (V=8 to match golden)
        // '{C: 13, V: 9,  B: 4,   name: "golden_B4_C13_V9"},     // Non-power-of-2 C and V
        // '{C: 14, V: 4,  B: 8,   name: "golden_B8_C14_V4"},     // 8 batches, 14 columns
        // '{C: 8,  V: 16, B: 8,   name: "golden_B8_C8_V16"},     // 8 batches
        // '{C: 16, V: 4,  B: 16,  name: "golden_B16_C16_V4"},    // 16 batches, 16 cols
        '{C: 16, V: 8,  B: 16,  name: "golden_B16_C16_V8"},    // Large: 16 batches, full cols
        '{C: 64, V: 2,  B: 1,   name: "golden_B1_C64_V2"},     // 64 columns (4 column groups)
        '{C: 64, V: 2,  B: 8,   name: "golden_B8_C64_V2"},     // 64 cols, 8 batches
        '{C: 128, V: 1, B: 1,   name: "golden_B1_C128_V1"}     // 128 columns (8 column groups)
    };

    // =========================================================================
    // Clock and Reset
    // =========================================================================
    logic clk;
    logic rstn;

    // =========================================================================
    // DUT Interface Signals - Raw Opcode Command Interface
    // =========================================================================
    // Master Control Interface (raw opcode - CE does internal edge detection)
    logic [7:0]   mc_cmd_op;            // Raw opcode (0xF2 = MATMUL)
    logic [7:0]   cmd_id;
    logic [31:0]  cmd_payload_word1;    // {left_addr[15:0], right_addr[15:0]}
    logic [31:0]  cmd_payload_word2;    // {B[15:0], C[15:0]}
    logic [31:0]  cmd_payload_word3;    // {V[15:0], flags[15:0]}
    logic         ce_ack_matmul;
    logic [7:0]   ce_id;
    logic         matmul_done;

    // Opcode constants
    localparam logic [7:0] OPC_NOP    = 8'h00;
    localparam logic [7:0] OPC_MATMUL = 8'hF2;

    // row_bram Write Interface (Activations)
    logic [ADDR_WIDTH-1:0]  man_left_wr_addr;
    logic                   man_left_wr_en;
    logic [MAN_WIDTH-1:0]   man_left_wr_data;
    logic [ADDR_WIDTH-1:0]  exp_left_wr_addr;
    logic                   exp_left_wr_en;
    logic [EXP_WIDTH-1:0]   exp_left_wr_data;

    // MLP Weight Write Interface
    logic                   wt_wr_en;
    logic                   wt_wr_ready;
    logic [255:0]           wt_wr_man;
    logic [EXP_WIDTH-1:0]   wt_wr_exp;
    logic [2:0]             wt_mlp_sel;
    logic [9:0]             wt_nv_idx;

    // Result FIFO Interface (unpacked arrays to match DUT ports)
    logic [15:0]            result_data [NUM_COLS-1:0];
    logic                   result_rd_en [NUM_COLS-1:0];
    logic                   result_empty [NUM_COLS-1:0];
    logic                   result_afull;

    // Debug Interface
    logic [3:0]             ce_state;
    logic [15:0]            result_count;
    logic                   read_empty_sticky;
    logic                   results_ready;

    // =========================================================================
    // Test Status
    // =========================================================================
    int     tests_run;
    int     tests_passed;
    logic   current_test_ok;
    int     num_results_collected;

    // Collected results (FP16 values)
    logic [15:0] collected_results [0:1023];

    // =========================================================================
    // Raw Hex Data Storage
    // =========================================================================
    logic [7:0] left_exp_data  [0:EXP_LINES-1][0:31];
    // For multi-file mode: one memory block per physical column (NUM_COLS=4)
    logic [7:0] right_exp_data [0:NUM_COLS-1][0:EXP_LINES-1][0:31];
    logic [7:0] left_man_data  [0:511][0:31];
    logic [7:0] right_man_data [0:NUM_COLS-1][0:511][0:31];

    int left_lines_loaded;
    int right_lines_loaded [0:NUM_COLS-1];

    // =========================================================================
    // DUT Instantiation - Raw Opcode Interface
    // =========================================================================
    compute_engine_2d #(
        .MATMUL_ID(0),
        .MAN_WIDTH(MAN_WIDTH),
        .EXP_WIDTH(EXP_WIDTH),
        .BRAM_DEPTH(BRAM_DEPTH),
        .ADDR_WIDTH(ADDR_WIDTH),
        .NUM_MLPS(NUM_MLPS),
        .NUM_COLS(NUM_COLS),
        .RESULT_FIFO_DEPTH(512)
    ) dut (
        .i_clk(clk),
        .i_reset_n(rstn),

        // Master Control Interface (raw opcode - CE does internal edge detection)
        .i_mc_cmd_op(mc_cmd_op),
        .i_cmd_id(cmd_id),
        .i_cmd_payload_word1(cmd_payload_word1),
        .i_cmd_payload_word2(cmd_payload_word2),
        .i_cmd_payload_word3(cmd_payload_word3),
        .o_ce_ack_matmul(ce_ack_matmul),
        .o_ce_id(ce_id),
        .o_matmul_done(matmul_done),

        // row_bram Write Interface
        .i_man_left_wr_addr(man_left_wr_addr),
        .i_man_left_wr_en(man_left_wr_en),
        .i_man_left_wr_data(man_left_wr_data),
        .i_exp_left_wr_addr(exp_left_wr_addr),
        .i_exp_left_wr_en(exp_left_wr_en),
        .i_exp_left_wr_data(exp_left_wr_data),

        // MLP Weight Write Interface
        .i_wt_wr_en(wt_wr_en),
        .o_wt_wr_ready(wt_wr_ready),
        .i_wt_wr_man(wt_wr_man),
        .i_wt_wr_exp(wt_wr_exp),
        .i_wt_mlp_sel(wt_mlp_sel),
        .i_wt_nv_idx(wt_nv_idx),

        // Result FIFO Interface
        .o_result_data(result_data),
        .i_result_rd_en(result_rd_en),
        .o_result_empty(result_empty),
        .o_result_afull(result_afull),

        // Debug Interface
        .o_ce_state(ce_state),
        .o_result_count(result_count),
        .o_read_empty_sticky(read_empty_sticky),
        .o_results_ready(results_ready)
    );

    // =========================================================================
    // Clock Generation
    // =========================================================================
    initial begin
        clk = 0;
        forever #(CLK_PERIOD_NS/2) clk = ~clk;
    end

    // =========================================================================
    // Exponent Conversion: GFP5 -> BFP8E8
    // Note: comp_row_bram stores RAW exponents, compute_engine_2d converts them
    //       MLPStack weights need converted exponents
    // =========================================================================
    localparam int GFP5_BIAS = 15;
    localparam int BFP8E8_BIAS = 133;
    localparam int ACX_BFP_BIAS_OFFSET = BFP8E8_BIAS - GFP5_BIAS;  // = 118

    function automatic logic [7:0] convert_exp(logic [7:0] raw_exp);
        return raw_exp + ACX_BFP_BIAS_OFFSET;
    endfunction

    // Get RAW exponent (no conversion) for row_bram activation writes
    function automatic logic [7:0] get_raw_exponent(
        input logic [7:0] exp_data [0:EXP_LINES-1][0:31],
        input int nv_idx,
        input int chunk_idx
    );
        int exp_idx;
        int exp_line;
        int exp_byte;

        exp_idx = nv_idx * 4 + chunk_idx;
        exp_line = exp_idx / 32;
        exp_byte = exp_idx % 32;

        return exp_data[exp_line][exp_byte];  // No bias conversion
    endfunction

    // =========================================================================
    // Load Memory Block Hex File
    // =========================================================================
    task automatic load_memory_block_hex(
        input string filename,
        output logic [7:0] exp_data [0:EXP_LINES-1][0:31],
        output logic [7:0] man_data [0:511][0:31],
        output int lines_loaded
    );
        integer fd;
        string line_str;
        logic [7:0] hex_bytes[0:31];
        integer scan_result;
        int line_idx;

        fd = $fopen(filename, "r");
        if (fd == 0) begin
            $display("[TB] ERROR: Cannot open %s", filename);
            lines_loaded = 0;
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
                        for (int i = 0; i < 32; i++) begin
                            exp_data[line_idx][i] = hex_bytes[i];
                        end
                    end else begin
                        int man_idx = line_idx - MAN_LINE_START;
                        for (int i = 0; i < 32; i++) begin
                            man_data[man_idx][i] = hex_bytes[i];
                        end
                    end
                    line_idx++;
                end
            end
        end
        $fclose(fd);
        lines_loaded = line_idx;
    endtask

    // =========================================================================
    // Get Exponent for NV chunk (with optional column index for right data)
    // =========================================================================
    function automatic logic [7:0] get_exponent(
        input logic [7:0] exp_data [0:EXP_LINES-1][0:31],
        input int nv_idx,
        input int chunk_idx
    );
        int exp_idx;
        int exp_line;
        int exp_byte;
        logic [7:0] raw_exp;

        exp_idx = nv_idx * 4 + chunk_idx;
        exp_line = exp_idx / 32;
        exp_byte = exp_idx % 32;

        raw_exp = exp_data[exp_line][exp_byte];
        return convert_exp(raw_exp);
    endfunction

    function automatic logic [7:0] get_exponent_col(
        input logic [7:0] exp_data [0:NUM_COLS-1][0:EXP_LINES-1][0:31],
        input int col_idx,
        input int nv_idx,
        input int chunk_idx
    );
        int exp_idx;
        int exp_line;
        int exp_byte;
        logic [7:0] raw_exp;

        exp_idx = nv_idx * 4 + chunk_idx;
        exp_line = exp_idx / 32;
        exp_byte = exp_idx % 32;

        raw_exp = exp_data[col_idx][exp_line][exp_byte];
        return convert_exp(raw_exp);
    endfunction

    // =========================================================================
    // Get 256-bit Mantissa Chunk (with optional column index for right data)
    // =========================================================================
    function automatic logic [255:0] get_mantissa_chunk(
        input logic [7:0] man_data [0:511][0:31],
        input int nv_idx,
        input int chunk_idx
    );
        int man_line;
        logic [255:0] chunk;

        man_line = nv_idx * 4 + chunk_idx;
        chunk = '0;
        for (int i = 0; i < 32; i++) begin
            chunk[i*8 +: 8] = man_data[man_line][i];
        end
        return chunk;
    endfunction

    function automatic logic [255:0] get_mantissa_chunk_col(
        input logic [7:0] man_data [0:NUM_COLS-1][0:511][0:31],
        input int col_idx,
        input int nv_idx,
        input int chunk_idx
    );
        int man_line;
        logic [255:0] chunk;

        man_line = nv_idx * 4 + chunk_idx;
        chunk = '0;
        for (int i = 0; i < 32; i++) begin
            chunk[i*8 +: 8] = man_data[col_idx][man_line][i];
        end
        return chunk;
    endfunction

    // =========================================================================
    // Write Activations to row_bram
    // =========================================================================
    task automatic write_activations(int B, int V);
        $display("[TB] Writing %0d x %0d = %0d activation NVs to row_bram", B, V, B*V);

        for (int nv = 0; nv < B * V; nv++) begin
            // Write 4 mantissa chunks per NV
            for (int chunk = 0; chunk < 4; chunk++) begin
                man_left_wr_addr = nv * 4 + chunk;
                man_left_wr_data = get_mantissa_chunk(left_man_data, nv, chunk);
                man_left_wr_en = 1'b1;
                @(posedge clk);
                man_left_wr_en = 1'b0;
            end
            // Write 4 exponents per NV (one per chunk) - RAW exponents, no conversion
            // comp_row_bram packs 4 exponents into 32-bit word using addr[1:0] as byte position
            for (int chunk = 0; chunk < 4; chunk++) begin
                exp_left_wr_addr = nv * 4 + chunk;  // {nv[6:0], chunk[1:0]}
                exp_left_wr_data = get_raw_exponent(left_exp_data, nv, chunk);
                exp_left_wr_en = 1'b1;
                @(posedge clk);
                exp_left_wr_en = 1'b0;
            end
        end

        $display("[TB] Activation write complete");
    endtask

    // =========================================================================
    // Write Weights to MLPStack
    // Note: compute_engine_2d applies E5->E8 bias conversion internally
    //       so we pass RAW exponents here
    //
    // For multi-file mode (C > NUM_COLS):
    //   - Each physical column has its own memory block file
    //   - right_data[col_idx] contains all logical columns that map to col_idx
    //   - Data is pre-organized in column-major, round-robin order
    //   - Each file contains num_col_groups = C/NUM_COLS column groups
    //   - wraddr pattern: wraddr = cg * V * 8 + v * 8 + chunk * 2 + bank
    //
    // Address scheme for asymmetric BRAM (rdaddr N reads wraddrs 2N and 2N+1):
    //   - bank0 (even columns) chunks go to EVEN wraddrs
    //   - bank1 (odd columns) chunks go to ODD wraddrs
    // =========================================================================
    task automatic write_weights_multifile(int C, int V);
        int num_col_groups;
        int mlp_idx, bank, col_idx;
        int src_nv_idx;
        int direct_wraddr;

        num_col_groups = C / NUM_COLS;  // Number of column groups
        $display("[TB] Writing weights (multi-file) for %0d columns x %0d NVs (NUM_COLS=%0d, groups=%0d)",
                 C, V, NUM_COLS, num_col_groups);

        // Iterate through each physical column
        for (col_idx = 0; col_idx < NUM_COLS; col_idx++) begin
            mlp_idx = col_idx / 2;  // Which MLP (0 to NUM_MLPS-1)
            bank = col_idx % 2;     // Which bank within MLP (0 or 1)

            $display("[TB]   Loading column %0d (MLP %0d bank %0d)", col_idx, mlp_idx, bank);

            // Each file contains num_col_groups logical columns × V NVs
            // Layout: cg0_v0, cg0_v1, ..., cg0_v(V-1), cg1_v0, ..., cg(num_col_groups-1)_v(V-1)
            for (int cg = 0; cg < num_col_groups; cg++) begin
                for (int v = 0; v < V; v++) begin
                    src_nv_idx = cg * V + v;  // NV index in this column's memory block

                    // Write 4 chunks with interleaved wraddrs
                    for (int chunk = 0; chunk < 4; chunk++) begin
                        // wraddr = cg * (V * 8) + v * 8 + chunk * 2 + bank
                        direct_wraddr = cg * V * 8 + v * 8 + chunk * 2 + bank;

                        wt_mlp_sel = mlp_idx[2:0];
                        wt_nv_idx = direct_wraddr[9:0];
                        wt_wr_man = get_mantissa_chunk_col(right_man_data, col_idx, src_nv_idx, chunk);
                        wt_wr_exp = get_raw_exponent(right_exp_data[col_idx], src_nv_idx, chunk);
                        wt_wr_en = 1'b1;
                        @(posedge clk);
                        @(negedge clk);  // Hold write enable for full cycle
                        wt_wr_en = 1'b0;
                    end
                end
            end

            $display("[TB]   Column %0d complete (loaded %0d column groups × %0d V = %0d NVs)",
                     col_idx, num_col_groups, V, num_col_groups * V);
        end

        $display("[TB] Weight write complete");
    endtask

    // Legacy single-file weight write (keep for backward compatibility)
    task automatic write_weights_singlefile(int C, int V);
        int mlp_idx;
        int bank;
        int src_nv;
        int direct_wraddr;
        int col_sel;         // Current logical column (0 to NUM_COLS-1)
        int wraddr_base;     // Base address, advances on column wrap

        $display("[TB] Writing weights (single-file) for %0d columns x %0d NVs (NUM_COLS=%0d)", C, V, NUM_COLS);

        col_sel = 0;         // Start at column 0
        wraddr_base = 0;     // Start at base address 0

        for (int c = 0; c < C; c++) begin
            // Map logical column to physical MLP and bank
            mlp_idx = col_sel / 2;  // Which MLP (0 to NUM_MLPS-1)
            bank = col_sel % 2;     // Which bank within MLP (0 or 1)

            for (int v = 0; v < V; v++) begin
                src_nv = c * V + v;  // Source NV index in hex file (c-major order)

                // Write 4 chunks with interleaved wraddrs
                for (int chunk = 0; chunk < 4; chunk++) begin
                    direct_wraddr = wraddr_base + v * 8 + chunk * 2 + bank;

                    wt_mlp_sel = mlp_idx[2:0];
                    wt_nv_idx = direct_wraddr[9:0];
                    wt_wr_man = get_mantissa_chunk_col(right_man_data, 0, src_nv, chunk);
                    wt_wr_exp = get_raw_exponent(right_exp_data[0], src_nv, chunk);
                    wt_wr_en = 1'b1;
                    @(posedge clk);
                    @(negedge clk);  // Hold write enable for full cycle
                    wt_wr_en = 1'b0;
                end
            end

            // Advance col_sel, wrap at NUM_COLS
            if (col_sel == NUM_COLS - 1) begin
                col_sel = 0;
                wraddr_base = wraddr_base + V * 8;
            end else begin
                col_sel = col_sel + 1;
            end
        end

        $display("[TB] Weight write complete");
    endtask

    // =========================================================================
    // Issue MATMUL Command (Raw Opcode Interface)
    // CE does internal edge detection on opcode transition to 0xF2
    // Payload format (per MULTI_ROW_REFERENCE.md):
    //   word1: {left_addr[15:0], right_addr[15:0]}
    //   word2: {B[15:0], C[15:0]}
    //   word3: {V[15:0], flags[15:0]}
    // =========================================================================
    task automatic issue_matmul(int B, int C, int V);
        $display("[TB] Issuing MATMUL: B=%0d, C=%0d, V=%0d", B, C, V);

        // Pack command payload - must match compute_engine_2d extraction:
        //   B_reg <= i_cmd_payload_word2[31:16]
        //   C_reg <= i_cmd_payload_word2[15:0]
        //   V_reg <= i_cmd_payload_word3[31:16]
        cmd_payload_word1 = {16'd0, 16'd0};              // {left_addr, right_addr}
        cmd_payload_word2 = {B[15:0], C[15:0]};          // {B, C}
        cmd_payload_word3 = {V[15:0], 16'd0};            // {V, flags}
        cmd_id = 8'd1;

        // Issue opcode - CE detects rising edge from NOP -> MATMUL
        @(posedge clk);
        mc_cmd_op = OPC_MATMUL;

        // Wait for ACK (CE generates ACK one cycle after detecting opcode)
        @(posedge clk);
        @(posedge clk);
        if (ce_ack_matmul) begin
            $display("[TB] MATMUL command acknowledged");
        end

        // Return opcode to NOP to allow next command
        @(posedge clk);
        mc_cmd_op = OPC_NOP;
    endtask

    // =========================================================================
    // Collect Results from FIFOs
    // flex_fifo has 1-cycle read latency:
    //   - Cycle N: Assert rd_en, FIFO latches mem[rd_ptr] and advances ptr
    //   - Cycle N+1: Data appears on o_rd_data
    //
    // Result ordering: All columns are read together, producing one batch
    // of results. For B batches, C columns: [b0c0, b0c1, ..., b1c0, b1c1, ...]
    // =========================================================================
    // Collect results: read B batches, each with C columns
    // Result order: [b0c0, b0c1, ... b0c(C-1), b1c0, b1c1, ... b(B-1)c(C-1)]
    task automatic collect_results(int B, int C, int expected_count);
        int collected;
        int timeout_cnt;
        int batch;
        logic any_available;

        $display("[TB] Collecting %0d results from FIFOs (B=%0d, C=%0d)", expected_count, B, C);
        collected = 0;
        timeout_cnt = 0;
        
        // Clear all rd_en signals
        for (int i = 0; i < NUM_COLS; i++) begin
            result_rd_en[i] = 1'b0;
        end

        // Read B batches, each batch reads from columns 0 to C-1
        for (batch = 0; batch < B && timeout_cnt < 100000; batch++) begin
            // Wait for data to be available in column 0
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

            // Assert rd_en for columns 0 to C-1
            for (int c = 0; c < NUM_COLS; c++) begin
                result_rd_en[c] = (c < C) ? 1'b1 : 1'b0;
            end

            @(posedge clk);  // Cycle N: FIFO latches data and advances ptr
            
            // Deassert rd_en
            for (int c = 0; c < NUM_COLS; c++) begin
                result_rd_en[c] = 1'b0;
            end
            
            @(posedge clk);  // Cycle N+1: Data appears on output

            // Collect results from columns 0 to C-1
            for (int c = 0; c < C && collected < expected_count; c++) begin
                collected_results[collected] = result_data[c];
                collected++;
            end
            timeout_cnt++;
        end

        num_results_collected = collected;
        $display("[TB] Collection complete: %0d results", collected);
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
    logic [15:0] golden_results [0:1023];
    int golden_count;

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
        while (!$feof(fd) && idx < 1024) begin
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

    task automatic load_golden_block(string filename, output logic [15:0] golden_data [0:255], output int count);
        integer fd;
        string line_str;
        logic [15:0] value;
        int idx;

        fd = $fopen(filename, "r");
        if (fd == 0) begin
            $display("[TB] ERROR: Cannot open golden block file %s", filename);
            count = 0;
            return;
        end

        idx = 0;
        while (!$feof(fd) && idx < 256) begin
            if ($fgets(line_str, fd)) begin
                if ($sscanf(line_str, "%h", value) == 1) begin
                    golden_data[idx] = value;
                    idx++;
                end
            end
        end
        $fclose(fd);
        count = idx;
        $display("[TB] Loaded %0d golden values from block file", count);
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
        string left_file, right_file;
        int expected_results;
        logic pass;
        logic [15:0] golden_block [0:NUM_COLS-1][0:255];  // Store golden for each block
        int golden_block_count [0:NUM_COLS-1];

        $display("");
        $display("======================================================================");
        $display("  Test: %s (B=%0d, C=%0d, V=%0d, multi=%0d, row=%0d)",
                 cfg.name, cfg.B, cfg.C, cfg.V, cfg.multi_file, cfg.row_id);
        $display("======================================================================");

        // Calculate expected results
        expected_results = cfg.B * cfg.C;
        $display("[TB] Expected results: %0d", expected_results);

        // Reset DUT between tests
        mc_cmd_op = OPC_NOP;
        num_results_collected = 0;
        for (int i = 0; i < NUM_COLS; i++) result_rd_en[i] = 1'b0;

        // Apply reset pulse to clear FIFOs and state
        rstn = 1'b0;
        repeat(5) @(posedge clk);
        rstn = 1'b1;
        repeat(5) @(posedge clk);

        // Load data files based on mode
        if (cfg.multi_file) begin
            // Multi-file mode: load from subdirectory
            $display("[TB] Loading multi-file test data from %s/", cfg.name);

            // Load left (activations)
            left_file = {HEX_PATH, cfg.name, "/left_", $sformatf("%0d", cfg.row_id), ".hex"};
            $display("[TB] Loading left file: %s", left_file);
            load_memory_block_hex(left_file, left_exp_data, left_man_data, left_lines_loaded);
            $display("[TB] Loaded %0d lines from left file", left_lines_loaded);

            // Load right (weights) - one file per physical column
            for (int col = 0; col < NUM_COLS; col++) begin
                right_file = {HEX_PATH, cfg.name, "/right_", $sformatf("%0d_%0d", cfg.row_id, col), ".hex"};
                $display("[TB] Loading right file %0d: %s", col, right_file);
                load_memory_block_hex(right_file, right_exp_data[col], right_man_data[col], right_lines_loaded[col]);
                $display("[TB] Loaded %0d lines from right file %0d", right_lines_loaded[col], col);
            end

            // Load golden files - one per physical column block
            for (int col = 0; col < NUM_COLS; col++) begin
                golden_file = {HEX_PATH, cfg.name, "/golden_", cfg.name, "_",
                              $sformatf("%0d_%0d", cfg.row_id, col), ".hex"};
                $display("[TB] Loading golden file %0d: %s", col, golden_file);
                load_golden_block(golden_file, golden_block[col], golden_block_count[col]);
            end
        end else begin
            // Single-file mode (legacy)
            left_file = {HEX_PATH, "left.hex"};
            load_memory_block_hex(left_file, left_exp_data, left_man_data, left_lines_loaded);

            right_file = {HEX_PATH, "right.hex"};
            load_memory_block_hex(right_file, right_exp_data[0], right_man_data[0], right_lines_loaded[0]);

            golden_file = {HEX_PATH, cfg.name, ".hex"};
            load_golden_file(golden_file);
        end

        // Write activations
        write_activations(cfg.B, cfg.V);

        // Write weights
        if (cfg.multi_file) begin
            write_weights_multifile(cfg.C, cfg.V);
        end else begin
            write_weights_singlefile(cfg.C, cfg.V);
        end

        // Issue MATMUL
        issue_matmul(cfg.B, cfg.C, cfg.V);

        // Concurrent drain: Read FIFOs using column group structure
        // RTL outputs: for each (batch, column_group), pushes to all NUM_COLS FIFOs
        // For partial column groups (C not divisible by NUM_COLS), pop ALL FIFOs
        // but only keep the first 'active_cols' results
        $display("[TB] Starting concurrent result collection...");
        begin
            int collected;
            int timeout_cnt;
            logic done_seen;
            int num_col_groups;
            int active_cols;
            int logical_col;

            collected = 0;
            timeout_cnt = 0;
            done_seen = 1'b0;

            // Calculate column groups: ceil(C / NUM_COLS)
            num_col_groups = (cfg.C + NUM_COLS - 1) / NUM_COLS;
            $display("[TB] Column groups: %0d (C=%0d, NUM_COLS=%0d)", num_col_groups, cfg.C, NUM_COLS);

            // Iterate: for each batch, for each column group
            for (int b = 0; b < cfg.B && timeout_cnt < 500000; b++) begin
                for (int cg = 0; cg < num_col_groups && timeout_cnt < 500000; cg++) begin
                    // Calculate active columns for this column group
                    // Last group may be partial
                    if (cg == num_col_groups - 1) begin
                        active_cols = cfg.C - cg * NUM_COLS;  // Remainder
                    end else begin
                        active_cols = NUM_COLS;  // Full group
                    end

                    // Wait for data in FIFO 0 (all FIFOs fill together)
                    while (result_empty[0] && timeout_cnt < 500000) begin
                        @(posedge clk);
                        timeout_cnt++;

                        // Check for matmul_done
                        if (matmul_done && !done_seen) begin
                            done_seen = 1'b1;
                            $display("[TB] matmul_done at cycle %0d, collected=%0d/%0d",
                                     timeout_cnt, collected, expected_results);
                        end
                    end

                    if (timeout_cnt >= 500000) break;

                    // Pop ALL NUM_COLS FIFOs (including garbage for partial groups)
                    // Assert rd_en for all FIFOs
                    for (int f = 0; f < NUM_COLS; f++) begin
                        result_rd_en[f] = 1'b1;
                    end

                    @(posedge clk);  // FIFO latches rd_en
                    timeout_cnt++;

                    // Deassert rd_en
                    for (int f = 0; f < NUM_COLS; f++) begin
                        result_rd_en[f] = 1'b0;
                    end

                    @(posedge clk);  // Data now stable on outputs
                    timeout_cnt++;

                    // Capture only valid results (first active_cols FIFOs)
                    for (int f = 0; f < active_cols; f++) begin
                        logical_col = cg * NUM_COLS + f;
                        collected_results[collected] = result_data[f];
                        collected++;
                    end

                    // Discard garbage from FIFOs active_cols to NUM_COLS-1
                    // (they were already popped, just don't store them)
                end
            end

            num_results_collected = collected;

            if (timeout_cnt >= 500000) begin
                $display("[TB] ERROR: Timeout! collected=%0d/%0d", collected, expected_results);
            end else begin
                $display("[TB] Collection complete: %0d results in %0d cycles",
                         collected, timeout_cnt);
            end
        end

        // Compare results
        if (cfg.multi_file) begin
            // Multi-file mode: reorganize golden data from per-column to sequential
            // Collected results are in order: [cg0_col0, cg0_col1, cg0_col2, cg0_col3, cg1_col0, ...]
            // Golden blocks are: [cg0_col0, cg1_col0, cg2_col0, ...], [cg0_col1, cg1_col1, ...]
            // Reorganize golden to match collected order
            int num_col_groups = cfg.C / NUM_COLS;
            int golden_idx = 0;

            for (int cg = 0; cg < num_col_groups; cg++) begin
                for (int col = 0; col < NUM_COLS; col++) begin
                    golden_results[golden_idx] = golden_block[col][cg];
                    golden_idx++;
                end
            end
            golden_count = golden_idx;

            compare_results(expected_results, pass);
        end else begin
            compare_results(expected_results, pass);
        end

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
        $display("  Compute Engine 2D Testbench");
        $display("======================================================================");

        // Initialize signals
        rstn = 1'b0;
        mc_cmd_op = OPC_NOP;
        cmd_id = 8'd0;
        cmd_payload_word1 = 32'd0;
        cmd_payload_word2 = 32'd0;
        cmd_payload_word3 = 32'd0;
        man_left_wr_addr = '0;
        man_left_wr_en = 1'b0;
        man_left_wr_data = '0;
        exp_left_wr_addr = '0;
        exp_left_wr_en = 1'b0;
        exp_left_wr_data = '0;
        wt_wr_en = 1'b0;
        wt_wr_man = '0;
        wt_wr_exp = '0;
        wt_mlp_sel = 3'd0;
        wt_nv_idx = 10'd0;
        for (int i = 0; i < NUM_COLS; i++) result_rd_en[i] = 1'b0;
        tests_run = 0;
        tests_passed = 0;

        // Reset
        repeat(10) @(posedge clk);
        rstn = 1'b1;
        repeat(10) @(posedge clk);

        // Run test suite (each test loads its own data files)
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
        $display("======================================================================");

        if (tests_passed == tests_run) begin
            $display("  ALL TESTS PASSED!");
        end else begin
            $display("  SOME TESTS FAILED!");
        end
        $display("======================================================================");

        #100;
        $finish;
    end

    // =========================================================================
    // Timeout Watchdog
    // =========================================================================
    initial begin
        #(TIMEOUT_NS);
        $display("[TB] ERROR: Simulation timeout!");
        $finish;
    end

endmodule
