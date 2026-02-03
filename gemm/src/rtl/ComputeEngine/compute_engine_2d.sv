// ------------------------------------------------------------------
// Compute Engine 2D
//
// Top-level wrapper integrating:
//   - comp_row_bram: L1 memory for ACTIVATIONS ONLY (left matrix)
//   - comp_MLPStack: MLP compute array with 16 columns (4 stacks each)
//   - comp_MLPStack_oFIFO: 16 result FIFOs for downstream consumption
//
// Memory Architecture:
//   - row_bram: Holds activations (left matrix) ONLY
//   - mlp_bram: Holds weights (right matrix) - written directly via line-by-line interface
//
// Command Interface:
//   - Receives packed command payload from Master Control
//   - Depacks and registers parameters internally
//   - Returns immediate ACK on command receipt
//   - Updates o_ce_id when computation completes
//
// BCV Dimensions (from MATMUL command):
//   - B (left_ugd_len): Number of activation batches
//   - C (right_ugd_len): Number of columns (may exceed 16)
//   - V (vec_len): Number of NVs to accumulate per output
//
// Simple Counter Architecture:
//   - b_cnt: Batch counter (0..B-1)
//   - cg_cnt: Column group counter (0..G-1, where G = ceil(C/16))
//   - v_cnt: NV counter (0..V-1)
//   - l_cnt: Line counter (0..3)
//
// 1/22/2026 - Refactored: simplified interface and FSM
// ------------------------------------------------------------------

`timescale 1ps / 1ps
`default_nettype none

module compute_engine_2d
import gemm_pkg::*;
#(
    parameter int MATMUL_ID = 0,                // CE ID for debugging
    parameter int MAN_WIDTH = 256,              // Mantissa line width (256 bits = 32 x 8-bit)
    parameter int EXP_WIDTH = 8,                // Exponent width
    parameter int BRAM_DEPTH = 512,             // row_bram depth (activations only)
    parameter int ADDR_WIDTH = $clog2(BRAM_DEPTH),
    parameter int NUM_MLPS = 8,                 // Number of MLP primitives (2 columns each)
    parameter int NUM_COLS = 2*NUM_MLPS,        // Number of MLP columns (fixed)
    parameter int MLP_SEL_WIDTH = $clog2(NUM_MLPS),  // Width for MLP selection
    parameter int RESULT_FIFO_DEPTH = 512       // Result FIFO depth per column (increased for large batch support)
) (
    input  logic                     i_clk,
    input  logic                     i_reset_n,

    // =========================================================================
    // Master Control Interface (MATMUL command) - Raw Opcode with Internal Detection
    // Consistent with dispatcher_control_2d and result_collector_2d
    // =========================================================================
    input  logic [7:0]               i_mc_cmd_op,            // Raw opcode from MC (edge-detected internally)
    input  logic [7:0]               i_cmd_id,               // Command ID
    input  logic [31:0]              i_cmd_payload_word1,    // {left_addr[15:0], right_addr[15:0]}
    input  logic [31:0]              i_cmd_payload_word2,    // {B[15:0], C[15:0]}
    input  logic [31:0]              i_cmd_payload_word3,    // {V[15:0], flags[15:0]}
    output logic                     o_ce_ack_matmul,        // Immediate ACK (renamed for consistency)
    output logic [7:0]               o_ce_id,                // Last completed cmd_id
    output logic                     o_matmul_done,          // Done pulse

    // =========================================================================
    // row_bram Write Interface (Activations ONLY)
    // External controller fills row_bram with left matrix before MATMUL
    // =========================================================================
    input  logic [ADDR_WIDTH-1:0]    i_man_left_wr_addr,
    input  logic                     i_man_left_wr_en,
    input  logic [MAN_WIDTH-1:0]     i_man_left_wr_data,
    input  logic [ADDR_WIDTH-1:0]    i_exp_left_wr_addr,
    input  logic                     i_exp_left_wr_en,
    input  logic [EXP_WIDTH-1:0]     i_exp_left_wr_data,

    // =========================================================================
    // MLP BRAM Weight Write Interface (VECTORIZED)
    // External controller writes weights directly to mlp_bram
    // =========================================================================
    input  logic                     i_wt_wr_en,
    output logic                     o_wt_wr_ready,
    input  logic [255:0]             i_wt_wr_man,
    input  logic [EXP_WIDTH-1:0]     i_wt_wr_exp,
    input  logic [MLP_SEL_WIDTH-1:0] i_wt_mlp_sel,
    input  logic [9:0]               i_wt_nv_idx,

    // =========================================================================
    // Result FIFO Interface (16 parallel FP16 outputs)
    // Using unpacked arrays for compatibility with parent module wiring
    // =========================================================================
    output logic [FP16_WIDTH-1:0]    o_result_data [NUM_COLS-1:0],
    input  logic                     i_result_rd_en [NUM_COLS-1:0],
    output logic                     o_result_empty [NUM_COLS-1:0],
    output logic                     o_result_afull,

    // =========================================================================
    // Debug Interface
    // =========================================================================
    output logic [3:0]               o_ce_state,
    output logic [15:0]              o_result_count
);

    // =========================================================================
    // Opcode Constants (must match gemm_pkg)
    // =========================================================================
    localparam logic [7:0] OPC_MATMUL = 8'hF2;

    // =========================================================================
    // State Machine - Simple 2-State Design
    // =========================================================================
    typedef enum logic [1:0] {
        CE_IDLE    = 2'd0,
        CE_RUNNING = 2'd1
    } ce_state_t;

    ce_state_t state_reg, state_next;

    // =========================================================================
    // Internal Opcode Edge Detection (consistent with dispatcher_control_2d)
    // =========================================================================
    logic [7:0] cmd_op_prev;
    logic       matmul_detected;

    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            cmd_op_prev <= 8'h00;
        end else begin
            cmd_op_prev <= i_mc_cmd_op;
        end
    end

    // Detect MATMUL opcode transition (rising edge)
    assign matmul_detected = (i_mc_cmd_op == OPC_MATMUL) && (cmd_op_prev != OPC_MATMUL);

    // =========================================================================
    // Registered Command Parameters (depacked from payload words)
    // Per MULTI_ROW_REFERENCE.md: B, C, V are all 16-bit fields
    // =========================================================================
    logic [15:0] left_addr_reg;      // Left base address for row_bram reads
    logic [15:0] right_addr_reg;     // Right base address for mlp_bram reads
    logic [15:0] B_reg;              // Number of activation batches (16-bit per spec)
    logic [15:0] C_reg;              // Number of columns (16-bit per spec)
    logic [15:0] V_reg;              // Number of NVs per dot product (16-bit per spec)
    logic [7:0]  cmd_id_reg;         // Registered command ID

    // =========================================================================
    // Column Group Support (for C > NUM_COLS)
    // Uses shift-based division for power-of-2 NUM_COLS values (4, 8, 16)
    // =========================================================================
    localparam int NUM_COLS_SHIFT = $clog2(NUM_COLS);  // 2 for 4, 3 for 8, 4 for 16
    logic [11:0] num_col_groups;     // G = ceil(C / NUM_COLS), 12-bit for 16-bit C

    always_comb begin
        // For power-of-2 NUM_COLS: use shift instead of division
        // C_reg is 16-bit, result fits in 12 bits (max 65535/16 = 4096)
        num_col_groups = (C_reg + NUM_COLS[15:0] - 16'd1) >> NUM_COLS_SHIFT;
        if (num_col_groups == 12'd0)
            num_col_groups = 12'd1;
    end

    // =========================================================================
    // Valid Column Mask for FIFO Alignment
    // =========================================================================
    // For C that doesn't divide evenly by NUM_COLS, the last column group has
    // fewer valid columns. Only push to FIFOs for valid columns to keep them aligned.
    logic [NUM_COLS-1:0] valid_cols_mask;
    logic [15:0] cols_in_group;
    
    always_comb begin
        // Calculate how many columns are valid in current column group
        // cols_in_group = min(NUM_COLS, C - cg_cnt * NUM_COLS)
        cols_in_group = C_reg - (cg_cnt << NUM_COLS_SHIFT);
        if (cols_in_group > NUM_COLS[15:0])
            cols_in_group = NUM_COLS[15:0];
        
        // Generate mask: (1 << cols_in_group) - 1
        // For cols_in_group=4: mask=1111, for cols_in_group=1: mask=0001
        valid_cols_mask = (NUM_COLS'(1) << cols_in_group) - NUM_COLS'(1);
    end

    // =========================================================================
    // Simple Counters (widened to match 16-bit B, C, V parameters)
    // =========================================================================
    logic [15:0] b_cnt;              // 0..B-1 (outer loop, 16-bit for full B range)
    logic [15:0] cg_cnt;             // 0..G-1 (column group, 16-bit)
    logic [15:0] v_cnt;              // 0..V-1 (NV within dot product, 16-bit for full V range)
    logic [1:0]  l_cnt;              // 0..3 (line within NV)

    // =========================================================================
    // Activation Interface Signals
    // =========================================================================
    logic        act_valid;
    logic        act_ready;
    logic        new_dot;
    logic        last_nv;
    logic        last_matmul;
    logic [255:0] act_payload_man;
    logic [7:0]   act_payload_exp;

    // =========================================================================
    // row_bram Read Signals
    // =========================================================================
    logic [31:0]          nv_left_exp_raw;
    logic [MAN_WIDTH-1:0] nv_left_man [0:3];
    logic [31:0]          nv_left_exp;       // Converted E5->E8
    logic [6:0]           nv_left_rd_idx;

    // =========================================================================
    // BRAM Pipeline Signals (for 1-cycle read latency)
    // =========================================================================
    logic        bram_rd_issued;       // Read address presented to BRAM
    logic        bram_data_valid;      // BRAM data valid (1 cycle after rd_issued)
    logic        new_dot_d1;           // Delayed control signals to match data
    logic        last_nv_d1;
    logic        last_matmul_d1;
    logic [1:0]  l_cnt_d1;             // Delayed l_cnt for mux selection
    logic [9:0]  rd_base_addr_d1;      // Delayed MLP read base address

    // =========================================================================
    // MLPStack Signals
    // =========================================================================
    logic [15:0] mlp_result_fp16 [NUM_COLS-1:0];
    logic        mlp_result_push;
    logic        mlp_result_fifo_full;
    logic        mlp_result_fifo_afull;  // Almost-full for backpressure (provides pipeline headroom)
    logic [NUM_COLS-1:0] mlp_result_valid_mask;  // Valid cols mask (delayed from MLPStack)
    logic [9:0]  rd_base_addr_eff;

    // =========================================================================
    // Result Tracking
    // =========================================================================
    logic [15:0] result_count_reg;
    logic [15:0] expected_results;
    logic        compute_done;
    logic        all_results_generated;  // All results pushed to FIFOs
    logic        all_fifos_empty;        // All output FIFOs are empty

    // Expected results = B * G
    assign expected_results = B_reg * num_col_groups;

    // Check if all output FIFOs are empty
    always_comb begin
        all_fifos_empty = 1'b1;
        for (int i = 0; i < NUM_COLS; i++) begin
            all_fifos_empty = all_fifos_empty & o_result_empty[i];
        end
    end

    // Compute done = all results generated AND all FIFOs drained
    assign compute_done = all_results_generated & all_fifos_empty;

    // =========================================================================
    // Exponent Conversion: GFP5 -> BFP8E8 for MLP BFP mode
    // E5 bias = 15, E8 bias = 133, delta = 118
    // =========================================================================
    always_comb begin
        for (int i = 0; i < 4; i++) begin
            nv_left_exp[i*8 +: 8] = nv_left_exp_raw[i*8 +: 8] + 8'd118;
        end
    end

    // =========================================================================
    // State Transition Logic (combinational)
    // =========================================================================
    always_comb begin
        state_next = state_reg;
        case (state_reg)
            CE_IDLE: begin
                if (matmul_detected)
                    state_next = CE_RUNNING;
            end
            CE_RUNNING: begin
                // Use current last_matmul - counter values match the current output
                if (act_valid && act_ready && last_matmul)
                    state_next = CE_IDLE;
            end
            default: state_next = CE_IDLE;
        endcase
    end

    // =========================================================================
    // Control Signal Generation (combinational)
    // =========================================================================
    // bram_rd_issued: We issue a read when in RUNNING state and downstream is ready
    // (or when starting the first read before handshake)
    assign bram_rd_issued = (state_reg == CE_RUNNING) && (act_ready || !bram_data_valid);

    // Control signals computed from current counter state (before BRAM latency)
    assign new_dot     = (v_cnt == 16'd0) && (l_cnt == 2'd0);
    assign last_nv     = (v_cnt == (V_reg - 16'd1)) && (l_cnt == 2'd3);
    assign last_matmul = (b_cnt == (B_reg - 16'd1)) && (cg_cnt == (num_col_groups - 16'd1)) && last_nv;

    // act_valid: For registered BRAM reads, gate with bram_data_valid
    // This ensures we wait for valid data after NV transitions
    assign act_valid   = (state_reg == CE_RUNNING) && bram_data_valid;

    // =========================================================================
    // NV Transition Detection
    // =========================================================================
    // Detect when we're finishing an NV and need new data
    // Stall when l=3 handshake UNLESS it's the last operation (last_matmul)
    // After l=3, counters update but BRAM read was with old counters - need to wait
    logic nv_transition;
    assign nv_transition = (l_cnt == 2'd3) && (act_valid && act_ready) && !last_matmul;

    // =========================================================================
    // BRAM Pipeline Registers (for 1-cycle read latency)
    // =========================================================================
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            bram_data_valid  <= 1'b0;
            new_dot_d1       <= 1'b0;
            last_nv_d1       <= 1'b0;
            last_matmul_d1   <= 1'b0;
            l_cnt_d1         <= 2'd0;
            rd_base_addr_d1  <= 10'd0;
        end else begin
            // Pipeline the data valid and control signals to match BRAM latency
            if (state_reg == CE_IDLE) begin
                // Clear pipeline when not running
                bram_data_valid  <= 1'b0;
                new_dot_d1       <= 1'b0;
                last_nv_d1       <= 1'b0;
                last_matmul_d1   <= 1'b0;
                l_cnt_d1         <= 2'd0;
                rd_base_addr_d1  <= 10'd0;
            end else if (nv_transition) begin
                // When transitioning to a new NV, invalidate current data
                // Wait for new read with updated counters
                bram_data_valid  <= 1'b0;
            end else if (bram_rd_issued) begin
                // Advance pipeline when read is issued
                bram_data_valid  <= 1'b1;
                new_dot_d1       <= new_dot;
                last_nv_d1       <= last_nv;
                last_matmul_d1   <= last_matmul;
                l_cnt_d1         <= l_cnt;
                rd_base_addr_d1  <= rd_base_addr_eff;
            end else if (act_valid && act_ready) begin
                // Data consumed, wait for next
                bram_data_valid <= 1'b0;
            end
        end
    end

    // =========================================================================
    // Sequential Logic: State Update, Counters, Parameter Registration
    // =========================================================================
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            state_reg       <= CE_IDLE;
            b_cnt           <= 16'd0;
            cg_cnt          <= 16'd0;
            v_cnt           <= 16'd0;
            l_cnt           <= 2'd0;
            left_addr_reg   <= 16'd0;
            right_addr_reg  <= 16'd0;
            B_reg           <= 16'd0;
            C_reg           <= 16'd0;
            V_reg           <= 16'd0;
            cmd_id_reg      <= 8'd0;
            result_count_reg <= 16'd0;
            all_results_generated <= 1'b0;
        end else begin
            state_reg    <= state_next;

            case (state_reg)
                CE_IDLE: begin
                    if (matmul_detected) begin
                        // Depack and register command parameters
                        // Per MULTI_ROW_REFERENCE.md MATMUL command encoding:
                        //   word1 = {left_addr[15:0], right_addr[15:0]}
                        //   word2 = {left_len[15:0], right_len[15:0]} where B=left_len, C=right_len
                        //   word3 = {ugd_len[15:0], flags[15:0]} where V=ugd_len
                        // Extract FULL 16-bit fields (not just low byte!)
                        left_addr_reg  <= i_cmd_payload_word1[31:16];
                        right_addr_reg <= i_cmd_payload_word1[15:0];
                        B_reg          <= i_cmd_payload_word2[31:16];  // Full 16-bit B
                        C_reg          <= i_cmd_payload_word2[15:0];   // Full 16-bit C
                        V_reg          <= i_cmd_payload_word3[31:16];  // Full 16-bit V
                        cmd_id_reg     <= i_cmd_id;

                        // synthesis translate_off
                        `ifdef DEBUG_COMPUTE
                        $display("[CE2D] @%0t MATMUL received: id=%0d, B=%0d, C=%0d, V=%0d, left_addr=%0d, right_addr=%0d",
                                 $time, i_cmd_id,
                                 i_cmd_payload_word2[31:16],  // B (full 16-bit)
                                 i_cmd_payload_word2[15:0],   // C (full 16-bit)
                                 i_cmd_payload_word3[31:16],  // V (full 16-bit)
                                 i_cmd_payload_word1[31:16],  // left_addr
                                 i_cmd_payload_word1[15:0]);  // right_addr
                        $display("[CE2D]   word1=0x%08x, word2=0x%08x, word3=0x%08x",
                                 i_cmd_payload_word1, i_cmd_payload_word2, i_cmd_payload_word3);
                        `endif
                        // synthesis translate_on

                        // Reset counters and flags
                        b_cnt  <= 16'd0;
                        cg_cnt <= 16'd0;
                        v_cnt  <= 16'd0;
                        l_cnt  <= 2'd0;
                        result_count_reg <= 16'd0;
                        all_results_generated <= 1'b0;
                    end
                end

                CE_RUNNING: begin
                    // Advance counters on handshake
                    if (act_valid && act_ready) begin
                        // l_cnt: innermost (0..3)
                        if (l_cnt == 2'd3) begin
                            l_cnt <= 2'd0;
                            // v_cnt: (0..V-1)
                            if (v_cnt == (V_reg - 16'd1)) begin
                                v_cnt <= 16'd0;
                                // cg_cnt: (0..G-1)
                                if (cg_cnt == (num_col_groups - 16'd1)) begin
                                    cg_cnt <= 16'd0;
                                    // b_cnt: outermost (0..B-1)
                                    b_cnt <= b_cnt + 16'd1;
                                end else begin
                                    cg_cnt <= cg_cnt + 16'd1;
                                end
                            end else begin
                                v_cnt <= v_cnt + 16'd1;
                            end
                        end else begin
                            l_cnt <= l_cnt + 2'd1;
                        end
                    end
                end

                default: ;
            endcase

            // Result counting - track mlp_result_push
            if (mlp_result_push) begin
                result_count_reg <= result_count_reg + 16'd1;
                if (result_count_reg == (expected_results - 16'd1)) begin
                    all_results_generated <= 1'b1;
                end
            end
        end
    end

    // =========================================================================
    // ACK and ID Outputs
    // =========================================================================
    // Immediate ACK when command is accepted (IDLE -> RUNNING transition)
    logic ce_ack_matmul_reg;
    logic [7:0] ce_id_reg;

    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            ce_ack_matmul_reg <= 1'b0;
            ce_id_reg         <= 8'd0;
        end else begin
            ce_ack_matmul_reg <= 1'b0;
            if (state_reg == CE_IDLE && matmul_detected) begin
                ce_ack_matmul_reg <= 1'b1;
            end
            if (compute_done) begin
                ce_id_reg <= cmd_id_reg;
            end
        end
    end

    assign o_ce_ack_matmul = ce_ack_matmul_reg;
    assign o_ce_id       = ce_id_reg;
    assign o_matmul_done = compute_done;
    assign o_ce_state    = {2'b0, state_reg};
    assign o_result_count = result_count_reg;

    // =========================================================================
    // Row BRAM Read Index Calculation
    // =========================================================================
    // Index = base/4 + batch * V + v_cnt
    // (base is line address, divide by 4 to get NV index)
    always_comb begin
        nv_left_rd_idx = left_addr_reg[8:2] + (b_cnt * V_reg) + v_cnt;
    end

    // =========================================================================
    // MLP BRAM Read Base Address Calculation
    // =========================================================================
    // rd_base = base + cg_cnt * V * 8
    // Each column group uses V*8 addresses (V NVs * 8 MLPs * 2 addresses/MLP interleaved)
    always_comb begin
        rd_base_addr_eff = right_addr_reg[9:0] + (cg_cnt * V_reg * 10'd8);
    end

    // =========================================================================
    // Activation Payload Mux (select line within NV based on l_cnt)
    // Use current l_cnt - BRAM outputs all chunks, we select based on current counter
    // =========================================================================
    always_comb begin
        case (l_cnt)
            2'd0: begin
                act_payload_man = nv_left_man[0];
                act_payload_exp = nv_left_exp[7:0];
            end
            2'd1: begin
                act_payload_man = nv_left_man[1];
                act_payload_exp = nv_left_exp[15:8];
            end
            2'd2: begin
                act_payload_man = nv_left_man[2];
                act_payload_exp = nv_left_exp[23:16];
            end
            2'd3: begin
                act_payload_man = nv_left_man[3];
                act_payload_exp = nv_left_exp[31:24];
            end
        endcase
    end

    // =========================================================================
    // Weight Exponent Conversion
    // =========================================================================
    logic [7:0] wt_line_exp_e8;
    assign wt_line_exp_e8 = i_wt_wr_exp + 8'd118;

    // =========================================================================
    // row_bram Instance
    // =========================================================================
    comp_row_bram #(
        .MAN_WIDTH(MAN_WIDTH),
        .EXP_WIDTH(EXP_WIDTH),
        .BRAM_DEPTH(BRAM_DEPTH),
        .ADDR_WIDTH(ADDR_WIDTH)
    ) u_row_bram (
        .i_clk(i_clk),
        .i_reset_n(i_reset_n),
        .i_man_left_wr_addr(i_man_left_wr_addr),
        .i_man_left_wr_en(i_man_left_wr_en),
        .i_man_left_wr_data(i_man_left_wr_data),
        .i_exp_left_wr_addr(i_exp_left_wr_addr),
        .i_exp_left_wr_en(i_exp_left_wr_en),
        .i_exp_left_wr_data(i_exp_left_wr_data),
        .i_nv_left_rd_idx(nv_left_rd_idx),
        .o_nv_left_exp(nv_left_exp_raw),
        .o_nv_left_man(nv_left_man)
    );

    // =========================================================================
    // comp_MLPStack Instance
    // =========================================================================
    comp_MLPStack #(
        .NUM_MLPS(NUM_MLPS),
        .MLP_SEL_WIDTH(MLP_SEL_WIDTH)
    ) u_mlp_stack (
        .clk(i_clk),
        .rstn(i_reset_n),
        // Use current address - matches the current counter state
        .i_rd_base_addr(rd_base_addr_eff),
        .i_wt_wr_en(i_wt_wr_en),
        .i_nv_right_man(i_wt_wr_man),
        .i_nv_right_exp(wt_line_exp_e8),
        .i_wt_mlp_sel(i_wt_mlp_sel),
        .i_wt_wr_addr(i_wt_nv_idx),
        .i_act_valid(act_valid),
        .o_act_ready(act_ready),
        .i_nv_left_man(act_payload_man),
        .i_nv_left_exp(act_payload_exp),
        // Use current control signals - BRAM outputs all chunks, counter matches current output
        .i_new_dot(new_dot),
        .i_last_nv(last_nv),
        .i_last_matmul(last_matmul),
        .i_valid_cols_mask(valid_cols_mask),
        .o_result_fp16(mlp_result_fp16),
        .o_result_push(mlp_result_push),
        .o_valid_cols_mask(mlp_result_valid_mask),
        // Use AFULL for backpressure to provide headroom for pipeline latency (~6 cycles)
        // AFULL triggers at (DEPTH - 10%), giving ~7 entries headroom for DEPTH=64
        .i_result_fifo_full(mlp_result_fifo_afull)
    );

    // =========================================================================
    // comp_MLPStack_oFIFO Instance (16 result FIFOs)
    // =========================================================================
    comp_MLPStack_oFIFO #(
        .NUM_COLS(NUM_COLS),
        .FIFO_DEPTH(RESULT_FIFO_DEPTH)
    ) u_result_fifos (
        .clk(i_clk),
        .rstn(i_reset_n),
        .i_result_fp16(mlp_result_fp16),
        .i_result_push(mlp_result_push),
        .i_valid_cols_mask(mlp_result_valid_mask),
        .o_result_fifo_full(mlp_result_fifo_full),  // Full flag (unused, but kept for monitoring)
        .o_result_data(o_result_data),
        .i_result_rd_en(i_result_rd_en),
        .o_result_empty(o_result_empty),
        .o_result_afull(mlp_result_fifo_afull)      // AFULL: used for MLPStack backpressure
    );

    // Export afull for external monitoring (to master_control for command flow control)
    assign o_result_afull = mlp_result_fifo_afull;

    // =========================================================================
    // Weight Write Ready - MLPStack has no backpressure
    // =========================================================================
    assign o_wt_wr_ready = 1'b1;

endmodule

`default_nettype wire
