// ------------------------------------------------------------------
// Master Control Module
//
// Purpose: Unified command processor for 2-D GEMM Architecture
// Features:
//  - Reads commands from cmd_fifo (header + payload)
//  - Parses command opcodes: FETCH, DISP, MATMUL, WAIT_DISP, WAIT_MATMUL, READOUT
//  - Routes to dispatcher_control (FETCH/DISP), compute_engine (MATMUL), and result_collector (READOUT)
//
// Author: Junhao Pan
// Date: 01/20/2026
// ------------------------------------------------------------------

module master_control_2d
import gemm_pkg::*;
#(
    parameter integer NUM_MLPS = 8,     // Number of MLPS in a MLPRow
    parameter integer STACK_DEPTH = 4,  // Number of MLPRows in a MLPStack
    parameter integer NUM_ROWS = 16     // Number of Dispatcher Control + Compute Engine in the GEMM, hardcoded to 16 which is the number of available GDDR6 Channels.
) 
(
    input  logic        i_clk,
    input  logic        i_reset_n,

    // Command FIFO Interface
    input  logic [cmd_buf_width_gp-1:0] i_cmd_fifo_rdata,
    input  logic                        i_cmd_fifo_empty,
    input  logic [12:0]                 i_cmd_fifo_count,
    output logic                        o_cmd_fifo_ren,
    
    // CMD out to Exec Units
    output logic [7:0]                   o_mc_cmd_op,                       // should be the same every row
    output logic [7:0]                   o_mc_cmd_id,                       // should be the same every row
    output logic [31:0]                  o_mc_cmd_payload_word1[NUM_ROWS-1:0],  // per-row payload (V partitioned)
    output logic [31:0]                  o_mc_cmd_payload_word2[NUM_ROWS-1:0],  // per-row payload (V partitioned)
    output logic [31:0]                  o_mc_cmd_payload_word3[NUM_ROWS-1:0],  // per-row payload (V partitioned)


    // Dispatcher Control Interface (FETCH/DISP commands) - PER ROW
    input  logic [3:0]                  i_dc_state       [NUM_ROWS-1:0],  // Per-row DC state
    input  logic                        i_dc_ack_fetch   [NUM_ROWS-1:0],  // Per-row FETCH acknowledge
    input  logic                        i_dc_ack_disp    [NUM_ROWS-1:0],  // Per-row DISP acknowledge
    input  logic [7:0]                  i_dc_id          [NUM_ROWS-1:0],  // Per-row last served cmd_id

    // Compute Engine Interface (MATMUL command) - PER ROW
    input  logic [3:0]                  i_ce_state       [NUM_ROWS-1:0],  // Per-row CE state
    input  logic                        i_ce_ack_matmul  [NUM_ROWS-1:0],  // Per-row MATMUL acknowledge
    input  logic [7:0]                  i_ce_id          [NUM_ROWS-1:0],  // Per-row last served cmd_id
    input  logic                        i_ce_result_fifo_afull [NUM_ROWS-1:0],  // Per-row result FIFO almost-full

    // Result Collector Interface (READOUT command) - GLOBAL (reduces all rows)
    input  logic [3:0]                  i_rc_state,          // RC state (global)
    input  logic                        i_rc_ack_readout,    // READOUT acknowledge (global)
    input  logic [7:0]                  i_rc_id,             // Current READOUT cmd_id RC is serving

    // Debug Interface
    output logic [3:0]                  o_mc_state,

    // Extended Debug Interface (for hardware debugging)
    output logic [NUM_ROWS-1:0]         o_dbg_ce_ack_matmul_reg,  // Captured CE ACK bits
    output logic [NUM_ROWS-1:0]         o_dbg_dc_ack_fetch_reg,   // Captured DC ACK bits
    output logic                        o_dbg_cmd_valid           // Current command is valid
);

    // ===================================================================
    // State Machine Definition
    // ===================================================================
    // Simplified FSM: 128-bit wide FIFO allows single-cycle command read
    // ST_IDLE: Wait for FIFO data, assert rd_en
    // ST_WAIT_DATA: Wait 1 cycle for FIFO read latency
    // ST_DECODE: Extract 128-bit command, route to EXEC state
    typedef enum logic [3:0] {
        ST_IDLE             = 4'd0,
        ST_WAIT_DATA        = 4'd1,  // Wait 1 cycle for FIFO read latency
        ST_DECODE           = 4'd2,  // Decode 128-bit command in single cycle
        ST_EXEC_FETCH       = 4'd3,  // FETCH command (0xF0)
        ST_EXEC_DISP        = 4'd4,  // DISP command (0xF1)
        ST_EXEC_MATMUL      = 4'd5,  // MATMUL command (0xF2)
        ST_WAIT_DISP        = 4'd6,  // WAIT_DISP command (0xF3)
        ST_WAIT_MATMUL      = 4'd7,  // WAIT_MATMUL command (0xF4)
        ST_EXEC_READOUT     = 4'd8,  // READOUT command (0xF5)
        ST_CMD_COMPLETE     = 4'd9,  // Command complete, return to IDLE
        ST_ERROR            = 4'd15
    } state_t;


    state_t state_reg, state_next;

    // ===================================================================
    // OPCODEs
    // ===================================================================
    typedef enum logic [7:0] {
        CMD_FETCH           = 8'hF0,
        CMD_DISP            = 8'hF1,
        CMD_MATMUL          = 8'hF2,
        CMD_WAIT_DISP       = 8'hF3,
        CMD_WAIT_MATMUL     = 8'hF4,
        CMD_READOUT         = 8'hF5
    } cmd_opcodes_t;

    // ===================================================================
    // Internal Registers
    // ===================================================================

    // Original CMD from the FIFO for internal use
    logic [31:0] cmd_reg[3:0];

    // Command header fields
    logic [7:0]  cmd_op_reg;
    logic [7:0]  cmd_id_reg;

    // Only output valid opcode when in EXEC states (payload is ready)
    // This ensures DC/CE don't detect commands before payload is populated
    logic cmd_valid;
    assign cmd_valid = (state_reg == ST_EXEC_FETCH)  ||
                       (state_reg == ST_EXEC_DISP)   ||
                       (state_reg == ST_EXEC_MATMUL) ||
                       (state_reg == ST_WAIT_DISP)   ||
                       (state_reg == ST_WAIT_MATMUL) ||
                       (state_reg == ST_EXEC_READOUT);
    assign o_mc_cmd_op = cmd_valid ? cmd_op_reg : 8'h00;
    assign o_mc_cmd_id = cmd_id_reg;

    // Payload storage - per-row (V dimension partitioned across rows)
    logic [31:0] cmd_payload_word1_reg[NUM_ROWS-1:0];
    logic [31:0] cmd_payload_word2_reg[NUM_ROWS-1:0];
    logic [31:0] cmd_payload_word3_reg[NUM_ROWS-1:0];

    // Generate per-row output assignments
    for (genvar r = 0; r < NUM_ROWS; r++) begin : gen_cmd_outputs
        assign o_mc_cmd_payload_word1[r] = cmd_payload_word1_reg[r];
        assign o_mc_cmd_payload_word2[r] = cmd_payload_word2_reg[r];
        assign o_mc_cmd_payload_word3[r] = cmd_payload_word3_reg[r];
    end

    // Command FIFO read enable
    logic cmd_fifo_ren_reg;
    assign o_cmd_fifo_ren = cmd_fifo_ren_reg;

    // Command ACK logic - PER ROW (DC and CE are per-row, RC is global)
    logic dc_ack_fetch_reg  [NUM_ROWS-1:0];
    logic dc_ack_disp_reg   [NUM_ROWS-1:0];
    logic ce_ack_matmul_reg [NUM_ROWS-1:0];
    logic rc_ack_readout_reg;  // RC is global

    // Reduction signals: all rows acknowledged
    logic all_dc_ack_fetch;
    logic all_dc_ack_disp;
    logic all_ce_ack_matmul;

    // Generate reduction AND for all-rows-acknowledged signals
    always_comb begin
        all_dc_ack_fetch  = 1'b1;
        all_dc_ack_disp   = 1'b1;
        all_ce_ack_matmul = 1'b1;
        for (int r = 0; r < NUM_ROWS; r++) begin
            all_dc_ack_fetch  = all_dc_ack_fetch  & dc_ack_fetch_reg[r];
            all_dc_ack_disp   = all_dc_ack_disp   & dc_ack_disp_reg[r];
            all_ce_ack_matmul = all_ce_ack_matmul & ce_ack_matmul_reg[r];
        end
    end

    // WAIT Command ID tracking
    logic [7:0] wait_disp_id_reg;
    logic [7:0] wait_matmul_id_reg;
    
    // WAIT completion: all rows have completed up to wait_id
    logic all_dc_wait_complete;
    logic all_ce_wait_complete;
    
    // Additional release condition: all rows are IDLE (state=0)
    // If the unit is idle, it has finished its work even if ID wasn't updated
    logic all_dc_idle;
    logic all_ce_idle;
    
    always_comb begin
        all_dc_wait_complete = 1'b1;
        all_ce_wait_complete = 1'b1;
        all_dc_idle = 1'b1;
        all_ce_idle = 1'b1;
        for (int r = 0; r < NUM_ROWS; r++) begin
            // Row is complete if its cmd_id >= wait_id
            all_dc_wait_complete = all_dc_wait_complete & (i_dc_id[r] >= wait_disp_id_reg);
            all_ce_wait_complete = all_ce_wait_complete & (i_ce_id[r] >= wait_matmul_id_reg);
            // Row is idle if state == 0
            all_dc_idle = all_dc_idle & (i_dc_state[r] == 4'd0);
            all_ce_idle = all_ce_idle & (i_ce_state[r] == 4'd0);
        end
    end
    
    // Backpressure: any row's result FIFO almost-full
    logic any_ce_result_fifo_afull;
    always_comb begin
        any_ce_result_fifo_afull = 1'b0;
        for (int r = 0; r < NUM_ROWS; r++) begin
            any_ce_result_fifo_afull = any_ce_result_fifo_afull | i_ce_result_fifo_afull[r];
        end
    end

    // ===================================================================
    // State Transition Logic
    // ===================================================================
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            state_reg <= ST_IDLE;
        end else begin
            state_reg <= state_next;
            // synthesis translate_off
            `ifdef DEBUG_MASTER_CTRL
            if (state_reg != state_next) begin
                $display("[MC] @%0t STATE: %0d -> %0d, cmd_op_reg=0x%02x, o_mc_cmd_op=0x%02x",
                         $time, state_reg, state_next, cmd_op_reg, o_mc_cmd_op);
            end
            `endif
            // synthesis translate_on
        end
    end

    always_comb begin
        state_next = state_reg;

        case (state_reg)
            ST_IDLE: begin
                // Only start next command if:
                // 1. Command FIFO has data
                // 2. No row's result FIFO is almost-full (backpressure)
                if (!i_cmd_fifo_empty && !any_ce_result_fifo_afull) begin
                    state_next = ST_WAIT_DATA;  // Wait for FIFO read latency
                end
            end

            ST_WAIT_DATA: begin
                // Wait 1 cycle for FIFO read latency (registered output)
                // 128-bit data will be valid on the NEXT clock edge
                state_next = ST_DECODE;
            end

            ST_DECODE: begin
                // Route to appropriate execution state based on opcode
                // Use i_cmd_fifo_rdata directly (128-bit, opcode at [103:96])
                case (i_cmd_fifo_rdata[103:96])
                    CMD_FETCH:          state_next = ST_EXEC_FETCH;
                    CMD_DISP:           state_next = ST_EXEC_DISP;
                    CMD_MATMUL:         state_next = ST_EXEC_MATMUL;
                    CMD_WAIT_DISP:      state_next = ST_WAIT_DISP;
                    CMD_WAIT_MATMUL:    state_next = ST_WAIT_MATMUL;
                    CMD_READOUT:        state_next = ST_EXEC_READOUT;
                    default:            state_next = ST_IDLE; // Error case
                endcase
            end

            ST_EXEC_FETCH: begin
                // Wait for ALL rows to acknowledge FETCH
                if (all_dc_ack_fetch) begin
                    state_next = ST_IDLE;
                end else begin
                    state_next = ST_EXEC_FETCH;
                end
            end

            ST_EXEC_DISP: begin
                // Wait for ALL rows to acknowledge DISPATCH
                if (all_dc_ack_disp) begin
                    state_next = ST_IDLE;
                end else begin
                    state_next = ST_EXEC_DISP;
                end
            end

            ST_EXEC_MATMUL: begin
                // Wait for ALL rows to acknowledge MATMUL
                if (all_ce_ack_matmul) begin
                    state_next = ST_CMD_COMPLETE;
                end else begin
                    state_next = ST_EXEC_MATMUL;
                end
            end

            ST_WAIT_DISP: begin
                // Wait for ALL rows' DC to complete up to wait_id
                // Release conditions (either one):
                //   1. dc_id >= wait_id for all rows (ID-based completion)
                //   2. All DCs are IDLE (state=0) - they finished their work
                if (all_dc_wait_complete || all_dc_idle) begin
                    state_next = ST_CMD_COMPLETE;
                end else begin
                    // Block when DC is still serving the prior DISP command
                    state_next = ST_WAIT_DISP;
                end
            end

            ST_WAIT_MATMUL: begin
                // Wait for ALL rows' CE to complete up to wait_id
                // Release conditions (either one):
                //   1. ce_id >= wait_id for all rows (ID-based completion)
                //   2. All CEs are IDLE (state=0) - they finished their work
                if (all_ce_wait_complete || all_ce_idle) begin
                    state_next = ST_CMD_COMPLETE;
                end else begin
                    state_next = ST_WAIT_MATMUL;
                end
            end

            ST_EXEC_READOUT: begin
                if (rc_ack_readout_reg) begin
                    state_next = ST_CMD_COMPLETE;
                end else begin
                    state_next = ST_EXEC_READOUT;
                end
            end

            ST_CMD_COMPLETE: begin
                // Command complete, return to IDLE
                state_next = ST_IDLE;
            end

            ST_ERROR: begin
                state_next = ST_ERROR;
            end

            default: begin
                state_next = ST_IDLE;
            end
        endcase
    end

    // ===================================================================
    // Register Update Logic
    // ===================================================================
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            cmd_op_reg          <= 8'h00;
            cmd_id_reg          <= 8'h00;
            for (int i = 0; i < 4; i++) cmd_reg[i] <= 32'h0;
            cmd_fifo_ren_reg    <= 1'b0;
            // Initialize per-row payload and ACK registers
            for (int r = 0; r < NUM_ROWS; r++) begin
                cmd_payload_word1_reg[r] <= 32'h0;
                cmd_payload_word2_reg[r] <= 32'h0;
                cmd_payload_word3_reg[r] <= 32'h0;
                dc_ack_fetch_reg[r]  <= 1'b0;
                dc_ack_disp_reg[r]   <= 1'b0;
                ce_ack_matmul_reg[r] <= 1'b0;
            end
            rc_ack_readout_reg <= 1'b0;  // RC is global
            wait_disp_id_reg   <= 8'h0;
            wait_matmul_id_reg <= 8'h0;
        end else begin
            // Default: disable FIFO read unless explicitly enabled in a reading state
            // This prevents reading ahead during command execution
            cmd_fifo_ren_reg <= 1'b0;

            case (state_reg)
            ST_IDLE: begin
                // Give cmd_fifo read enable when the cmd_fifo has data
                // and no row's result FIFO is almost-full (backpressure)
                if (!i_cmd_fifo_empty && !any_ce_result_fifo_afull) begin
                    cmd_fifo_ren_reg <= 1'b1;
                end
            end

            ST_WAIT_DATA: begin
                // Wait for FIFO read latency - data will be valid next cycle
                // Do NOT assert rd_en here to avoid reading next entry
            end

            ST_DECODE: begin
                // 128-bit FIFO data is now valid after 1-cycle wait
                // Extract all 4 words from single 128-bit read:
                // Layout: [127:96]=word0 (header), [95:64]=word1, [63:32]=word2, [31:0]=word3
                //
                // Local aliases for readability (combinational, used within this cycle):
                // word0 = i_cmd_fifo_rdata[127:96]  -> Header: {reserved, cmd_id, cmd_op}
                // word1 = i_cmd_fifo_rdata[95:64]   -> Payload word 1
                // word2 = i_cmd_fifo_rdata[63:32]   -> Payload word 2
                // word3 = i_cmd_fifo_rdata[31:0]    -> Payload word 3
                // opcode = i_cmd_fifo_rdata[103:96] -> cmd_op from word0[7:0]

                // Register the raw command words for debug visibility
                cmd_reg[0] <= i_cmd_fifo_rdata[127:96];
                cmd_reg[1] <= i_cmd_fifo_rdata[95:64];
                cmd_reg[2] <= i_cmd_fifo_rdata[63:32];
                cmd_reg[3] <= i_cmd_fifo_rdata[31:0];
                cmd_op_reg <= i_cmd_fifo_rdata[103:96];
                cmd_id_reg <= i_cmd_fifo_rdata[111:104];

                // Clear ACK registers before transitioning to EXEC state
                for (int r = 0; r < NUM_ROWS; r++) begin
                    dc_ack_fetch_reg[r]  <= 1'b0;
                    dc_ack_disp_reg[r]   <= 1'b0;
                    ce_ack_matmul_reg[r] <= 1'b0;
                end
                rc_ack_readout_reg <= 1'b0;

                // ============================================================
                // Per-Row Command Decomposition (uses i_cmd_fifo_rdata directly)
                // ============================================================
                // V (ugd_len) is partitioned across rows using the formula:
                //   v_base = V / num_rows  (since num_rows=16, use V >> 4)
                //   v_rem  = V % num_rows  (V - (v_base << 4))
                //   if (r < v_rem): v_count = v_base + 1
                //   else:           v_count = v_base
                // This matches get_v_partition() in multi-row_gemm.py
                // ============================================================
                
                case (i_cmd_fifo_rdata[103:96])  // Use opcode directly from FIFO data
                    CMD_FETCH: begin
                        // FETCH Word Layout (per MULTI_ROW_REFERENCE.md):
                        // word1 = start_addr[31:0]
                        // word2 = {ugd_len[15:0], len[15:0]}
                        // word3 = {31'b0, fetch_right}
                        // V is in word2[31:16] = i_cmd_fifo_rdata[63:48]
                        automatic logic [15:0] v_total = i_cmd_fifo_rdata[63:48];
                        automatic logic [15:0] v_base  = v_total >> 4;
                        automatic logic [15:0] v_rem   = v_total - (v_base << 4);
                        for (int r = 0; r < NUM_ROWS; r++) begin
                            automatic logic [15:0] v_count = (r < v_rem) ? (v_base + 16'd1) : v_base;
                            cmd_payload_word1_reg[r] <= i_cmd_fifo_rdata[95:64];  // start_addr unchanged
                            cmd_payload_word2_reg[r] <= {v_count, i_cmd_fifo_rdata[47:32]};  // {v_count, len}
                            cmd_payload_word3_reg[r] <= i_cmd_fifo_rdata[31:0];   // fetch_right unchanged
                        end
                    end

                    CMD_DISP: begin
                        // DISPATCH Word Layout (per MULTI_ROW_REFERENCE.md):
                        // word1 = {nv_cnt[15:0], ugd_len[15:0]}
                        // word2 = {16'b0, tile_addr[15:0]}
                        // word3 = {16'b0, col_start[7:0], 5'b0, disp_right, broadcast, man_4b}
                        // V is in word1[15:0] = i_cmd_fifo_rdata[79:64]
                        automatic logic [15:0] v_total = i_cmd_fifo_rdata[79:64];
                        automatic logic [15:0] v_base  = v_total >> 4;
                        automatic logic [15:0] v_rem   = v_total - (v_base << 4);
                        for (int r = 0; r < NUM_ROWS; r++) begin
                            automatic logic [15:0] v_count = (r < v_rem) ? (v_base + 16'd1) : v_base;
                            cmd_payload_word1_reg[r] <= {i_cmd_fifo_rdata[95:80], v_count};  // {nv_cnt, v_count}
                            cmd_payload_word2_reg[r] <= i_cmd_fifo_rdata[63:32];  // tile_addr unchanged
                            cmd_payload_word3_reg[r] <= i_cmd_fifo_rdata[31:0];   // flags unchanged
                        end
                    end

                    CMD_MATMUL: begin
                        // MATMUL Word Layout (per MULTI_ROW_REFERENCE.md):
                        // word1 = {left_addr[15:0], right_addr[15:0]}
                        // word2 = {left_len[15:0], right_len[15:0]}
                        // word3 = {ugd_len[15:0], 13'b0, left_4b, right_4b, main_loop_left}
                        // V is in word3[31:16] = i_cmd_fifo_rdata[31:16]
                        automatic logic [15:0] v_total = i_cmd_fifo_rdata[31:16];
                        automatic logic [15:0] v_base  = v_total >> 4;
                        automatic logic [15:0] v_rem   = v_total - (v_base << 4);
                        for (int r = 0; r < NUM_ROWS; r++) begin
                            automatic logic [15:0] v_count = (r < v_rem) ? (v_base + 16'd1) : v_base;
                            cmd_payload_word1_reg[r] <= i_cmd_fifo_rdata[95:64];  // addresses unchanged
                            cmd_payload_word2_reg[r] <= i_cmd_fifo_rdata[63:32];  // B, C unchanged
                            cmd_payload_word3_reg[r] <= {v_count, i_cmd_fifo_rdata[15:0]};  // {v_count, flags}
                        end
                    end

                    CMD_READOUT: begin
                        // READOUT Word Layout (per MULTI_ROW_REFERENCE.md):
                        // word1 = {left_len[15:0], right_len[15:0]}
                        // word2 = {16'b0, ugd_len[15:0]}
                        // word3 = 0
                        // V is in word2[15:0] = i_cmd_fifo_rdata[47:32]
                        automatic logic [15:0] v_total = i_cmd_fifo_rdata[47:32];
                        automatic logic [15:0] v_base  = v_total >> 4;
                        automatic logic [15:0] v_rem   = v_total - (v_base << 4);
                        for (int r = 0; r < NUM_ROWS; r++) begin
                            automatic logic [15:0] v_count = (r < v_rem) ? (v_base + 16'd1) : v_base;
                            cmd_payload_word1_reg[r] <= i_cmd_fifo_rdata[95:64];  // B, C unchanged
                            cmd_payload_word2_reg[r] <= {16'b0, v_count};  // {reserved, v_count}
                            cmd_payload_word3_reg[r] <= i_cmd_fifo_rdata[31:0];   // reserved (0)
                        end
                    end

                    CMD_WAIT_DISP: begin
                        // WAIT commands don't need V partitioning - pass through unchanged
                        // word1[7:0] = i_cmd_fifo_rdata[71:64]
                        wait_disp_id_reg <= i_cmd_fifo_rdata[71:64];
                        for (int r = 0; r < NUM_ROWS; r++) begin
                            cmd_payload_word1_reg[r] <= i_cmd_fifo_rdata[95:64];
                            cmd_payload_word2_reg[r] <= i_cmd_fifo_rdata[63:32];
                            cmd_payload_word3_reg[r] <= i_cmd_fifo_rdata[31:0];
                        end
                    end

                    CMD_WAIT_MATMUL: begin
                        // WAIT commands don't need V partitioning - pass through unchanged
                        // word1[7:0] = i_cmd_fifo_rdata[71:64]
                        wait_matmul_id_reg <= i_cmd_fifo_rdata[71:64];
                        for (int r = 0; r < NUM_ROWS; r++) begin
                            cmd_payload_word1_reg[r] <= i_cmd_fifo_rdata[95:64];
                            cmd_payload_word2_reg[r] <= i_cmd_fifo_rdata[63:32];
                            cmd_payload_word3_reg[r] <= i_cmd_fifo_rdata[31:0];
                        end
                    end

                    default: begin
                        // Unknown opcode - pass through unchanged
                        for (int r = 0; r < NUM_ROWS; r++) begin
                            cmd_payload_word1_reg[r] <= i_cmd_fifo_rdata[95:64];
                            cmd_payload_word2_reg[r] <= i_cmd_fifo_rdata[63:32];
                            cmd_payload_word3_reg[r] <= i_cmd_fifo_rdata[31:0];
                        end
                    end
                endcase
            end

            ST_EXEC_FETCH: begin
                // Capture per-row FETCH acknowledges (STICKY - once set, stays set)
                for (int r = 0; r < NUM_ROWS; r++) begin
                    if (i_dc_ack_fetch[r]) dc_ack_fetch_reg[r] <= 1'b1;
                end
            end

            ST_EXEC_DISP: begin
                // Capture per-row DISPATCH acknowledges (STICKY - once set, stays set)
                for (int r = 0; r < NUM_ROWS; r++) begin
                    if (i_dc_ack_disp[r]) dc_ack_disp_reg[r] <= 1'b1;
                end
            end

            ST_EXEC_MATMUL: begin
                // Capture per-row MATMUL acknowledges (STICKY - once set, stays set)
                for (int r = 0; r < NUM_ROWS; r++) begin
                    if (i_ce_ack_matmul[r]) ce_ack_matmul_reg[r] <= 1'b1;
                end
            end

            ST_WAIT_DISP: begin
                // wait_id already captured in ST_DECODE
                // Just wait for completion (combinational check handles exit)
            end

            ST_WAIT_MATMUL: begin
                // wait_id already captured in ST_DECODE
                // Just wait for completion (combinational check handles exit)
            end

            ST_EXEC_READOUT: begin
                // RC is global - single acknowledge
                rc_ack_readout_reg <= i_rc_ack_readout;
            end

            ST_CMD_COMPLETE: begin
                // Command complete - clear opcode for next iteration
                cmd_op_reg <= 8'h00;
            end

            ST_ERROR: begin
                // Stay in error state
            end

            default: begin
            end
        endcase
        end
    end


    // ===================================================================
    // Output Assignment
    // ===================================================================
    assign o_mc_state = state_reg;

    // ===================================================================
    // Debug Output Assignment
    // ===================================================================
    // Pack the per-row ACK registers into vectors for debug visibility
    generate
        for (genvar r = 0; r < NUM_ROWS; r++) begin : gen_dbg_ack
            assign o_dbg_ce_ack_matmul_reg[r] = ce_ack_matmul_reg[r];
            assign o_dbg_dc_ack_fetch_reg[r]  = dc_ack_fetch_reg[r];
        end
    endgenerate
    assign o_dbg_cmd_valid = cmd_valid;

endmodule : master_control_2d
