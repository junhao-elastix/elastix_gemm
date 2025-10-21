// ------------------------------------------------------------------
// Master Control Module
//
// Purpose: Unified command processor for MS2.0 microcode architecture
// Features:
//  - Reads commands from cmd_fifo (header + payload)
//  - Parses command opcodes: FETCH, DISP, TILE, WAIT_DISP, WAIT_TILE
//  - Routes to dispatcher_control (FETCH/DISP) or compute_engine (TILE)
//  - Tracks command IDs for WAIT synchronization
//  - FSM: IDLE → READ_HDR → READ_PAYLOAD → DECODE → EXECUTE → WAIT_DONE
//
// Author: MS2.0 Migration
// Date: Thu Oct 2 00:06:48 AM PDT 2025
// ------------------------------------------------------------------

module master_control
import gemm_pkg::*;
(
    input  logic        i_clk,
    input  logic        i_reset_n,
    
    // Bypass Mode Control (for gemm compatibility - not used in this version)
    input  logic [1:0]  i_bypass_mode,

    // Command FIFO Interface
    input  logic [cmd_buf_width_gp-1:0] i_cmd_fifo_rdata,
    input  logic                        i_cmd_fifo_empty,
    input  logic [12:0]                 i_cmd_fifo_count,
    output logic                        o_cmd_fifo_ren,
    
    // Peripheral State Inputs (for command synchronization)
    input  logic [3:0]                  i_dc_state,        // Dispatcher Control state
    input  logic [3:0]                  i_ce_state,        // Compute Engine state
    input  logic                        i_result_fifo_afull, // Result FIFO almost-full flag

    // Dispatcher Control Interface (FETCH/DISP commands)
    output logic                         o_dc_fetch_en,
    output logic [link_addr_width_gp-1:0] o_dc_fetch_addr,
    output logic [link_len_width_gp-1:0]  o_dc_fetch_len,
    output logic                         o_dc_fetch_target, // 0=left, 1=right
    input  logic                         i_dc_fetch_done,

    output logic                          o_dc_disp_en,
    output logic [tile_mem_addr_width_gp-1:0] o_dc_disp_addr,
    output logic [tile_mem_addr_width_gp-1:0] o_dc_disp_len,
    output logic                          o_dc_man_4b_8b_n,
    input  logic                          i_dc_disp_done,

    // Compute Engine Interface (TILE command)
    output logic                          o_ce_tile_en,
    output logic [tile_mem_addr_width_gp-1:0] o_ce_left_addr,
    output logic [tile_mem_addr_width_gp-1:0] o_ce_right_addr,
    output logic [tile_mem_addr_width_gp-1:0] o_ce_left_ugd_len,
    output logic [tile_mem_addr_width_gp-1:0] o_ce_right_ugd_len,
    output logic [tile_mem_addr_width_gp-1:0] o_ce_vec_len,
    output logic [7:0]                    o_ce_dim_b,
    output logic [7:0]                    o_ce_dim_c,
    output logic [7:0]                    o_ce_dim_v,
    output logic                          o_ce_left_man_4b,
    output logic                          o_ce_right_man_4b,
    output logic                          o_ce_main_loop_over_left,
    input  logic                          i_ce_tile_done,

    // Debug
    output logic [3:0]                    o_mc_state,
    output logic [3:0]                    o_mc_state_next,  // Next state (for gemm compatibility)
    output logic [cmd_op_width_gp-1:0]    o_last_opcode,
    output logic [12:0]                   o_mc_sees_count,  // Debug: what count MC sees
    output logic [7:0]                    o_cmd_op_debug,   // Debug: opcode captured
    output logic [31:0]                   o_mc_tile_dimensions,  // Debug: {dim_b, dim_c, dim_v, 8'h00}
    output logic [31:0]                   o_mc_payload_word1,   // Debug: payload word 1
    output logic [31:0]                   o_mc_payload_word2,   // Debug: payload word 2
    output logic [31:0]                   o_mc_payload_word3    // Debug: payload word 3
);

    // ===================================================================
    // State Machine Definition
    // ===================================================================
    typedef enum logic [3:0] {
        ST_IDLE         = 4'd0,
        ST_READ_HDR     = 4'd1,
        ST_READ_PAYLOAD1 = 4'd2,
        ST_READ_PAYLOAD2 = 4'd3,
        ST_READ_PAYLOAD3 = 4'd4,  // Added for 3-word TILE command payload
        ST_DECODE       = 4'd5,
        ST_EXEC_FETCH   = 4'd6,
        ST_EXEC_DISP    = 4'd7,
        ST_EXEC_TILE    = 4'd8,
        ST_WAIT_DISP    = 4'd9,   // Separate WAIT_DISP state for proper blocking
        ST_WAIT_TILE    = 4'd10,  // Separate WAIT_TILE state for proper blocking
        ST_WAIT_DONE    = 4'd11,
        ST_CMD_COMPLETE = 4'd12
    } state_t;

    state_t state_reg, state_next;

    // ===================================================================
    // Internal Registers
    // ===================================================================

    // Command header fields
    logic [cmd_op_width_gp-1:0]  cmd_op_reg;
    logic [cmd_id_width_gp-1:0]  cmd_id_reg;
    logic [cmd_len_width_gp-1:0] cmd_len_reg;

    // Payload storage (up to 2 words for cmd_tile_s)
    logic [31:0] payload_word1_reg;
    logic [31:0] payload_word2_reg;
    logic [31:0] payload_word3_reg;  // Added for 74-bit TILE command payload

    // Payload read counter (always 3 payload words in 4-word-per-command architecture)
    logic [2:0] payload_count_reg;

    // ID tracking for WAIT commands
    logic [cmd_id_width_gp-1:0] last_disp_id_reg;
    logic [cmd_id_width_gp-1:0] last_tile_id_reg;
    logic [cmd_id_width_gp-1:0] wait_id_reg;

    // Control signal registers
    logic cmd_fifo_ren_reg;
    logic dc_fetch_en_reg;
    logic dc_disp_en_reg;
    logic ce_tile_en_reg;
    logic ce_tile_params_set;  // Delayed enable for proper address setup

    // ===================================================================
    // State Transition Logic
    // ===================================================================
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            state_reg <= ST_IDLE;
        end else begin
            state_reg <= state_next;
            if (state_reg != state_next) begin
                $display("[MC_STATE] @%0t %0d -> %0d", $time, state_reg, state_next);
            end
        end
    end

    // Next state combinational logic
    // NEW: Fixed 4-word-per-command architecture
    // All commands are 4 words: header + 3 payload words (unused words ignored)
    always_comb begin
        state_next = state_reg;

        case (state_reg)
            ST_IDLE: begin
                // Only start next command if:
                // 1. Command FIFO has data
                // 2. All peripherals are idle
                // 3. Result FIFO is not almost-full (backpressure)
                if (!i_cmd_fifo_empty && 
                    (i_dc_state == 4'd0) && 
                    (i_ce_state == 4'd0) &&
                    !i_result_fifo_afull) begin
                    state_next = ST_READ_HDR;
                end
            end

            ST_READ_HDR: begin
                // Wait for FIFO to have data before advancing
                if (!i_cmd_fifo_empty) begin
                    state_next = ST_READ_PAYLOAD1;
                end else begin
                    state_next = ST_READ_HDR;  // Stay here until data available
                end
            end

            ST_READ_PAYLOAD1: begin
                // Wait for FIFO to have data before advancing
                if (!i_cmd_fifo_empty) begin
                    state_next = ST_READ_PAYLOAD2;
                end else begin
                    state_next = ST_READ_PAYLOAD1;  // Stay here until data available
                end
            end

            ST_READ_PAYLOAD2: begin
                // Wait for FIFO to have data before advancing
                if (!i_cmd_fifo_empty) begin
                    state_next = ST_READ_PAYLOAD3;
                end else begin
                    state_next = ST_READ_PAYLOAD2;  // Stay here until data available
                end
            end

            ST_READ_PAYLOAD3: begin
                // Wait for FIFO to have data before advancing
                if (!i_cmd_fifo_empty) begin
                    state_next = ST_DECODE;
                end else begin
                    state_next = ST_READ_PAYLOAD3;  // Stay here until data available
                end
            end

            ST_DECODE: begin
                // Route to appropriate execution state based on opcode
                case (cmd_op_reg)
                    e_cmd_op_fetch:     state_next = ST_EXEC_FETCH;
                    e_cmd_op_disp:      state_next = ST_EXEC_DISP;
                    e_cmd_op_tile:      state_next = ST_EXEC_TILE;
                    e_cmd_op_wait_disp: state_next = ST_WAIT_DISP;
                    e_cmd_op_wait_tile: state_next = ST_WAIT_TILE;
                    default:            state_next = ST_IDLE; // Error case
                endcase
            end

            ST_EXEC_FETCH: begin
                state_next = ST_WAIT_DONE;
            end

            ST_EXEC_DISP: begin
                state_next = ST_WAIT_DONE;
            end

            ST_EXEC_TILE: begin
                // Stay in EXEC_TILE for 2 cycles: cycle 1 sets params, cycle 2 asserts enable
                if (ce_tile_params_set) begin
                    state_next = ST_WAIT_DONE;
                end
            end

            ST_WAIT_DISP: begin
                // Block until dispatcher operation with ID >= wait_id completes
                if (last_disp_id_reg >= wait_id_reg) begin
                    state_next = ST_CMD_COMPLETE;
                end else begin
                    state_next = ST_WAIT_DISP; // Keep blocking
                end
            end

            ST_WAIT_TILE: begin
                // Block until tile operation with ID >= wait_id completes
                if (last_tile_id_reg >= wait_id_reg) begin
                    state_next = ST_CMD_COMPLETE;
                end else begin
                    state_next = ST_WAIT_TILE; // Keep blocking
                    $display("[MC] @%0t WAIT_TILE blocking: last_tile_id=%0d < wait_id=%0d",
                             $time, last_tile_id_reg, wait_id_reg);
                end
            end

            ST_WAIT_DONE: begin
                if ((dc_fetch_en_reg && i_dc_fetch_done) ||
                    (dc_disp_en_reg && i_dc_disp_done) ||
                    (ce_tile_en_reg && i_ce_tile_done)) begin
                    state_next = ST_CMD_COMPLETE;
                end
            end

            ST_CMD_COMPLETE: begin
                $display("[MC_DEBUG] @%0t CMD_COMPLETE: dc_fetch_en=%b, dc_disp_en=%b, clearing enables",
                         $time, dc_fetch_en_reg, dc_disp_en_reg);
                state_next = ST_IDLE;
            end

            default: begin
                state_next = ST_IDLE;
            end
        endcase
    end

    // ===================================================================
    // Command Header and Payload Capture
    // ===================================================================
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            cmd_op_reg <= 8'h00;
            cmd_id_reg <= 8'h00;
            cmd_len_reg <= 8'h00;
            payload_word1_reg <= 32'h0;
            payload_word2_reg <= 32'h0;
            payload_word3_reg <= 32'h0;
            payload_count_reg <= 3'd0;
        end else begin
            case (state_reg)
                ST_READ_HDR: begin
                    // Wait 1 cycle for FIFO data to be ready (registered FIFO has 1-cycle latency)
                    // Header will be latched in ST_READ_PAYLOAD1
                end

                ST_READ_PAYLOAD1: begin
                    // Latch header ONLY if we successfully transitioned (FIFO not empty)
                    if (state_reg != state_next) begin  // Transitioning to PAYLOAD2
                        cmd_op_reg  <= i_cmd_fifo_rdata[7:0];
                        cmd_id_reg  <= i_cmd_fifo_rdata[15:8];
                        cmd_len_reg <= i_cmd_fifo_rdata[23:16];
                        payload_count_reg <= 3'd0;
                        $display("[MC] @%0t LATCH_HDR: op=0x%02x, id=%0d, len=%0d",
                                 $time, i_cmd_fifo_rdata[7:0], i_cmd_fifo_rdata[15:8], i_cmd_fifo_rdata[23:16]);
                    end
                end

                ST_READ_PAYLOAD2: begin
                    // Latch payload word 1 ONLY if we successfully transitioned
                    if (state_reg != state_next) begin  // Transitioning to PAYLOAD3
                        payload_word1_reg <= i_cmd_fifo_rdata;
                        payload_count_reg <= 3'd1;
                        $display("[MC] @%0t LATCH_PAYLOAD1: cmd[1]=0x%08x", $time, i_cmd_fifo_rdata);
                    end
                end

                ST_READ_PAYLOAD3: begin
                    // Latch payload word 2 ONLY if we successfully transitioned
                    if (state_reg != state_next) begin  // Transitioning to DECODE
                        payload_word2_reg <= i_cmd_fifo_rdata;
                        payload_count_reg <= 3'd2;
                        $display("[MC] @%0t LATCH_PAYLOAD2: cmd[2]=0x%08x", $time, i_cmd_fifo_rdata);
                    end
                end

                ST_DECODE: begin
                    // Latch payload word 3 (final word from ST_READ_PAYLOAD3 read)
                    // This happens as we enter DECODE state
                    payload_word3_reg <= i_cmd_fifo_rdata;
                    payload_count_reg <= 3'd3;
                    $display("[MC] @%0t LATCH_PAYLOAD3: cmd[3]=0x%08x", $time, i_cmd_fifo_rdata);
                    
                    // Display decoded command with all 4 words
                    $display("[MC] @%0t DECODE: op=0x%02x, payload=[0x%08x, 0x%08x, 0x%08x]",
                             $time, cmd_op_reg, payload_word1_reg, payload_word2_reg, payload_word3_reg);
                end

                ST_CMD_COMPLETE: begin
                    payload_count_reg <= 3'd0;
                end
            endcase
        end
    end

    // Removed payload_words_needed logic - all commands are now 4 words (header + 3 payload)

    // ===================================================================
    // Command Execution - Dispatcher Control (FETCH/DISP)
    // ===================================================================
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            dc_fetch_en_reg <= 1'b0;
            o_dc_fetch_addr <= '0;
            o_dc_fetch_len  <= '0;
            o_dc_fetch_target <= 1'b0;
            dc_disp_en_reg  <= 1'b0;
            o_dc_disp_addr  <= '0;
            o_dc_disp_len   <= '0;
            o_dc_man_4b_8b_n <= 1'b0;
        end else begin
            // Clear enables immediately when done signal detected in WAIT_DONE state
            // This prevents re-triggering when peripheral returns to IDLE before we do
            if (state_reg == ST_WAIT_DONE) begin
                if (dc_fetch_en_reg && i_dc_fetch_done) begin
                    dc_fetch_en_reg <= 1'b0;
                end
                if (dc_disp_en_reg && i_dc_disp_done) begin
                    dc_disp_en_reg <= 1'b0;
                end
            end

            case (state_reg)
                ST_EXEC_FETCH: begin
                    // Parse cmd_fetch_s (64-bit structure):
                    // Word1 [31:0]: start_addr
                    // Word2 [15:0]: len, [16]: fetch_right, [31:17]: reserved
                    dc_fetch_en_reg <= 1'b1;
                    o_dc_fetch_addr <= payload_word1_reg[link_addr_width_gp-1:0];
                    o_dc_fetch_len  <= payload_word2_reg[link_len_width_gp-1:0];
                    o_dc_fetch_target <= payload_word2_reg[16];  // Extract fetch_right bit
                    $display("[MC] @%0t EXEC_FETCH: addr=0x%08x, len=%0d, target=%s",
                             $time, payload_word1_reg[link_addr_width_gp-1:0], 
                             payload_word2_reg[link_len_width_gp-1:0],
                             payload_word2_reg[16] ? "RIGHT" : "LEFT");
                end

                ST_EXEC_DISP: begin
                    // Parse cmd_disp_s structure (updated for 11-bit addressing)
                    cmd_disp_s disp_cmd;
                    disp_cmd = payload_word1_reg;

                    dc_disp_en_reg   <= 1'b1;
                    o_dc_disp_addr   <= disp_cmd.tile_addr;
                    o_dc_disp_len    <= disp_cmd.len;
                    o_dc_man_4b_8b_n <= disp_cmd.man_4b_8b_n;
                    $display("[MC] @%0t EXEC_DISP: tile_addr=%0d, len=%0d, man_4b=%0b",
                             $time, disp_cmd.tile_addr, disp_cmd.len, disp_cmd.man_4b_8b_n);
                end
            endcase
        end
    end

    // ===================================================================
    // Command Execution - Compute Engine (TILE)
    // ===================================================================
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            ce_tile_en_reg <= 1'b0;
            ce_tile_params_set <= 1'b0;
            o_ce_left_addr  <= '0;
            o_ce_right_addr <= '0;
            o_ce_left_ugd_len  <= '0;
            o_ce_right_ugd_len <= '0;
            o_ce_vec_len    <= '0;
            o_ce_dim_b      <= '0;
            o_ce_dim_c      <= '0;
            o_ce_dim_v      <= '0;
            o_ce_left_man_4b  <= 1'b0;
            o_ce_right_man_4b <= 1'b0;
            o_ce_main_loop_over_left <= 1'b0;
        end else begin
            // Clear params_set flag when command completes (ready for next TILE)
            if (state_reg == ST_CMD_COMPLETE) begin
                ce_tile_params_set <= 1'b0;
                $display("[MC] @%0t CMD_COMPLETE: Clearing ce_tile_params_set for next tile", $time);
            end
            
            // Clear enable when tile completes (in WAIT_DONE state)
            if (state_reg == ST_WAIT_DONE && ce_tile_en_reg && i_ce_tile_done) begin
                ce_tile_en_reg <= 1'b0;
                $display("[MC] @%0t WAIT_DONE: Tile complete, clearing ce_tile_en", $time);
            end

            if (state_reg == ST_EXEC_TILE) begin
                // Parse cmd_tile_s (3 words for 87-bit payload):
                // Use structure casting for correct bit extraction
                cmd_tile_s tile_cmd;
                tile_cmd = {payload_word3_reg[22:0], payload_word2_reg, payload_word1_reg};

                // Cycle 1: Set all parameters
                if (!ce_tile_params_set) begin
                    o_ce_left_addr  <= tile_cmd.left_addr;
                    o_ce_right_addr <= tile_cmd.right_addr;
                    o_ce_left_ugd_len  <= tile_cmd.left_ugd_len;
                    o_ce_right_ugd_len <= tile_cmd.right_ugd_len;
                    o_ce_vec_len    <= tile_cmd.vec_len;
                    o_ce_dim_b      <= tile_cmd.dim_b;
                    o_ce_dim_c      <= tile_cmd.dim_c;
                    o_ce_dim_v      <= tile_cmd.dim_v;
                    o_ce_left_man_4b  <= tile_cmd.flags.left_man_4b;
                    o_ce_right_man_4b <= tile_cmd.flags.right_man_4b;
                    o_ce_main_loop_over_left <= tile_cmd.flags.main_loop_over_left;
                    ce_tile_params_set <= 1'b1;  // Mark parameters as set

                    $display("[MC] @%0t EXEC_TILE Cycle 1: Setting params B=%0d, C=%0d, V=%0d, left_addr=%0d, right_addr=%0d",
                             $time, tile_cmd.dim_b, tile_cmd.dim_c, tile_cmd.dim_v,
                             tile_cmd.left_addr, tile_cmd.right_addr);
                end
                // Cycle 2: Assert enable after parameters are stable (will be high for 1 cycle)
                else begin
                    ce_tile_en_reg <= 1'b1;
                    $display("[MC] @%0t EXEC_TILE Cycle 2: Asserting ce_tile_en (left=%0d, right=%0d)",
                             $time, o_ce_left_addr, o_ce_right_addr);
                end
            end
        end
    end

    // ===================================================================
    // ID Tracking for WAIT Commands
    // ===================================================================
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            last_disp_id_reg <= 8'h00;
            last_tile_id_reg <= 8'h00;
            wait_id_reg <= 8'h00;
        end else begin
            // Track last completed DISP/TILE IDs
            if (state_reg == ST_CMD_COMPLETE) begin
                if (cmd_op_reg == e_cmd_op_disp) begin
                    last_disp_id_reg <= cmd_id_reg;
                end else if (cmd_op_reg == e_cmd_op_tile) begin
                    last_tile_id_reg <= cmd_id_reg;
                end
            end

            // Capture wait ID for WAIT commands
            if (state_reg == ST_DECODE &&
                (cmd_op_reg == e_cmd_op_wait_disp || cmd_op_reg == e_cmd_op_wait_tile)) begin
                // wait_id is in header bits [15:8] (id field) per software spec
                // Software constructs: {reserved[31:24], len[23:16], wait_id[15:8], opcode[7:0]}
                wait_id_reg <= cmd_id_reg;
            end
        end
    end

    // ===================================================================
    // Command FIFO Read Control
    // ===================================================================
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            cmd_fifo_ren_reg <= 1'b0;
        end else begin
            cmd_fifo_ren_reg <= 1'b0;  // Default

            case (state_reg)
                ST_IDLE: begin
                    if (!i_cmd_fifo_empty) begin
                        cmd_fifo_ren_reg <= 1'b1;  // Read header
                    end
                end

                ST_READ_HDR: begin
                    // Always read word 1 (payload word 1) next
                    cmd_fifo_ren_reg <= 1'b1;
                end

                ST_READ_PAYLOAD1: begin
                    // Always read word 2 (payload word 2) next
                    cmd_fifo_ren_reg <= 1'b1;
                    $display("[MC_RDEN] @%0t ST_READ_PAYLOAD1: setting rd_en=1", $time);
                end

                ST_READ_PAYLOAD2: begin
                    // Always read word 3 (payload word 3) next
                    cmd_fifo_ren_reg <= 1'b1;
                    $display("[MC_RDEN] @%0t ST_READ_PAYLOAD2: setting rd_en=1", $time);
                end

                ST_READ_PAYLOAD3: begin
                    // All 4 words read, no more FIFO reads until next command
                    cmd_fifo_ren_reg <= 1'b0;
                end
            endcase
        end
    end

    assign o_cmd_fifo_ren = cmd_fifo_ren_reg;
    
    // Debug: Display rd_en value
    always @(posedge i_clk) begin
        if (cmd_fifo_ren_reg) begin
            $display("[MC_RDEN_OUT] @%0t o_cmd_fifo_ren=1 (state=%0d)", $time, state_reg);
        end
    end

    // ===================================================================
    // Output Enables
    // ===================================================================
    assign o_dc_fetch_en = dc_fetch_en_reg;
    assign o_dc_disp_en  = dc_disp_en_reg;
    assign o_ce_tile_en  = ce_tile_en_reg;

    // ===================================================================
    // Debug Outputs
    // ===================================================================
    assign o_mc_state = state_reg;
    assign o_last_opcode = cmd_op_reg;

    // ===================================================================
    // Assertions (for simulation only)
    // ===================================================================

    `ifdef SIM
        // Check for valid opcodes
        property valid_opcode;
            @(posedge i_clk) disable iff (~i_reset_n)
            (state_reg == ST_DECODE) |->
                (cmd_op_reg inside {e_cmd_op_fetch, e_cmd_op_disp, e_cmd_op_tile,
                                   e_cmd_op_wait_disp, e_cmd_op_wait_tile});
        endproperty
        assert property (valid_opcode) else
            $error("[MASTER_CONTROL] Invalid opcode detected: 0x%02x", cmd_op_reg);

        // Check FIFO underflow
        property no_fifo_underflow;
            @(posedge i_clk) disable iff (~i_reset_n)
            (cmd_fifo_ren_reg) |-> (!i_cmd_fifo_empty);
        endproperty
        assert property (no_fifo_underflow) else
            $error("[MASTER_CONTROL] Attempted to read from empty command FIFO!");

        // Check only one module enable active at a time
        property one_enable_active;
            @(posedge i_clk) disable iff (~i_reset_n)
            $onehot0({dc_fetch_en_reg, dc_disp_en_reg, ce_tile_en_reg});
        endproperty
        assert property (one_enable_active) else
            $error("[MASTER_CONTROL] Multiple module enables active simultaneously!");
    `endif

    // ===================================================================
    // Debug Display (for simulation)
    // ===================================================================

    `ifdef SIM_VERBOSE
        always @(posedge i_clk) begin
            // Debug: Show why commands are blocked in IDLE
            if (state_reg == ST_IDLE && !i_cmd_fifo_empty && state_next == ST_IDLE) begin
                // Command available but blocked - show why
                if (i_dc_state != 4'd0) 
                    $display("[MC_SYNC] @%0t Command blocked: DC not idle (state=%0d)", $time, i_dc_state);
                if (i_ce_state != 4'd0)
                    $display("[MC_SYNC] @%0t Command blocked: CE not idle (state=%0d)", $time, i_ce_state);
                if (i_result_fifo_afull)
                    $display("[MC_SYNC] @%0t Command blocked: Result FIFO almost-full", $time);
            end
            
            if (state_reg == ST_READ_HDR) begin
                $display("[MASTER_CONTROL] Header: op=0x%02x, id=%0d, len=%0d",
                         i_cmd_fifo_rdata[7:0], i_cmd_fifo_rdata[15:8], i_cmd_fifo_rdata[23:16]);
            end

            if (state_reg == ST_EXEC_FETCH) begin
                $display("[MASTER_CONTROL] FETCH: payload1=0x%08x, payload2=0x%08x -> addr=0x%08x, len=%0d",
                         payload_word1_reg, payload_word2_reg,
                         payload_word1_reg[link_addr_width_gp-1:0], payload_word2_reg[link_len_width_gp-1:0]);
            end

            if (state_reg == ST_EXEC_DISP) begin
                $display("[MASTER_CONTROL] DISP: addr=%0d, len=%0d, man_4b=%0b",
                         o_dc_disp_addr, o_dc_disp_len, o_dc_man_4b_8b_n);
            end

            if (state_reg == ST_EXEC_TILE) begin
                $display("[MASTER_CONTROL] TILE: L_addr=%0d, R_addr=%0d, vec_len=%0d",
                         o_ce_left_addr, o_ce_right_addr, o_ce_vec_len);
            end
        end
    `endif
    
    // ===================================================================
    // Debug Output Assignments (for gemm compatibility)
    // ===================================================================
    assign o_mc_state_next = state_next;
    assign o_cmd_op_debug = cmd_op_reg;
    assign o_mc_sees_count = i_cmd_fifo_count;
    assign o_mc_tile_dimensions = {o_ce_dim_b, o_ce_dim_c, o_ce_dim_v, 8'h00};
    assign o_mc_payload_word1 = payload_word1_reg;
    assign o_mc_payload_word2 = payload_word2_reg;
    assign o_mc_payload_word3 = payload_word3_reg;

endmodule : master_control
