// ------------------------------------------------------------------
// Master Control Module
//
// Purpose: Unified command processor for MS2.0 microcode architecture
// Features:
//  - Reads commands from cmd_fifo (header + payload)
//  - Parses command opcodes: FETCH, DISP, TILE, WAIT_DISP, WAIT_TILE
//  - Routes to dispatcher_control (FETCH/DISP) or compute_engine (TILE)
//  - MS2.0 ASYNC MODEL:
//    * DISPATCH and MATMUL return immediately after trigger (no blocking)
//    * WAIT_DISPATCH barrier checks i_dc_state == IDLE
//    * WAIT_MATMUL barrier checks i_ce_state == IDLE
//  - FSM: IDLE -> READ_HDR -> READ_PAYLOAD -> DECODE -> EXECUTE -> CMD_COMPLETE
//
// Author: Junhao Pan
// Date: 10/27/2025
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
    output logic [15:0]                   o_dc_disp_tile_addr,    // Tile destination address
    output logic [7:0]                    o_dc_disp_man_nv_cnt,   // Total NVs to dispatch
    output logic [7:0]                    o_dc_disp_ugd_vec_size, // NVs per UGD vector
    output logic                          o_dc_disp_man_4b,       // Mantissa width (0=8-bit, 1=4-bit)
    output logic [23:0]                   o_dc_disp_col_en,       // Column enable mask (24 tiles max)
    output logic [4:0]                    o_dc_disp_col_start,    // Distribution start column
    output logic                          o_dc_disp_right,        // Dispatch side (0=left, 1=right)
    output logic                          o_dc_disp_broadcast,    // Distribution mode (0=distribute, 1=broadcast)
    input  logic                          i_dc_disp_done,

    // Compute Engine Interface (TILE command)
    output logic [23:0]                   o_ce_tile_en,           // Per-tile enable (24 tiles max)
    // Compute Engine TILE Interface (spec-compliant per SINGLE_ROW_REFERENCE.md)
    output logic [15:0] o_ce_tile_left_addr,          // 16 bits: Left matrix start address
    output logic [15:0] o_ce_tile_right_addr,         // 16 bits: Right matrix start address
    output logic [7:0]  o_ce_tile_left_ugd_len,       // 8 bits: Left UGD vectors (Batch dimension)
    output logic [7:0]  o_ce_tile_right_ugd_len,      // 8 bits: Right UGD vectors (Column dimension)
    output logic [7:0]  o_ce_tile_vec_len,            // 8 bits: UGD vector size (Vector count)
    output logic        o_ce_tile_left_man_4b,
    output logic        o_ce_tile_right_man_4b,
    output logic        o_ce_tile_main_loop_over_left,
    input  logic        i_ce_tile_done,

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
        ST_IDLE           = 4'd0,
        ST_READ_HDR       = 4'd1,
        ST_READ_PAYLOAD1  = 4'd2,
        ST_READ_PAYLOAD2  = 4'd3,
        ST_READ_PAYLOAD3  = 4'd4,  // Added for 3-word TILE command payload
        ST_DECODE         = 4'd5,
        ST_EXEC_FETCH     = 4'd6,
        ST_EXEC_DISP      = 4'd7,
        ST_EXEC_TILE      = 4'd8,
        ST_WAIT_FETCH     = 4'd9,
        ST_WAIT_DISP      = 4'd10,  // WAIT_DISPATCH barrier command (0xF3)
        ST_WAIT_TILE      = 4'd11,  // WAIT_MATMUL barrier command (0xF4)
        ST_CMD_COMPLETE   = 4'd12,
        ST_EXEC_READOUT   = 4'd13,  // READOUT command (0xF5)
        ST_WAIT_READOUT   = 4'd14   // Wait for READOUT completion
        // ST_WAIT_DISP_OP removed - DISPATCH returns immediately per MS2.0 async model
    } state_t;

    state_t state_reg, state_next;

    // ===================================================================
    // Internal Registers
    // ===================================================================

    // Command header fields
    logic [cmd_op_width_gp-1:0]  cmd_op_reg;
    logic [cmd_id_width_gp-1:0]  cmd_id_reg;

    // Payload storage (up to 2 words for cmd_tile_s)
    logic [31:0] payload_word1_reg;
    logic [31:0] payload_word2_reg;
    logic [31:0] payload_word3_reg;  // Added for 74-bit TILE command payload

    // ID tracking for WAIT commands
    logic [cmd_id_width_gp-1:0] last_disp_id_reg;
    logic [cmd_id_width_gp-1:0] last_tile_id_reg;
    logic [cmd_id_width_gp-1:0] pending_disp_id_reg;  // ID of DISPATCH currently executing
    logic [cmd_id_width_gp-1:0] pending_tile_id_reg;  // ID of MATMUL currently executing
    logic [cmd_id_width_gp-1:0] wait_id_reg;

    // Control signal registers
    logic cmd_fifo_ren_reg;
    logic dc_fetch_en_reg;
    logic dc_disp_en_reg;
    logic [23:0] ce_tile_en_reg;       // Per-tile enable (gated by col_en)
    logic [23:0] ce_col_en_reg;        // Column enable mask from MATMUL command
    logic ce_tile_params_set;  // Delayed enable for proper address setup

    // ===================================================================
    // State Transition Logic
    // ===================================================================
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            state_reg <= ST_IDLE;
        end else begin
            state_reg <= state_next;
        end
    end

    // Next state combinational logic
    // Fixed 4-word-per-command architecture: header + 3 payload words (unused words ignored)
    always_comb begin
        state_next = state_reg;

        case (state_reg)
            ST_IDLE: begin
                // Only start next command if:
                // 1. Command FIFO has data
                // 2. All peripherals are idle (OR command is WAIT, which monitors busy engines)
                // 3. Result FIFO is not almost-full (backpressure)
                //
                // NOTE: WAIT commands must be accepted even when engines are busy,
                // otherwise we get deadlock: TILE launches CE -> CE busy -> WAIT_TILE
                // stuck in FIFO because we won't accept commands while CE busy
                if (!i_cmd_fifo_empty &&
                    !i_result_fifo_afull) begin
                    // Accept all commands when engines idle, or any command when FIFO has data
                    // The actual busy check will happen per-command type in execution states
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
                    e_cmd_op_readout:   state_next = ST_EXEC_READOUT;
                    default:            state_next = ST_IDLE; // Error case
                endcase
            end

            ST_EXEC_FETCH: begin
                // Only execute FETCH if dispatcher is idle
                if (i_dc_state == 4'd0) begin
                    state_next = ST_WAIT_FETCH;
                end else begin
                    state_next = ST_EXEC_FETCH;  // Wait for DC to be idle

                end
            end

            ST_WAIT_FETCH: begin
                if (i_dc_fetch_done) begin
                    state_next = ST_CMD_COMPLETE;
                end else begin
                    state_next = ST_WAIT_FETCH;
                end
            end

            ST_EXEC_DISP: begin
                // DISPATCH triggers copy operation: dispatcher_bram → tile_bram
                // MS2.0 ASYNC MODEL: Trigger and return immediately (no blocking!)
                // Only execute if dispatcher is idle
                if (i_dc_state == 4'd0) begin
                    state_next = ST_CMD_COMPLETE;  // Return immediately after trigger
                end else begin
                    state_next = ST_EXEC_DISP;  // Wait for dispatcher to be idle
                end
            end

            ST_WAIT_DISP: begin
                // WAIT_DISPATCH barrier: Block until dispatcher operation completes
                // MS2.0 ASYNC MODEL: Check BOTH state and done signal
                if (i_dc_state == 4'd0 && i_dc_disp_done) begin
                    state_next = ST_CMD_COMPLETE;
                end else begin
                    state_next = ST_WAIT_DISP; // Keep blocking
                end
            end

            ST_EXEC_TILE: begin
                // MS2.0 ASYNC MODEL: Trigger MATMUL and return immediately (no blocking!)
                // Stay in EXEC_TILE for 2 cycles: cycle 1 sets params, cycle 2 asserts enable
                if (ce_tile_params_set) begin
                    state_next = ST_CMD_COMPLETE;  // Return immediately after trigger (async)
                end
            end

            ST_WAIT_TILE: begin
                // WAIT_MATMUL barrier: Block until compute engine returns to IDLE
                // MS2.0 ASYNC MODEL: Check state machine directly (not ID comparison)
                if (i_ce_state == 4'd0) begin  // Check: i_ce_state == IDLE
                    state_next = ST_CMD_COMPLETE;
                end else begin
                    state_next = ST_WAIT_TILE; // Keep blocking
                end
            end

            ST_EXEC_READOUT: begin
                // READOUT command: Initiate result collection
                // Payload word1 contains start_col parameter
                state_next = ST_WAIT_READOUT;
            end

            ST_WAIT_READOUT: begin
                // Wait for result readout to complete
                // For now, immediately complete (will sync with result_arbiter later)
                state_next = ST_CMD_COMPLETE;
            end

            ST_CMD_COMPLETE: begin
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
            payload_word1_reg <= 32'h0;
            payload_word2_reg <= 32'h0;
            payload_word3_reg <= 32'h0;
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
                    end
                end

                ST_READ_PAYLOAD2: begin
                    // Latch payload word 1 ONLY if we successfully transitioned
                    if (state_reg != state_next) begin  // Transitioning to PAYLOAD3
                        payload_word1_reg <= i_cmd_fifo_rdata;
                    end
                end

                ST_READ_PAYLOAD3: begin
                    // Latch payload word 2 ONLY if we successfully transitioned
                    if (state_reg != state_next) begin  // Transitioning to DECODE
                        payload_word2_reg <= i_cmd_fifo_rdata;
                    end
                end

                ST_DECODE: begin
                    // Latch payload word 3 (final word from ST_READ_PAYLOAD3 read)
                    // This happens as we enter DECODE state
                    payload_word3_reg <= i_cmd_fifo_rdata;
                end

                ST_CMD_COMPLETE: begin
                    // Command complete, ready for next command
                    // (dc_disp_en clearing moved to dispatcher control block)
                end
            endcase
        end
    end

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
            o_dc_disp_tile_addr  <= '0;
            o_dc_disp_man_nv_cnt  <= '0;
            o_dc_disp_ugd_vec_size <= '0;
            o_dc_disp_man_4b <= 1'b0;
            o_dc_disp_col_en <= '0;
            o_dc_disp_col_start <= '0;
            o_dc_disp_right <= 1'b0;
            o_dc_disp_broadcast <= 1'b0;
        end else begin
            // Clear enables when transitioning out of EXEC states
            if (state_reg == ST_EXEC_FETCH && state_next != ST_EXEC_FETCH) begin
                dc_fetch_en_reg <= 1'b0;
            end
            // DON'T auto-clear dc_disp_en here - it conflicts with case ST_EXEC_DISP setting
            // Instead, clear it in ST_CMD_COMPLETE to ensure proper pulse timing
            // Note: ce_tile_en_reg is managed in its own always_ff block below
            
            // Clear enables immediately when done signal detected in WAIT_DONE state
            // This prevents re-triggering when peripheral returns to IDLE before we do
            if (state_reg == ST_WAIT_FETCH) begin
                if (dc_fetch_en_reg && i_dc_fetch_done) begin
                    dc_fetch_en_reg <= 1'b0;
                end
            end
            // MS2.0 ASYNC MODEL: Clear dc_disp_en in CMD_COMPLETE state
            // This creates falling edge for next DISPATCH command
            if (state_reg == ST_CMD_COMPLETE && dc_disp_en_reg) begin
                dc_disp_en_reg <= 1'b0;
            end

            case (state_reg)
                ST_EXEC_FETCH: begin
                    // Parse cmd_fetch_s structure (SPEC-COMPLIANT):
                    // Word1 [31:0]: start_addr
                    // Word2 [15:0]: len, [31:16]: reserved2
                    // Word3 [0]: fetch_right, [31:1]: reserved
                    dc_fetch_en_reg <= 1'b1;
                    o_dc_fetch_addr <= payload_word1_reg[link_addr_width_gp-1:0];
                    o_dc_fetch_len  <= payload_word2_reg[link_len_width_gp-1:0];
                    o_dc_fetch_target <= payload_word3_reg[0];  // FIXED: Word3[0] per spec
                end

                ST_EXEC_DISP: begin
                    // Parse cmd_disp_s structure (SPEC-COMPLIANT per SINGLE_ROW_REFERENCE.md):
                    // Word1: {8'b0, man_nv_cnt[7:0], 8'b0, ugd_vec_size[7:0]}
                    // Word2: {reserved2[15:0], tile_addr[15:0]}
                    // Word3: {col_en[23:0], col_start[4:0], disp_right, broadcast, man_4b}
                    cmd_disp_s disp_cmd;
                    disp_cmd = {payload_word3_reg[31:0], payload_word2_reg, payload_word1_reg};

                    // ASYNC FIX: Always set enable in EXEC_DISP
                    // Clear happens in CMD_COMPLETE to avoid same-cycle conflict
                    dc_disp_en_reg <= 1'b1;

                    o_dc_disp_tile_addr  <= disp_cmd.tile_addr;
                    o_dc_disp_man_nv_cnt <= disp_cmd.man_nv_cnt;
                    o_dc_disp_ugd_vec_size <= disp_cmd.ugd_vec_size;
                    o_dc_disp_man_4b     <= disp_cmd.man_4b;
                    o_dc_disp_col_en     <= disp_cmd.col_en;
                    o_dc_disp_col_start  <= disp_cmd.col_start;
                    o_dc_disp_right      <= disp_cmd.disp_right;
                    o_dc_disp_broadcast  <= disp_cmd.broadcast;
                end
            endcase
        end
    end

    // ===================================================================
    // Command Execution - Compute Engine (TILE)
    // ===================================================================
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            ce_tile_en_reg <= '0;
            ce_col_en_reg  <= '0;
            ce_tile_params_set <= 1'b0;
            o_ce_tile_left_addr  <= '0;
            o_ce_tile_right_addr <= '0;
            o_ce_tile_left_ugd_len  <= '0;
            o_ce_tile_right_ugd_len <= '0;
            o_ce_tile_vec_len    <= '0;
            o_ce_tile_left_man_4b  <= 1'b0;
            o_ce_tile_right_man_4b <= 1'b0;
            o_ce_tile_main_loop_over_left <= 1'b0;
        end else begin
            // MS2.0 ASYNC MODEL: Clear ce_tile_en when compute engine signals completion
            // (Not tied to specific state - works with async MATMUL trigger)
            if (|ce_tile_en_reg && i_ce_tile_done) begin  // Check if ANY tile enabled
                ce_tile_en_reg <= '0;
            end

            // Clear params_set flag when command completes (ready for next TILE)
            if (state_reg == ST_CMD_COMPLETE) begin
                ce_tile_params_set <= 1'b0;
            end

            if (state_reg == ST_EXEC_TILE) begin
                // Parse cmd_tile_s structure (SPEC-COMPLIANT, 96-bit):
                // Word1: {left_addr[15:0], right_addr[15:0]}
                // Word2: {reserved2[7:0], left_ugd_len[7:0], right_ugd_len[7:0], vec_len[7:0]}
                // Word3: {col_en[15:0], reserved[12:0], left_4b, right_4b, main_loop_left}
                cmd_tile_s tile_cmd;
                tile_cmd = {payload_word3_reg, payload_word2_reg, payload_word1_reg};  // Full 96 bits

                if (!ce_tile_params_set) begin
                    // Assign TILE command parameters
                    o_ce_tile_left_addr         <= tile_cmd.left_addr;
                    o_ce_tile_right_addr        <= tile_cmd.right_addr;
                    o_ce_tile_left_ugd_len      <= tile_cmd.left_ugd_len;   // Batch dimension
                    o_ce_tile_right_ugd_len     <= tile_cmd.right_ugd_len;  // Column dimension
                    o_ce_tile_vec_len           <= tile_cmd.vec_len;        // Vector count
                    o_ce_tile_left_man_4b       <= tile_cmd.left_4b;
                    o_ce_tile_right_man_4b      <= tile_cmd.right_4b;
                    o_ce_tile_main_loop_over_left <= tile_cmd.main_loop_left;
                    ce_col_en_reg               <= tile_cmd.col_en;        // Store column enable mask
                    ce_tile_params_set <= 1'b1;  // Mark parameters as set
                end else begin
                    ce_tile_en_reg <= ce_col_en_reg;  // Enable only tiles specified by col_en
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
            pending_disp_id_reg <= 8'h00;
            pending_tile_id_reg <= 8'h00;
            wait_id_reg <= 8'h00;
        end else begin
            if (i_dc_disp_done && dc_disp_en_reg) begin
                last_disp_id_reg <= pending_disp_id_reg;
            end

            if (state_reg == ST_EXEC_DISP) begin
                pending_disp_id_reg <= cmd_id_reg;
            end

            if (i_ce_tile_done && ce_tile_en_reg) begin
                last_tile_id_reg <= pending_tile_id_reg;
            end

            if (state_reg == ST_EXEC_TILE) begin
                pending_tile_id_reg <= cmd_id_reg;
            end

            if (state_reg == ST_DECODE && (cmd_op_reg == e_cmd_op_wait_disp || cmd_op_reg == e_cmd_op_wait_tile)) begin
                wait_id_reg <= payload_word1_reg[7:0];
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
                end

                ST_READ_PAYLOAD2: begin
                    // Always read word 3 (payload word 3) next
                    cmd_fifo_ren_reg <= 1'b1;
                end

                ST_READ_PAYLOAD3: begin
                    // All 4 words read, no more FIFO reads until next command
                    cmd_fifo_ren_reg <= 1'b0;
                end
            endcase
        end
    end

    assign o_cmd_fifo_ren = cmd_fifo_ren_reg;

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
    // Debug Display (for simulation)
    // ===================================================================

    // `ifdef SIMULATION
    //     always @(posedge i_clk) begin
    //         // Debug: Show why commands are blocked in IDLE
    //         if (state_reg == ST_IDLE && !i_cmd_fifo_empty && state_next == ST_IDLE) begin
    //             // Command available but blocked - show why
    //             if (i_dc_state != 4'd0) 
    //                 $display("[MC_SYNC] @%0t Command blocked: DC not idle (state=%0d)", $time, i_dc_state);
    //             if (i_ce_state != 4'd0)
    //                 $display("[MC_SYNC] @%0t Command blocked: CE not idle (state=%0d)", $time, i_ce_state);
    //             if (i_result_fifo_afull)
    //                 $display("[MC_SYNC] @%0t Command blocked: Result FIFO almost-full", $time);
    //         end
            
    //         if (state_reg == ST_READ_HDR) begin
    //             $display("[MASTER_CONTROL] Header: op=0x%02x, id=%0d, len=%0d",
    //                      i_cmd_fifo_rdata[7:0], i_cmd_fifo_rdata[15:8], i_cmd_fifo_rdata[23:16]);
    //         end

    //         if (state_reg == ST_EXEC_FETCH) begin
    //             $display("[MASTER_CONTROL] FETCH: payload1=0x%08x, payload2=0x%08x -> addr=0x%08x, len=%0d",
    //                      payload_word1_reg, payload_word2_reg,
    //                      payload_word1_reg[link_addr_width_gp-1:0], payload_word2_reg[link_len_width_gp-1:0]);
    //         end

    //         if (state_reg == ST_EXEC_DISP) begin
    //             $display("[MASTER_CONTROL] DISP: tile_addr=%0d, man_nv_cnt=%0d, ugd_vec_size=%0d, man_4b=%0b, col_en=0x%04x",
    //                      o_dc_disp_tile_addr, o_dc_disp_man_nv_cnt, o_dc_disp_ugd_vec_size, o_dc_disp_man_4b, o_dc_disp_col_en);
    //         end

    //         if (state_reg == ST_EXEC_TILE) begin
    //             $display("[MASTER_CONTROL] TILE: L_addr=%0d, R_addr=%0d, vec_len=%0d",
    //                      o_ce_tile_left_addr, o_ce_tile_right_addr, o_ce_tile_vec_len);
    //         end
    //     end
    // `endif
    
    // ===================================================================
    // Debug Output Assignments (for gemm compatibility)
    // ===================================================================
    assign o_mc_state_next = state_next;
    assign o_cmd_op_debug = cmd_op_reg;
    assign o_mc_sees_count = i_cmd_fifo_count;
    assign o_mc_tile_dimensions = {o_ce_tile_left_ugd_len, o_ce_tile_right_ugd_len, o_ce_tile_vec_len, 8'h00};
    assign o_mc_payload_word1 = payload_word1_reg;
    assign o_mc_payload_word2 = payload_word2_reg;
    assign o_mc_payload_word3 = payload_word3_reg;

endmodule : master_control
