// ------------------------------------------------------------------
// CSR to FIFO Bridge
//
// Purpose: Simple bridge to convert CSR register writes into FIFO pushes
// This allows the validated engine_top.sv (with FIFO interface) to be
// used in hardware with CSR register interface from PCIe.
//
// Functionality:
//  - On i_cmd_submit pulse, push 4 words sequentially to command FIFO
//  - Handles multi-cycle CSR strobes with edge detection
//  - Provides backpressure via o_bridge_busy signal
//
// Author: Junhao Pan
// Date: 10/12/2025
// ------------------------------------------------------------------

module csr_to_fifo_bridge
import gemm_pkg::*;
(
    // Clock and Reset
    input  logic        i_clk,
    input  logic        i_reset_n,

    // CSR Interface (from reg_control_block)
    input  logic [31:0] i_cmd_word0,
    input  logic [31:0] i_cmd_word1,
    input  logic [31:0] i_cmd_word2,
    input  logic [31:0] i_cmd_word3,
    input  logic        i_cmd_submit,  // Write strobe (may be multi-cycle)
    output logic        o_bridge_busy,

    // FIFO Interface (to engine_top command FIFO)
    output logic [31:0] o_fifo_wdata,
    output logic        o_fifo_wen,
    input  logic        i_fifo_full,
    input  logic        i_fifo_afull
);

    // ===================================================================
    // Edge Detection for Multi-Cycle CSR Strobes
    // ===================================================================
    logic cmd_submit_prev;
    logic cmd_submit_pulse;

    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            cmd_submit_prev <= 1'b0;
        end else begin
            cmd_submit_prev <= i_cmd_submit;
        end
    end

    // Rising edge detection: generates 1-cycle pulse on 0->1 transition
    assign cmd_submit_pulse = i_cmd_submit & ~cmd_submit_prev;

    // ===================================================================
    // Command Push State Machine
    // ===================================================================
    typedef enum logic [2:0] {
        ST_IDLE      = 3'd0,
        ST_PUSH_W0   = 3'd1,
        ST_PUSH_W1   = 3'd2,
        ST_PUSH_W2   = 3'd3,
        ST_PUSH_W3   = 3'd4
    } state_t;

    state_t state_reg, state_next;

    // Captured command words
    logic [31:0] word0_reg, word1_reg, word2_reg, word3_reg;

    // ===================================================================
    // State Machine: Sequential Logic
    // ===================================================================
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            state_reg <= ST_IDLE;
            word0_reg <= 32'd0;
            word1_reg <= 32'd0;
            word2_reg <= 32'd0;
            word3_reg <= 32'd0;
        end else begin
            state_reg <= state_next;
            
            // Capture command words on submit pulse
            if (cmd_submit_pulse && state_reg == ST_IDLE) begin
                word0_reg <= i_cmd_word0;
                word1_reg <= i_cmd_word1;
                word2_reg <= i_cmd_word2;
                word3_reg <= i_cmd_word3;
            end
        end
    end

    // ===================================================================
    // State Machine: Combinational Next-State Logic
    // ===================================================================
    always_comb begin
        state_next = state_reg;
        
        case (state_reg)
            ST_IDLE: begin
                if (cmd_submit_pulse && !i_fifo_full) begin
                    state_next = ST_PUSH_W0;
                end
            end
            
            ST_PUSH_W0: begin
                if (!i_fifo_full) begin
                    state_next = ST_PUSH_W1;
                end
            end
            
            ST_PUSH_W1: begin
                if (!i_fifo_full) begin
                    state_next = ST_PUSH_W2;
                end
            end
            
            ST_PUSH_W2: begin
                if (!i_fifo_full) begin
                    state_next = ST_PUSH_W3;
                end
            end
            
            ST_PUSH_W3: begin
                if (!i_fifo_full) begin
                    state_next = ST_IDLE;
                end
            end
            
            default: begin
                state_next = ST_IDLE;
            end
        endcase
    end

    // ===================================================================
    // State Machine: Output Control
    // ===================================================================
    always_comb begin
        // Defaults
        o_fifo_wdata = 32'd0;
        o_fifo_wen = 1'b0;
        o_bridge_busy = 1'b0;
        
        case (state_reg)
            ST_IDLE: begin
                o_fifo_wdata = 32'd0;
                o_fifo_wen = 1'b0;
                o_bridge_busy = 1'b0;
            end
            
            ST_PUSH_W0: begin
                o_fifo_wdata = word0_reg;
                o_fifo_wen = !i_fifo_full;
                o_bridge_busy = 1'b1;
            end
            
            ST_PUSH_W1: begin
                o_fifo_wdata = word1_reg;
                o_fifo_wen = !i_fifo_full;
                o_bridge_busy = 1'b1;
            end
            
            ST_PUSH_W2: begin
                o_fifo_wdata = word2_reg;
                o_fifo_wen = !i_fifo_full;
                o_bridge_busy = 1'b1;
            end
            
            ST_PUSH_W3: begin
                o_fifo_wdata = word3_reg;
                o_fifo_wen = !i_fifo_full;
                o_bridge_busy = 1'b1;
            end
            
            default: begin
                o_fifo_wdata = 32'd0;
                o_fifo_wen = 1'b0;
                o_bridge_busy = 1'b0;
            end
        endcase
    end

endmodule : csr_to_fifo_bridge














