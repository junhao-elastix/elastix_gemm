// ------------------------------------------------------------------
// First-Word Fall-Through (FWFT) FIFO for Stack Outputs
//
// Purpose: Small flip-flop based FIFO to decouple MLP stack outputs
//          from the adder tree consumption. Zero-latency read when
//          data is available.
//
// Features:
//   - Parameterizable width and depth (default: 24-bit, 4 entries)
//   - FWFT: Data appears at output immediately when FIFO not empty
//   - Flip-flop based (no BRAM inference - too small)
//   - Full/Empty status flags
//   - Simple push/pop interface
//
// Usage:
//   - Push: Assert i_push when !o_full, data latched on clock edge
//   - Pop:  Assert i_pop when !o_empty, next data appears next cycle
//   - FWFT: o_data is valid whenever !o_empty (no read latency)
//
// Author: FIFO-based MLP Architecture Refactoring
// Date: Jan 16, 2026
// ------------------------------------------------------------------

`timescale 1ps / 1ps
`default_nettype none

module comp_stack_fifo #(
    parameter integer DATA_WIDTH = 24,    // FP24 from MLP stack
    parameter integer DEPTH      = 4      // 2-4 entries sufficient for timing decoupling
) (
    input  logic                    clk,
    input  logic                    rstn,

    // Write Interface
    input  logic [DATA_WIDTH-1:0]   i_data,
    input  logic                    i_push,
    output logic                    o_full,

    // Read Interface (FWFT)
    output logic [DATA_WIDTH-1:0]   o_data,
    input  logic                    i_pop,
    output logic                    o_empty,

    // Status
    output logic [$clog2(DEPTH+1)-1:0] o_count
);

    // =========================================================================
    // Parameters
    // =========================================================================
    localparam PTR_WIDTH = $clog2(DEPTH);
    localparam CNT_WIDTH = $clog2(DEPTH+1);

    // =========================================================================
    // Storage
    // =========================================================================
    logic [DATA_WIDTH-1:0] mem [0:DEPTH-1];

    // =========================================================================
    // Pointers and Count
    // =========================================================================
    logic [PTR_WIDTH-1:0] wr_ptr;
    logic [PTR_WIDTH-1:0] rd_ptr;
    logic [CNT_WIDTH-1:0] count;

    // =========================================================================
    // Status Flags
    // =========================================================================
    logic full_reg;
    logic empty_reg;

    assign o_full  = full_reg;
    assign o_empty = empty_reg;
    assign o_count = count;

    // =========================================================================
    // FWFT Output: Data at read pointer is always valid when not empty
    // =========================================================================
    assign o_data = mem[rd_ptr];

    // =========================================================================
    // Control Logic
    // =========================================================================
    logic do_push;
    logic do_pop;

    assign do_push = i_push && !full_reg;
    assign do_pop  = i_pop && !empty_reg;

    // =========================================================================
    // Pointer and Count Update
    // =========================================================================
    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            wr_ptr    <= '0;
            rd_ptr    <= '0;
            count     <= '0;
            full_reg  <= 1'b0;
            empty_reg <= 1'b1;
        end else begin
            // Write operation
            if (do_push) begin
                mem[wr_ptr] <= i_data;
                if (wr_ptr == DEPTH - 1)
                    wr_ptr <= '0;
                else
                    wr_ptr <= wr_ptr + 1'b1;
            end

            // Read operation
            if (do_pop) begin
                if (rd_ptr == DEPTH - 1)
                    rd_ptr <= '0;
                else
                    rd_ptr <= rd_ptr + 1'b1;
            end

            // Update count
            case ({do_push, do_pop})
                2'b10:   count <= count + 1'b1;  // Push only
                2'b01:   count <= count - 1'b1;  // Pop only
                default: count <= count;          // Both or neither
            endcase

            // Update status flags (combinational next-state calculation)
            case ({do_push, do_pop})
                2'b10: begin
                    // Push only: might become full, definitely not empty
                    full_reg  <= (count == DEPTH - 1);
                    empty_reg <= 1'b0;
                end
                2'b01: begin
                    // Pop only: might become empty, definitely not full
                    full_reg  <= 1'b0;
                    empty_reg <= (count == 1);
                end
                default: begin
                    // Both or neither: no change
                    full_reg  <= full_reg;
                    empty_reg <= empty_reg;
                end
            endcase
        end
    end

    // =========================================================================
    // Simulation Debug
    // =========================================================================
    // synthesis translate_off
    initial begin
        for (int i = 0; i < DEPTH; i++) begin
            mem[i] = '0;
        end
    end

    // Assertions for debugging
    always @(posedge clk) begin
        if (rstn) begin
            if (i_push && full_reg) begin
                $display("[STACK_FIFO] WARNING: Push when full at %0t", $time);
            end
            if (i_pop && empty_reg) begin
                $display("[STACK_FIFO] WARNING: Pop when empty at %0t", $time);
            end
        end
    end
    // synthesis translate_on

endmodule

`default_nettype wire
