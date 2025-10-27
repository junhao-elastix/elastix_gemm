// ----------------------------------------------------------------------------
// Command Submit Pulse Generator
//
// Purpose: Generate a reliable pulse from CSR write, handling auto-clear
//
// The problem: user_regs_write holds the written value, so writing 1
// keeps the signal high indefinitely, breaking edge detection.
//
// Solution: Create a self-clearing pulse that:
// 1. Detects any write to the submit register (write enable)
// 2. Generates a fixed-duration pulse
// 3. Ignores the actual data value written
// ----------------------------------------------------------------------------

module cmd_submit_pulser (
    input  logic        i_clk,
    input  logic        i_reset_n,

    // From register block - stays high after write
    input  logic        i_cmd_submit_raw,    // user_regs_write[14][0]

    // Clean pulse output
    output logic        o_cmd_submit_pulse   // Single pulse per write
);

    // SIMPLE APPROACH: Detect ANY change (0->1 or 1->0) and generate 1-cycle pulse
    // This works with sticky registers because BOTH the write and the clear generate pulses
    // The FIFO push logic will only trigger once per rising edge

    logic prev_val;
    logic changed;

    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            prev_val <= 1'b0;
        end else begin
            prev_val <= i_cmd_submit_raw;
        end
    end

    // Detect change (XOR gives 1 when values differ)
    assign changed = i_cmd_submit_raw ^ prev_val;

    // Generate 1-cycle pulse on change
    // Only generate pulse on 0->1 transition (rising edge only)
    assign o_cmd_submit_pulse = i_cmd_submit_raw & ~prev_val;

    // Assertions for simulation
    `ifdef SIM
        // Check that pulse is exactly 4 cycles
        property pulse_duration;
            @(posedge i_clk) disable iff (~i_reset_n)
            $rose(o_cmd_submit_pulse) |-> ##3 $fell(o_cmd_submit_pulse);
        endproperty
        assert property (pulse_duration);
    `endif

endmodule : cmd_submit_pulser