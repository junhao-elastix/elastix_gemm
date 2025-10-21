// ------------------------------------------------------------------
//
// This Software constitutes an unpublished work and contains
// valuable proprietary information and trade secrets belonging
// to Achronix Semiconductor Corp.
//
// Permission is hereby granted to use this Software including
// without limitation the right to copy, modify, merge or distribute
// copies of the software subject to the following condition:
//
// The above copyright notice and this permission notice shall
// be included in in all copies of the Software.
//
// The Software is provided “as is” without warranty of any kind
// expressed or implied, including  but not limited to the warranties
// of merchantability fitness for a particular purpose and non-infringement.
// In no event shall the copyright holder be liable for any claim,
// damages, or other liability for any damages or other liability,
// whether an action of contract, tort or otherwise, arising from, 
// out of, or in connection with the Software
//
// ------------------------------------------------------------------
// Generate periodically toggling interrupt signals
//      Periods configured by a register (1ms granularity) for each interrupt
// ------------------------------------------------------------------

`include "reg_control_defines.svh"

module irq_gen
#(
    parameter   NUM_CHANNELS            = 1,                            // Number of interrupt channels
    parameter   NUM_REGS                = NUM_CHANNELS * 3              // Number of read and write registers used by the handler
)
(
    input  wire                         i_clk,                          // expecting 200 MHz
    input  wire                         i_reset_n,
    input  t_ACX_USER_REG               i_regs_write [NUM_REGS -1:0],   // Array of registers to configure channel
    
    output t_ACX_USER_REG               o_regs_read  [NUM_REGS -1:0]    // Array of registers to monitor channel
);

    // Register Interface
    localparam    CH_REGS_NUM = 3;  // Each interrupt channel has a CONTROL_REG, PERIOD_REG, and IRQ_REG
    localparam    CONTROL_REG = 0;  // Bit0 enable bit for interrupt channel
    localparam    PERIOD_REG  = 1;  // interrupt period in milliseconds, valid for 1ms to 1s
    localparam    IRQ_REG     = 2;  // Bit0 interrupt signal

    localparam    CLK_CYCLE_CNT_1MS = 'd200000;     // 200,000 clock cycles at 200MHz is 1ms

    logic [NUM_CHANNELS -1:0] irq_signals;
    logic [NUM_CHANNELS -1:0] enable;
    logic [31:0] counter;
    logic [31:0] counters_ms [0:NUM_CHANNELS -1];   // counters in milliseconds

    // count milliseconds increments
    always_ff @(posedge i_clk)
    begin
        if ( ~i_reset_n )
            counter <= 32'h0;
        else if ( enable )
        begin
            if (counter == (CLK_CYCLE_CNT_1MS-1))
                counter <= 32'h0;
            else
                counter <= counter + 32'h1;
        end
        else
            counter <= 32'h0;
    end

    genvar i;
    generate
        for (i = 0; i < NUM_CHANNELS; i++) begin : gb_interrupt_timing
            assign o_regs_read[PERIOD_REG+(CH_REGS_NUM*i)] = i_regs_write[PERIOD_REG+(CH_REGS_NUM*i)];
            assign o_regs_read[IRQ_REG+(CH_REGS_NUM*i)]    = { 31'b0, irq_signals[i] };

            assign enable[i] = i_regs_write[CONTROL_REG+(CH_REGS_NUM*i)][0];

            // Pulse irq signal for one clock cycle every n ms (n being the PERIOD_REG register value)
            always_ff @(posedge i_clk)
            begin
                irq_signals[i] <= 1'b0;
                
                if ( ~i_reset_n )
                begin
                    irq_signals[i] <= 1'b0;
                    counters_ms[i] <= 32'h0;
                end
                else if ( enable[i] )
                begin
                    // interrupt period valid for values 1 to 1000 (1ms to 1s)
                    if ((i_regs_write[PERIOD_REG+(CH_REGS_NUM*i)] > 32'd0) && (i_regs_write[PERIOD_REG+(CH_REGS_NUM*i)] <= 32'd1000))
                    begin
                        if (counter == (CLK_CYCLE_CNT_1MS-1))
                        begin
                            if (counters_ms[i] >= (i_regs_write[PERIOD_REG+(CH_REGS_NUM*i)] - 32'h1))
                            begin
                                irq_signals[i] <= 1'b1;     // set irq signal high since period is reached
                                counters_ms[i] <= 32'h0;    // reset counter to count next period
                            end
                            else
                                counters_ms[i] <= counters_ms[i] + 32'h1;
                        end
                    end
                    else if (i_regs_write[PERIOD_REG+(CH_REGS_NUM*i)] == 32'd0)
                        irq_signals[i] <= 1'b1;     // in the case that period is 0, trigger interrupt once (one rising edge)
                    else
                        counters_ms[i] <= 32'h0;
                end
                else
                begin
                    irq_signals[i] <= 1'b0;
                    counters_ms[i] <= 32'h0;
                end
            end
        end
    endgenerate

endmodule : irq_gen
