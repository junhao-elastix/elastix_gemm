// ------------------------------------------------------------------
// Parameterized Pipelined Integer Adder Tree
//
// Purpose: Sum N wide signed integers using a binary adder tree
//          with configurable pipelining for timing closure
//
// Features:
//   - Parameterized integer width (64-256 bits)
//   - Parameterized number of inputs (power of 2: 2, 4, 8, 16)
//   - Configurable pipeline segment length
//   - Signed 2's complement arithmetic
//
// Latency: ceil(log2(NUM_ELS) / SEG_LEN) cycles
//
// Author: Generated for MLP GEMM project
// Date: Dec 2025
// ------------------------------------------------------------------

`timescale 1ps / 1ps
`default_nettype none

module int_adder_tree #(
    parameter int INT_WIDTH = 128,    // Integer width: 64-256
    parameter int NUM_ELS   = 4,      // Number of inputs (power of 2: 2, 4, 8, 16)
    parameter int SEG_LEN   = 2       // Pipeline segment length (stages per register)
) (
    input  logic                                clk,
    input  logic                                rst_n,
    input  logic                                en,
    
    input  logic                                i_valid,
    input  logic [NUM_ELS-1:0][INT_WIDTH-1:0]   i_data,
    
    output logic [INT_WIDTH-1:0]                o_sum,
    output logic                                o_valid
);

    // =========================================================================
    // Local Functions
    // =========================================================================
    
    // Ceiling division
    function automatic int cdiv(input int x, input int y);
        return (x + y - 1) / y;
    endfunction

    // =========================================================================
    // Derived Parameters
    // =========================================================================
    localparam int STAGES  = $clog2(NUM_ELS);
    localparam int LATENCY = cdiv(STAGES, SEG_LEN);

    // =========================================================================
    // Intermediate Signals
    // =========================================================================
    // Stage data arrays - each stage has fewer active elements
    logic [STAGES:0][NUM_ELS-1:0][INT_WIDTH-1:0] stage_add;
    logic [STAGES:0][NUM_ELS-1:0][INT_WIDTH-1:0] stage_reg;
    logic [STAGES:0][NUM_ELS-1:0][INT_WIDTH-1:0] stage_data;
    
    // Valid signal delay line
    logic [LATENCY-1:0] valid_delay;

    // =========================================================================
    // Input Assignment
    // =========================================================================
    assign stage_data[0] = i_data;

    // =========================================================================
    // Output Assignment
    // =========================================================================
    assign o_sum = stage_data[STAGES][0];
    assign o_valid = valid_delay[LATENCY-1];

    // =========================================================================
    // Valid Signal Pipeline
    // =========================================================================
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            valid_delay <= '0;
        end else if (en) begin
            if (LATENCY > 1) begin
                valid_delay <= {valid_delay[LATENCY-2:0], i_valid};
            end else begin
                valid_delay <= i_valid;
            end
        end
    end

    // =========================================================================
    // Adder Tree Generation
    // =========================================================================
    genvar s, i;
    generate
        for (s = 0; s < STAGES; s = s + 1) begin : stage_gen
            // Number of active elements at this stage
            localparam int STAGE_ELS = NUM_ELS >> s;
            
            // Addition: pair up adjacent elements
            for (i = 0; i < STAGE_ELS/2; i = i + 1) begin : add_gen
                assign stage_add[s+1][i] = $signed(stage_data[s][2*i]) + 
                                           $signed(stage_data[s][2*i+1]);
            end
            
            // Handle odd number of elements (pass through last element)
            if (STAGE_ELS % 2 == 1) begin : odd_gen
                assign stage_add[s+1][STAGE_ELS/2] = stage_data[s][STAGE_ELS-1];
            end
            
            // Pipeline registers at segment boundaries
            if ((s % SEG_LEN == SEG_LEN - 1) || (s == STAGES - 1)) begin : reg_stage
                // This stage gets a register
                assign stage_data[s+1] = stage_reg[s+1];
                
                for (i = 0; i < (STAGE_ELS + 1) / 2; i = i + 1) begin : reg_gen
                    always_ff @(posedge clk or negedge rst_n) begin
                        if (!rst_n) begin
                            stage_reg[s+1][i] <= '0;
                        end else if (en) begin
                            stage_reg[s+1][i] <= stage_add[s+1][i];
                        end
                    end
                end
            end else begin : comb_stage
                // This stage is combinational (no register)
                assign stage_data[s+1] = stage_add[s+1];
            end
        end
    endgenerate

    // =========================================================================
    // Parameter Validation
    // =========================================================================
    initial begin
        assert (INT_WIDTH >= 64 && INT_WIDTH <= 256)
            else $error("INT_WIDTH must be between 64 and 256");
        assert (NUM_ELS >= 2 && NUM_ELS <= 16)
            else $error("NUM_ELS must be between 2 and 16");
        assert ((NUM_ELS & (NUM_ELS - 1)) == 0)
            else $error("NUM_ELS must be a power of 2");
        assert (SEG_LEN >= 1 && SEG_LEN <= STAGES)
            else $error("SEG_LEN must be between 1 and log2(NUM_ELS)");
    end

endmodule

`default_nettype wire

