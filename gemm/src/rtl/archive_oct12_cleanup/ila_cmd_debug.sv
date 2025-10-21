// ILA Module for Command Submission Debug
// Captures MMIO writes and command path signals

module ila_cmd_debug (
    input  logic        i_clk,
    input  logic        i_reset_n,
    
    // MMIO Register Writes
    input  logic [31:0] i_cmd_word0,
    input  logic [31:0] i_cmd_word1,
    input  logic [31:0] i_cmd_word2,
    input  logic [31:0] i_cmd_word3,
    input  logic [31:0] i_cmd_submit_reg,
    
    // Write Strobe
    input  logic        i_write_strobe,
    
    // Engine Wrapper Inputs
    input  logic        i_engine_submit,
    input  logic        i_cmd_fifo_wen,
    input  logic [31:0] i_cmd_fifo_wdata,
    
    // FIFO Status
    input  logic        i_cmd_fifo_empty,
    input  logic [12:0] i_cmd_fifo_count,
    
    // FSM States
    input  logic [3:0]  i_mc_state,
    input  logic [3:0]  i_dc_state,
    input  logic [3:0]  i_ce_state
);

    // ILA capture depth: 1024 samples
    localparam DEPTH = 1024;
    
    // Probe signals packed for ILA
    logic [255:0] ila_probe;
    
    assign ila_probe = {
        96'h0,                      // [255:160] Reserved
        i_ce_state,                 // [159:156] CE state
        i_dc_state,                 // [155:152] DC state  
        i_mc_state,                 // [151:148] MC state
        3'b0,                       // [147:145] Reserved
        i_cmd_fifo_count,           // [144:132] FIFO count
        i_cmd_fifo_empty,           // [131] FIFO empty
        i_cmd_fifo_wdata,           // [130:99] FIFO write data
        i_cmd_fifo_wen,             // [98] FIFO write enable
        i_engine_submit,            // [97] Engine submit input
        i_write_strobe,             // [96] Write strobe from reg_control_block
        i_cmd_submit_reg,           // [95:64] CMD_SUBMIT register value
        i_cmd_word3,                // [63:32] CMD_WORD3
        i_cmd_word2,                // [31:0]  CMD_WORD2... wait, need more bits
        // Let me reorganize
    };
    
    // Actually pack properly:
    wire [255:0] ila_probe_full;
    assign ila_probe_full = {
        88'h0,                      // [255:168] Reserved
        i_ce_state,                 // [167:164] CE state
        i_dc_state,                 // [163:160] DC state
        i_mc_state,                 // [159:156] MC state
        3'b0,                       // [155:153] Reserved
        i_cmd_fifo_count,           // [152:140] FIFO count (13 bits)
        i_cmd_fifo_empty,           // [139] FIFO empty
        i_cmd_fifo_wen,             // [138] FIFO write enable
        i_engine_submit,            // [137] Engine submit
        i_write_strobe,             // [136] Write strobe
        i_cmd_submit_reg,           // [135:104] CMD_SUBMIT register
        i_cmd_word3,                // [103:72] CMD_WORD3
        i_cmd_word2,                // [71:40] CMD_WORD2
        i_cmd_word1[7:0],           // [39:32] CMD_WORD1 (partial)
        i_cmd_word0                 // [31:0] CMD_WORD0
    };
    
    // Achronix ILA instantiation
    ACX_ILA #(
        .PROBE_WIDTH(256),
        .CAPTURE_DEPTH(1024),
        .TRIGGER_POSITION(128)
    ) i_ila (
        .clk        (i_clk),
        .probe      (ila_probe_full),
        .trigger    (i_write_strobe)  // Trigger on write strobe
    );

endmodule
