//-----------------------------------------------------------------------------
// Module: g2b_data_processor
// Description: GDDR6-to-BRAM data processing pipeline with configurable
//              processing modes. Implements ready/valid streaming interface
//              with single-cycle processing latency for 256-bit data paths.
//
// Target: Achronix Speedster7t @ 400 MHz
// Author: FPGA Architect
// Date: 2025-01-06
//-----------------------------------------------------------------------------

module g2b_data_processor #(
    parameter DATA_WIDTH = 256,
    parameter WORD_WIDTH = 32,
    parameter NUM_WORDS  = DATA_WIDTH / WORD_WIDTH  // 8 words
)(
    // Clock and Reset
    input  logic                    i_clk,
    input  logic                    i_reset_n,

    // Configuration
    input  logic [31:0]            i_mode,     // Processing mode selection
    input  logic [31:0]            i_param,    // Mode-specific parameter

    // Input Stream Interface
    input  logic [DATA_WIDTH-1:0]  i_data,     // Input data (8x32-bit words)
    input  logic                   i_valid,    // Input data valid
    output logic                   o_ready,    // Ready to accept input

    // Output Stream Interface
    output logic [DATA_WIDTH-1:0]  o_data,     // Processed output data
    output logic                   o_valid,    // Output data valid
    input  logic                   i_ready     // Downstream ready
);

    //-------------------------------------------------------------------------
    // Processing Mode Definitions
    //-------------------------------------------------------------------------
    localparam MODE_PASSTHROUGH  = 8'h00;  // Direct passthrough
    localparam MODE_ADD_SCALAR   = 8'h01;  // Add scalar to each word
    localparam MODE_MUL_SCALAR   = 8'h02;  // Multiply each word by scalar
    localparam MODE_RELU         = 8'h03;  // ReLU activation (signed)
    localparam MODE_SCALE_SHIFT  = 8'h04;  // y = (x * scale) + shift
    localparam MODE_QUANTIZE     = 8'h05;  // Round to nearest multiple
    localparam MODE_CUSTOM       = 8'hFF;  // Reserved for future use

    //-------------------------------------------------------------------------
    // Internal Signals
    //-------------------------------------------------------------------------
    logic [DATA_WIDTH-1:0]  data_reg;          // Pipeline register for input data
    logic [31:0]           mode_reg;           // Registered mode for stability
    logic [31:0]           param_reg;          // Registered parameter
    logic                   valid_reg;         // Pipeline stage valid flag
    logic                   pipeline_ready;    // Internal pipeline ready

    // Processed data for each mode (combinational)
    logic [DATA_WIDTH-1:0]  processed_data;

    // Scale and shift extraction for MODE_SCALE_SHIFT
    logic [15:0]           scale_factor;
    logic [15:0]           shift_value;

    // Temporary signals for processing
    logic signed [31:0]    word_in      [NUM_WORDS-1:0];
    logic signed [31:0]    word_out     [NUM_WORDS-1:0];
    logic signed [63:0]    mult_result  [NUM_WORDS-1:0];  // For multiplication ops

    //-------------------------------------------------------------------------
    // Pipeline Control Logic
    //-------------------------------------------------------------------------

    // Ready signal generation - can accept data when:
    // 1. Pipeline is empty (!valid_reg), OR
    // 2. Current data is being accepted downstream (valid_reg && i_ready)
    assign pipeline_ready = !valid_reg || i_ready;
    assign o_ready = pipeline_ready;

    // Pipeline register stage
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            data_reg  <= '0;
            mode_reg  <= '0;
            param_reg <= '0;
            valid_reg <= 1'b0;
        end else begin
            // Update pipeline when ready and input valid
            if (pipeline_ready && i_valid) begin
                data_reg  <= i_data;
                mode_reg  <= i_mode;
                param_reg <= i_param;
                valid_reg <= 1'b1;
            end else if (i_ready && valid_reg) begin
                // Clear valid when data accepted downstream
                valid_reg <= 1'b0;
            end
        end
    end

    //-------------------------------------------------------------------------
    // Data Processing Logic (Combinational)
    //-------------------------------------------------------------------------

    // Extract scale and shift for MODE_SCALE_SHIFT
    assign scale_factor = param_reg[31:16];
    assign shift_value  = param_reg[15:0];

    // Unpack input data into word array for easier processing
    always_comb begin
        for (int i = 0; i < NUM_WORDS; i++) begin
            word_in[i] = data_reg[i*WORD_WIDTH +: WORD_WIDTH];
        end
    end

    // Main processing logic - single cycle, parallel for all 8 words
    always_comb begin
        // Default passthrough
        for (int i = 0; i < NUM_WORDS; i++) begin
            word_out[i] = word_in[i];
        end

        // Process based on mode
        case (mode_reg[7:0])
            MODE_PASSTHROUGH: begin
                // Direct passthrough - already set as default
                for (int i = 0; i < NUM_WORDS; i++) begin
                    word_out[i] = word_in[i];
                end
            end

            MODE_ADD_SCALAR: begin
                // Add parameter to each word (signed addition)
                for (int i = 0; i < NUM_WORDS; i++) begin
                    word_out[i] = word_in[i] + $signed(param_reg);
                end
            end

            MODE_MUL_SCALAR: begin
                // Multiply each word by parameter, truncate to 32-bit
                for (int i = 0; i < NUM_WORDS; i++) begin
                    mult_result[i] = word_in[i] * $signed(param_reg);
                    word_out[i] = mult_result[i][31:0];  // Truncate to 32-bit
                end
            end

            MODE_RELU: begin
                // ReLU activation: if x < 0 then 0, else x
                for (int i = 0; i < NUM_WORDS; i++) begin
                    word_out[i] = (word_in[i] < 0) ? 32'h0 : word_in[i];
                end
            end

            MODE_SCALE_SHIFT: begin
                // y = (x * scale) + shift
                // scale in upper 16 bits, shift in lower 16 bits
                for (int i = 0; i < NUM_WORDS; i++) begin
                    mult_result[i] = word_in[i] * $signed({16'h0, scale_factor});
                    // Right shift by 16 to maintain precision, then add shift
                    word_out[i] = (mult_result[i] >>> 16) + $signed({16'h0, shift_value});
                end
            end

            MODE_QUANTIZE: begin
                // Round to nearest multiple of parameter
                // Avoid division by zero - if param is 0, passthrough
                if (param_reg == 32'h0) begin
                    for (int i = 0; i < NUM_WORDS; i++) begin
                        word_out[i] = word_in[i];
                    end
                end else begin
                    for (int i = 0; i < NUM_WORDS; i++) begin
                        // Round to nearest: add half quantum before truncation
                        logic signed [31:0] half_quantum;
                        logic signed [31:0] quotient;
                        half_quantum = $signed(param_reg) >>> 1;

                        // Handle negative numbers properly
                        if (word_in[i] >= 0) begin
                            quotient = (word_in[i] + half_quantum) / $signed(param_reg);
                        end else begin
                            quotient = (word_in[i] - half_quantum) / $signed(param_reg);
                        end
                        word_out[i] = quotient * $signed(param_reg);
                    end
                end
            end

            MODE_CUSTOM: begin
                // Reserved for future use - passthrough for now
                for (int i = 0; i < NUM_WORDS; i++) begin
                    word_out[i] = word_in[i];
                end
            end

            default: begin
                // Undefined mode - passthrough
                for (int i = 0; i < NUM_WORDS; i++) begin
                    word_out[i] = word_in[i];
                end
            end
        endcase
    end

    // Pack processed words back into output data
    always_comb begin
        for (int i = 0; i < NUM_WORDS; i++) begin
            processed_data[i*WORD_WIDTH +: WORD_WIDTH] = word_out[i];
        end
    end

    //-------------------------------------------------------------------------
    // Output Assignment
    //-------------------------------------------------------------------------
    assign o_data  = processed_data;
    assign o_valid = valid_reg;

    //-------------------------------------------------------------------------
    // Assertions for Verification (Simulation Only)
    //-------------------------------------------------------------------------
    `ifdef SIMULATION
        // Check for valid handshake protocol
        property valid_handshake;
            @(posedge i_clk) disable iff (!i_reset_n)
            (i_valid && o_ready) |=> valid_reg;
        endproperty
        assert property (valid_handshake)
            else $error("Valid handshake protocol violated");

        // Check for no data loss
        property no_data_loss;
            @(posedge i_clk) disable iff (!i_reset_n)
            (o_valid && !i_ready) |=> (o_valid && (o_data == $past(o_data)));
        endproperty
        assert property (no_data_loss)
            else $error("Data loss detected in pipeline");

        // Parameter validation warnings
        always @(posedge i_clk) begin
            if (mode_reg == MODE_QUANTIZE && param_reg == 0) begin
                $warning("QUANTIZE mode with zero parameter - defaulting to passthrough");
            end
        end
    `endif

endmodule