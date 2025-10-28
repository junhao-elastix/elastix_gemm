// ------------------------------------------------------------------
// GDDR6-to-BRAM Processor with Configurable Data Processing
//
// This module implements a complete data path that:
// 1. Reads data from GDDR6 memory via AXI4 interface
// 2. Processes data using configurable processing modes
// 3. Writes processed data to BRAM via internal port
//
// Key Features:
// - Internal NAP initiator wrapper (self-contained, follows reg_control_block pattern)
// - Configurable burst length (1-16 beats, each beat = 256 bits)
// - Modular data processor with 6 processing modes (passthrough, add, multiply, ReLU, scale/shift, quantize)
// - Direct BRAM write via internal port (bypasses PCIe DMA)
// - Clock domain crossing for control/status registers
//
// Register Interface (i_reg_clk domain):
// - i_control_reg[0]: Enable (must be 1 for operation)
// - i_control_reg[1]: Trigger (rising edge starts transfer)
// - i_process_mode[31:0]: Processing mode selection
// - i_process_param[31:0]: Processing parameter (mode-specific)
// - o_status_reg[0]: Busy (transfer in progress)
// - o_status_reg[1]: Done (transfer complete)
// - o_status_reg[2]: Error (AXI error or invalid configuration)
// - i_gddr_addr_lo[31:0]: GDDR6 address lower 32 bits
// - i_gddr_addr_hi[9:0]: GDDR6 address upper 10 bits (bits[41:32])
// - i_bram_addr[8:0]: BRAM starting address (9-bit)
// - i_length[7:0]: Transfer length in 256-bit words (1-256)
//
// Processing Modes (i_process_mode):
// - 0x00: Passthrough (no processing)
// - 0x01: Add scalar (adds i_process_param to each 32-bit word)
// - 0x02: Multiply scalar (multiplies each word by i_process_param)
// - 0x03: ReLU activation (if x < 0 then 0, else x)
// - 0x04: Scale and shift (y = (x * scale) + shift, scale in upper 16 bits, shift in lower 16 bits)
// - 0x05: Quantize (round to nearest multiple of i_process_param)
//
// NAP Configuration:
// - NAP placement set in ace_placements.pdc file
// - 28-bit local addressing (NoC handles full 42-bit GDDR6 routing)
// - 256-bit data width
//
// BRAM Interface (i_nap_clk domain):
// - o_bram_wr_en: Write enable
// - o_bram_wr_addr[8:0]: Write address
// - o_bram_wr_data[255:0]: Write data
//
// Timing:
// - Control/status registers cross from i_reg_clk to i_nap_clk
// - All AXI and BRAM operations run in i_nap_clk domain
// - Typical latency: ~100-200 cycles for 1-word transfer
//
// ------------------------------------------------------------------

`include "nap_interfaces.svh"

module gddr6_to_bram_processor
    (
    // Clock and reset
    input  logic        i_nap_clk,          // NAP clock (300-400 MHz) for memory operations
    input  logic        i_reg_clk,          // Register clock (200 MHz) for control/status
    input  logic        i_nap_reset_n,      // Active-low reset synchronized to nap_clk
    input  logic        i_reg_reset_n,      // Active-low reset synchronized to reg_clk

    // Control and status registers (i_reg_clk domain)
    input  logic [31:0] i_control_reg,      // [0]=enable, [1]=trigger
    input  logic [31:0] i_process_mode,     // Processing mode selection
    input  logic [31:0] i_process_param,    // Processing parameter
    output logic [31:0] o_status_reg,       // [0]=busy, [1]=done, [2]=error
    input  logic [31:0] i_gddr_addr_lo,     // GDDR6 address[31:0]
    input  logic [31:0] i_gddr_addr_hi,     // GDDR6 address[41:32] in bits[9:0]
    input  logic [31:0] i_bram_addr,        // BRAM address in bits[8:0]
    input  logic [31:0] i_length,           // Transfer length in bits[7:0] (number of 256-bit words)

    // AXI Interface (connects to NAP responder at top level)
    // Pattern matches reference design: user logic drives AXI interface
    t_AXI4.initiator    axi_if,             // AXI4 interface to NAP responder

    // BRAM write interface (i_nap_clk domain)
    output logic        o_bram_wr_en,       // BRAM write enable
    output logic [8:0]  o_bram_wr_addr,     // BRAM write address
    output logic [255:0] o_bram_wr_data     // BRAM write data
);

    // ----------------------------------------------------------------
    // AXI Interface Configuration
    // ----------------------------------------------------------------
    // axi_if interface is passed as parameter from top level (reference design pattern)
    // NAP responder wrapper is instantiated at TOP LEVEL, not here
    // This module drives AXI master signals through the interface

    // Static AR channel signals (continuous assignment)
    assign axi_if.arsize   = 3'b101;        // 32 bytes (256 bits)
    assign axi_if.arburst  = 2'b01;         // INCR burst
    assign axi_if.arlock   = 1'b0;          // No exclusive access
    assign axi_if.arcache  = 4'b0011;       // Bufferable
    assign axi_if.arprot   = 3'b000;        // Unprivileged, secure, data
    assign axi_if.arqos    = 4'b0000;       // No QoS
    assign axi_if.arregion = 4'b0000;       // No region

    // Static AW (write address) channel tie-offs - never used for read-only operation
    assign axi_if.awvalid  = 1'b0;          // Never initiate writes
    assign axi_if.awaddr   = 42'b0;         // 42-bit address space
    assign axi_if.awlen    = 8'b0;
    assign axi_if.awid     = 8'b0;
    assign axi_if.awsize   = 3'b000;
    assign axi_if.awburst  = 2'b00;
    assign axi_if.awlock   = 1'b0;
    assign axi_if.awcache  = 4'b0000;
    assign axi_if.awprot   = 3'b000;
    assign axi_if.awqos    = 4'b0000;
    assign axi_if.awregion = 4'b0000;

    // Static W (write data) channel tie-offs
    assign axi_if.wvalid   = 1'b0;          // Never send write data
    assign axi_if.wdata    = 256'b0;
    assign axi_if.wstrb    = 32'b0;
    assign axi_if.wlast    = 1'b0;

    // Static B (write response) channel tie-offs
    assign axi_if.bready   = 1'b1;          // Always ready (though never expect responses)

    // ----------------------------------------------------------------
    // Clock Domain Crossing for Control/Status Registers
    // ----------------------------------------------------------------
    // Synchronize control signals from i_reg_clk to i_nap_clk domain

    logic enable_sync, enable_sync_d1;
    logic trigger_sync, trigger_sync_d1, trigger_pulse;
    logic [41:0] gddr_addr_sync;        // Full 42-bit address for GDDR6
    logic [8:0] bram_addr_sync;
    logic [7:0] length_sync;
    logic [31:0] process_mode_sync;
    logic [31:0] process_param_sync;

    // Enable signal (level synchronizer)
    ACX_SYNCHRONIZER i_sync_enable (
        .din    (i_control_reg[0]),
        .dout   (enable_sync),
        .clk    (i_nap_clk),
        .rstn   (i_nap_reset_n)
    );

    // Trigger signal (level synchronizer + edge detector)
    ACX_SYNCHRONIZER i_sync_trigger (
        .din    (i_control_reg[1]),
        .dout   (trigger_sync),
        .clk    (i_nap_clk),
        .rstn   (i_nap_reset_n)
    );

    // Edge detector for trigger (rising edge)
    always_ff @(posedge i_nap_clk or negedge i_nap_reset_n) begin
        if (!i_nap_reset_n) begin
            trigger_sync_d1 <= 1'b0;
            trigger_pulse <= 1'b0;
        end else begin
            trigger_sync_d1 <= trigger_sync;
            trigger_pulse <= trigger_sync & ~trigger_sync_d1;
        end
    end

    // Address synchronizers (full 42-bit GDDR6 address)
    // Lower 32 bits from i_gddr_addr_lo, upper 10 bits from i_gddr_addr_hi[9:0]
    genvar i;
    generate
        for (i = 0; i < 32; i++) begin : gen_addr_lo_sync
            ACX_SYNCHRONIZER i_sync_addr_lo (
                .din    (i_gddr_addr_lo[i]),
                .dout   (gddr_addr_sync[i]),
                .clk    (i_nap_clk),
                .rstn   (i_nap_reset_n)
            );
        end
        for (i = 0; i < 10; i++) begin : gen_addr_hi_sync
            ACX_SYNCHRONIZER i_sync_addr_hi (
                .din    (i_gddr_addr_hi[i]),
                .dout   (gddr_addr_sync[32+i]),
                .clk    (i_nap_clk),
                .rstn   (i_nap_reset_n)
            );
        end
        for (i = 0; i < 9; i++) begin : gen_bram_addr_sync
            ACX_SYNCHRONIZER i_sync_bram_addr (
                .din    (i_bram_addr[i]),
                .dout   (bram_addr_sync[i]),
                .clk    (i_nap_clk),
                .rstn   (i_nap_reset_n)
            );
        end
        for (i = 0; i < 8; i++) begin : gen_length_sync
            ACX_SYNCHRONIZER i_sync_length (
                .din    (i_length[i]),
                .dout   (length_sync[i]),
                .clk    (i_nap_clk),
                .rstn   (i_nap_reset_n)
            );
        end
        // Synchronize process mode and parameter
        for (i = 0; i < 32; i++) begin : gen_process_sync
            ACX_SYNCHRONIZER i_sync_mode (
                .din    (i_process_mode[i]),
                .dout   (process_mode_sync[i]),
                .clk    (i_nap_clk),
                .rstn   (i_nap_reset_n)
            );
            ACX_SYNCHRONIZER i_sync_param (
                .din    (i_process_param[i]),
                .dout   (process_param_sync[i]),
                .clk    (i_nap_clk),
                .rstn   (i_nap_reset_n)
            );
        end
    endgenerate

    // Status register synchronization back to i_reg_clk domain
    logic busy_nap, done_nap, error_nap;
    logic busy_reg, done_reg, error_reg;

    ACX_SYNCHRONIZER i_sync_busy_back (
        .din    (busy_nap),
        .dout   (busy_reg),
        .clk    (i_reg_clk),
        .rstn   (i_reg_reset_n)
    );

    ACX_SYNCHRONIZER i_sync_done_back (
        .din    (done_nap),
        .dout   (done_reg),
        .clk    (i_reg_clk),
        .rstn   (i_reg_reset_n)
    );

    ACX_SYNCHRONIZER i_sync_error_back (
        .din    (error_nap),
        .dout   (error_reg),
        .clk    (i_reg_clk),
        .rstn   (i_reg_reset_n)
    );

    assign o_status_reg = {29'b0, error_reg, done_reg, busy_reg};

    // ----------------------------------------------------------------
    // GDDR6 Address Construction with Page ID
    // ----------------------------------------------------------------
    // GDDR6 address format (42 bits total):
    // [41:33] = 9-bit page ID (channel routing)
    // [32:31] = 2-bit padding
    // [30:5]  = 26-bit local address
    // [4:0]   = 5-bit byte alignment (32-byte words)
    //
    // GDDR6 Channel 0 uses page ID = 13 (from top-level GDDR6_ID_NOC_CH1 mapping)
    // Future enhancement: add register to select channel dynamically

    localparam [8:0] GDDR6_CH0_PAGE_ID = 9'd13;  // Channel 0 page ID (CORRECTED)
    localparam [1:0] GDDR6_ADDR_PAD    = 2'b00;  // Padding bits

    // Construct 42-bit GDDR6 address from synchronized register address
    // Input gddr_addr_sync is byte address from host
    // Output is properly formatted NoC address with embedded page ID
    logic [41:0] gddr_addr_constructed;

    always_comb begin
        // Extract 26-bit word address from byte address (shift right by 5)
        logic [25:0] word_addr_26bit;
        word_addr_26bit = gddr_addr_sync[30:5];  // Byte addr >> 5 = word address

        // Construct full 42-bit NoC address
        gddr_addr_constructed = {
            GDDR6_CH0_PAGE_ID,      // [41:33] 9-bit page ID for channel routing
            GDDR6_ADDR_PAD,         // [32:31] 2-bit padding
            word_addr_26bit,        // [30:5]  26-bit local address
            5'b00000                // [4:0]   5-bit byte alignment (always 0 for aligned access)
        };
    end

    // ----------------------------------------------------------------
    // Data Processor Instance
    // ----------------------------------------------------------------

    logic [255:0] proc_in_data;
    logic         proc_in_valid;
    logic         proc_in_ready;
    logic [255:0] proc_out_data;
    logic         proc_out_valid;
    logic         proc_out_ready;

    g2b_data_processor #(
        .DATA_WIDTH(256),
        .WORD_WIDTH(32),
        .NUM_WORDS(8)
    ) i_data_processor (
        .i_clk          (i_nap_clk),
        .i_reset_n      (i_nap_reset_n),
        .i_mode         (process_mode_sync),
        .i_param        (process_param_sync),
        .i_data         (proc_in_data),
        .i_valid        (proc_in_valid),
        .o_ready        (proc_in_ready),
        .o_data         (proc_out_data),
        .o_valid        (proc_out_valid),
        .i_ready        (proc_out_ready)
    );

    // ----------------------------------------------------------------
    // Main State Machine (i_nap_clk domain)
    // ----------------------------------------------------------------

    typedef enum logic [2:0] {
        IDLE        = 3'b000,   // Waiting for trigger
        READ_ADDR   = 3'b001,   // Issue AXI read address
        READ_DATA   = 3'b010,   // Receive AXI read data
        PROCESS     = 3'b011,   // Process data through data processor
        WRITE_BRAM  = 3'b100,   // Write to BRAM
        CHECK_DONE  = 3'b101,   // Check if all words processed
        DONE        = 3'b110,   // Transfer complete
        ERROR       = 3'b111    // Error occurred
    } state_t;

    state_t state, next_state;

    // State transition
    always_ff @(posedge i_nap_clk or negedge i_nap_reset_n) begin
        if (!i_nap_reset_n)
            state <= IDLE;
        else
            state <= next_state;
    end

    // Counters and registers
    logic [7:0] word_count;         // Number of words remaining
    logic [8:0] bram_write_addr;    // Current BRAM write address
    logic [41:0] gddr_read_addr;    // Current GDDR6 read address (42-bit)
    logic [255:0] read_data_buf;    // Buffer for read data
    logic [255:0] processed_data;   // Data after processing

    // Registered AXI master signals (to avoid multiple drivers on interface)
    logic        arvalid_reg;
    logic [41:0] araddr_reg;        // 42-bit address for GDDR6
    logic [7:0]  arlen_reg;
    logic [7:0]  arid_reg;
    logic        rready_reg;

    // Connect registered outputs to interface (continuous assignment)
    assign axi_if.arvalid = arvalid_reg;
    assign axi_if.araddr  = araddr_reg;
    assign axi_if.arlen   = arlen_reg;
    assign axi_if.arid    = arid_reg;
    assign axi_if.rready  = rready_reg;

    // Next state logic
    always_comb begin
        next_state = state;

        case (state)
            IDLE: begin
                if (enable_sync && trigger_pulse)
                    next_state = READ_ADDR;
            end

            READ_ADDR: begin
                if (axi_if.arvalid && axi_if.arready)
                    next_state = READ_DATA;
            end

            READ_DATA: begin
                if (axi_if.rvalid && axi_if.rready) begin
                    if (axi_if.rresp != 2'b00)
                        next_state = ERROR;
                    else
                        next_state = PROCESS;
                end
            end

            PROCESS: begin
                // Wait for processor to produce valid output
                if (proc_out_valid)
                    next_state = WRITE_BRAM;
            end

            WRITE_BRAM: begin
                next_state = CHECK_DONE;
            end

            CHECK_DONE: begin
                if (word_count == 8'd0)
                    next_state = DONE;
                else
                    next_state = READ_ADDR;
            end

            DONE: begin
                if (!enable_sync || !trigger_sync)
                    next_state = IDLE;
            end

            ERROR: begin
                if (!enable_sync)
                    next_state = IDLE;
            end

            default: next_state = IDLE;
        endcase
    end

    // Control logic for each state
    always_ff @(posedge i_nap_clk or negedge i_nap_reset_n) begin
        if (!i_nap_reset_n) begin
            // Reset registered AXI master signals
            arvalid_reg <= 1'b0;
            araddr_reg <= 42'b0;        // 42-bit address reset
            arlen_reg <= 8'b0;
            arid_reg <= 8'b0;
            rready_reg <= 1'b0;

            word_count <= 8'b0;
            bram_write_addr <= 9'b0;
            gddr_read_addr <= 42'b0;    // 42-bit address reset
            read_data_buf <= 256'b0;
            processed_data <= 256'b0;
            o_bram_wr_en <= 1'b0;
            o_bram_wr_addr <= 9'b0;
            o_bram_wr_data <= 256'b0;
            busy_nap <= 1'b0;
            done_nap <= 1'b0;
            error_nap <= 1'b0;

            // Processor interface signals
            proc_in_data <= 256'b0;
            proc_in_valid <= 1'b0;
            proc_out_ready <= 1'b0;

        end else begin
            // Default: clear one-cycle signals
            arvalid_reg <= 1'b0;
            o_bram_wr_en <= 1'b0;
            proc_in_valid <= 1'b0;  // Default to not sending data to processor

            case (state)
                IDLE: begin
                    busy_nap <= 1'b0;
                    done_nap <= 1'b0;
                    error_nap <= 1'b0;
                    rready_reg <= 1'b0;
                    arvalid_reg <= 1'b0;      // Clear arvalid in IDLE
                    proc_out_ready <= 1'b0;

                    // Capture parameters when trigger is detected (before state transition)
                    if (enable_sync && trigger_pulse) begin
                        word_count <= (length_sync == 8'b0) ? 8'd1 : length_sync;
                        bram_write_addr <= bram_addr_sync;
                        // Use constructed address with embedded page ID for GDDR6 routing
                        gddr_read_addr <= gddr_addr_constructed;
                        // Note: busy_nap stays 0 here, will be set to 1 in READ_ADDR next cycle
                    end
                end

                READ_ADDR: begin
                    busy_nap <= 1'b1;

                    // Set arvalid and address only if not already valid (first cycle in state)
                    if (!arvalid_reg) begin
                        arvalid_reg <= 1'b1;
                        araddr_reg <= gddr_read_addr;
                        arlen_reg <= 8'b0;           // Single beat transfer
                        arid_reg <= 8'h42;           // Transaction ID
                    end

                    // Clear arvalid after handshake completes
                    if (arvalid_reg && axi_if.arready) begin
                        arvalid_reg <= 1'b0;
                    end

                    rready_reg <= 1'b1;          // Ready to receive data
                end

                READ_DATA: begin
                    busy_nap <= 1'b1;
                    rready_reg <= 1'b1;

                    if (axi_if.rvalid && rready_reg) begin
                        // Capture read data
                        read_data_buf <= axi_if.rdata;
                        rready_reg <= 1'b0;
                    end
                end

                PROCESS: begin
                    busy_nap <= 1'b1;
                    // Send data to processor and wait for result
                    if (proc_in_ready && !proc_in_valid && !proc_out_valid) begin
                        // Processor is ready and we haven't sent data yet
                        proc_in_data <= read_data_buf;
                        proc_in_valid <= 1'b1;
                    end else begin
                        proc_in_valid <= 1'b0;
                    end

                    // Be ready to receive processed data
                    proc_out_ready <= 1'b1;

                    // Capture processed data when available
                    if (proc_out_valid) begin
                        processed_data <= proc_out_data;
                        proc_out_ready <= 1'b0;  // Clear ready after capturing
                    end
                end

                WRITE_BRAM: begin
                    busy_nap <= 1'b1;
                    proc_out_ready <= 1'b0;

                    // Write processed data to BRAM
                    o_bram_wr_en <= 1'b1;
                    o_bram_wr_addr <= bram_write_addr;
                    o_bram_wr_data <= processed_data;

                    // Update addresses and counter for next word
                    bram_write_addr <= bram_write_addr + 9'd1;
                    gddr_read_addr <= gddr_read_addr + 42'd32;  // Increment by 32 bytes (256 bits) - 42-bit address
                    word_count <= word_count - 8'd1;
                end

                CHECK_DONE: begin
                    busy_nap <= 1'b1;
                    // Check if more words to process
                    // (Logic handled in next_state)
                end

                DONE: begin
                    busy_nap <= 1'b0;
                    done_nap <= 1'b1;
                    error_nap <= 1'b0;
                end

                ERROR: begin
                    busy_nap <= 1'b0;
                    done_nap <= 1'b0;
                    error_nap <= 1'b1;
                end

                default: begin
                    busy_nap <= 1'b0;
                    done_nap <= 1'b0;
                    error_nap <= 1'b0;
                end
            endcase
        end
    end

endmodule : gddr6_to_bram_processor