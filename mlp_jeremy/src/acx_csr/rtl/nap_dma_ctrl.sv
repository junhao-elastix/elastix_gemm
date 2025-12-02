// ------------------------------------------------------------------
// Simplified interface to NAP AXI responder for memory reads & writes over AXI4
// Connect to a NAP AXI responder 

`include "nap_interfaces.svh"
`include "reg_control_defines.svh"
`include "version_defines.svh"

module nap_dma_ctrl
#(
    parameter   DUMP_WAVES            = 0,  // When set to 1, enables dumping of waves for simulation
    parameter   NAP_COL               = 4'hx,
    parameter   NAP_ROW               = 4'hx,
    localparam  AXI_DATA_WIDTH        = `ACX_NAP_AXI_DATA_WIDTH,
    localparam  MAX_READS_OUTSTANDING = 16
)
(
    // Inputs
    input  wire                         i_clk,
    input  wire                         i_reset_n,
    // AXI-Stream of read requests in
    input  wire                         i_read_valid,
    output wire                         o_read_ready,
    input  wire [36:0]                  i_read_base_addr, // GDDR6 address space
    input  wire [25:0]                  i_read_length,    // In 256-bit words (change to bytes?)
    // AXI-Stream of read data out
    output wire                         o_read_data_valid,
    input  wire                         i_read_data_ready,
    output wire [AXI_DATA_WIDTH -1:0]   o_read_data,
    output wire                         o_read_data_last,
    // (TODO) AXI-Stream of write requests in
    input wire i_write_valid,
    output wire o_write_ready,
    input wire [36:0] i_write_base_addr,
    input wire [25:0] i_write_length,
    // (TODO) AXI-Stream of write data in
    input wire i_write_data_valid,
    output wire o_write_data_ready,
    input wire [AXI_DATA_WIDTH -1:0] i_write_data,
    input wire i_write_data_last
);

assign o_write_ready = 1'b0;
assign o_write_data_ready = 1'b0;

    // Main AXI interface
    t_AXI4 #(
            .DATA_WIDTH (`ACX_NAP_AXI_DATA_WIDTH),
            .ADDR_WIDTH (`ACX_NAP_AXI_INITIATOR_ADDR_WIDTH),
            .LEN_WIDTH  (8),
            .ID_WIDTH   (8))
    axi_if();

    logic nap_output_rstn;  
    logic nap_error_valid;  
    logic [2:0] nap_error_info;

    // Upper bits map to controller - unused, just for info
    logic [32:0] memory_address = i_read_base_addr[32:0];
    logic [3:0] ctrl_id = i_read_base_addr[36:33];

    nap_responder_wrapper #(
        .COLUMN             (NAP_COL),
        .ROW                (NAP_ROW)
    ) i_nap_responder_wrapper (
        .i_clk              (i_clk),
        .i_reset_n          (i_reset_n),
        .nap                (axi_if),
        // TODO - connect error outputs (how are these used?)
        .o_output_rstn      (nap_output_rstn),
        .o_error_valid      (nap_error_valid),
        .o_error_info       (nap_error_info)
    );


    // AXI handshaking signals
    wire ar_fire = axi_if.arvalid & axi_if.arready;
    wire r_fire  = axi_if.rvalid  & axi_if.rready;
    wire r_last = r_fire & axi_if.rlast;
    wire req_fire = i_read_valid & o_read_ready;
    wire o_fire = o_read_data_valid & i_read_data_ready;

    //------------------------------------------------------------
    // DMA Read Burst State Machine
    //------------------------------------------------------------
    
    // Reads don't have to be page-aligned, but they do have to be word-aligned
    // So the lower 5 bits of the address must be zero
    // The length is in 256-bit words, so no alignment issues there
    
    // AXI4 burst constraints
    localparam MAX_BURST_LEN = 256;     // Maximum AXI4 burst length
    
    // Read state machine
    typedef enum logic [2:0] {
        AR_IDLE     = 3'b000,
        AR_SETUP    = 3'b001,
        AR_BURST    = 3'b010,
        AR_WAIT     = 3'b011,
        AR_ERROR    = 3'b111
    } ar_state_t;

    ar_state_t ar_state, ar_next_state;

    // Read request tracking
    logic [36:0] current_addr;          // Current read address
    logic [25:0] words_remaining;       // Words remaining in current request
    logic [7:0]  current_burst_len;     // Current burst length (0-255, actual length is +1)
    logic [7:0]  outstanding_reads;     // Number of outstanding read transactions
    
    // Burst calculation
    logic [25:0] max_words_this_burst;  // Maximum words we can read in this burst
    logic [25:0] words_this_burst;      // Actual words to read in this burst
    
    // Control signals
    logic        can_issue_read;        // Can issue new read transaction
    logic        addr_aligned;          // Address is properly aligned
    logic        length_valid;          // Length is valid (non-zero)
    
    //------------------------------------------------------------
    // Address and Length Validation
    //------------------------------------------------------------
    
    // Check address alignment (must be aligned to 256-bit word boundary)
    assign addr_aligned = (i_read_base_addr[4:0] == 5'b00000);
    
    // Check length validity
    assign length_valid = (i_read_length > 0);
    
    // Can issue read if we have space for outstanding transactions and data remaining
    assign can_issue_read = (outstanding_reads < MAX_READS_OUTSTANDING) && 
                           (words_remaining > 0) && 
                           axi_if.arready;
    
    //------------------------------------------------------------
    // Burst Length Calculation
    //------------------------------------------------------------
    
    // Calculate maximum words we can read in a single burst
    assign max_words_this_burst = (words_remaining > MAX_BURST_LEN) ? 
                                  MAX_BURST_LEN : words_remaining;
    
    // Actual words to read (limited by remaining words)
    assign words_this_burst = max_words_this_burst;
    
    //------------------------------------------------------------
    // Outstanding Transaction Tracking
    //------------------------------------------------------------
    
    always @(posedge i_clk) begin
        if (~i_reset_n) begin
            outstanding_reads <= 8'd0;
        end else begin
            // Count AR as pending until R last received
            case ({ar_fire, r_last})
                2'b10: outstanding_reads <= outstanding_reads + 1;  // AR issued
                2'b01: outstanding_reads <= outstanding_reads - 1;  // R completed
                2'b11: outstanding_reads <= outstanding_reads;      // Both (net zero)
                default: outstanding_reads <= outstanding_reads;     // No change
            endcase
        end
    end
    
    //------------------------------------------------------------
    // Read Request State Machine
    //------------------------------------------------------------
    
    // State register
    always @(posedge i_clk) begin
        if (~i_reset_n) begin
            ar_state <= AR_IDLE;
        end else begin
            ar_state <= ar_next_state;
        end
    end
    
    // Next state logic
    always @(*) begin
        ar_next_state = ar_state;
        
        case (ar_state)
            AR_IDLE: begin
                if (req_fire && addr_aligned && length_valid) begin
                    ar_next_state = AR_SETUP;
                end else if (req_fire && (!addr_aligned || !length_valid)) begin
                    ar_next_state = AR_ERROR;
                end
            end
            
            AR_SETUP: begin
                ar_next_state = AR_BURST;
            end
            
            AR_BURST: begin
                if (can_issue_read) begin
                    if (words_remaining <= words_this_burst) begin
                        // This is the last burst for this request
                        ar_next_state = AR_WAIT;
                    end else begin
                        // More bursts needed, stay in AR_BURST
                        ar_next_state = AR_BURST;
                    end
                end
                // Stay in AR_BURST if can't issue read yet
            end
            
            AR_WAIT: begin
                // Wait for all outstanding reads to complete
                if (outstanding_reads < MAX_READS_OUTSTANDING) begin
                    ar_next_state = AR_IDLE;
                end
            end
            
            AR_ERROR: begin
                ar_next_state = AR_SETUP;
                // TODO - handle bad requests?
                // if (req_fire && addr_aligned && length_valid) begin
                //     ar_next_state = AR_SETUP;
                // end
            end
            
            default: begin
                ar_next_state = AR_IDLE;
            end
        endcase
    end
    
    //------------------------------------------------------------
    // Read Request Control Logic
    //------------------------------------------------------------
    
    always @(posedge i_clk) begin
        if (~i_reset_n) begin
            current_addr <= 37'h0;
            words_remaining <= 26'h0;
            current_burst_len <= 8'h0;
        end else begin
            case (ar_state)
                AR_IDLE: begin
                    if (ar_next_state == AR_SETUP) begin
                        current_addr <= i_read_base_addr;
                        words_remaining <= i_read_length;
                    end
                end
                
                AR_SETUP: begin
                    // Calculate burst length for first transaction
                    current_burst_len <= words_this_burst[7:0] - 1; // AXI len is beats-1
                end
                
                AR_BURST: begin
                    if (ar_fire) begin
                        // Update for next burst
                        current_addr <= current_addr + (words_this_burst << 5); // 32 bytes per word
                        words_remaining <= words_remaining - words_this_burst;
                        current_burst_len <= words_this_burst[7:0] - 1;
                    end
                end
            endcase
        end
    end
    
    //------------------------------------------------------------
    // AXI Read Address Channel Outputs
    //------------------------------------------------------------
    
    assign o_read_ready = (ar_state == AR_IDLE); // && axi_if.arready;
    assign axi_if.araddr[41:37] = 5'b0; // Prefix for GDDR6 address space
    
    always @(posedge i_clk) begin
        if (~i_reset_n) begin
            axi_if.arvalid <= 1'b0;
            axi_if.araddr[36:0]  <= 37'h0;
            axi_if.arlen   <= 8'h0;
            axi_if.arsize  <= 3'b101;  // 32 bytes (256 bits)
            axi_if.arburst <= 2'b01;   // INCR
            axi_if.arlock  <= 1'b0;
            axi_if.arcache <= 4'b0010; // Normal non-cacheable
            axi_if.arprot  <= 3'b000;  // Normal, secure, data
            axi_if.arqos   <= 4'b0000;
            axi_if.arregion <= 4'b0000;
            axi_if.arid    <= 8'h0;
        end else begin
            case (ar_state)
                AR_BURST: begin
                    if (can_issue_read) begin
                        axi_if.arvalid <= 1'b1;
                        axi_if.araddr[36:0] <= current_addr;
                        axi_if.arlen   <= current_burst_len;
                        axi_if.arid    <= 8'h0; // Just set ID to a fixed # to enforce read ordering
                    end else begin
                        axi_if.arvalid <= 1'b0;
                    end
                end
                
                default: begin
                    if (axi_if.arready) begin
                        axi_if.arvalid <= 1'b0;
                    end
                end
            endcase
        end
    end
    
    //------------------------------------------------------------
    // AXI Read Data Channel and Stream Output
    //------------------------------------------------------------
    
    // Direct connection from AXI read data to output stream
    assign o_read_data_valid = axi_if.rvalid;
    assign o_read_data = axi_if.rdata;
    assign o_read_data_last = axi_if.rlast;
    assign axi_if.rready = i_read_data_ready;

initial begin
    if (DUMP_WAVES) begin
        $dumpfile("nap_dma_ctrl_waves.vcd");
        $dumpvars(0, nap_dma_ctrl);
    end
end

endmodule
