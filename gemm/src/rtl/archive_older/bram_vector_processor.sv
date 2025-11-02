// ------------------------------------------------------------------
// BRAM Vector Processor - FSM-based Vector Addition
//
// This module implements host-controlled vector addition across 3 BRAM instances:
//   BRAM0[i] + BRAM1[i] -> BRAM2[i] for i ∈ [0, 127]
//
// Data Format:
//   - Each BRAM stores ONE int16 per 256-bit line at bits [15:0]
//   - 128 values total (addresses 0-127)
//   - Byte offset for value i = i x 32 bytes
//
// Operation:
//   1. Host DMAs data to BRAM0 and BRAM1
//   2. Host asserts i_enable and i_process_trigger
//   3. FSM reads BRAM0[i], BRAM1[i], adds them, writes to BRAM2[i]
//   4. FSM asserts o_process_done when complete
//   5. Host DMAs result from BRAM2
//
// FSM States:
//   IDLE         - Waiting for trigger, reset counters and data registers
//   READ_A       - Issue read to BRAM0 (cycle 0)
//   READ_B       - Issue read to BRAM1 (cycle 1)
//   WAIT_DATA_1  - Wait cycle 1 for BRAM read latency (cycle 2)
//   WAIT_DATA_2  - Wait cycle 2, capture data_a and write_addr (cycle 3)
//   ADD_COMPUTE  - Capture data_b, perform addition (cycle 4)
//   WRITE_C      - Write result to BRAM2[write_addr] (cycle 5)
//   INCREMENT    - Increment addr_counter (cycle 6)
//   COMPLETE     - Processing complete, wait for disable
//
// CRITICAL TIMING NOTES:
//   - BRAMs configured with outreg_enable=1 -> 2-cycle read latency
//   - Data capture timing MUST align with BRAM output register delay:
//     * data_a captured in WAIT_DATA_2 (2 cycles after READ_A)
//     * data_b captured in ADD_COMPUTE (2 cycles after READ_B)
//   - Separate write_addr register prevents hazards when addr_counter increments
//   - Per-iteration latency: 7 cycles @ 200 MHz = 35 ns
//   - Total processing time: 128 iterations x 35 ns = 4.48 µs
//
// Development History:
//   - Oct 3, 2025: Fixed BRAM read timing and address increment logic
//     * Root cause: Data captured 1 cycle too early (before output regs stabilized)
//     * Fix: Moved data capture to match 2-cycle BRAM latency
//     * Validation: All 128 vector additions compute correctly
// ------------------------------------------------------------------

`include "nap_interfaces.svh"

module bram_vector_processor (
    // Clock and Reset
    input  logic        i_clk,
    input  logic        i_reset_n,
    
    // Control Interface
    input  logic        i_enable,           // Enable processing
    input  logic        i_process_trigger,  // Start processing (pulse)
    
    // BRAM0 Read Interface (Input A)
    output logic        o_bram0_rd_en,
    output logic [8:0]  o_bram0_rd_addr,
    input  logic [255:0] i_bram0_rd_data,
    
    // BRAM1 Read Interface (Input B)
    output logic        o_bram1_rd_en,
    output logic [8:0]  o_bram1_rd_addr,
    input  logic [255:0] i_bram1_rd_data,
    
    // BRAM2 Write Interface (Output C)
    output logic        o_bram2_wr_en,
    output logic [8:0]  o_bram2_wr_addr,
    output logic [255:0] o_bram2_wr_data,
    
    // Status Outputs
    output logic        o_dma_complete,     // DMA transfer complete (software controlled)
    output logic        o_process_busy,     // Processing in progress
    output logic        o_process_done      // Processing complete
);

    // FSM State Definition
    typedef enum logic [3:0] {
        IDLE         = 4'b0000,  // Waiting for trigger
        READ_A       = 4'b0001,  // Issue read to BRAM0
        READ_B       = 4'b0010,  // Issue read to BRAM1
        WAIT_DATA_1  = 4'b0011,  // Wait cycle 1 for BRAM latency
        WAIT_DATA_2  = 4'b0100,  // Wait cycle 2 for BRAM latency
        ADD_COMPUTE  = 4'b0101,  // Perform addition
        WRITE_C      = 4'b0110,  // Write result to BRAM2
        INCREMENT    = 4'b0111,  // Increment address, check completion
        COMPLETE     = 4'b1000   // Processing done
    } bram_proc_state_t;
    
    bram_proc_state_t current_state, next_state;
    
    // Address Counter (0-127 for 128 int16 values)
    logic [6:0] addr_counter;
    logic [6:0] next_addr_counter;
    logic [6:0] write_addr;       // Separate write address register
    logic [6:0] next_write_addr;
    
    // Data Registers
    logic [15:0] data_a;       // Input A (from BRAM0)
    logic [15:0] data_b;       // Input B (from BRAM1)
    logic [15:0] data_c;       // Output C (sum)
    logic [15:0] next_data_a;
    logic [15:0] next_data_b;
    
    // Control Signals
    logic processing_complete;
    
    localparam NUM_VALUES = 128;
    
    //--------------------------------------------------------------------
    // FSM State Transition Logic
    //--------------------------------------------------------------------
    always_comb begin
        next_state = current_state;
        
        case (current_state)
            IDLE: begin
                if (i_enable && i_process_trigger) begin
                    next_state = READ_A;
                end
            end
            
            READ_A: begin
                next_state = READ_B;  // Immediately move to read B
            end
            
            READ_B: begin
                next_state = WAIT_DATA_1;  // Wait for BRAM read latency
            end
            
            WAIT_DATA_1: begin
                next_state = WAIT_DATA_2;  // Second wait cycle
            end
            
            WAIT_DATA_2: begin
                next_state = ADD_COMPUTE;  // Data ready, proceed to add
            end
            
            ADD_COMPUTE: begin
                next_state = WRITE_C;  // Immediately write result
            end
            
            WRITE_C: begin
                if (processing_complete) begin
                    next_state = COMPLETE;
                end else begin
                    next_state = INCREMENT;  // Go to INCREMENT state
                end
            end
            
            INCREMENT: begin
                next_state = READ_A;  // Next iteration after increment
            end
            
            COMPLETE: begin
                if (!i_enable) begin
                    next_state = IDLE;  // Reset when disabled
                end
            end
            
            default: begin
                next_state = IDLE;
            end
        endcase
    end
    
    //--------------------------------------------------------------------
    // FSM Control Signal Assignments
    //--------------------------------------------------------------------
    always_comb begin
        // Default assignments
        o_bram0_rd_en = 1'b0;
        o_bram1_rd_en = 1'b0;
        o_bram2_wr_en = 1'b0;
        o_process_busy = 1'b0;
        o_process_done = 1'b0;
        next_addr_counter = addr_counter;
        next_write_addr = write_addr;
        next_data_a = data_a;
        next_data_b = data_b;
        
        case (current_state)
            IDLE: begin
                o_bram0_rd_en = 1'b0;
                o_bram1_rd_en = 1'b0;
                o_bram2_wr_en = 1'b0;
                o_process_busy = 1'b0;
                o_process_done = 1'b0;
                next_addr_counter = 7'b0;  // Reset counter
                next_write_addr = 7'b0;     // Reset write address
                next_data_a = 16'b0;        // Reset data_a
                next_data_b = 16'b0;        // Reset data_b
            end
            
            READ_A: begin
                o_bram0_rd_en = 1'b1;      // Issue read to BRAM0
                o_bram1_rd_en = 1'b0;
                o_bram2_wr_en = 1'b0;
                o_process_busy = 1'b1;
                o_process_done = 1'b0;
            end
            
            READ_B: begin
                o_bram0_rd_en = 1'b0;
                o_bram1_rd_en = 1'b1;      // Issue read to BRAM1
                o_bram2_wr_en = 1'b0;
                o_process_busy = 1'b1;
                o_process_done = 1'b0;
            end
            
            WAIT_DATA_1: begin
                o_bram0_rd_en = 1'b0;
                o_bram1_rd_en = 1'b0;
                o_bram2_wr_en = 1'b0;
                o_process_busy = 1'b1;
                o_process_done = 1'b0;
                // Wait cycle 1 - data not yet valid
            end
            
            WAIT_DATA_2: begin
                o_bram0_rd_en = 1'b0;
                o_bram1_rd_en = 1'b0;
                o_bram2_wr_en = 1'b0;
                o_process_busy = 1'b1;
                o_process_done = 1'b0;
                // Capture data_a from BRAM0 (now valid, 2 cycles after READ_A)
                next_data_a = i_bram0_rd_data[15:0];
                next_write_addr = addr_counter;  // Capture write address for current iteration
            end
            
            ADD_COMPUTE: begin
                o_bram0_rd_en = 1'b0;
                o_bram1_rd_en = 1'b0;
                o_bram2_wr_en = 1'b0;
                o_process_busy = 1'b1;
                o_process_done = 1'b0;
                // Capture data_b from BRAM1 (now valid, 2 cycles after READ_B)
                next_data_b = i_bram1_rd_data[15:0];
                // Addition performed in combinational logic below
            end
            
            WRITE_C: begin
                o_bram0_rd_en = 1'b0;
                o_bram1_rd_en = 1'b0;
                o_bram2_wr_en = 1'b1;      // Write result to BRAM2
                o_process_busy = 1'b1;
                o_process_done = 1'b0;
                // Don't increment here - let write complete first
            end
            
            INCREMENT: begin
                o_bram0_rd_en = 1'b0;
                o_bram1_rd_en = 1'b0;
                o_bram2_wr_en = 1'b0;
                o_process_busy = 1'b1;
                o_process_done = 1'b0;
                next_addr_counter = addr_counter + 7'b1;  // Increment address after write
            end
            
            COMPLETE: begin
                o_bram0_rd_en = 1'b0;
                o_bram1_rd_en = 1'b0;
                o_bram2_wr_en = 1'b0;
                o_process_busy = 1'b0;
                o_process_done = 1'b1;     // Signal completion
            end
        endcase
    end
    
    //--------------------------------------------------------------------
    // Address Output Assignment
    //--------------------------------------------------------------------
    assign o_bram0_rd_addr = {2'b00, addr_counter};  // 9-bit address (0-127)
    assign o_bram1_rd_addr = {2'b00, addr_counter};
    assign o_bram2_wr_addr = {2'b00, write_addr};    // Use separate write address
    
    //--------------------------------------------------------------------
    // Addition Logic (Combinational)
    //--------------------------------------------------------------------
    assign data_c = data_a + data_b;  // 16-bit addition
    
    //--------------------------------------------------------------------
    // Write Data Output (256-bit with int16 at [15:0])
    //--------------------------------------------------------------------
    assign o_bram2_wr_data = {240'b0, data_c};  // Place int16 result at [15:0]
    
    //--------------------------------------------------------------------
    // Processing Complete Detection
    //--------------------------------------------------------------------
    assign processing_complete = (addr_counter >= NUM_VALUES - 1);
    
    //--------------------------------------------------------------------
    // DMA Complete Signal (Software Controlled via Future Register)
    //--------------------------------------------------------------------
    // For now, tie to '1' - will be controlled by software in future
    assign o_dma_complete = 1'b1;
    
    //--------------------------------------------------------------------
    // Sequential State Update
    //--------------------------------------------------------------------
    always_ff @(posedge i_clk) begin
        if (!i_reset_n) begin
            current_state <= IDLE;
            addr_counter <= 7'b0;
            write_addr <= 7'b0;
            data_a <= 16'b0;
            data_b <= 16'b0;
        end else begin
            current_state <= next_state;
            addr_counter <= next_addr_counter;
            write_addr <= next_write_addr;
            data_a <= next_data_a;
            data_b <= next_data_b;
        end
    end

endmodule : bram_vector_processor


