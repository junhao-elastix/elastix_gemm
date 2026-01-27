// ------------------------------------------------------------------
// Command BRAM to FIFO Bridge
//
// Purpose: Simple bridge that reads batched commands from DMA BRAM
//          and pushes them to the command FIFO.
//
// Features:
//  - No data manipulation - just transfers data from BRAM to FIFO
//  - Host DMAs commands to BRAM, sets CMD_CNT and CMD_VALID
//  - Bridge reads commands and pushes to FIFO
//  - Clears CMD_VALID when all commands transferred
//  - Backpressure support via FIFO almost-full flag
//
// Data Flow:
//  1. Host DMAs N commands to dma_cmd_in_bram (addresses 0..N-1)
//  2. Host writes CMD_CNT = N
//  3. Host writes CMD_VALID = 1
//  4. Bridge reads from BRAM, pushes 128-bit commands to FIFO
//  5. Bridge clears CMD_VALID when done
//  6. Host polls CMD_VALID, sees 0, can DMA next batch
//
// Command Format:
//  - 1 command = 128 bits = 4 x 32-bit words
//  - BRAM line = 256 bits (lower 128 bits used)
//  - Command bits: [127:96]=word0, [95:64]=word1, [63:32]=word2, [31:0]=word3
//
// FSM (2 states):
//  - IDLE: Wait for VALID, capture cmd_cnt, set rd_addr, go to READ_BRAM
//  - READ_BRAM: Read BRAM, push to FIFO when not afull, decrement cnt
//               When cnt=0, clear VALID and return to IDLE
//
// Author: Junhao Pan
// Date: 2026-01-25
// ------------------------------------------------------------------

module cmd_bram_fifo_bridge (
    input  logic        i_clk,
    input  logic        i_reset_n,

    // Register Interface
    input  logic [31:0] i_cmd_cnt,        // Number of commands to read (from host)
    input  logic        i_cmd_valid,      // Start signal (host writes 1)
    output logic        o_cmd_valid_clr,  // Pulse to clear CMD_VALID when done
    output logic [8:0]  o_rd_addr,        // Current read address (for debug readback)
    output logic        o_bridge_busy,    // Bridge is actively transferring

    // BRAM Read Interface (to dma_cmd_in_bram)
    output logic        o_bram_rd_en,
    output logic [8:0]  o_bram_rd_addr,
    input  logic [255:0] i_bram_rd_data,

    // FIFO Write Interface - 128-bit
    output logic [127:0] o_fifo_wdata,
    output logic         o_fifo_wen,
    input  logic         i_fifo_full,
    input  logic         i_fifo_afull
);

    // ===================================================================
    // State Machine Definition (3 states for proper BRAM timing)
    // ===================================================================
    typedef enum logic [1:0] {
        ST_IDLE        = 2'b00,  // Wait for CMD_VALID
        ST_READ_REQ    = 2'b01,  // Issue BRAM read request
        ST_READ_CAPTURE= 2'b10   // Capture BRAM data and push to FIFO
    } state_t;

    state_t state_reg, state_next;

    // ===================================================================
    // Internal Registers
    // ===================================================================
    logic [8:0]  rd_addr_reg;      // Current read address
    logic [8:0]  cnt_reg;          // Remaining commands to transfer

    // Edge detection for CMD_VALID
    logic cmd_valid_prev;
    logic cmd_valid_rise;

    // ===================================================================
    // Edge Detection for CMD_VALID
    // ===================================================================
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            cmd_valid_prev <= 1'b0;
        end else begin
            cmd_valid_prev <= i_cmd_valid;
        end
    end

    assign cmd_valid_rise = i_cmd_valid & ~cmd_valid_prev;

    // ===================================================================
    // State Machine: Sequential Logic
    // ===================================================================
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            state_reg <= ST_IDLE;
            rd_addr_reg <= 9'd0;
            cnt_reg <= 9'd0;
        end else begin
            state_reg <= state_next;

            case (state_reg)
                ST_IDLE: begin
                    if (cmd_valid_rise && i_cmd_cnt != 32'd0) begin
                        // Capture command count, start at address 0
                        cnt_reg <= i_cmd_cnt[8:0];
                        rd_addr_reg <= 9'd0;
                    end
                end

                ST_READ_REQ: begin
                    // Read request issued this cycle, data arrives next cycle
                    // Nothing to update here - just wait for data
                end

                ST_READ_CAPTURE: begin
                    // BRAM data is now valid on i_bram_rd_data (used directly by output)
                    // If we can push (FIFO not full), advance to next command
                    if (!i_fifo_afull) begin
                        rd_addr_reg <= rd_addr_reg + 1'b1;
                        cnt_reg <= cnt_reg - 1'b1;
                    end
                end

                default: begin
                    state_reg <= ST_IDLE;
                end
            endcase
        end
    end

    // ===================================================================
    // State Machine: Combinational Next-State Logic
    // ===================================================================
    always_comb begin
        state_next = state_reg;

        case (state_reg)
            ST_IDLE: begin
                if (cmd_valid_rise && i_cmd_cnt != 32'd0) begin
                    state_next = ST_READ_REQ;
                end
            end

            ST_READ_REQ: begin
                // After issuing read, always go to capture (1-cycle latency)
                state_next = ST_READ_CAPTURE;
            end

            ST_READ_CAPTURE: begin
                if (i_fifo_afull) begin
                    // FIFO full - wait (stay in capture, will re-read same data)
                    state_next = ST_READ_CAPTURE;
                end else if (cnt_reg == 9'd1) begin
                    // Last command - go back to IDLE
                    state_next = ST_IDLE;
                end else begin
                    // More commands - issue next read
                    state_next = ST_READ_REQ;
                end
            end

            default: begin
                state_next = ST_IDLE;
            end
        endcase
    end

    // ===================================================================
    // Output Logic
    // ===================================================================
    
    // BRAM read interface - enable read in READ_REQ state
    assign o_bram_rd_en = (state_reg == ST_READ_REQ);
    assign o_bram_rd_addr = rd_addr_reg;

    // FIFO write interface - push BRAM data directly in READ_CAPTURE state (if not full)
    // Use i_bram_rd_data directly since it's valid in CAPTURE state (after 1-cycle read latency)
    assign o_fifo_wdata = i_bram_rd_data[127:0];  // Lower 128 bits
    assign o_fifo_wen = (state_reg == ST_READ_CAPTURE) && !i_fifo_afull;

    // Clear CMD_VALID when transitioning from READ_CAPTURE to IDLE (transfer complete)
    assign o_cmd_valid_clr = (state_reg == ST_READ_CAPTURE) && (state_next == ST_IDLE);

    // Bridge busy when not idle
    assign o_bridge_busy = (state_reg != ST_IDLE);
    
    // Debug output
    assign o_rd_addr = rd_addr_reg;

    // ===================================================================
    // Debug Assertions (Simulation Only)
    // ===================================================================
    `ifdef SIMULATION
    always @(posedge i_clk) begin
        if (state_reg == ST_IDLE && cmd_valid_rise) begin
            $display("[CMD_BRAM_BRIDGE] @%0t Starting transfer of %0d commands", 
                     $time, i_cmd_cnt);
        end
        if (o_fifo_wen) begin
            $display("[CMD_BRAM_BRIDGE] @%0t Pushed cmd[%0d] = 0x%032x", 
                     $time, rd_addr_reg, i_bram_rd_data[127:0]);
        end
        if (o_cmd_valid_clr) begin
            $display("[CMD_BRAM_BRIDGE] @%0t Transfer complete", $time);
        end
    end
    `endif

endmodule : cmd_bram_fifo_bridge
