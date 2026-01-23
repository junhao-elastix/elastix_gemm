// ------------------------------------------------------------------
// Memory Model for Multi-Iteration GEMM Test
//
// Purpose: Memory model with weight persistence for multi-iteration tests.
//          - Weights (right_*.hex) loaded at addr 0-527 at init (persistent)
//          - Activations (left_*.hex) loaded at addr 528-1055 at init
//          - mem_array is accessible for runtime activation reloading
//
// Memory Layout:
//   Block 0 (addr 0-527):   Weights from right_*.hex (loaded once)
//   Block 1 (addr 528-1055): Activations from left_*.hex (reloadable)
//
// Author: Junhao Pan
// Date: 01/22/2026
// ------------------------------------------------------------------

`include "nap_interfaces.svh"

module tb_mem_model_multi_iter
#(
    parameter DATA_WIDTH = 256,
    parameter ADDR_WIDTH = 42,
    parameter LINES_PER_BLOCK = 528,
    parameter NUM_BLOCKS = 2,
    parameter LATENCY_CYCLES = 40,
    parameter MAX_OUTSTANDING = 32,
    parameter VERBOSITY = 0,
    parameter int CHANNEL_ID = 0,
    parameter string HEX_BASE_PATH = "/home/dev/Dev/elastix_gemm/hex/B4_C4_V32/"
)
(
    input  logic        i_clk,
    input  logic        i_reset_n,
    t_AXI4.responder    axi_mem_if,
    output logic [31:0] o_outstanding_count,
    output logic [31:0] o_total_ar_received,
    output logic [31:0] o_total_r_issued
);

    // ===================================================================
    // Memory Array - Public for hierarchical access from TB
    // ===================================================================
    logic [DATA_WIDTH-1:0] mem_array [0:NUM_BLOCKS*LINES_PER_BLOCK-1];

    // ===================================================================
    // Activation Data Cache - For reloading activations in multi-iter
    // Loaded from left_*.hex at init, can be copied to mem_array[528:1055]
    // ===================================================================
    logic [DATA_WIDTH-1:0] activation_cache [0:LINES_PER_BLOCK-1];

    // ===================================================================
    // AR Transaction Queue (FIFO for outstanding requests)
    // ===================================================================
    typedef struct {
        logic [ADDR_WIDTH-1:0] addr;
        logic [7:0]            arid;
        logic [7:0]            arlen;
        logic [2:0]            arsize;
        logic [1:0]            arburst;
        int                    latency_remaining;
    } ar_transaction_t;

    ar_transaction_t ar_queue[$];
    logic [5:0]      outstanding_count;
    logic            ar_queue_full;

    assign ar_queue_full = (outstanding_count >= MAX_OUTSTANDING);
    assign o_outstanding_count = outstanding_count;

    // ===================================================================
    // Statistics
    // ===================================================================
    logic [31:0] total_ar_received;
    logic [31:0] total_r_issued;
    logic [31:0] max_outstanding_reached;

    assign o_total_ar_received = total_ar_received;
    assign o_total_r_issued = total_r_issued;

    // ===================================================================
    // Memory Initialization - Weights @ 0-527, Activations @ 528-1055
    // ===================================================================
    initial begin
        string left_file, right_file, line_str;
        integer fd_left, fd_right, line_idx, scan_result;
        logic [7:0] hex_bytes[0:31];

        // Initialize all memory to zero
        for (int i = 0; i < NUM_BLOCKS*LINES_PER_BLOCK; i = i + 1) begin
            mem_array[i] = '0;
        end
        for (int i = 0; i < LINES_PER_BLOCK; i = i + 1) begin
            activation_cache[i] = '0;
        end

        // Construct file paths for this channel
        $sformat(left_file, "%sleft_%0d.hex", HEX_BASE_PATH, CHANNEL_ID);
        $sformat(right_file, "%sright_%0d.hex", HEX_BASE_PATH, CHANNEL_ID);

        // ---------------------------------------------------------------
        // Load Block 0: Weights from right_*.hex (addr 0-527)
        // These persist across all iterations - never overwritten
        // ---------------------------------------------------------------
        if (VERBOSITY >= 1) begin
            $display("[MEM_CH%0d] Loading weights from %s to addr 0-527", CHANNEL_ID, right_file);
        end

        fd_right = $fopen(right_file, "r");
        if (fd_right != 0) begin
            line_idx = 0;
            while (!$feof(fd_right) && line_idx < LINES_PER_BLOCK) begin
                if ($fgets(line_str, fd_right)) begin
                    scan_result = $sscanf(line_str,
                        "%h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h",
                        hex_bytes[0], hex_bytes[1], hex_bytes[2], hex_bytes[3],
                        hex_bytes[4], hex_bytes[5], hex_bytes[6], hex_bytes[7],
                        hex_bytes[8], hex_bytes[9], hex_bytes[10], hex_bytes[11],
                        hex_bytes[12], hex_bytes[13], hex_bytes[14], hex_bytes[15],
                        hex_bytes[16], hex_bytes[17], hex_bytes[18], hex_bytes[19],
                        hex_bytes[20], hex_bytes[21], hex_bytes[22], hex_bytes[23],
                        hex_bytes[24], hex_bytes[25], hex_bytes[26], hex_bytes[27],
                        hex_bytes[28], hex_bytes[29], hex_bytes[30], hex_bytes[31]);
                    if (scan_result == 32) begin
                        for (int byte_idx = 0; byte_idx < 32; byte_idx = byte_idx + 1) begin
                            mem_array[line_idx][(byte_idx*8) +: 8] = hex_bytes[byte_idx];
                        end
                    end
                    line_idx = line_idx + 1;
                end
            end
            $fclose(fd_right);
            if (VERBOSITY >= 1) $display("[MEM_CH%0d] Loaded %0d lines of weights", CHANNEL_ID, line_idx);
        end else begin
            $display("[MEM_CH%0d] WARNING: Cannot open %s", CHANNEL_ID, right_file);
        end

        // ---------------------------------------------------------------
        // Load Block 1: Activations from left_*.hex (addr 528-1055)
        // Also cache in activation_cache for runtime reloading
        // ---------------------------------------------------------------
        if (VERBOSITY >= 1) begin
            $display("[MEM_CH%0d] Loading activations from %s to addr 528-1055", CHANNEL_ID, left_file);
        end

        fd_left = $fopen(left_file, "r");
        if (fd_left != 0) begin
            line_idx = 0;
            while (!$feof(fd_left) && line_idx < LINES_PER_BLOCK) begin
                if ($fgets(line_str, fd_left)) begin
                    scan_result = $sscanf(line_str,
                        "%h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h",
                        hex_bytes[0], hex_bytes[1], hex_bytes[2], hex_bytes[3],
                        hex_bytes[4], hex_bytes[5], hex_bytes[6], hex_bytes[7],
                        hex_bytes[8], hex_bytes[9], hex_bytes[10], hex_bytes[11],
                        hex_bytes[12], hex_bytes[13], hex_bytes[14], hex_bytes[15],
                        hex_bytes[16], hex_bytes[17], hex_bytes[18], hex_bytes[19],
                        hex_bytes[20], hex_bytes[21], hex_bytes[22], hex_bytes[23],
                        hex_bytes[24], hex_bytes[25], hex_bytes[26], hex_bytes[27],
                        hex_bytes[28], hex_bytes[29], hex_bytes[30], hex_bytes[31]);
                    if (scan_result == 32) begin
                        for (int byte_idx = 0; byte_idx < 32; byte_idx = byte_idx + 1) begin
                            // Store to main memory (addr 528+)
                            mem_array[LINES_PER_BLOCK + line_idx][(byte_idx*8) +: 8] = hex_bytes[byte_idx];
                            // Also cache for reloading
                            activation_cache[line_idx][(byte_idx*8) +: 8] = hex_bytes[byte_idx];
                        end
                    end
                    line_idx = line_idx + 1;
                end
            end
            $fclose(fd_left);
            if (VERBOSITY >= 1) $display("[MEM_CH%0d] Loaded %0d lines of activations", CHANNEL_ID, line_idx);
        end else begin
            $display("[MEM_CH%0d] WARNING: Cannot open %s", CHANNEL_ID, left_file);
        end
    end

    // ===================================================================
    // Task: Reload Activations from Cache to Memory
    // Called by TB before each iteration to reset activation data
    // ===================================================================
    task automatic reload_activations();
        for (int i = 0; i < LINES_PER_BLOCK; i = i + 1) begin
            mem_array[LINES_PER_BLOCK + i] = activation_cache[i];
        end
    endtask

    // ===================================================================
    // AXI Read Address Channel - Accept ARs with 32-outstanding limit
    // ===================================================================
    logic ar_accepted;
    logic r_burst_complete;

    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            total_ar_received <= '0;
        end else begin
            if (axi_mem_if.arvalid && axi_mem_if.arready) begin
                ar_transaction_t new_ar;
                new_ar.addr = axi_mem_if.araddr;
                new_ar.arid = axi_mem_if.arid;
                new_ar.arlen = axi_mem_if.arlen;
                new_ar.arsize = axi_mem_if.arsize;
                new_ar.arburst = axi_mem_if.arburst;
                new_ar.latency_remaining = LATENCY_CYCLES;
                ar_queue.push_back(new_ar);
                total_ar_received <= total_ar_received + 1;
            end
        end
    end

    assign ar_accepted = (axi_mem_if.arvalid && axi_mem_if.arready);
    assign axi_mem_if.arready = ~ar_queue_full;

    // ===================================================================
    // Outstanding Counter Management
    // ===================================================================
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            outstanding_count <= '0;
            max_outstanding_reached <= '0;
        end else begin
            case ({ar_accepted, r_burst_complete})
                2'b00: outstanding_count <= outstanding_count;
                2'b01: outstanding_count <= outstanding_count - 1;
                2'b10: outstanding_count <= outstanding_count + 1;
                2'b11: outstanding_count <= outstanding_count;
            endcase
            if (ar_accepted && !r_burst_complete) begin
                if ((outstanding_count + 1) > max_outstanding_reached) begin
                    max_outstanding_reached <= outstanding_count + 1;
                end
            end
        end
    end

    // ===================================================================
    // AR Queue Processing - Decrement latency counters
    // ===================================================================
    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            // Queue cleared by reset
        end else begin
            for (int i = 0; i < ar_queue.size(); i = i + 1) begin
                if (ar_queue[i].latency_remaining > 0) begin
                    ar_queue[i].latency_remaining = ar_queue[i].latency_remaining - 1;
                end
            end
        end
    end

    // ===================================================================
    // AXI Read Data Channel - Issue R beats when latency expires
    // ===================================================================
    typedef enum logic [1:0] {
        R_IDLE    = 2'b00,
        R_SERVING = 2'b01
    } r_state_t;

    r_state_t r_state;
    logic [7:0] r_beat_count;
    ar_transaction_t current_ar;
    logic [ADDR_WIDTH-1:0] current_addr;
    logic [31:0] line_idx;

    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            r_state <= R_IDLE;
            r_beat_count <= '0;
            current_addr <= '0;
            total_r_issued <= '0;
            r_burst_complete <= 1'b0;
        end else begin
            r_burst_complete <= 1'b0;

            case (r_state)
                R_IDLE: begin
                    if (ar_queue.size() > 0 && ar_queue[0].latency_remaining == 0) begin
                        current_ar <= ar_queue[0];
                        current_addr <= ar_queue[0].addr;
                        r_beat_count <= 0;
                        r_state <= R_SERVING;
                    end
                end

                R_SERVING: begin
                    if (axi_mem_if.rready) begin
                        r_beat_count <= r_beat_count + 1;
                        total_r_issued <= total_r_issued + 1;
                        if (current_ar.arburst == 2'b01 && r_beat_count < current_ar.arlen) begin
                            if (current_addr[29:5] != 26'h3FFFFFF) begin
                                current_addr <= current_addr + 42'h20;
                            end
                        end
                        if (r_beat_count >= current_ar.arlen) begin
                            void'(ar_queue.pop_front());
                            r_state <= R_IDLE;
                            r_burst_complete <= 1'b1;
                        end
                    end
                end

                default: r_state = R_IDLE;
            endcase
        end
    end

    // Convert address to memory line index
    function automatic logic [31:0] addr_to_line(logic [ADDR_WIDTH-1:0] addr);
        logic [25:0] line_addr_26bit;
        line_addr_26bit = addr[30:5];
        return {6'b0, line_addr_26bit};
    endfunction

    // R channel outputs
    logic [DATA_WIDTH-1:0] rdata_reg;
    logic                  rvalid_reg;
    logic                  rlast_reg;
    logic [7:0]            rid_reg;

    always_comb begin
        line_idx = addr_to_line(current_addr);
    end

    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            rdata_reg <= '0;
            rvalid_reg <= 1'b0;
            rlast_reg <= 1'b0;
            rid_reg <= '0;
        end else begin
            rvalid_reg <= 1'b0;
            rlast_reg <= 1'b0;

            if (r_state == R_SERVING) begin
                rvalid_reg <= 1'b1;
                rid_reg <= current_ar.arid;
                rlast_reg <= (r_beat_count == current_ar.arlen);

                if (line_idx < (NUM_BLOCKS * LINES_PER_BLOCK)) begin
                    rdata_reg <= mem_array[line_idx];
                end else begin
                    rdata_reg <= {DATA_WIDTH{1'b0}};
                end
            end
        end
    end

    assign axi_mem_if.rvalid = rvalid_reg;
    assign axi_mem_if.rdata = rdata_reg;
    assign axi_mem_if.rid = rid_reg;
    assign axi_mem_if.rlast = rlast_reg;
    assign axi_mem_if.rresp = 2'b00;

    // ===================================================================
    // AXI Write Channels (unused - tie off)
    // ===================================================================
    assign axi_mem_if.awready = 1'b0;
    assign axi_mem_if.wready = 1'b0;
    assign axi_mem_if.bvalid = 1'b0;
    assign axi_mem_if.bid = '0;
    assign axi_mem_if.bresp = '0;

endmodule : tb_mem_model_multi_iter
