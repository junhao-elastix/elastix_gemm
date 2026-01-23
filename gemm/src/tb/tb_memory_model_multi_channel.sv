// ------------------------------------------------------------------
// Multi-Channel GDDR6 Memory Model for All 16 Controller IDs
//
// Purpose: Emulates GDDR6 memory with all 16 controller IDs (0x0-0xF)
// Key Features:
//  - Routes based on Ctrl ID in addr[36:33]
//  - Each Ctrl ID has its own 528-line memory block
//  - Supports hex file loading per controller ID
//  - 32 outstanding request limit per channel
//
// Controller ID Mapping (from GDDR6_ADDR_MAPPING.md):
//   0xC, 0xD: Controller 0 Ch0/Ch1 (West)
//   0x4, 0x5: Controller 1 Ch0/Ch1 (West)
//   0x0, 0x1: Controller 2 Ch0/Ch1 (West)
//   0x8, 0x9: Controller 3 Ch0/Ch1 (West)
//   0xF, 0xE: Controller 4 Ch0/Ch1 (East, reversed)
//   0x7, 0x6: Controller 5 Ch0/Ch1 (East, reversed)
//   0x3, 0x2: Controller 6 Ch0/Ch1 (East, reversed)
//   0xB, 0xA: Controller 7 Ch0/Ch1 (East, reversed)
//
// Author: Junhao Pan
// Date: Jan 2026
// ------------------------------------------------------------------

`include "nap_interfaces.svh"

module tb_memory_model_multi_channel
#(
    parameter DATA_WIDTH = 256,
    parameter ADDR_WIDTH = 42,
    parameter LINES_PER_BLOCK = 528,
    parameter NUM_CTRL_IDS = 16,           // 16 controller IDs (0x0-0xF)
    parameter LATENCY_CYCLES = 40,         // 100ns @ 400MHz
    parameter MAX_OUTSTANDING = 32,
    parameter VERBOSITY = 1
)
(
    input  logic        i_clk,
    input  logic        i_reset_n,

    // AXI4 Responder Interface
    t_AXI4.responder    axi_mem_if,

    // Filter to specific Ctrl ID (9'd16 means accept all)
    input  logic [8:0]  i_ctrl_id_filter,

    // Debug/Statistics
    output logic [31:0] o_outstanding_count,
    output logic [31:0] o_total_ar_received,
    output logic [31:0] o_total_r_issued
);

    // ===================================================================
    // Memory Array - Separate block for each Ctrl ID
    // ===================================================================
    // Index: [ctrl_id][line_within_block]
    logic [DATA_WIDTH-1:0] mem_array [0:NUM_CTRL_IDS-1][0:LINES_PER_BLOCK-1];

    // ===================================================================
    // AR Transaction Queue
    // ===================================================================
    typedef struct {
        logic [ADDR_WIDTH-1:0] addr;
        logic [7:0]            arid;
        logic [7:0]            arlen;
        logic [2:0]            arsize;
        logic [1:0]            arburst;
        logic [3:0]            ctrl_id;      // Extracted Ctrl ID
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
    // Ctrl ID Extraction
    // ===================================================================
    function automatic logic [3:0] extract_ctrl_id(logic [ADDR_WIDTH-1:0] addr);
        // Ctrl ID is in addr[36:33]
        extract_ctrl_id = addr[36:33];
    endfunction

    // ===================================================================
    // Line Address Extraction (within a Ctrl ID's memory block)
    // ===================================================================
    function automatic logic [31:0] extract_line_addr(logic [ADDR_WIDTH-1:0] addr);
        // Line address is in addr[30:5] (byte address / 32)
        extract_line_addr = {6'b0, addr[30:5]};
    endfunction

    // ===================================================================
    // Memory Initialization
    // ===================================================================
    initial begin
        if (VERBOSITY >= 1) begin
            $display("[MEM_MULTI_CH] ===============================================");
            $display("[MEM_MULTI_CH] MULTI-CHANNEL GDDR6 MEMORY MODEL");
            $display("[MEM_MULTI_CH] - Ctrl IDs: 16 (0x0-0xF)");
            $display("[MEM_MULTI_CH] - Lines per block: %0d", LINES_PER_BLOCK);
            $display("[MEM_MULTI_CH] - Read Latency: %0d cycles", LATENCY_CYCLES);
            $display("[MEM_MULTI_CH] - Max Outstanding: %0d", MAX_OUTSTANDING);
            $display("[MEM_MULTI_CH] ===============================================");
        end

        // Initialize all memory to zero
        for (int c = 0; c < NUM_CTRL_IDS; c++) begin
            for (int l = 0; l < LINES_PER_BLOCK; l++) begin
                mem_array[c][l] = '0;
            end
        end

        // Load hex files for all 16 controller IDs
        // Using row index mapping from engine_top_2d.sv
        load_hex_to_ctrl_id(4'hC, "/home/dev/Dev/elastix_gemm/hex/left.hex");   // Row 0
        load_hex_to_ctrl_id(4'hD, "/home/dev/Dev/elastix_gemm/hex/right.hex");  // Row 1
        load_hex_to_ctrl_id(4'h4, "/home/dev/Dev/elastix_gemm/hex/left.hex");   // Row 2
        load_hex_to_ctrl_id(4'h5, "/home/dev/Dev/elastix_gemm/hex/right.hex");  // Row 3
        load_hex_to_ctrl_id(4'h0, "/home/dev/Dev/elastix_gemm/hex/left.hex");   // Row 4
        load_hex_to_ctrl_id(4'h1, "/home/dev/Dev/elastix_gemm/hex/right.hex");  // Row 5
        load_hex_to_ctrl_id(4'h8, "/home/dev/Dev/elastix_gemm/hex/left.hex");   // Row 6
        load_hex_to_ctrl_id(4'h9, "/home/dev/Dev/elastix_gemm/hex/right.hex");  // Row 7
        load_hex_to_ctrl_id(4'hF, "/home/dev/Dev/elastix_gemm/hex/left.hex");   // Row 8
        load_hex_to_ctrl_id(4'hE, "/home/dev/Dev/elastix_gemm/hex/right.hex");  // Row 9
        load_hex_to_ctrl_id(4'h7, "/home/dev/Dev/elastix_gemm/hex/left.hex");   // Row 10
        load_hex_to_ctrl_id(4'h6, "/home/dev/Dev/elastix_gemm/hex/right.hex");  // Row 11
        load_hex_to_ctrl_id(4'h3, "/home/dev/Dev/elastix_gemm/hex/left.hex");   // Row 12
        load_hex_to_ctrl_id(4'h2, "/home/dev/Dev/elastix_gemm/hex/right.hex");  // Row 13
        load_hex_to_ctrl_id(4'hB, "/home/dev/Dev/elastix_gemm/hex/left.hex");   // Row 14
        load_hex_to_ctrl_id(4'hA, "/home/dev/Dev/elastix_gemm/hex/right.hex");  // Row 15

        if (VERBOSITY >= 1) $display("[MEM_MULTI_CH] Memory initialization complete");
    end

    // ===================================================================
    // Hex File Loading Task
    // ===================================================================
    task automatic load_hex_to_ctrl_id(
        input [3:0] ctrl_id,
        input string filename
    );
        integer fd;
        string line_str;
        integer line_idx, scan_result;
        logic [7:0] hex_bytes[0:31];
        logic [DATA_WIDTH-1:0] packed_line;

        fd = $fopen(filename, "r");
        if (fd == 0) begin
            if (VERBOSITY >= 1) $display("[MEM_MULTI_CH] WARNING: Cannot open %s for Ctrl ID 0x%01x", filename, ctrl_id);
            return;
        end

        line_idx = 0;
        while (!$feof(fd) && line_idx < LINES_PER_BLOCK) begin
            if ($fgets(line_str, fd)) begin
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
                    packed_line = '0;
                    for (int i = 0; i < 32; i++) begin
                        packed_line[i*8 +: 8] = hex_bytes[i];
                    end
                    mem_array[ctrl_id][line_idx] = packed_line;
                end
                line_idx++;
            end
        end
        $fclose(fd);

        if (VERBOSITY >= 2) begin
            $display("[MEM_MULTI_CH] Loaded %0d lines from %s to Ctrl ID 0x%01x", line_idx, filename, ctrl_id);
        end
    endtask

    // ===================================================================
    // Public Task: Load Hex File to Specific Ctrl ID
    // ===================================================================
    task automatic load_hex_file(
        input [3:0] ctrl_id,
        input string filename
    );
        load_hex_to_ctrl_id(ctrl_id, filename);
    endtask

    // ===================================================================
    // AR Channel Processing
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
                new_ar.ctrl_id = extract_ctrl_id(axi_mem_if.araddr);
                new_ar.latency_remaining = LATENCY_CYCLES;

                // Check if we should accept this Ctrl ID
                if (i_ctrl_id_filter == 9'd16 || i_ctrl_id_filter[3:0] == new_ar.ctrl_id) begin
                    ar_queue.push_back(new_ar);
                    total_ar_received <= total_ar_received + 1;

                    if (VERBOSITY >= 2) begin
                        $display("[MEM_MULTI_CH] @%0t AR: CTRL_ID=0x%01x, ADDR=0x%010h, LEN=%0d",
                                 $time, new_ar.ctrl_id, new_ar.addr, new_ar.arlen + 1);
                    end
                end
            end
        end
    end

    assign ar_accepted = (axi_mem_if.arvalid && axi_mem_if.arready);
    assign axi_mem_if.arready = ~ar_queue_full;

    // ===================================================================
    // Outstanding Counter
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
    // Latency Countdown
    // ===================================================================
    always_ff @(posedge i_clk) begin
        if (i_reset_n) begin
            for (int i = 0; i < ar_queue.size(); i++) begin
                if (ar_queue[i].latency_remaining > 0) begin
                    ar_queue[i].latency_remaining = ar_queue[i].latency_remaining - 1;
                end
            end
        end
    end

    // ===================================================================
    // R Channel State Machine
    // ===================================================================
    typedef enum logic [1:0] {
        R_IDLE    = 2'b00,
        R_SERVING = 2'b01
    } r_state_t;

    r_state_t r_state;
    logic [7:0] r_beat_count;
    ar_transaction_t current_ar;
    logic [ADDR_WIDTH-1:0] current_addr;

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

                        if (VERBOSITY >= 2) begin
                            $display("[MEM_MULTI_CH] @%0t R_START: CTRL_ID=0x%01x, ADDR=0x%010h",
                                     $time, ar_queue[0].ctrl_id, ar_queue[0].addr);
                        end
                    end
                end

                R_SERVING: begin
                    if (axi_mem_if.rready) begin
                        r_beat_count <= r_beat_count + 1;
                        total_r_issued <= total_r_issued + 1;

                        if (current_ar.arburst == 2'b01 && r_beat_count < current_ar.arlen) begin
                            current_addr <= current_addr + 42'h20;
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

    // ===================================================================
    // R Channel Data Output
    // ===================================================================
    logic [DATA_WIDTH-1:0] rdata_reg;
    logic                  rvalid_reg;
    logic                  rlast_reg;
    logic [7:0]            rid_reg;

    logic [3:0]  rd_ctrl_id;
    logic [31:0] rd_line_idx;

    always_comb begin
        rd_ctrl_id = extract_ctrl_id(current_addr);
        rd_line_idx = extract_line_addr(current_addr);
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

                if (rd_line_idx < LINES_PER_BLOCK) begin
                    rdata_reg <= mem_array[rd_ctrl_id][rd_line_idx];
                end else begin
                    rdata_reg <= '0;
                    if (VERBOSITY >= 1) begin
                        $display("[MEM_MULTI_CH] WARNING: Out-of-range access CTRL_ID=0x%01x, LINE=%0d",
                                 rd_ctrl_id, rd_line_idx);
                    end
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
    // AXI Write Channels (unused)
    // ===================================================================
    assign axi_mem_if.awready = 1'b0;
    assign axi_mem_if.wready = 1'b0;
    assign axi_mem_if.bvalid = 1'b0;
    assign axi_mem_if.bid = '0;
    assign axi_mem_if.bresp = '0;

    // ===================================================================
    // Final Statistics
    // ===================================================================
    final begin
        if (VERBOSITY >= 1) begin
            $display("[MEM_MULTI_CH] ===============================================");
            $display("[MEM_MULTI_CH] FINAL: AR=%0d, R=%0d, MaxOutstanding=%0d",
                     total_ar_received, total_r_issued, max_outstanding_reached);
            $display("[MEM_MULTI_CH] ===============================================");
        end
    end

endmodule : tb_memory_model_multi_channel
