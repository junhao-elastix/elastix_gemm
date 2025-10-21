// ------------------------------------------------------------------
// GFP8 BCV Loop Controller
//
// Purpose: Orchestrate B×C×V nested loops for matrix multiplication
// Algorithm: For each (b,c): accumulate V Native Vector dot products
//
// Matrix Dimensions:
//  - Matrix A (left): B rows × (128×V) columns → uses B×V Native Vectors
//  - Matrix B (right): (128×V) rows × C columns → uses C×V Native Vectors
//  - Output: B × C results (one per (b,c) pair)
//
// State Machine:
//  IDLE         → Wait for TILE command
//  FILL_BUFFER  → Load exponent + 4 mantissa lines for both NV_left and NV_right (11 cycles)
//                 Each BRAM read takes 2 cycles (address reg + data reg), 5 reads total, pipelined
//  COMPUTE_NV   → Compute NV dot product (3 cycles: 2-cycle wait + 1 transition)
//  ACCUM        → Accumulate result into V-loop accumulator (1 cycle)
//  RETURN       → Output final result after V iterations complete (1 cycle)
//
// Latency per output: 11 (fill) + 3 (compute) + 1 (accum) = 15 cycles per V
//                     Total: 15×V + 1 (return) cycles per B×C result
//
// Author: Refactoring from compute_engine.sv
// Date: Fri Oct 10 2025
// ------------------------------------------------------------------

module gfp8_bcv_controller (
    // Clock and Reset
    input  logic        i_clk,
    input  logic        i_reset_n,
    
    // TILE Command Interface
    input  logic        i_tile_en,
    input  logic [7:0]  i_dim_b,              // Output rows (batch)
    input  logic [7:0]  i_dim_c,              // Output columns
    input  logic [7:0]  i_dim_v,              // Inner dimension multiplier (V Native Vectors)
    input  logic [10:0] i_left_base_addr,     // Base address for left matrix in BRAM
    input  logic [10:0] i_right_base_addr,    // Base address for right matrix in BRAM
    output logic        o_tile_done,
    
    // BRAM Mantissa Read Interface (to tile_bram - 512 entries, 9-bit addr)
    output logic [8:0]  o_mem_left_rd_addr,
    output logic        o_mem_left_rd_en,
    input  logic [255:0] i_mem_left_rd_data,

    output logic [8:0]  o_mem_right_rd_addr,
    output logic        o_mem_right_rd_en,
    input  logic [255:0] i_mem_right_rd_data,
    
    // NEW: Exponent Read Interface (to dispatcher_bram exp ports)
    output logic [8:0]  o_left_exp_rd_addr,
    input  logic [7:0]  i_left_exp_rd_data,
    
    output logic [8:0]  o_right_exp_rd_addr,
    input  logic [7:0]  i_right_exp_rd_data,
    
    // Result Interface
    output logic signed [31:0] o_result_mantissa,
    output logic signed [7:0]  o_result_exponent,
    output logic               o_result_valid
);

    // ===================================================================
    // State Machine Definition
    // ===================================================================
    typedef enum logic [2:0] {
        ST_IDLE        = 3'd0,
        ST_FILL_BUFFER = 3'd1,  // Load both NV_left and NV_right (4 cycles)
        ST_COMPUTE_NV  = 3'd2,  // Compute NV dot product (2 cycles)
        ST_ACCUM       = 3'd3,  // Accumulate into V-loop accumulator
        ST_RETURN      = 3'd4,  // Output final result
        ST_DONE        = 3'd5
    } state_t;
    
    state_t state_reg, state_next;
    
    // ===================================================================
    // Loop Indices (B, C, V nested loops)
    // ===================================================================
    logic [7:0] b_idx;  // Batch index (0 to B-1)
    logic [7:0] c_idx;  // Column index (0 to C-1)
    logic [7:0] v_idx;  // Vector index (0 to V-1)
    
    // Dimension registers
    logic [7:0] dim_b_reg, dim_c_reg, dim_v_reg;
    logic [10:0] left_base_reg, right_base_reg;
    
    // Rising edge detection for i_tile_en
    logic i_tile_en_prev;
    logic i_tile_en_rising;
    
    assign i_tile_en_rising = i_tile_en && !i_tile_en_prev;
    
    // ===================================================================
    // Native Vector Buffers (Local Storage)
    // ===================================================================
    
    // NV_left buffer
    logic [31:0]  nv_left_exp;         // 4 bytes (one per group)
    logic [255:0] nv_left_man [0:3];   // 4 lines × 256 bits
    
    // NV_right buffer
    logic [31:0]  nv_right_exp;        // 4 bytes (one per group)
    logic [255:0] nv_right_man [0:3];  // 4 lines × 256 bits
    
    // Fill cycle counter (0-10: grab exponent + 4 mantissa lines from both mem_left and mem_right)
    // Each read takes 2 cycles (pipelined): issue, wait, capture
    logic [4:0] fill_cycle;  // 5 bits to count 0-16
    
    // ===================================================================
    // NV Dot Product Instance
    // ===================================================================
    logic signed [31:0] nv_dot_mantissa;
    logic signed [7:0]  nv_dot_exponent;
    
    // Enable signal: pulse high when entering ST_COMPUTE_NV
    logic nv_dot_input_valid;
    assign nv_dot_input_valid = (state_reg != ST_COMPUTE_NV) && (state_next == ST_COMPUTE_NV);
    
    gfp8_nv_dot u_nv_dot (
        .i_clk              (i_clk),
        .i_reset_n          (i_reset_n),
        .i_input_valid      (nv_dot_input_valid),  // Latch inputs only when entering COMPUTE
        .i_exp_left         (nv_left_exp),
        .i_man_left         (nv_left_man),
        .i_exp_right        (nv_right_exp),
        .i_man_right        (nv_right_man),
        .o_result_mantissa  (nv_dot_mantissa),
        .o_result_exponent  (nv_dot_exponent)
    );
    
    // ===================================================================
    // V-Loop Accumulator
    // ===================================================================
    logic signed [31:0] accum_mantissa;
    logic signed [7:0]  accum_exponent;
    
    // Compute pipeline counter (track 6-cycle latency: 3-stage input + 2 compute + 1 output)
    logic [2:0] compute_wait;
    
    // ===================================================================
    // State Machine - Next State Logic
    // ===================================================================
    always_comb begin
        state_next = state_reg;
        
        case (state_reg)
            ST_IDLE: begin
                if (i_tile_en_rising) begin
                    state_next = ST_FILL_BUFFER;
                end
            end
            
            ST_FILL_BUFFER: begin
                // Wait for fill_cycle 25 to ensure man[3] has been written before transitioning
                // This prevents sampling OLD values in the same cycle as register writes
                if (fill_cycle >= 5'd25) begin  // All exponents + mantissas captured with 2-cycle BRAM latency + 1 wait
                    state_next = ST_COMPUTE_NV;
                end
            end
            
            ST_COMPUTE_NV: begin
                // Wait for gfp8_nv_dot 6-cycle pipeline (3-stage input + 2 compute + 1 output)
                // Cycle 0: i_input_valid high, capture to man_left_captured
                // Cycle 1: propagate man_left_captured → man_left_prop
                // Cycle 2: propagate man_left_prop → man_left_stable
                // Cycle 3: GROUP_DOT can now read stable data (combinational compute)
                // Cycle 4: GROUP_DOT output registered
                // Cycle 5: NV_DOT summation and output ready
                if (compute_wait == 3'd5) begin
                    state_next = ST_ACCUM;
                end
            end
            
            ST_ACCUM: begin
                // Check if V loop is complete
                if (v_idx >= dim_v_reg - 1) begin
                    state_next = ST_RETURN;
                end else begin
                    // More V iterations needed
                    state_next = ST_FILL_BUFFER;
                end
            end
            
            ST_RETURN: begin
                // Check if all B×C outputs are complete
                if (c_idx >= dim_c_reg - 1 && b_idx >= dim_b_reg - 1) begin
                    state_next = ST_DONE;
                end else begin
                    // Start next output element (next b,c pair)
                    state_next = ST_FILL_BUFFER;
                end
            end
            
            ST_DONE: begin
                state_next = ST_IDLE;
            end
            
            default: state_next = ST_IDLE;
        endcase
    end
    
    // ===================================================================
    // State Machine - Sequential Logic
    // ===================================================================
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            state_reg <= ST_IDLE;
        end else begin
            state_reg <= state_next;
        end
    end
    
    // ===================================================================
    // BRAM Read Address Calculation - UNIFIED ADDRESSING
    // ===================================================================
    // NEW: Unified addressing: line_addr = nv_idx * 4 + g_idx
    //   - nv_idx: Native vector index = b_idx * V + v_idx (for left) or c_idx * V + v_idx (for right)
    //   - g_idx: Group index within NV [0-3]
    //   - Exp and Man BRAMs share same line addressing (separate BRAMs, same index)
    
    logic [10:0] left_addr_next, right_addr_next;
    logic [8:0]  left_exp_addr_next, right_exp_addr_next;
    logic left_en_next, right_en_next;
    logic left_exp_en_next, right_exp_en_next;
    
    always_comb begin
        left_addr_next = 11'd0;
        right_addr_next = 11'd0;
        left_exp_addr_next = 9'd0;
        right_exp_addr_next = 9'd0;
        left_en_next = 1'b0;
        right_en_next = 1'b0;
        left_exp_en_next = 1'b0;
        right_exp_en_next = 1'b0;
        
        if (state_reg == ST_FILL_BUFFER) begin
            // Calculate NV index with base address from MATMUL command
            // Base addresses are in BRAM lines (4 lines per NV), convert to NV index
            automatic logic [15:0] left_nv_index;
            automatic logic [15:0] right_nv_index;
            automatic logic [15:0] left_base_nv;
            automatic logic [15:0] right_base_nv;
            automatic logic [8:0] left_line_addr;   // 9-bit for tile_bram (512 entries, 0-511 range)
            automatic logic [8:0] right_line_addr;  // 9-bit for tile_bram (512 entries, 0-511 range)
            automatic logic [1:0] g_idx;
            
            // Convert line addresses to NV indices (divide by 4: addr[10:2])
            // Use registered values for timing stability
            left_base_nv = {5'd0, left_base_reg[10:2]};
            right_base_nv = {5'd0, right_base_reg[10:2]};
            
            // Add base address + relative offset from B/C/V loop counters
            left_nv_index = left_base_nv + ({8'd0, b_idx} * {8'd0, dim_v_reg} + {8'd0, v_idx});
            right_nv_index = right_base_nv + ({8'd0, c_idx} * {8'd0, dim_v_reg} + {8'd0, v_idx});
            
            `ifdef SIMULATION
            if (fill_cycle == 4'd0) begin
                $display("[BCV_ADDR] @%0t [B%0d,C%0d,V%0d] base_nv: L=%0d R=%0d, nv_idx: L=%0d R=%0d, V=%0d",
                         $time, b_idx, c_idx, v_idx, left_base_nv, right_base_nv, 
                         left_nv_index, right_nv_index, dim_v_reg);
            end
            `endif
            
            // Read all 4 group exponents first, then all 4 mantissas
            // With 2-cycle BRAM latency, each address must be held for 3 cycles
            if (fill_cycle == 4'd0 || fill_cycle == 4'd1 || fill_cycle == 4'd2) begin
                // Cycles 0-2: Read exponent for group 0 (hold addr for 3 cycles)
                g_idx = 2'd0;
                left_line_addr = ({left_nv_index[6:0], 2'b00}) + {7'd0, g_idx};   // 9-bit: 128 NVs max (7-bit idx)
                right_line_addr = ({right_nv_index[6:0], 2'b00}) + {7'd0, g_idx}; // 9-bit: 128 NVs max (7-bit idx)

                left_exp_addr_next = left_line_addr[8:0];   // Exponent port is 9-bit
                right_exp_addr_next = right_line_addr[8:0];
                left_exp_en_next = 1'b1;
                right_exp_en_next = 1'b1;
            end else if (fill_cycle == 4'd3 || fill_cycle == 4'd4 || fill_cycle == 5'd5) begin
                // Cycles 3-5: Read exponent for group 1 (hold addr for 3 cycles)
                g_idx = 2'd1;
                left_line_addr = ({left_nv_index[6:0], 2'b00}) + {7'd0, g_idx};
                right_line_addr = ({right_nv_index[6:0], 2'b00}) + {7'd0, g_idx};

                left_exp_addr_next = left_line_addr[8:0];   // Exponent port is 9-bit
                right_exp_addr_next = right_line_addr[8:0];
                left_exp_en_next = 1'b1;
                right_exp_en_next = 1'b1;
            end else if (fill_cycle == 5'd6 || fill_cycle == 5'd7 || fill_cycle == 5'd8) begin
                // Cycles 6-8: Read exponent for group 2 (hold addr for 3 cycles)
                g_idx = 2'd2;
                left_line_addr = ({left_nv_index[6:0], 2'b00}) + {7'd0, g_idx};
                right_line_addr = ({right_nv_index[6:0], 2'b00}) + {7'd0, g_idx};

                left_exp_addr_next = left_line_addr[8:0];   // Exponent port is 9-bit
                right_exp_addr_next = right_line_addr[8:0];
                left_exp_en_next = 1'b1;
                right_exp_en_next = 1'b1;
            end else if (fill_cycle == 5'd9 || fill_cycle == 5'd10 || fill_cycle == 5'd11) begin
                // Cycles 9-11: Read exponent for group 3 (hold addr for 3 cycles)
                g_idx = 2'd3;
                left_line_addr = ({left_nv_index[6:0], 2'b00}) + {7'd0, g_idx};
                right_line_addr = ({right_nv_index[6:0], 2'b00}) + {7'd0, g_idx};

                left_exp_addr_next = left_line_addr[8:0];   // Exponent port is 9-bit
                right_exp_addr_next = right_line_addr[8:0];
                left_exp_en_next = 1'b1;
                right_exp_en_next = 1'b1;
            end else if (fill_cycle == 5'd12 || fill_cycle == 5'd13 || fill_cycle == 5'd14) begin
                // Cycles 12-14: Read mantissa Group 0
                // NEW: NO +16 offset needed - exp and man are in separate BRAMs
                g_idx = 2'd0;
                left_line_addr = ({left_nv_index[6:0], 2'b00}) + {7'd0, g_idx};
                right_line_addr = ({right_nv_index[6:0], 2'b00}) + {7'd0, g_idx};

                left_addr_next = left_line_addr;   // 9-bit addressing for tile_bram [0-511]
                right_addr_next = right_line_addr; // 9-bit addressing for tile_bram [0-511]
                left_en_next = 1'b1;
                right_en_next = 1'b1;
            end else if (fill_cycle == 5'd15 || fill_cycle == 5'd16 || fill_cycle == 5'd17) begin
                // Cycles 15-17: Read mantissa Group 1
                g_idx = 2'd1;
                left_line_addr = ({left_nv_index[6:0], 2'b00}) + {7'd0, g_idx};
                right_line_addr = ({right_nv_index[6:0], 2'b00}) + {7'd0, g_idx};

                left_addr_next = left_line_addr;
                right_addr_next = right_line_addr;
                left_en_next = 1'b1;
                right_en_next = 1'b1;
            end else if (fill_cycle == 5'd18 || fill_cycle == 5'd19 || fill_cycle == 5'd20) begin
                // Cycles 18-20: Read mantissa Group 2
                g_idx = 2'd2;
                left_line_addr = ({left_nv_index[6:0], 2'b00}) + {7'd0, g_idx};
                right_line_addr = ({right_nv_index[6:0], 2'b00}) + {7'd0, g_idx};

                left_addr_next = left_line_addr;
                right_addr_next = right_line_addr;
                left_en_next = 1'b1;
                right_en_next = 1'b1;
            end else if (fill_cycle == 5'd21 || fill_cycle == 5'd22 || fill_cycle == 5'd23) begin
                // Cycles 21-23: Read mantissa Group 3
                g_idx = 2'd3;
                left_line_addr = ({left_nv_index[6:0], 2'b00}) + {7'd0, g_idx};
                right_line_addr = ({right_nv_index[6:0], 2'b00}) + {7'd0, g_idx};

                left_addr_next = left_line_addr;
                right_addr_next = right_line_addr;
                left_en_next = 1'b1;
                right_en_next = 1'b1;
            end
        end
    end
    
    // Register BRAM control signals (mantissa and exponent)
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            o_mem_left_rd_addr <= 11'd0;
            o_mem_left_rd_en <= 1'b0;
            o_mem_right_rd_addr <= 11'd0;
            o_mem_right_rd_en <= 1'b0;
            o_left_exp_rd_addr <= 9'd0;
            o_right_exp_rd_addr <= 9'd0;
        end else begin
            // Mantissa addresses
            o_mem_left_rd_addr <= left_addr_next;
            o_mem_left_rd_en <= left_en_next;
            o_mem_right_rd_addr <= right_addr_next;
            o_mem_right_rd_en <= right_en_next;
            
            // NEW: Exponent addresses
            o_left_exp_rd_addr <= left_exp_addr_next;
            o_right_exp_rd_addr <= right_exp_addr_next;
            
            // `ifdef SIMULATION
            // if (b_idx == 0 && c_idx == 0 && v_idx == 0 && fill_cycle <= 5'd5) begin  // Show cycles 0-5 for first iteration
            //     $display("[BCV_ADDR_REG] @%0t cycle=%0d: right_exp_addr_next=%0d, will be registered to o_right_exp_rd_addr",
            //              $time, fill_cycle, right_exp_addr_next);
            // end
            // `endif
        end
    end
    
    // ===================================================================
    // Buffer Filling Logic (6 cycles to grab both NVs: 1 exp + 4 mantissa + 1 capture)
    // ===================================================================
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            fill_cycle <= 3'd0;
            nv_left_exp <= 32'd0;
            nv_right_exp <= 32'd0;
            for (int i = 0; i < 4; i++) begin
                nv_left_man[i] <= 256'd0;
                nv_right_man[i] <= 256'd0;
            end
        end else begin
            case (state_reg)
                ST_IDLE: begin
                    fill_cycle <= 4'd0;
                end
                
                ST_FILL_BUFFER: begin
                    `ifdef SIMULATION
                    if (b_idx == 0 && c_idx == 0 && v_idx == 0) begin
                        $display("[BCV_FILL_STATE] @%0t ENTERED ST_FILL_BUFFER, fill_cycle=%0d", $time, fill_cycle);
                    end
                    `endif
                    // NEW: Addresses held for 3 cycles, captures on last cycle of new address
                    // Exp addresses: cycles 0-2, 3-5, 6-8, 9-11 → captures at 3, 6, 9, 12
                    // Man addresses: cycles 12-14, 15-17, 18-20, 21-23 → captures at 15, 18, 21, 24
                    if (fill_cycle == 4'd0 || fill_cycle == 4'd1 || fill_cycle == 4'd2) begin
                        // Cycles 0-2: Wait for exp[0] (address held)
                        `ifdef SIMULATION
                        if (b_idx == 0 && c_idx == 0 && v_idx == 0) begin
                            $display("[BCV_INC] @%0t fill_cycle %0d → %0d", $time, fill_cycle, fill_cycle + 1);
                        end
                        `endif
                        fill_cycle <= fill_cycle + 1;
                    end else if (fill_cycle == 4'd3) begin
                        // Cycle 3: Capture exp[0]
                        nv_left_exp[7:0] <= i_left_exp_rd_data;
                        nv_right_exp[7:0] <= i_right_exp_rd_data;
                        `ifdef SIMULATION
                        if (b_idx == 0 && c_idx == 0 && v_idx == 0) begin
                            $display("[BCV_EXP] @%0t V=%0d G=0: left=0x%02x, right=0x%02x",
                                     $time, v_idx, i_left_exp_rd_data, i_right_exp_rd_data);
                        end
                        `endif
                        fill_cycle <= fill_cycle + 1;
                    end else if (fill_cycle == 4'd4 || fill_cycle == 4'd5) begin
                        // Cycles 4-5: Wait for exp[1] (address held)
                        fill_cycle <= fill_cycle + 1;
                    end else if (fill_cycle == 5'd6) begin
                        // Cycle 6: Capture exp[1]
                        nv_left_exp[15:8] <= i_left_exp_rd_data;
                        nv_right_exp[15:8] <= i_right_exp_rd_data;
                        `ifdef SIMULATION
                        if (b_idx == 0 && c_idx == 0 && v_idx == 0) begin
                            $display("[BCV_EXP] @%0t V=%0d G=1: left=0x%02x, right=0x%02x",
                                     $time, v_idx, i_left_exp_rd_data, i_right_exp_rd_data);
                        end
                        `endif
                        fill_cycle <= fill_cycle + 1;
                    end else if (fill_cycle == 5'd7 || fill_cycle == 5'd8) begin
                        // Cycles 7-8: Wait for exp[2] (address held)
                        fill_cycle <= fill_cycle + 1;
                    end else if (fill_cycle == 5'd9) begin
                        // Cycle 9: Capture exp[2]
                        nv_left_exp[23:16] <= i_left_exp_rd_data;
                        nv_right_exp[23:16] <= i_right_exp_rd_data;
                        `ifdef SIMULATION
                        if (b_idx == 0 && c_idx == 0 && v_idx == 0) begin
                            $display("[BCV_EXP] @%0t V=%0d G=2: left=0x%02x, right=0x%02x",
                                     $time, v_idx, i_left_exp_rd_data, i_right_exp_rd_data);
                        end
                        `endif
                        fill_cycle <= fill_cycle + 1;
                    end else if (fill_cycle == 5'd10 || fill_cycle == 5'd11) begin
                        // Cycles 10-11: Wait for exp[3] (address held)
                        fill_cycle <= fill_cycle + 1;
                    end else if (fill_cycle == 5'd12) begin
                        // Cycle 12: Capture exp[3]
                        nv_left_exp[31:24] <= i_left_exp_rd_data;
                        nv_right_exp[31:24] <= i_right_exp_rd_data;
                        `ifdef SIMULATION
                        if (b_idx == 0 && c_idx == 0 && v_idx == 0) begin
                            $display("[BCV_EXP] @%0t V=%0d G=3: left=0x%02x, right=0x%02x",
                                     $time, v_idx, i_left_exp_rd_data, i_right_exp_rd_data);
                        end
                        `endif
                        fill_cycle <= fill_cycle + 1;
                    end else if (fill_cycle == 5'd13 || fill_cycle == 5'd14) begin
                        // Cycles 13-14: Wait for man[0] (address held)
                        fill_cycle <= fill_cycle + 1;
                    end else if (fill_cycle == 5'd15) begin
                        // Cycle 15: Capture man[0]
                        nv_left_man[0] <= i_mem_left_rd_data;
                        nv_right_man[0] <= i_mem_right_rd_data;
                        `ifdef SIMULATION
                        if (b_idx == 0 && c_idx == 0 && v_idx == 0) begin
                            $display("[BCV_DATA] @%0t V=0 G0 CAPTURE: left[0:3]=0x%02x%02x%02x%02x, right[0:3]=0x%02x%02x%02x%02x",
                                     $time,
                                     i_mem_left_rd_data[7:0], i_mem_left_rd_data[15:8], 
                                     i_mem_left_rd_data[23:16], i_mem_left_rd_data[31:24],
                                     i_mem_right_rd_data[7:0], i_mem_right_rd_data[15:8],
                                     i_mem_right_rd_data[23:16], i_mem_right_rd_data[31:24]);
                            $display("[BCV_DATA] @%0t V=0 G0 INTO REG: nv_left_man[0]=0x%064x",
                                     $time, i_mem_left_rd_data);
                        end
                        `endif
                        fill_cycle <= fill_cycle + 1;
                    end else if (fill_cycle == 5'd16 || fill_cycle == 5'd17) begin
                        // Cycles 16-17: Wait for man[1] (address held)
                        fill_cycle <= fill_cycle + 1;
                    end else if (fill_cycle == 5'd18) begin
                        // Cycle 18: Capture man[1]
                        nv_left_man[1] <= i_mem_left_rd_data;
                        nv_right_man[1] <= i_mem_right_rd_data;
                        fill_cycle <= fill_cycle + 1;
                    end else if (fill_cycle == 5'd19 || fill_cycle == 5'd20) begin
                        // Cycles 19-20: Wait for man[2] (address held)
                        fill_cycle <= fill_cycle + 1;
                    end else if (fill_cycle == 5'd21) begin
                        // Cycle 21: Capture man[2]
                        nv_left_man[2] <= i_mem_left_rd_data;
                        nv_right_man[2] <= i_mem_right_rd_data;
                        fill_cycle <= fill_cycle + 1;
                    end else if (fill_cycle == 5'd22 || fill_cycle == 5'd23) begin
                        // Cycles 22-23: Wait for man[3] (address held)
                        fill_cycle <= fill_cycle + 1;
                    end else if (fill_cycle == 5'd24) begin
                        // Cycle 24: Capture man[3]
                        nv_left_man[3] <= i_mem_left_rd_data;
                        nv_right_man[3] <= i_mem_right_rd_data;
                        `ifdef SIMULATION
                        if (b_idx == 0 && c_idx == 0 && v_idx == 0) begin
                            $display("[BCV_MAN3_CAPTURE] @%0t V=0 G3: left=0x%064x, right=0x%064x",
                                     $time, i_mem_left_rd_data, i_mem_right_rd_data);
                        end
                        `endif
                        fill_cycle <= fill_cycle + 1;
                    end else if (fill_cycle == 5'd25) begin
                        // Cycle 25: Wait 1 cycle for man[3] write to propagate before i_input_valid samples
                        fill_cycle <= 5'd0;  // Reset for next iteration
                    end
                end
                
                default: begin
                    fill_cycle <= 4'd0;
                end
            endcase
        end
    end
    
    // ===================================================================
    // Compute Pipeline Control
    // ===================================================================
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            compute_wait <= 3'd0;
        end else begin
            case (state_reg)
                ST_COMPUTE_NV: begin
                    if (compute_wait < 3'd5) begin
                        `ifdef SIMULATION
                        if (compute_wait == 3'd0 && b_idx == 0 && v_idx == 0) begin
                            $display("[BCV_COMPUTE_START] @%0t [B%0d,C%0d,V%0d]", $time, b_idx, c_idx, v_idx);
                            $display("  nv_left_exp=0x%08x  [G0=0x%02x, G1=0x%02x, G2=0x%02x, G3=0x%02x]",
                                     nv_left_exp, nv_left_exp[7:0], nv_left_exp[15:8], nv_left_exp[23:16], nv_left_exp[31:24]);
                            $display("  nv_right_exp=0x%08x [G0=0x%02x, G1=0x%02x, G2=0x%02x, G3=0x%02x]",
                                     nv_right_exp, nv_right_exp[7:0], nv_right_exp[15:8], nv_right_exp[23:16], nv_right_exp[31:24]);
                        end
                        if (compute_wait == 3'd4) begin
                            $display("[BCV_NV_DOT_RESULT] @%0t [B%0d,C%0d,V%0d] mantissa=%0d (0x%08x), exponent=%0d",
                                     $time, b_idx, c_idx, v_idx, nv_dot_mantissa, nv_dot_mantissa, nv_dot_exponent);
                        end
                        `endif
                        compute_wait <= compute_wait + 1;  // Count: 0→1→2→3→4→5
                    end
                end
                default: begin
                    compute_wait <= 3'd0;
                end
            endcase
        end
    end
    
    // ===================================================================
    // V-Loop Accumulation (with Exponent Alignment)
    // ===================================================================
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            accum_mantissa <= 32'sd0;
            accum_exponent <= 8'sd0;
        end else begin
            case (state_reg)
                ST_IDLE: begin
                    accum_mantissa <= 32'sd0;
                    accum_exponent <= 8'sd0;
                end
                
                ST_ACCUM: begin
                    if (v_idx == 8'd0) begin
                        // First V iteration - initialize accumulator
                        accum_mantissa <= nv_dot_mantissa;
                        accum_exponent <= nv_dot_exponent;
                        `ifdef SIMULATION
                        $display("[BCV_ACCUM] @%0t [B%0d,C%0d] V=%0d INIT: mant=%0d (0x%08x), exp=%0d",
                                 $time, b_idx, c_idx, v_idx, nv_dot_mantissa, nv_dot_mantissa, nv_dot_exponent);
                        `endif
                    end else begin
                        // Accumulate with exponent alignment (FIXED: match original implementation)
                        automatic logic signed [7:0] max_exp;
                        automatic logic [7:0] exp_diff_accum, exp_diff_dot;
                        automatic logic signed [31:0] aligned_accum, aligned_dot;
                        automatic logic signed [31:0] sum_mantissa;
                        
                        // Find maximum exponent (using signed comparison for negative exponents)
                        if ($signed(accum_exponent) > $signed(nv_dot_exponent)) begin
                            max_exp = accum_exponent;
                        end else begin
                            max_exp = nv_dot_exponent;
                        end
                        
                        // Align mantissas to maximum exponent
                        exp_diff_accum = max_exp - accum_exponent;
                        exp_diff_dot = max_exp - nv_dot_exponent;
                        
                        // Align accumulated mantissa with underflow check
                        if (exp_diff_accum > 31) begin
                            aligned_accum = 32'sd0;  // Underflow - set to zero
                        end else begin
                            aligned_accum = $signed(accum_mantissa) >>> exp_diff_accum;
                        end
                        
                        // Align dot product mantissa with underflow check
                        if (exp_diff_dot > 31) begin
                            aligned_dot = 32'sd0;  // Underflow - set to zero
                        end else begin
                            aligned_dot = $signed(nv_dot_mantissa) >>> exp_diff_dot;
                        end
                        
                        // Sum aligned mantissas
                        sum_mantissa = aligned_accum + aligned_dot;
                        
                        // Update accumulator
                        accum_mantissa <= sum_mantissa;
                        accum_exponent <= max_exp;
                        `ifdef SIMULATION
                        $display("[BCV_ACCUM] @%0t [B%0d,C%0d] V=%0d ADD: accum_m=%0d(exp=%0d), dot_m=%0d(exp=%0d) → aligned_a=%0d, aligned_d=%0d → sum=%0d(exp=%0d)",
                                 $time, b_idx, c_idx, v_idx, accum_mantissa, accum_exponent, nv_dot_mantissa, nv_dot_exponent,
                                 aligned_accum, aligned_dot, sum_mantissa, max_exp);
                        `endif
                    end
                end
                
                ST_RETURN: begin
                    // Reset accumulator for next B×C output (after outputting result)
                    accum_mantissa <= 32'sd0;
                    accum_exponent <= 8'sd0;
                end
            endcase
        end
    end
    
    // ===================================================================
    // Loop Index Control (B, C, V nested loops)
    // ===================================================================
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            b_idx <= 8'd0;
            c_idx <= 8'd0;
            v_idx <= 8'd0;
            dim_b_reg <= 8'd0;
            dim_c_reg <= 8'd0;
            dim_v_reg <= 8'd0;
            left_base_reg <= 11'd0;
            right_base_reg <= 11'd0;
            i_tile_en_prev <= 1'b0;
        end else begin
            // Update previous value for edge detection
            i_tile_en_prev <= i_tile_en;
            
            case (state_reg)
                ST_IDLE: begin
                    if (i_tile_en_rising) begin
                        // Capture dimensions
                        dim_b_reg <= i_dim_b;
                        dim_c_reg <= i_dim_c;
                        dim_v_reg <= i_dim_v;
                        left_base_reg <= i_left_base_addr;
                        right_base_reg <= i_right_base_addr;
                        // Initialize indices
                        b_idx <= 8'd0;
                        c_idx <= 8'd0;
                        v_idx <= 8'd0;
                        $display("[BCV_LOOP] @%0t NEW TILE: B=%0d, C=%0d, V=%0d, left_base=%0d, right_base=%0d", 
                                 $time, i_dim_b, i_dim_c, i_dim_v, i_left_base_addr, i_right_base_addr);
                        $display("[BCV_LOOP] @%0t DIM_CAPTURE: dim_b_reg=%0d->%0d, dim_c_reg=%0d->%0d, dim_v_reg=%0d->%0d",
                                 $time, dim_b_reg, i_dim_b, dim_c_reg, i_dim_c, dim_v_reg, i_dim_v);
                    end
                end
                
                ST_ACCUM: begin
                    // Advance V index within current (b,c) pair
                    v_idx <= v_idx + 1;
                    $display("[BCV_LOOP] ACCUM: b=%0d, c=%0d, v=%0d -> v=%0d", 
                             b_idx, c_idx, v_idx, v_idx + 1);
                end
                
                ST_RETURN: begin
                    // V loop complete, advance C and B indices
                    v_idx <= 8'd0;  // Reset V for next (b,c) pair
                    
                    $display("[BCV_LOOP] RETURN: b=%0d, c=%0d completed V loop, advancing indices", 
                             b_idx, c_idx);
                    
                    // Only advance indices if NOT done with all outputs
                    if (!(c_idx >= dim_c_reg - 1 && b_idx >= dim_b_reg - 1)) begin
                        // Advance C index
                        if (c_idx >= dim_c_reg - 1) begin
                            c_idx <= 8'd0;
                            // Advance B index
                            b_idx <= b_idx + 1;
                            $display("[BCV_LOOP]   -> Next: b=%0d, c=0", b_idx + 1);
                        end else begin
                            c_idx <= c_idx + 1;
                            $display("[BCV_LOOP]   -> Next: b=%0d, c=%0d", b_idx, c_idx + 1);
                        end
                    end else begin
                        $display("[BCV_LOOP]   -> DONE (all B×C outputs complete)");
                    end
                end
            endcase
        end
    end
    
    // ===================================================================
    // Output Control
    // ===================================================================
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            o_result_mantissa <= 32'sd0;
            o_result_exponent <= 8'sd0;
            o_result_valid <= 1'b0;
            o_tile_done <= 1'b0;
        end else begin
            // Default
            o_result_valid <= 1'b0;
            o_tile_done <= 1'b0;
            
            case (state_reg)
                ST_RETURN: begin
                    // Output accumulated result for this (b,c) pair
                    o_result_mantissa <= accum_mantissa;
                    o_result_exponent <= accum_exponent;
                    o_result_valid <= 1'b1;
                    `ifdef SIMULATION
                    $display("[BCV_ACCUM] @%0t [B%0d,C%0d] RETURN: Final GFP result = mant=%0d (0x%08x), exp=%0d",
                             $time, b_idx, c_idx, accum_mantissa, accum_mantissa, accum_exponent);
                    `endif
                end
                
                ST_DONE: begin
                    o_tile_done <= 1'b1;
                end
            endcase
        end
    end

endmodule

