`timescale 1ns / 1ps

// MLP BRAM Column Controller
//
// Wrapper around mlp_bram_col that handles:
//   1. Weight Loading: Takes Native Vector and loads into BRAM over 16 cycles
//   2. Compute Control: Takes activation NV and streams din, generating control signals
//
// Weight Loading:
//   - nv_right_man[1023:0]: 128 mantissas (8-bit each)
//   - nv_right_exp[31:0]: 4 exponents (8-bit each), one per 32 elements
//   - col_sel[3:0]: Target column index (0-15)
//   - 16 cycles to load one NV into one bank of one MLP
//
// Compute:
//   - nv_left_man[1023:0]: 128 activation mantissas (8-bit each)
//   - nv_left_exp[31:0]: 4 exponents (8-bit each), one per 32 elements
//   - Streams 8 elements per cycle over 16 cycles
//   - Generates ce, load, accumulate, rdaddr automatically
//
// Column to MLP/Bank Mapping:
//   - mlp_index = col_sel / 2
//   - bank = col_sel % 2 (0 = Bank1/CD/even wraddr, 1 = Bank0/AB/odd wraddr)
//
// Ready-Valid Protocol:
//   - Weight input: i_wt_valid, o_wt_ready
//   - Activation input: i_act_valid, o_act_ready
//   - Results output: o_dout_valid, i_dout_ready

`default_nettype none

module mlp_bram_col_ctrl #(
    parameter integer NUM_MLPS = 8,
    parameter integer PIPELINE_LATENCY = 2  // MLP pipeline latency for load timing
) (
    // Clock and Reset
    input  wire        clk,
    input  wire        rstn,

    // =========================================================================
    // Weight Loading Interface (upstream)
    // =========================================================================
    input  wire        i_wt_valid,           // Weight data valid
    output wire        o_wt_ready,           // Ready to accept weight data
    input  wire [1023:0] i_nv_right_man,     // 128 mantissas (8-bit each)
    input  wire [31:0]   i_nv_right_exp,     // 4 exponents (8-bit each)
    input  wire [3:0]    i_col_sel,          // Target column (0-15)

    // =========================================================================
    // Compute/Activation Interface (upstream)
    // =========================================================================
    input  wire        i_act_valid,          // Activation data valid
    output wire        o_act_ready,          // Ready to accept activation data
    input  wire [1023:0] i_nv_left_man,      // 128 activation mantissas (8-bit each)
    input  wire [31:0]   i_nv_left_exp,      // 4 exponents (8-bit each)
    input  wire        i_new_dot,            // Start new dot product (reset accumulator)

    // =========================================================================
    // Result Interface (downstream)
    // =========================================================================
    output wire [71:0] o_dout [NUM_MLPS-1:0], // MLP outputs
    output wire        o_dout_valid,          // Results valid
    input  wire        i_dout_ready           // Downstream ready

);

    // =========================================================================
    // Weight Loading FSM
    // =========================================================================
    typedef enum logic [1:0] {
        WT_IDLE   = 2'b00,
        WT_LOAD   = 2'b01,
        WT_DONE   = 2'b10
    } wt_state_t;

    wt_state_t wt_state_reg, wt_state_next;

    // Weight cycle counter (0-15 for 16 cycles)
    logic [3:0] wt_cycle_cnt;

    // Latched weight data
    logic [1023:0] wt_man_reg;
    logic [31:0]   wt_exp_reg;
    logic [3:0]    col_sel_reg;

    // =========================================================================
    // Compute FSM
    // =========================================================================
    typedef enum logic [2:0] {
        COMP_IDLE    = 3'b000,
        COMP_SETUP   = 3'b001,  // Setup cycle: ce=1, rdaddr=0, wait for BRAM
        COMP_STREAM  = 3'b010,
        COMP_DRAIN   = 3'b011
    } comp_state_t;

    comp_state_t comp_state_reg, comp_state_next;

    // Compute cycle counter (0-15 for 16 cycles of streaming)
    logic [3:0] comp_cycle_cnt;

    // Drain counter for pipeline flush
    logic [2:0] drain_cnt;

    // Latched activation data
    logic [1023:0] act_man_reg;
    logic [31:0]   act_exp_reg;
    logic          new_dot_reg;

    // =========================================================================
    // Weight Data Extraction
    // =========================================================================
    logic [63:0] wt_man_group;
    logic [7:0]  wt_exp_group;

    always_comb begin
        // Select 64-bit mantissa group (8 elements × 8 bits)
        case (wt_cycle_cnt)
            4'd0:  wt_man_group = wt_man_reg[63:0];
            4'd1:  wt_man_group = wt_man_reg[127:64];
            4'd2:  wt_man_group = wt_man_reg[191:128];
            4'd3:  wt_man_group = wt_man_reg[255:192];
            4'd4:  wt_man_group = wt_man_reg[319:256];
            4'd5:  wt_man_group = wt_man_reg[383:320];
            4'd6:  wt_man_group = wt_man_reg[447:384];
            4'd7:  wt_man_group = wt_man_reg[511:448];
            4'd8:  wt_man_group = wt_man_reg[575:512];
            4'd9:  wt_man_group = wt_man_reg[639:576];
            4'd10: wt_man_group = wt_man_reg[703:640];
            4'd11: wt_man_group = wt_man_reg[767:704];
            4'd12: wt_man_group = wt_man_reg[831:768];
            4'd13: wt_man_group = wt_man_reg[895:832];
            4'd14: wt_man_group = wt_man_reg[959:896];
            4'd15: wt_man_group = wt_man_reg[1023:960];
        endcase

        // Select exponent based on cycle count (one exp per 32 elements = 4 cycles)
        case (wt_cycle_cnt[3:2])
            2'd0: wt_exp_group = wt_exp_reg[7:0];
            2'd1: wt_exp_group = wt_exp_reg[15:8];
            2'd2: wt_exp_group = wt_exp_reg[23:16];
            2'd3: wt_exp_group = wt_exp_reg[31:24];
        endcase
    end

    // Pack into 72-bit bram_din format: {exp[7:0], man[63:0]}
    // Reference testbench packs with reversal: [exp,m0,m1,m2,m3,m4,m5,m6,m7]
    // This puts exponent at MSB (bits 71:64), mantissas at LSB (bits 63:0)
    wire [71:0] bram_din_wt = {wt_exp_group, wt_man_group};

    // =========================================================================
    // Activation Data Extraction
    // =========================================================================
    logic [63:0] act_man_group;
    logic [7:0]  act_exp_group;

    always_comb begin
        // Select 64-bit mantissa group (8 elements × 8 bits)
        case (comp_cycle_cnt)
            4'd0:  act_man_group = act_man_reg[63:0];
            4'd1:  act_man_group = act_man_reg[127:64];
            4'd2:  act_man_group = act_man_reg[191:128];
            4'd3:  act_man_group = act_man_reg[255:192];
            4'd4:  act_man_group = act_man_reg[319:256];
            4'd5:  act_man_group = act_man_reg[383:320];
            4'd6:  act_man_group = act_man_reg[447:384];
            4'd7:  act_man_group = act_man_reg[511:448];
            4'd8:  act_man_group = act_man_reg[575:512];
            4'd9:  act_man_group = act_man_reg[639:576];
            4'd10: act_man_group = act_man_reg[703:640];
            4'd11: act_man_group = act_man_reg[767:704];
            4'd12: act_man_group = act_man_reg[831:768];
            4'd13: act_man_group = act_man_reg[895:832];
            4'd14: act_man_group = act_man_reg[959:896];
            4'd15: act_man_group = act_man_reg[1023:960];
        endcase

        // Select exponent based on cycle count (one exp per 32 elements = 4 cycles)
        case (comp_cycle_cnt[3:2])
            2'd0: act_exp_group = act_exp_reg[7:0];
            2'd1: act_exp_group = act_exp_reg[15:8];
            2'd2: act_exp_group = act_exp_reg[23:16];
            2'd3: act_exp_group = act_exp_reg[31:24];
        endcase
    end

    // Pack into 72-bit din format: {exp[7:0], man[63:0]}
    // Matches reference testbench format where exponent at MSB (bits 71:64), mantissas at LSB
    wire [71:0] din_act = {act_exp_group, act_man_group};

    // =========================================================================
    // Column to MLP/Bank Mapping (for weight loading)
    // =========================================================================
    wire [2:0] mlp_index = col_sel_reg[3:1];  // col_sel / 2
    wire       bank_sel  = col_sel_reg[0];     // col_sel % 2

    // Generate wren mask (only one MLP enabled during weight loading)
    wire [NUM_MLPS-1:0] wren_wt = (wt_state_reg == WT_LOAD) ?
        ({{(NUM_MLPS-1){1'b0}}, 1'b1} << mlp_index) : {NUM_MLPS{1'b0}};

    // Generate wraddr:
    //   From MLP_COL_MAPPING.md Section 4:
    //   - Bank 1 (CD, even columns): ODD addresses (1,3,5,7,...) -> BRAM_DOUT[143:72]
    //   - Bank 0 (AB, odd columns):  EVEN addresses (0,2,4,6,...) -> BRAM_DOUT[71:0]
    //   bank_sel = col_sel[0]: 0 for even columns, 1 for odd columns
    //   Need to INVERT: even columns (bank_sel=0) -> odd wraddr (LSB=1)
    //                   odd columns (bank_sel=1) -> even wraddr (LSB=0)
    wire [9:0] wraddr_wt = {5'b0, wt_cycle_cnt, ~bank_sel};

    // =========================================================================
    // Compute Control Signal Generation
    // =========================================================================
    // ce: Active during streaming AND drain (drain flushes pipeline results)
    // Reference testbench sets ce=1 AFTER setup clock edge, so ce=1 starts with first din
    // ce must stay high during drain to let remaining pipeline results accumulate
    wire comp_ce = (comp_state_reg == COMP_STREAM) || (comp_state_reg == COMP_DRAIN);

    // rdaddr: Points to CURRENT weight group needed
    // - COMP_SETUP: rdaddr=0, BRAM starts reading weights[0]
    // - COMP_STREAM cycle N: rdaddr=N, using weights[N] from BRAM
    // The rdaddr is combinational to match the testbench timing
    // (reference testbench sets rdaddr=i+1 at cycle i, which we match by
    //  using comp_cycle_cnt directly since it's the NEXT cycle's count)

    // accumulate: Enable after first cycle of COMP_STREAM, and during COMP_DRAIN
    // During drain, we're still accumulating the final pipeline results
    wire comp_accumulate = ((comp_state_reg == COMP_STREAM) && (comp_cycle_cnt > 4'd0)) ||
                           (comp_state_reg == COMP_DRAIN);

    // load: Pulse at cycle 2 for new dot product (accounts for pipeline latency)
    wire comp_load = (comp_state_reg == COMP_STREAM) &&
                     (comp_cycle_cnt == PIPELINE_LATENCY) && new_dot_reg;

    // =========================================================================
    // MLP BRAM Column Signal Muxing
    // =========================================================================
    // Priority: Weight loading > Compute
    wire is_loading = (wt_state_reg == WT_LOAD);
    wire is_streaming = (comp_state_reg == COMP_STREAM);

    wire [71:0]         mlp_bram_din  = is_loading ? bram_din_wt : 72'b0;
    wire [9:0]          mlp_wraddr    = is_loading ? wraddr_wt : 10'b0;
    wire [NUM_MLPS-1:0] mlp_wren      = wren_wt;
    // rdaddr should be set ONE CYCLE AHEAD due to BRAM read latency
    // Reference testbench sets rdaddr=i+1 at iteration i (for next cycle)
    // During COMP_SETUP: rdaddr=0, BRAM will output weights[0] at COMP_STREAM cycle 0
    // During COMP_STREAM cycle N: set rdaddr=N+1 so BRAM outputs weights[N+1] at cycle N+1
    wire [8:0]          mlp_rdaddr    = is_loading ? 9'b0 :
                                        (comp_state_reg == COMP_SETUP) ? 9'd0 :
                                        (comp_state_reg == COMP_STREAM) ? {5'b0, comp_cycle_cnt + 4'd1} :
                                        9'b0;
    wire                mlp_ce        = is_loading ? 1'b1 : comp_ce;
    wire                mlp_load      = is_loading ? 1'b0 : comp_load;
    wire                mlp_accumulate = is_loading ? 1'b0 : comp_accumulate;
    // din valid only during COMP_STREAM (COMP_SETUP has din=0 like reference testbench)
    wire [71:0]         mlp_din       = (is_loading || !is_streaming) ? 72'b0 : din_act;

    // =========================================================================
    // Weight Loading FSM: Next State Logic
    // =========================================================================
    always_comb begin
        wt_state_next = wt_state_reg;

        case (wt_state_reg)
            WT_IDLE: begin
                if (i_wt_valid) begin
                    wt_state_next = WT_LOAD;
                end
            end

            WT_LOAD: begin
                if (wt_cycle_cnt == 4'd15) begin
                    wt_state_next = WT_DONE;
                end
            end

            WT_DONE: begin
                wt_state_next = WT_IDLE;
            end

            default: wt_state_next = WT_IDLE;
        endcase
    end

    // =========================================================================
    // Weight Loading FSM: Registered Logic
    // =========================================================================
    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            wt_state_reg <= WT_IDLE;
            wt_cycle_cnt <= 4'd0;
            wt_man_reg   <= 1024'b0;
            wt_exp_reg   <= 32'b0;
            col_sel_reg  <= 4'd0;
        end else begin
            wt_state_reg <= wt_state_next;

            case (wt_state_reg)
                WT_IDLE: begin
                    wt_cycle_cnt <= 4'd0;
                    if (i_wt_valid) begin
                        wt_man_reg  <= i_nv_right_man;
                        wt_exp_reg  <= i_nv_right_exp;
                        col_sel_reg <= i_col_sel;
                    end
                end

                WT_LOAD: begin
                    wt_cycle_cnt <= wt_cycle_cnt + 4'd1;
                end

                WT_DONE: begin
                    wt_cycle_cnt <= 4'd0;
                end

                default: ;
            endcase
        end
    end

    // =========================================================================
    // Compute FSM: Next State Logic
    // =========================================================================
    always_comb begin
        comp_state_next = comp_state_reg;

        case (comp_state_reg)
            COMP_IDLE: begin
                // Only start compute when not loading weights
                if (i_act_valid && !is_loading) begin
                    comp_state_next = COMP_SETUP;
                end
            end

            COMP_SETUP: begin
                // Setup cycle: ce=1, rdaddr=0, BRAM outputs first weights
                // Next cycle will be first data cycle
                comp_state_next = COMP_STREAM;
            end

            COMP_STREAM: begin
                if (comp_cycle_cnt == 4'd15) begin
                    comp_state_next = COMP_DRAIN;
                end
            end

            COMP_DRAIN: begin
                // Wait for pipeline to flush
                if (drain_cnt == 3'd2) begin
                    comp_state_next = COMP_IDLE;
                end
            end

            default: comp_state_next = COMP_IDLE;
        endcase
    end

    // =========================================================================
    // Compute FSM: Registered Logic
    // =========================================================================
    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn) begin
            comp_state_reg  <= COMP_IDLE;
            comp_cycle_cnt  <= 4'd0;
            drain_cnt       <= 3'd0;
            act_man_reg     <= 1024'b0;
            act_exp_reg     <= 32'b0;
            new_dot_reg     <= 1'b0;
        end else begin
            comp_state_reg <= comp_state_next;

            case (comp_state_reg)
                COMP_IDLE: begin
                    comp_cycle_cnt  <= 4'd0;
                    drain_cnt       <= 3'd0;
                    if (i_act_valid && !is_loading) begin
                        act_man_reg <= i_nv_left_man;
                        act_exp_reg <= i_nv_left_exp;
                        new_dot_reg <= i_new_dot;
                    end
                end

                COMP_SETUP: begin
                    // Setup cycle: rdaddr=0, BRAM reads weights[0]
                    // Keep comp_cycle_cnt=0 for first data cycle
                end

                COMP_STREAM: begin
                    comp_cycle_cnt <= comp_cycle_cnt + 4'd1;
                end

                COMP_DRAIN: begin
                    drain_cnt <= drain_cnt + 3'd1;
                end

                default: ;
            endcase
        end
    end

    // =========================================================================
    // Ready-Valid Signals
    // =========================================================================
    // Weight ready when idle (not loading)
    assign o_wt_ready = (wt_state_reg == WT_IDLE);

    // Activation ready when compute idle AND not loading weights
    assign o_act_ready = (comp_state_reg == COMP_IDLE) && !is_loading;

    // Results valid after compute drain completes
    assign o_dout_valid = (comp_state_reg == COMP_IDLE) && !is_loading;

    // =========================================================================
    // MLP BRAM Column Instance
    // =========================================================================
    mlp_bram_col #(
        .NUM_MLPS(NUM_MLPS)
    ) u_mlp_bram_col (
        .clk(clk),
        .rstn(rstn),
        .ce(mlp_ce),
        .din(mlp_din),
        .load(mlp_load),
        .accumulate(mlp_accumulate),
        .bram_din(mlp_bram_din),
        .wraddr(mlp_wraddr),
        .wren(mlp_wren),
        .rdaddr(mlp_rdaddr),
        .dout(o_dout)
    );

endmodule

`default_nettype wire
