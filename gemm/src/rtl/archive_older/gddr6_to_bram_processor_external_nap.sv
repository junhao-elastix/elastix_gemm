// ------------------------------------------------------------------
// GDDR6-to-BRAM Processor with External NAP Interface
//
// This version uses an external NAP connection, avoiding the
// synthesis issues with encapsulated NAP instances.
//
// The NAP should be instantiated at the top level and connected
// via the AXI interface ports.
// ------------------------------------------------------------------

`include "nap_interfaces.svh"

module gddr6_to_bram_processor_external_nap
    (
    // Clock and reset
    input  logic        i_nap_clk,          // NAP clock (300-400 MHz)
    input  logic        i_reg_clk,          // Register clock (200 MHz)
    input  logic        i_nap_reset_n,      // Active-low reset for nap_clk
    input  logic        i_reg_reset_n,      // Active-low reset for reg_clk

    // Control and status registers (i_reg_clk domain)
    input  logic [31:0] i_control_reg,      // [0]=enable, [1]=trigger
    output logic [31:0] o_status_reg,       // [0]=busy, [1]=done, [2]=error
    input  logic [31:0] i_gddr_addr_lo,     // GDDR6 address[31:0]
    input  logic [31:0] i_gddr_addr_hi,     // GDDR6 address[41:32] in bits[9:0]
    input  logic [31:0] i_bram_addr,        // BRAM address in bits[8:0]
    input  logic [31:0] i_length,           // Transfer length in bits[7:0]

    // BRAM write interface (i_nap_clk domain)
    output logic        o_bram_wr_en,       // BRAM write enable
    output logic [8:0]  o_bram_wr_addr,     // BRAM write address
    output logic [255:0] o_bram_wr_data,    // BRAM write data

    // AXI4 Master Interface to NAP (i_nap_clk domain)
    // Address Read Channel
    output logic         o_axi_arvalid,
    input  logic         i_axi_arready,
    output logic [27:0]  o_axi_araddr,
    output logic [7:0]   o_axi_arlen,
    output logic [7:0]   o_axi_arid,
    output logic [2:0]   o_axi_arsize,
    output logic [1:0]   o_axi_arburst,

    // Read Data Channel
    input  logic         i_axi_rvalid,
    output logic         o_axi_rready,
    input  logic [255:0] i_axi_rdata,
    input  logic         i_axi_rlast,
    input  logic [1:0]   i_axi_rresp,
    input  logic [7:0]   i_axi_rid,

    // Address Write Channel (tied off - read-only)
    output logic         o_axi_awvalid,
    input  logic         i_axi_awready,
    output logic [27:0]  o_axi_awaddr,
    output logic [7:0]   o_axi_awlen,
    output logic [7:0]   o_axi_awid,
    output logic [2:0]   o_axi_awsize,
    output logic [1:0]   o_axi_awburst,

    // Write Data Channel (tied off - read-only)
    output logic         o_axi_wvalid,
    input  logic         i_axi_wready,
    output logic [255:0] o_axi_wdata,
    output logic [31:0]  o_axi_wstrb,
    output logic         o_axi_wlast,

    // Write Response Channel (tied off - read-only)
    input  logic         i_axi_bvalid,
    output logic         o_axi_bready,
    input  logic [1:0]   i_axi_bresp,
    input  logic [7:0]   i_axi_bid
);

    // ----------------------------------------------------------------
    // FSM State Encoding
    // ----------------------------------------------------------------
    typedef enum logic [2:0] {
        ST_IDLE         = 3'b000,
        ST_READ_ADDR    = 3'b001,
        ST_READ_DATA    = 3'b010,
        ST_PROCESS      = 3'b011,
        ST_WRITE_BRAM   = 3'b100,
        ST_CHECK_DONE   = 3'b101,
        ST_DONE         = 3'b110,
        ST_ERROR        = 3'b111
    } t_state;

    t_state state_reg, state_next;

    // ----------------------------------------------------------------
    // Clock Domain Crossing: Control Signals (reg_clk -> nap_clk)
    // ----------------------------------------------------------------
    logic enable_sync;
    logic trigger_sync, trigger_sync_d, trigger_posedge;
    logic [27:0] gddr_addr_sync;
    logic [8:0]  bram_addr_sync;
    logic [7:0]  length_sync;

    // Synchronize enable
    ACX_SYNCHRONIZER x_sync_enable (
        .din(i_control_reg[0]),
        .dout(enable_sync),
        .clk(i_nap_clk),
        .rstn(i_nap_reset_n)
    );

    // Synchronize trigger and detect rising edge
    ACX_SYNCHRONIZER x_sync_trigger (
        .din(i_control_reg[1]),
        .dout(trigger_sync),
        .clk(i_nap_clk),
        .rstn(i_nap_reset_n)
    );

    always_ff @(posedge i_nap_clk or negedge i_nap_reset_n) begin
        if (!i_nap_reset_n) begin
            trigger_sync_d <= 1'b0;
        end else begin
            trigger_sync_d <= trigger_sync;
        end
    end

    assign trigger_posedge = trigger_sync && !trigger_sync_d;

    // Synchronize configuration
    logic [41:0] gddr_addr_full;
    assign gddr_addr_full = {i_gddr_addr_hi[9:0], i_gddr_addr_lo[31:0]};

    always_ff @(posedge i_nap_clk or negedge i_nap_reset_n) begin
        if (!i_nap_reset_n) begin
            gddr_addr_sync <= 28'b0;
            bram_addr_sync <= 9'b0;
            length_sync <= 8'b0;
        end else if (state_reg == ST_IDLE && enable_sync) begin
            gddr_addr_sync <= gddr_addr_full[27:0];
            bram_addr_sync <= i_bram_addr[8:0];
            length_sync <= i_length[7:0];
        end
    end

    // ----------------------------------------------------------------
    // Clock Domain Crossing: Status Signals (nap_clk -> reg_clk)
    // ----------------------------------------------------------------
    logic busy_nap, done_nap, error_nap;
    logic busy_sync, done_sync, error_sync;

    assign busy_nap  = (state_reg != ST_IDLE && state_reg != ST_DONE && state_reg != ST_ERROR);
    assign done_nap  = (state_reg == ST_DONE);
    assign error_nap = (state_reg == ST_ERROR);

    ACX_SYNCHRONIZER x_sync_busy (
        .din(busy_nap),
        .dout(busy_sync),
        .clk(i_reg_clk),
        .rstn(i_reg_reset_n)
    );

    ACX_SYNCHRONIZER x_sync_done (
        .din(done_nap),
        .dout(done_sync),
        .clk(i_reg_clk),
        .rstn(i_reg_reset_n)
    );

    ACX_SYNCHRONIZER x_sync_error (
        .din(error_nap),
        .dout(error_sync),
        .clk(i_reg_clk),
        .rstn(i_reg_reset_n)
    );

    assign o_status_reg = {29'b0, error_sync, done_sync, busy_sync};

    // ----------------------------------------------------------------
    // Internal Signals (i_nap_clk domain)
    // ----------------------------------------------------------------
    logic [7:0] beat_count_reg, beat_count_next;
    logic [27:0] curr_gddr_addr_reg, curr_gddr_addr_next;
    logic [8:0] curr_bram_addr_reg, curr_bram_addr_next;
    logic [255:0] axi_rdata_reg;
    logic [255:0] processed_data_reg;

    // ----------------------------------------------------------------
    // FSM State Transition Logic
    // ----------------------------------------------------------------
    always_ff @(posedge i_nap_clk or negedge i_nap_reset_n) begin
        if (!i_nap_reset_n) begin
            state_reg <= ST_IDLE;
        end else begin
            state_reg <= state_next;
        end
    end

    always_comb begin
        state_next = state_reg;

        case (state_reg)
            ST_IDLE: begin
                if (enable_sync && trigger_posedge && length_sync > 0) begin
                    state_next = ST_READ_ADDR;
                end
            end

            ST_READ_ADDR: begin
                if (i_axi_arready && o_axi_arvalid) begin
                    state_next = ST_READ_DATA;
                end
            end

            ST_READ_DATA: begin
                if (i_axi_rvalid && o_axi_rready && i_axi_rlast) begin
                    if (i_axi_rresp != 2'b00) begin
                        state_next = ST_ERROR;
                    end else begin
                        state_next = ST_PROCESS;
                    end
                end
            end

            ST_PROCESS: begin
                state_next = ST_WRITE_BRAM;
            end

            ST_WRITE_BRAM: begin
                state_next = ST_CHECK_DONE;
            end

            ST_CHECK_DONE: begin
                if (beat_count_reg >= length_sync) begin
                    state_next = ST_DONE;
                end else begin
                    state_next = ST_READ_ADDR;
                end
            end

            ST_DONE: begin
                if (!trigger_sync) begin
                    state_next = ST_IDLE;
                end
            end

            ST_ERROR: begin
                if (!trigger_sync) begin
                    state_next = ST_IDLE;
                end
            end

            default: begin
                state_next = ST_IDLE;
            end
        endcase
    end

    // ----------------------------------------------------------------
    // Beat Counter Management
    // ----------------------------------------------------------------
    always_comb begin
        beat_count_next = beat_count_reg;

        case (state_reg)
            ST_IDLE: begin
                if (enable_sync && trigger_posedge) begin
                    beat_count_next = 8'd1;
                end
            end

            ST_CHECK_DONE: begin
                beat_count_next = beat_count_reg + 8'd1;
            end

            default: begin
                beat_count_next = beat_count_reg;
            end
        endcase
    end

    always_ff @(posedge i_nap_clk or negedge i_nap_reset_n) begin
        if (!i_nap_reset_n) begin
            beat_count_reg <= 8'b0;
        end else begin
            beat_count_reg <= beat_count_next;
        end
    end

    // ----------------------------------------------------------------
    // Address Management
    // ----------------------------------------------------------------
    always_comb begin
        curr_gddr_addr_next = curr_gddr_addr_reg;
        curr_bram_addr_next = curr_bram_addr_reg;

        case (state_reg)
            ST_IDLE: begin
                if (enable_sync && trigger_posedge) begin
                    curr_gddr_addr_next = gddr_addr_sync;
                    curr_bram_addr_next = bram_addr_sync;
                end
            end

            ST_CHECK_DONE: begin
                curr_gddr_addr_next = curr_gddr_addr_reg + 28'd32;
                curr_bram_addr_next = curr_bram_addr_reg + 9'd1;
            end

            default: begin
                curr_gddr_addr_next = curr_gddr_addr_reg;
                curr_bram_addr_next = curr_bram_addr_reg;
            end
        endcase
    end

    always_ff @(posedge i_nap_clk or negedge i_nap_reset_n) begin
        if (!i_nap_reset_n) begin
            curr_gddr_addr_reg <= 28'b0;
            curr_bram_addr_reg <= 9'b0;
        end else begin
            curr_gddr_addr_reg <= curr_gddr_addr_next;
            curr_bram_addr_reg <= curr_bram_addr_next;
        end
    end

    // ----------------------------------------------------------------
    // AXI4 Read Address Channel
    // ----------------------------------------------------------------
    always_ff @(posedge i_nap_clk or negedge i_nap_reset_n) begin
        if (!i_nap_reset_n) begin
            o_axi_arvalid <= 1'b0;
            o_axi_araddr  <= 28'b0;
            o_axi_arlen   <= 8'b0;
            o_axi_arid    <= 8'b0;
            o_axi_arsize  <= 3'b0;
            o_axi_arburst <= 2'b0;
        end else begin
            case (state_reg)
                ST_READ_ADDR: begin
                    o_axi_arvalid <= 1'b1;
                    o_axi_araddr  <= curr_gddr_addr_reg;
                    o_axi_arlen   <= 8'd0;         // 1 beat
                    o_axi_arid    <= 8'd0;
                    o_axi_arsize  <= 3'd5;         // 32 bytes
                    o_axi_arburst <= 2'b01;        // INCR
                end

                default: begin
                    if (i_axi_arready) begin
                        o_axi_arvalid <= 1'b0;
                    end
                end
            endcase
        end
    end

    // ----------------------------------------------------------------
    // AXI4 Read Data Channel
    // ----------------------------------------------------------------
    always_ff @(posedge i_nap_clk or negedge i_nap_reset_n) begin
        if (!i_nap_reset_n) begin
            o_axi_rready <= 1'b0;
            axi_rdata_reg <= 256'b0;
        end else begin
            case (state_reg)
                ST_READ_DATA: begin
                    o_axi_rready <= 1'b1;
                    if (i_axi_rvalid && o_axi_rready) begin
                        axi_rdata_reg <= i_axi_rdata;
                    end
                end

                default: begin
                    o_axi_rready <= 1'b0;
                end
            endcase
        end
    end

    // ----------------------------------------------------------------
    // +42 Processing Logic
    // ----------------------------------------------------------------
    always_ff @(posedge i_nap_clk or negedge i_nap_reset_n) begin
        if (!i_nap_reset_n) begin
            processed_data_reg <= 256'b0;
        end else begin
            case (state_reg)
                ST_PROCESS: begin
                    // Add +42 to each 32-bit word
                    processed_data_reg[31:0]    <= axi_rdata_reg[31:0]    + 32'd42;
                    processed_data_reg[63:32]   <= axi_rdata_reg[63:32]   + 32'd42;
                    processed_data_reg[95:64]   <= axi_rdata_reg[95:64]   + 32'd42;
                    processed_data_reg[127:96]  <= axi_rdata_reg[127:96]  + 32'd42;
                    processed_data_reg[159:128] <= axi_rdata_reg[159:128] + 32'd42;
                    processed_data_reg[191:160] <= axi_rdata_reg[191:160] + 32'd42;
                    processed_data_reg[223:192] <= axi_rdata_reg[223:192] + 32'd42;
                    processed_data_reg[255:224] <= axi_rdata_reg[255:224] + 32'd42;
                end

                default: begin
                    processed_data_reg <= processed_data_reg;
                end
            endcase
        end
    end

    // ----------------------------------------------------------------
    // BRAM Write Interface
    // ----------------------------------------------------------------
    always_ff @(posedge i_nap_clk or negedge i_nap_reset_n) begin
        if (!i_nap_reset_n) begin
            o_bram_wr_en   <= 1'b0;
            o_bram_wr_addr <= 9'b0;
            o_bram_wr_data <= 256'b0;
        end else begin
            case (state_reg)
                ST_WRITE_BRAM: begin
                    o_bram_wr_en   <= 1'b1;
                    o_bram_wr_addr <= curr_bram_addr_reg;
                    o_bram_wr_data <= processed_data_reg;
                end

                default: begin
                    o_bram_wr_en   <= 1'b0;
                    o_bram_wr_addr <= 9'b0;
                    o_bram_wr_data <= 256'b0;
                end
            endcase
        end
    end

    // ----------------------------------------------------------------
    // Tie off unused AXI Write Channels
    // ----------------------------------------------------------------
    assign o_axi_awvalid = 1'b0;
    assign o_axi_awaddr  = 28'b0;
    assign o_axi_awlen   = 8'b0;
    assign o_axi_awid    = 8'b0;
    assign o_axi_awsize  = 3'b0;
    assign o_axi_awburst = 2'b0;

    assign o_axi_wvalid  = 1'b0;
    assign o_axi_wdata   = 256'b0;
    assign o_axi_wstrb   = 32'b0;
    assign o_axi_wlast   = 1'b0;

    assign o_axi_bready  = 1'b0;

endmodule : gddr6_to_bram_processor_external_nap