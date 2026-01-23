// Xilinx Versal BRAM36 1-Read 1-Write Wrapper
module bram36_1r1w
    import common_pkg::*;
#(
    parameter addr_width_p,
    parameter data_width_p,
    parameter reg_out_p,

    localparam ramb36_awidth_lp = 9,
    localparam ramb36_dwidth_lp = 72,
    localparam ramb36_ewidth_lp = ramb36_dwidth_lp / 8,

    localparam num_ramb36_lp = cdiv(data_width_p, ramb36_dwidth_lp),
    localparam padded_width_lp = num_ramb36_lp * ramb36_dwidth_lp
) (
    input logic r_clk_i,
    input logic r_reset_i,

    input logic w_clk_i,
    input logic w_reset_i,

    input logic r_v_i,
    input logic [addr_width_p-1:0] r_addr_i,

    input logic w_v_i,
    input logic [addr_width_p-1:0] w_addr_i,
    input logic [data_width_p-1:0] w_data_i,
    input logic [data_width_p/8-1:0] w_en_i,

    output logic r_v_o,
    output logic [data_width_p-1:0] r_data_o
);

    // Output valid
    logic r_v_r;
    always_ff @(posedge r_clk_i) begin
        if (r_reset_i) begin
            r_v_o <= 1'b0;
            r_v_r <= 1'b0;
        end else begin
            r_v_r <= r_v_i;
            r_v_o <= reg_out_p ? r_v_r : r_v_i;
        end
    end

    // Padded data signals
    logic [padded_width_lp-1:0] w_data_padded_li, r_data_padded_lo;
    logic [padded_width_lp/8-1:0] w_en_padded_li;

    // RAMB36 ports
    logic [num_ramb36_lp-1:0][ramb36_dwidth_lp-1:0] ramb36_w_data_li, ramb36_r_data_lo;
    logic [num_ramb36_lp-1:0][ramb36_ewidth_lp-1:0] ramb36_w_en_li;

    // Connections
    assign r_data_o = r_data_padded_lo[0 +: data_width_p];
    assign w_data_padded_li = {{(padded_width_lp - data_width_p){1'b0}}, w_data_i};
    assign w_en_padded_li = {{(padded_width_lp/8 - data_width_p/8){1'b0}}, w_en_i};

    for (genvar i = 0; i < num_ramb36_lp; i++) begin : gen_ramb_ports
        assign r_data_padded_lo[i * ramb36_dwidth_lp +: ramb36_dwidth_lp] = ramb36_r_data_lo[i];
        assign ramb36_w_data_li[i] = w_data_padded_li[i * ramb36_dwidth_lp +: ramb36_dwidth_lp];
        assign ramb36_w_en_li[i] = w_en_padded_li[i * ramb36_ewidth_lp +: ramb36_ewidth_lp];
    end

    // Xilinx Versal RAMB36E5 primitive
    // 512 x 72 mode: 9-bit address, 72-bit data, Simple Dual Port
    for (genvar i = 0; i < num_ramb36_lp; i++) begin : gen_ramb
        RAMB36E5 #(
           // ByteWideWrite: Sets the byte-wide write enable feature in SDP mode
           .BWE_MODE_B("PARITY_INDEPENDENT"),
           // CASCADE_ORDER_A, CASCADE_ORDER_B: "FIRST", "MIDDLE", "LAST", "NONE"
           .CASCADE_ORDER_A("NONE"),
           .CASCADE_ORDER_B("NONE"),
           // CLOCK_DOMAINS: "COMMON", "INDEPENDENT"
           .CLOCK_DOMAINS("INDEPENDENT"),
           // Collision check: "ALL", "GENERATE_X_ONLY", "NONE", "WARNING_ONLY"
           .SIM_COLLISION_CHECK("ALL"),
           // DOA_REG, DOB_REG: Optional output register (0, 1)
           .DOA_REG(reg_out_p ? 1 : 0),
           .DOB_REG(reg_out_p ? 1 : 0),
           // Programmable Inversion Attributes: Specifies the use of the built-in programmable inversion
           .IS_ARST_A_INVERTED(1'b0),
           .IS_ARST_B_INVERTED(1'b0),
           .IS_CLKARDCLK_INVERTED(1'b0),
           .IS_CLKBWRCLK_INVERTED(1'b0),
           .IS_ENARDEN_INVERTED(1'b0),
           .IS_ENBWREN_INVERTED(1'b0),
           .IS_RSTRAMARSTRAM_INVERTED(1'b0),
           .IS_RSTRAMB_INVERTED(1'b0),
           .IS_RSTREGARSTREG_INVERTED(1'b0),
           .IS_RSTREGB_INVERTED(1'b0),
           // READ_WIDTH_A/B, WRITE_WIDTH_A/B: Read/write width per port
           .READ_WIDTH_A(ramb36_dwidth_lp),
           .READ_WIDTH_B(0),
           .WRITE_WIDTH_A(0),
           .WRITE_WIDTH_B(ramb36_dwidth_lp),
           // RSTREG_PRIORITY_A, RSTREG_PRIORITY_B: Reset or enable priority ("RSTREG", "REGCE")
           .RSTREG_PRIORITY_A("RSTREG"),
           .RSTREG_PRIORITY_B("RSTREG"),
           // RST_MODE_A, RST_MODE_B: Set synchronous or asynchronous reset.
           .RST_MODE_A("SYNC"),
           .RST_MODE_B("SYNC"),
           // SRVAL_A, SRVAL_B: Set/reset value for output
           .SRVAL_A(36'h000000000),
           .SRVAL_B(36'h000000000),
           // Sleep Async: Sleep function asynchronous or synchronous ("TRUE", "FALSE")
           .SLEEP_ASYNC("FALSE"),
           // WriteMode: "WRITE_FIRST", "NO_CHANGE", "READ_FIRST"
           .WRITE_MODE_A("NO_CHANGE"),
           .WRITE_MODE_B("NO_CHANGE")
        )
        i_RAMB36E5 (
           // Cascade Signals outputs: Multi-BRAM cascade signals
           .CASDOUTA(),                       // 32-bit output: Port A cascade output data
           .CASDOUTB(),                       // 32-bit output: Port B cascade output data
           .CASDOUTPA(),                      // 4-bit output: Port A cascade output parity data
           .CASDOUTPB(),                      // 4-bit output: Port B cascade output parity data
           .CASOUTDBITERR(),                  // 1-bit output: DBITERR cascade output
           .CASOUTSBITERR(),                  // 1-bit output: SBITERR cascade output
           // ECC Signals outputs: Error Correction Circuitry ports
           .DBITERR(),                        // 1-bit output: Double bit error status
           .SBITERR(),                        // 1-bit output: Single bit error status
           // Port A Data outputs: Port A data
           .DOUTADOUT(ramb36_r_data_lo[i][0 +: 32]),   // 32-bit output: Port A Data/LSB data
           .DOUTPADOUTP(ramb36_r_data_lo[i][64 +: 4]), // 4-bit output: Port A parity/LSB parity
           // Port B Data outputs: Port B dataA
           .DOUTBDOUT(ramb36_r_data_lo[i][32 +: 32]),  // 32-bit output: Port B data/MSB data
           .DOUTPBDOUTP(ramb36_r_data_lo[i][68 +: 4]), // 4-bit output: Port B parity/MSB parity
           // Cascade Signals inputs: Multi-BRAM cascade signals
           .CASDINA('0),                      // 32-bit input: Port A cascade input data
           .CASDINB('0),                      // 32-bit input: Port B cascade input data
           .CASDINPA('0),                     // 4-bit input: Port A cascade input parity data
           .CASDINPB('0),                     // 4-bit input: Port B cascade input parity data
           .CASDOMUXA(1'b0),                  // 1-bit input: Port A unregistered data (0=BRAM data, 1=CASDINA)
           .CASDOMUXB(1'b0),                  // 1-bit input: Port B unregistered data (0=BRAM data, 1=CASDINB)
           .CASDOMUXEN_A(1'b0),               // 1-bit input: Port A unregistered output data enable
           .CASDOMUXEN_B(1'b0),               // 1-bit input: Port B unregistered output data enable
           .CASINDBITERR('0),                 // 1-bit input: DBITERR cascade input
           .CASINSBITERR('0),                 // 1-bit input: SBITERR cascade input
           .CASOREGIMUXA(1'b0),               // 1-bit input: Port A registered data (0=BRAM data, 1=CASDINA)
           .CASOREGIMUXB(1'b0),               // 1-bit input: Port B registered data (0=BRAM data, 1=CASDINB)
           .CASOREGIMUXEN_A(1'b0),            // 1-bit input: Port A registered output data enable
           .CASOREGIMUXEN_B(1'b0),            // 1-bit input: Port B registered output data enable
           // ECC Signals inputs: Error Correction Circuitry ports
           .ECCPIPECE(1'b0),                  // 1-bit input: ECC Pipeline Register Enable
           .INJECTDBITERR(1'b0),              // 1-bit input: Inject a double-bit error
           .INJECTSBITERR(1'b0),              // 1-bit input: Inject a single-bit error
           // Port A Address/Control Signals inputs: Port A address and control signals
           .ADDRARDADDR({r_addr_i[0 +: ramb36_awidth_lp], 3'b0}), // 12-bit input: A/Read port address
           .ARST_A(r_reset_i),                // 1-bit input: Port A asynchronous reset
           .CLKARDCLK(r_clk_i),               // 1-bit input: A/Read port clock
           .ENARDEN(r_v_i),                   // 1-bit input: Port A enable/Read enable
           .REGCEAREGCE(reg_out_p ? 1'b1 : 1'b0),        // 1-bit input: Port A register enable/Register enable
           .RSTRAMARSTRAM(reg_out_p ? 1'b0 : r_reset_i), // 1-bit input: Port A set/reset
           .RSTREGARSTREG(reg_out_p ? r_reset_i : 1'b0), // 1-bit input: Port A register set/reset
           .SLEEP(1'b0),                      // 1-bit input: Sleep Mode
           .WEA('0),                          // 4-bit input: Port A write enable
           // Port A Data inputs: Port A data
           .DINADIN(ramb36_w_data_li[i][0 +: 32]),   // 32-bit input: Port A data/LSB data
           .DINPADINP(ramb36_w_data_li[i][64 +: 4]), // 4-bit input: Port A parity/LSB parity
           // Port B Address/Control Signals inputs: Port B address and control signals
           .ADDRBWRADDR({w_addr_i[0 +: ramb36_awidth_lp], 3'b0}), // 12-bit input: B/Write port address
           .ARST_B(w_reset_i),                // 1-bit input: Port B asynchronous reset
           .CLKBWRCLK(w_clk_i),               // 1-bit input: B/Write port clock
           .ENBWREN(w_v_i),                   // 1-bit input: Port B enable/Write enable
           .REGCEB(1'b0),                     // 1-bit input: Port B register enable
           .RSTRAMB(1'b0),                    // 1-bit input: Port B set/reset
           .RSTREGB(1'b0),                    // 1-bit input: Port B register set/reset
           .WEBWE(ramb36_w_en_li[i]),         // 9-bit input: Port B write enable/Write enable
           // Port B Data inputs: Port B dataA
           .DINBDIN(ramb36_w_data_li[i][32 +: 32]), // 32-bit input: Port B data/MSB data
           .DINPBDINP(ramb36_w_data_li[i][68 +: 4]) // 4-bit input: Port B parity/MSB parity
        );
    end

    initial begin
        assert(data_width_p % 8 == 0) else $error("data_width_p must be a multiple of 8");
        assert(addr_width_p == ramb36_awidth_lp) else $error("addr_width_p must match the RAMB36 address width of %0d", ramb36_awidth_lp);
    end

endmodule