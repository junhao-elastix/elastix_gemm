// Xilinx Versal BRAM18 1-Read 1-Write Wrapper
module bram18_1r1w
    import common_pkg::*;
#(
    parameter addr_width_p,
    parameter data_width_p,
    parameter reg_out_p,

    localparam ramb18_awidth_lp = 9,
    localparam ramb18_dwidth_lp = 32,
    localparam ramb18_ewidth_lp = ramb18_dwidth_lp / 8,

    localparam num_ramb18_lp = cdiv(data_width_p, ramb18_dwidth_lp),
    localparam padded_width_lp = num_ramb18_lp * ramb18_dwidth_lp
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

    // RAMB18 ports
    logic [num_ramb18_lp-1:0][ramb18_dwidth_lp-1:0] ramb18_w_data_li, ramb18_r_data_lo;
    logic [num_ramb18_lp-1:0][ramb18_ewidth_lp-1:0] ramb18_w_en_li;

    // Connections
    assign r_data_o = r_data_padded_lo[0 +: data_width_p];
    assign w_data_padded_li = {{(padded_width_lp - data_width_p){1'b0}}, w_data_i};
    assign w_en_padded_li = {{(padded_width_lp/8 - data_width_p/8){1'b0}}, w_en_i};

    for (genvar i = 0; i < num_ramb18_lp; i++) begin : gen_ramb_ports
        assign r_data_padded_lo[i * ramb18_dwidth_lp +: ramb18_dwidth_lp] = ramb18_r_data_lo[i];
        assign ramb18_w_data_li[i] = w_data_padded_li[i * ramb18_dwidth_lp +: ramb18_dwidth_lp];
        assign ramb18_w_en_li[i] = w_en_padded_li[i * ramb18_ewidth_lp +: ramb18_ewidth_lp];
    end

    // Xilinx Versal RAMB18E5 primitive
    // 512 x 36 mode: 9-bit address, 36-bit data, Simple Dual Port
    for (genvar i = 0; i < num_ramb18_lp; i++) begin : gen_ramb
        RAMB18E5 #(
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
           .READ_WIDTH_A(ramb18_dwidth_lp + 4),
           .READ_WIDTH_B(0),
           .WRITE_WIDTH_A(0),
           .WRITE_WIDTH_B(ramb18_dwidth_lp + 4),
           // RSTREG_PRIORITY_A, RSTREG_PRIORITY_B: Reset or enable priority ("RSTREG", "REGCE")
           .RSTREG_PRIORITY_A("RSTREG"),
           .RSTREG_PRIORITY_B("RSTREG"),
           // RST_MODE_A, RST_MODE_B: Set synchronous or asynchronous reset.
           .RST_MODE_A("SYNC"),
           .RST_MODE_B("SYNC"),
           // SRVAL_A, SRVAL_B: Set/reset value for output
           .SRVAL_A(18'h00000),
           .SRVAL_B(18'h00000),
           // Sleep Async: Sleep function asynchronous or synchronous ("TRUE", "FALSE")
           .SLEEP_ASYNC("FALSE"),
           // WriteMode: "WRITE_FIRST", "NO_CHANGE", "READ_FIRST"
           .WRITE_MODE_A("NO_CHANGE"),
           .WRITE_MODE_B("NO_CHANGE")
        )
        i_RAMB18E5 (
           // Cascade Signals outputs: Multi-BRAM cascade signals
           .CASDOUTA(),                       // 16-bit output: Port A cascade output data
           .CASDOUTB(),                       // 16-bit output: Port B cascade output data
           .CASDOUTPA(),                      // 2-bit output: Port A cascade output parity data
           .CASDOUTPB(),                      // 2-bit output: Port B cascade output parity data
           // Port A Data outputs: Port A data
           .DOUTADOUT(ramb18_r_data_lo[i][0 +: 16]),  // 16-bit output: Port A Data/LSB data
           .DOUTPADOUTP(),                            // 2-bit output: Port A parity/LSB parity
           // Port B Data outputs: Port B data
           .DOUTBDOUT(ramb18_r_data_lo[i][16 +: 16]), // 16-bit output: Port B data/MSB data
           .DOUTPBDOUTP(),                            // 2-bit output: Port B parity/MSB parity
           // Cascade Signals inputs: Multi-BRAM cascade signals
           .CASDINA('0),                      // 16-bit input: Port A cascade input data
           .CASDINB('0),                      // 16-bit input: Port B cascade input data
           .CASDINPA('0),                     // 2-bit input: Port A cascade input parity data
           .CASDINPB('0),                     // 2-bit input: Port B cascade input parity data
           .CASDOMUXA(1'b0),                  // 1-bit input: Port A unregistered data (0=BRAM data, 1=CASDINA)
           .CASDOMUXB(1'b0),                  // 1-bit input: Port B unregistered data (0=BRAM data, 1=CASDINB)
           .CASDOMUXEN_A(1'b0),               // 1-bit input: Port A unregistered output data enable
           .CASDOMUXEN_B(1'b0),               // 1-bit input: Port B unregistered output data enable
           .CASOREGIMUXA(1'b0),               // 1-bit input: Port A registered data (0=BRAM data, 1=CASDINA)
           .CASOREGIMUXB(1'b0),               // 1-bit input: Port B registered data (0=BRAM data, 1=CASDINB)
           .CASOREGIMUXEN_A(1'b0),            // 1-bit input: Port A registered output data enable
           .CASOREGIMUXEN_B(1'b0),            // 1-bit input: Port B registered output data enable
           // Port A Address/Control Signals inputs: Port A address and control signals
           .ADDRARDADDR({r_addr_i[0 +: ramb18_awidth_lp], 2'b0}), // 11-bit input: A/Read port address
           .ARST_A(r_reset_i),                // 1-bit input: Port A asynchronous reset
           .CLKARDCLK(r_clk_i),               // 1-bit input: A/Read port clock
           .ENARDEN(r_v_i),                   // 1-bit input: Port A enable/Read enable
           .REGCEAREGCE(reg_out_p ? 1'b1 : 1'b0),        // 1-bit input: Port A register enable/Register enable
           .RSTRAMARSTRAM(reg_out_p ? 1'b0 : r_reset_i), // 1-bit input: Port A set/reset
           .RSTREGARSTREG(reg_out_p ? r_reset_i : 1'b0), // 1-bit input: Port A register set/reset
           .SLEEP(1'b0),                      // 1-bit input: Sleep Mode
           .WEA('0),                          // 2-bit input: Port A write enable
           // Port A Data inputs: Port A data
           .DINADIN(ramb18_w_data_li[i][0 +: 16]),  // 16-bit input: Port A data/LSB data
           .DINPADINP(2'b0),                        // 2-bit input: Port A parity/LSB parity
           // Port B Address/Control Signals inputs: Port B address and control signals
           .ADDRBWRADDR({w_addr_i[0 +: ramb18_awidth_lp], 2'b0}), // 11-bit input: B/Write port address
           .ARST_B(w_reset_i),                // 1-bit input: Port B asynchronous reset
           .CLKBWRCLK(w_clk_i),               // 1-bit input: B/Write port clock
           .ENBWREN(w_v_i),                   // 1-bit input: Port B enable/Write enable
           .REGCEB(1'b0),                     // 1-bit input: Port B register enable
           .RSTRAMB(1'b0),                    // 1-bit input: Port B set/reset
           .RSTREGB(1'b0),                    // 1-bit input: Port B register set/reset
           .WEBWE(ramb18_w_en_li[i]),         // 4-bit input: Port B write enable/Write enable
           // Port B Data inputs: Port B data
           .DINBDIN(ramb18_w_data_li[i][16 +: 16]), // 16-bit input: Port B data/MSB data
           .DINPBDINP(2'b0)                         // 2-bit input: Port B parity/MSB parity
        );
    end

    initial begin
        assert(data_width_p % 8 == 0) else $error("data_width_p must be a multiple of 8");
        assert(addr_width_p == ramb18_awidth_lp) else $error("addr_width_p must match the RAMB18 address width of %0d", ramb18_awidth_lp);
    end

endmodule