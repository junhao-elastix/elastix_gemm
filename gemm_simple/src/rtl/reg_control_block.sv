// ------------------------------------------------------------------
//
// Copyright (c) 2021 Achronix Semiconductor Corp.
// All Rights Reserved.
//
// This Software constitutes an unpublished work and contains
// valuable proprietary information and trade secrets belonging
// to Achronix Semiconductor Corp.
//
// Permission is hereby granted to use this Software including
// without limitation the right to copy, modify, merge or distribute
// copies of the software subject to the following condition:
//
// The above copyright notice and this permission notice shall
// be included in in all copies of the Software.
//
// The Software is provided “as is” without warranty of any kind
// expressed or implied, including  but not limited to the warranties
// of merchantability fitness for a particular purpose and non-infringement.
// In no event shall the copyright holder be liable for any claim,
// damages, or other liability for any damages or other liability,
// whether an action of contract, tort or otherwise, arising from, 
// out of, or in connection with the Software
//
// ------------------------------------------------------------------
// Register control block
//      Provides a set of default system registers at address 0xfff_0000
//      Provides a set of user registers from address 0x0
//      Provides optional pipelining of input and output registers
// ------------------------------------------------------------------

`include "nap_interfaces.svh"
`include "reg_control_defines.svh"
`include "version_defines.svh"

module reg_control_block
#(
    parameter   NUM_USER_REGS         = 2,        // Number of user registers
    parameter   IN_REGS_PIPE          = 0,        // Stages of pipeline for input registers
    parameter   OUT_REGS_PIPE         = 0,        // Stages of pipeline for output registers
    parameter   ENABLE_PCIE_DMA_ACCEL = 0,        // When enabled, turns on support for PCIe DMA acceleration
                                                  // Boosts the response of the AC7t1500 device
    localparam  AXI_DATA_WIDTH        = `ACX_NAP_AXI_DATA_WIDTH,
    localparam  AXI_STRB_WIDTH        = (AXI_DATA_WIDTH/8)

)
(
    // Inputs
    input  wire                         i_clk,
    input  wire                         i_reset_n,
    input  t_ACX_USER_REG               i_user_regs_in[NUM_USER_REGS -1:0],

    // Outputs
    output t_ACX_USER_REG               o_user_regs_out[NUM_USER_REGS -1:0],

    // Write strobes (one per register, pulses for 1 cycle on write)
    output logic [NUM_USER_REGS -1:0]   o_write_strobes
);

    //------------------------------------------------------------
    // AXI initiator NAP and interface
    //------------------------------------------------------------
    logic       output_rstn_nap_main;
    logic       error_valid_nap_main;
    logic [2:0] error_info_nap_main;

    // Main AXI interface
    t_AXI4 #(
            .DATA_WIDTH (`ACX_NAP_AXI_DATA_WIDTH),
            .ADDR_WIDTH (`ACX_NAP_AXI_INITIATOR_ADDR_WIDTH),
            .LEN_WIDTH  (8),
            .ID_WIDTH   (8))
    axi_main_if();

    // Set location in pdc file / testbench bind statement
    nap_initiator_wrapper #(
    ) i_axi_initiator (
        .i_clk              (i_clk),
        .i_reset_n          (i_reset_n),
        .nap                (axi_main_if),
        .o_output_rstn      (output_rstn_nap_main),
        .o_error_valid      (error_valid_nap_main),
        .o_error_info       (error_info_nap_main)
    );

    //------------------------------------------------------------
    // Input pipelining
    //------------------------------------------------------------
    t_ACX_USER_REG   user_regs_in_post_pipe [NUM_USER_REGS -1:0];

    generate if ( IN_REGS_PIPE != 0 ) begin : gb_in_pipe

        // Define pipeline registers as 2D array.  Actually 3D when you include the bits in the register
        t_ACX_USER_REG user_regs_in_d [NUM_USER_REGS -1:0][IN_REGS_PIPE -1:0];

        for ( genvar ur=0; ur < NUM_USER_REGS; ur++ ) begin : gb_in_per_ur

            // Connect first stage
            always @(posedge i_clk)
                user_regs_in_d[ur][0] <= i_user_regs_in[ur];

            // Additional pipeline if specified
            for ( genvar ii=1; ii < IN_REGS_PIPE; ii++ ) begin : gb_in_pipe_del
                always @(posedge i_clk)
                    user_regs_in_d[ur][ii] <= user_regs_in_d[ur][ii-1];
            end
        
            // Connect output of pipeline
            assign user_regs_in_post_pipe[ur] = user_regs_in_d[ur][IN_REGS_PIPE -1];
        end

    end
    else
    begin : gb_no_in_pipe
        assign user_regs_in_post_pipe = i_user_regs_in;
    end
    endgenerate

    //------------------------------------------------------------
    // AXI NAP register read and write sequence
    //------------------------------------------------------------
    // Simple sequence from nap initiator when written to via FCU
    // Get AW followed by W, usually on the next cycle
    // Do not (normally), get the two on the same cycle

    t_ACX_USER_REG_AXI_ADDR reg_addr;
    t_ACX_USER_REG          reg_wr_data;
    t_ACX_USER_REG          reg_rd_data;
    logic                   new_write;
    logic                   new_read;
    logic                   pcie_dbi_w_access_q;
    logic                   pcie_dbi_r_access_q;
    logic                   pcie_dbi_w_access;
    logic                   pcie_dbi_r_access;
    logic                   dma_accel_bvalid;         // AXI B write response valid from DMA accel
    logic [2 -1:0]          dma_accel_bresp;          // AXI B write response from DMA accel
    logic                   dma_accel_rvalid;         // AXI R read response valid from DMA accel
    logic [2 -1:0]          dma_accel_rresp;          // AXI R read response from DMA accel
    logic [4 -1:0]          dma_accel_read_zero_threshold;  // Threshold for number of zero reads required.

    // When PCIe DMA acceleration is present, then generate flags if an access is done to one of the reserved registers
    generate if ( ENABLE_PCIE_DMA_ACCEL != 0 ) begin : gb_dma_access
        // Number of address bits to check for a valid user register access
        // Note : clog2 is the ceiling, so rounds up.  Still works if the value is a power
        // of 2, as we number registers from NUM_USER_REGS-1:0.
        // Add 2 as all registers are on 4 byte boundaries, so 2 extra address bits needed
        localparam USER_REGS_BITS = $clog2(NUM_USER_REGS) + 2;

        // When doing PCIe acceleration, trap all registers below 0x34.
        // 0x34 is used as an internal register to set the read threshold
        always_comb
        begin
            pcie_dbi_w_access_q = (axi_main_if.awaddr[USER_REGS_BITS-1:0] < 'h34);
            // pcie_dbi_r_access_q = (axi_main_if.araddr[USER_REGS_BITS-1:0] < 'h40) && (axi_main_if.araddr[27:16] != 12'hfff);
            // Do not read the DBI registers from this block; instead read them directly
            // The issue is with between the DBI registers and the PCIe core.  The DBI registers themselves are reliable.
            pcie_dbi_r_access_q = 1'b0;
        end
    end
    else
    begin : gb_no_dma_access
        assign pcie_dbi_w_access_q = 1'b0;
        assign pcie_dbi_r_access_q = 1'b0;
    end
    endgenerate

    enum {AXI_IDLE, AXI_WRITE_RESP, AXI_WRITE_PENDING, AXI_GET_VALUE, AXI_READ} axi_state;

    always @(posedge i_clk)
    begin
        if ( ~i_reset_n )
        begin
            axi_state <= AXI_IDLE;
            axi_main_if.awready <= 1'b0;
            axi_main_if.wready  <= 1'b0;
            axi_main_if.arready <= 1'b0;
            axi_main_if.rvalid  <= 1'b0;
            axi_main_if.rlast   <= 1'b0;
            axi_main_if.bvalid  <= 1'b0;
        end
        else
        begin
            case (axi_state)
                AXI_IDLE : begin
                    new_write           <= 1'b0;
                    new_read            <= 1'b0;
                    axi_main_if.awready <= 1'b1;
                    axi_main_if.wready  <= 1'b1;
                    axi_main_if.arready <= 1'b1;
                    axi_main_if.rvalid  <= 1'b0;
                    axi_main_if.rlast   <= 1'b0;
                    axi_main_if.bvalid  <= 1'b0;
                    pcie_dbi_w_access   <= 1'b0;
                    pcie_dbi_r_access   <= 1'b0;

                    if ( axi_main_if.awvalid & axi_main_if.awready )
                    begin
                        axi_main_if.awready <= 1'b0;
                        axi_main_if.arready <= 1'b0;
                        reg_addr            <= axi_main_if.awaddr[27:0];
                        axi_main_if.bid     <= axi_main_if.awid;
                        pcie_dbi_w_access   <= pcie_dbi_w_access_q;
                        if ( axi_main_if.wvalid & axi_main_if.wready )
                        begin
                            // Need to mux the 32-bits from the 256 bits based on the byte lane
                            case (axi_main_if.wstrb)
                                32'h0000_000f : reg_wr_data <= axi_main_if.wdata[(0*32) +: 32];
                                32'h0000_00f0 : reg_wr_data <= axi_main_if.wdata[(1*32) +: 32];
                                32'h0000_0f00 : reg_wr_data <= axi_main_if.wdata[(2*32) +: 32];
                                32'h0000_f000 : reg_wr_data <= axi_main_if.wdata[(3*32) +: 32];
                                32'h000f_0000 : reg_wr_data <= axi_main_if.wdata[(4*32) +: 32];
                                32'h00f0_0000 : reg_wr_data <= axi_main_if.wdata[(5*32) +: 32];
                                32'h0f00_0000 : reg_wr_data <= axi_main_if.wdata[(6*32) +: 32];
                                32'hf000_0000 : reg_wr_data <= axi_main_if.wdata[(7*32) +: 32];
                            endcase
                            new_write          <= 1'b1;
                            axi_main_if.wready <= 1'b0;
                            axi_state          <= AXI_WRITE_RESP;
                            // axi_main_if.bvalid <= 1'b1;
                        end
                        else
                        begin
                            axi_state <= AXI_WRITE_PENDING;
                        end
                    end
                    else if ( axi_main_if.arvalid & axi_main_if.arready )
                    begin
                        reg_addr            <= axi_main_if.araddr[27:0];
                        axi_state           <= AXI_GET_VALUE;
                        new_read            <= 1'b1;
                        axi_main_if.awready <= 1'b0;
                        axi_main_if.arready <= 1'b0;
                        axi_main_if.wready  <= 1'b0;
                        axi_main_if.rid     <= axi_main_if.arid;
                        pcie_dbi_r_access   <= pcie_dbi_r_access_q;
                    end
                    else
                        axi_state <= AXI_IDLE;
                end
                AXI_WRITE_RESP : begin
                    // Set bvalid based on mode
                    if ( pcie_dbi_w_access == 1'b1 )
                        axi_main_if.bvalid <= dma_accel_bvalid;
                    else
                        axi_main_if.bvalid <= 1'b1;

                    // Once valid bresp received, clear flags and return to idle
                    // Note that for a DBI read, it's still a write cycle and the bvalid
                    // is not sent until after the value has been read from DBI and put into dbi_rdata_reg
                    if ( axi_main_if.bready & axi_main_if.bvalid )
                    begin
                        axi_main_if.bvalid <= 1'b0;
                        axi_state          <= AXI_IDLE;
                    end
                end
                AXI_WRITE_PENDING : begin
                    if ( axi_main_if.wvalid & axi_main_if.wready )
                    begin
                        // Need to mux the 32-bits from the 256 bits based on the byte lane
                        case (axi_main_if.wstrb)
                            32'h0000_000f : reg_wr_data <= axi_main_if.wdata[(0*32) +: 32];
                            32'h0000_00f0 : reg_wr_data <= axi_main_if.wdata[(1*32) +: 32];
                            32'h0000_0f00 : reg_wr_data <= axi_main_if.wdata[(2*32) +: 32];
                            32'h0000_f000 : reg_wr_data <= axi_main_if.wdata[(3*32) +: 32];
                            32'h000f_0000 : reg_wr_data <= axi_main_if.wdata[(4*32) +: 32];
                            32'h00f0_0000 : reg_wr_data <= axi_main_if.wdata[(5*32) +: 32];
                            32'h0f00_0000 : reg_wr_data <= axi_main_if.wdata[(6*32) +: 32];
                            32'hf000_0000 : reg_wr_data <= axi_main_if.wdata[(7*32) +: 32];
                        endcase
                        axi_main_if.wready <= 1'b0;
                        new_write          <= 1'b1;
                        axi_state          <= AXI_WRITE_RESP;
                        // axi_main_if.bvalid <= 1'b1;
                    end
                    else
                        axi_state <= AXI_WRITE_PENDING;
                end
                AXI_GET_VALUE : begin
                    // For non-dbi access, advance straight to AXI_READ
                    // For dbi access, wait until value has been read (3x)
                    if ( (pcie_dbi_r_access == 1'b0) || (dma_accel_rvalid == 1'b1) )
                    begin
                        // Single cycle state to get value from register array
                        axi_state          <= AXI_READ;
                        axi_main_if.rvalid <= 1'b1;
                        // All reads are a single word
                        axi_main_if.rlast  <= 1'b1;
                    end
                end
                AXI_READ : begin
                    if (axi_main_if.rready)
                    begin
                        axi_state          <= AXI_IDLE;
                        axi_main_if.rvalid <= 1'b0;
                    end
                end
                default : axi_state <= AXI_IDLE;
            endcase
        end
    end

    // Assign internal read register to AXI
    // Below is the "correct" way to do this.  If this becomes
    // timing problematic, then just repeat reg_rd_data across
    // all 8 lanes of rdata - the FCU will select the lane it requires
    always_comb
    begin
        axi_main_if.rdata = {256{1'b0}};
        case (reg_addr[4:2])
            3'b000 : axi_main_if.rdata[(32*0) +: 32] = reg_rd_data;
            3'b001 : axi_main_if.rdata[(32*1) +: 32] = reg_rd_data;
            3'b010 : axi_main_if.rdata[(32*2) +: 32] = reg_rd_data;
            3'b011 : axi_main_if.rdata[(32*3) +: 32] = reg_rd_data;
            3'b100 : axi_main_if.rdata[(32*4) +: 32] = reg_rd_data;
            3'b101 : axi_main_if.rdata[(32*5) +: 32] = reg_rd_data;
            3'b110 : axi_main_if.rdata[(32*6) +: 32] = reg_rd_data;
            3'b111 : axi_main_if.rdata[(32*7) +: 32] = reg_rd_data;
        endcase
    end

    //------------------------------------------------------------
    // System registers
    //------------------------------------------------------------
    // Read only
    // Hard coded to locations 0x0fff_0000 to 0x0fff_0010
    t_ACX_USER_REG  sys_reg_major_version = `ACX_MAJOR_VERSION;
    t_ACX_USER_REG  sys_reg_minor_version = `ACX_MINOR_VERSION;
    t_ACX_USER_REG  sys_reg_patch_version = `ACX_PATCH_VERSION;
    t_ACX_USER_REG  sys_reg_p4_version    = `REVISON_CONTROL_VERSION;    // Auto-derived

    //------------------------------------------------------------
    // User registers
    //------------------------------------------------------------

    // Write decode bit per register
    logic [NUM_USER_REGS -1:0] write_addr_sel;

    // Generate write strobes (1-cycle pulse when register is written)
    // Register them to ensure proper timing since new_write and write_addr_sel
    // may not be synchronous in all cases
    logic [NUM_USER_REGS -1:0] write_strobes_reg;

    always_ff @(posedge i_clk) begin
        if (~i_reset_n) begin
            write_strobes_reg <= '0;
        end else begin
            write_strobes_reg <= write_addr_sel & {NUM_USER_REGS{new_write}};
        end
    end

    assign o_write_strobes = write_strobes_reg;

    // Addresses and read data for DBI block
    localparam [24 -1:0] MAGIC_VAL_ADDR      =  24'h00_0000;
    localparam [24 -1:0] DBI_RDATA_ADDR      =  24'h00_002C;
    localparam [24 -1:0] DBI_READ_TH_ADDR    =  24'h00_0034;

    t_ACX_USER_REG dbi_rdata_reg;
    t_ACX_USER_REG dbi_mismatch_reg;

    generate begin : gb_decode
        int jj;
        always @(posedge i_clk)
        begin
            write_addr_sel      <= {NUM_USER_REGS{1'b0}};           // No address decoded
            axi_main_if.bresp <= 2'b10;                             // Write response error
            axi_main_if.rresp <= 2'b10;                             // Read response error
            reg_rd_data         <= '0;
            for ( jj=0; jj < (NUM_USER_REGS+4); jj++ )
                if ( jj < NUM_USER_REGS )
                begin
                    if ( reg_addr == (jj*4) )
                    begin
                        if ( ENABLE_PCIE_DMA_ACCEL != 0 ) begin : gb_accel_bresp
                            // bresp
                            if ( reg_addr < 24'h34 )
                                axi_main_if.bresp  <= dma_accel_bresp;   // Dependant upon the multi-writes response
                            else
                                axi_main_if.bresp  <= 2'b00;             // Good write decode

                            // Read data
                            if ( reg_addr == MAGIC_VAL_ADDR )
                                reg_rd_data <= 32'habacabef;             // Magic value that PCIE_DMA_ACCELERATION is enabled.
                            else if ( reg_addr == DBI_RDATA_ADDR )
                                reg_rd_data <= dbi_rdata_reg;            // DBI RDATA from accelerator
                            else if ( reg_addr == DBI_READ_TH_ADDR)
                                reg_rd_data <= {28'h0, dma_accel_read_zero_threshold}; // DBI read threshold register
                            else
                                reg_rd_data <= user_regs_in_post_pipe[jj];  // Read data
                        end
                        else
                        begin : gb_no_accel_bresp
                            // bresp
                            axi_main_if.bresp  <= 2'b00;                // Good write decode
                            // Read data
                            reg_rd_data <= user_regs_in_post_pipe[jj];  // Read data
                        end

                        // If reading from the DBI, pass back the read response
                        // This will signal error if the 3 read values don't match
                        if ( pcie_dbi_r_access )
                            axi_main_if.rresp <= dma_accel_rresp;       // Read response for dbi
                        else
                            axi_main_if.rresp <= 2'b00;                 // Good read decode

                        write_addr_sel[jj] <= (axi_state == AXI_WRITE_RESP);   
                                                                    // Valid address decoded
                                                                    // Only write on a single cycle
                    end
                end
                else
                begin
                    if ( reg_addr == (((jj-NUM_USER_REGS)*4) + 32'h0fff_0000) )     // System register offset
                    begin
                        axi_main_if.rresp <= 2'b00;               // Good read decode
                        case ( jj )
                            NUM_USER_REGS   : reg_rd_data <= sys_reg_major_version;
                            NUM_USER_REGS+1 : reg_rd_data <= sys_reg_minor_version;
                            NUM_USER_REGS+2 : reg_rd_data <= sys_reg_patch_version;
                            NUM_USER_REGS+3 : reg_rd_data <= sys_reg_p4_version;
                        endcase
                    end
                end
        end
    end
    endgenerate

    t_ACX_USER_REG   user_regs_out_pre_pipe [NUM_USER_REGS -1:0];

    generate for (genvar ii=0; ii < NUM_USER_REGS; ii++ ) begin : gb_user_regs

        // Write to user register
        always @(posedge i_clk)
            if ( write_addr_sel[ii] && new_write )
            begin
                user_regs_out_pre_pipe[ii] <= reg_wr_data;
            end

        // Purely to give visibility in simulation
        // synthesis synthesis_off
        t_ACX_USER_REG   sim_monitor_reg_out;
        t_ACX_USER_REG   sim_monitor_reg_in;

        assign sim_monitor_reg_out = o_user_regs_out[ii];
        assign sim_monitor_reg_in  = i_user_regs_in[ii];
        // synthesis synthesis_on

    end
    endgenerate

    //------------------------------------------------------------
    // Output pipelining
    //------------------------------------------------------------

    generate if ( OUT_REGS_PIPE != 0 ) begin : gb_out_pipe

        // Define output pipeline registers as 2D array
        t_ACX_USER_REG user_regs_out_d [NUM_USER_REGS -1:0][OUT_REGS_PIPE -1:0];

        for ( genvar uro=0; uro < NUM_USER_REGS; uro++ ) begin : gb_out_per_ur

            // Connect first stage
            always @(posedge i_clk)
                user_regs_out_d[uro][0] <= user_regs_out_pre_pipe[uro];

            for ( genvar jj=1; jj < OUT_REGS_PIPE; jj++ ) begin : gb_out_pipe_del
                // Pipeline other stages if specified
                always @(posedge i_clk)
                    user_regs_out_d[uro][jj] <= user_regs_out_d[uro][jj-1];
            end
            
            // Connect output of pipeline
            assign o_user_regs_out[uro] = user_regs_out_d[uro][OUT_REGS_PIPE -1];
        end
    end
    else
    begin : gb_no_out_pipe
        assign o_user_regs_out = user_regs_out_pre_pipe;
    end
    endgenerate

    //------------------------------------------------------------
    // DMA accelerator, (optional)
    //------------------------------------------------------------

    generate if ( ENABLE_PCIE_DMA_ACCEL != 0 ) begin : gb_dma_accel

        logic           dma_accel_write_req;
        logic           reg_control_fsm_idle;
        logic           target_doorbell;
        logic [32 -1:0] dbi_rdata;              // Value from DBI RDATA reg
        logic           dbi_read_mismatch;
        logic [4  -1:0] dbi_num_reads;

        // Code explicitly to avoid X's
        always_comb
            if (axi_main_if.wvalid & axi_main_if.wready)
                dma_accel_write_req <= 1'b1;
            else
                dma_accel_write_req <= 1'b0;

        assign reg_control_fsm_idle = (axi_state == AXI_IDLE);

        // Each of the DBI addresses has +1 as it is a 33-bit address to the DBI
        localparam [32 -1:0] DMA_DOORBELL_WRITE_PF0 = 32'h80080011;
        localparam [32 -1:0] DMA_DOORBELL_READ_PF0  = 32'h80080031;
        // DBI register locations
        localparam integer   DBI_ADDRESS_REG_NUM = (24'h00_0024/4);
        // Local reg for threshold. Not used for DBI accesses
        localparam integer   DBI_READ_TH_REG_NUM = (DBI_READ_TH_ADDR/4);

        // Pre-calculate if the doorbell register is the target of the next DBI write
        // Assign explicitly to remove X when address not defined
        // Four DMA channels, all as part of PF0.
        always @(posedge i_clk)
            if ( (user_regs_out_pre_pipe[DBI_ADDRESS_REG_NUM] == DMA_DOORBELL_WRITE_PF0) ||
                 (user_regs_out_pre_pipe[DBI_ADDRESS_REG_NUM] == DMA_DOORBELL_READ_PF0) )
                target_doorbell <= 1'b1;
            else
                target_doorbell <= 1'b0;

        // Register the DBI RDATA register value, and the number of mismatches
        always @(posedge i_clk)
            if ( dma_accel_rvalid )
            begin
                dbi_rdata_reg    <= dbi_rdata;
                dbi_mismatch_reg <= {dbi_read_mismatch, 27'b0, dbi_num_reads};
            end

        always @(posedge i_clk)
            dma_accel_read_zero_threshold <= user_regs_out_pre_pipe[DBI_READ_TH_REG_NUM];

        // DMA accelerator block
        reg_control_block_dma_accel  #(
        ) i_dma_accel (
            .i_clk                      (i_clk),
            .i_reset_n                  (i_reset_n),
            .i_reg_addr                 (reg_addr),
            .i_axi_wdata                (axi_main_if.wdata),
            .i_axi_wstrb                (axi_main_if.wstrb),
            .i_pcie_dbi_w_access        (pcie_dbi_w_access),
            .i_write_req                (dma_accel_write_req),
            .i_target_doorbell          (target_doorbell),
            .i_reg_control_idle         (reg_control_fsm_idle),
            .i_dbi_read_zero_threshold  (dma_accel_read_zero_threshold),
            .o_write_bvalid             (dma_accel_bvalid),
            .o_write_bresp              (dma_accel_bresp),
            .o_read_rvalid              (dma_accel_rvalid),
            .o_read_rresp               (dma_accel_rresp),
            .o_dbi_rdata                (dbi_rdata),
            .o_dbi_num_reads            (dbi_num_reads),
            .o_dbi_read_mismatch        (dbi_read_mismatch)
        );
    end
    else
    begin : gb_no_dma_accel
        assign dma_accel_bvalid        = 1'b1;
        assign dma_accel_bresp         = 2'b00;
        assign dma_accel_rvalid        = 1'b1;
        assign dma_accel_rresp         = 2'b00;
        assign dbi_rdata_reg           = 'h0;
        assign dbi_mismatch_reg        = 'h0;
    end
    endgenerate

endmodule : reg_control_block

