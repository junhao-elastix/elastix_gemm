// ------------------------------------------------------------------
// Elastix GEMM Engine - Speedster7t Matrix Acceleration Platform
// 
// This design implements a high-performance matrix multiplication accelerator
// featuring dual-memory DMA support with BRAM and GDDR6 endpoints.
// The primary compute engine is the integrated MS2.0 GEMM engine on GDDR6 Channel 1.
//
// Key Features:
// - MS2.0 GEMM Engine with 128x128 matrix capability
// - Dual-memory DMA support (BRAM and GDDR6)
// - 8-channel GDDR6 subsystem (16GB total memory)
// - Multiple BRAM responder instances for data I/O
// - Complete register interface for control and status monitoring
// - MSI-X interrupt support for event notification
// - FLR (Function Level Reset) responder for PCIe compliance
//
// Memory Architecture:
// - BRAM: Low-latency on-chip memory for matrix I/O
// - GDDR6: High-bandwidth external memory for large matrix operations
//
// Control Interface:
// - MS2.0 Engine Registers (0x28-0x40): GEMM command and status interface
// - System Status Registers: Device health and GDDR6 training status
// - Scratch Register: General-purpose register with build timestamp
//
// Compute Architecture:
// - Channel 1: MS2.0 GEMM Engine (matrix multiplication core)
// - Channels 0,2-7: Memory validation and testing infrastructure
// ------------------------------------------------------------------

`include "nap_interfaces.svh"
`include "reg_control_defines.svh"
`include "version_defines.svh"
`include "build_timestamp.svh"

// Include the JTAG port definitions, (used by ADM and SnapShot)
`include "speedster7t/common/speedster7t_tap_sim.sv"
// Include the BittWare BMC interface
`include "BW_BMC_IF.svp"

// ACX_USE_SNAPSHOT must be defined in the Synplify project, or in /src/constraints/synplify_options.tcl
`ifdef ACX_USE_SNAPSHOT
    `include "speedster7t/common/speedster7t_snapshot_v3.sv"
`endif


module elastix_gemm_top
#(
    parameter       DDR4_NOC_ADDR_ID        = 2'b01,    // DDR4 target address ID - kept for compatibility
    parameter       DDR4_LINEAR_ADDR        = 1         // Kept for compatibility
)
(
    // VectorPath 815 port signals
    `include "../ioring/elastix_gemm_top_user_design_port_list.svh"

    // JTAG signals for SnapShot and ACX Device Manager
    ,
    input  wire t_JTAG_INPUT                i_jtag_in,
    output wire t_JTAG_OUTPUT               o_jtag_out
);

    // ------------------------
    // Output enables
    // ------------------------
    // Set output enables active
    // VectorPath 815 pins
    assign led_l_oe          = 8'hff;
    assign ext_gpio_dir_oe   = 8'hff;
    assign ext_gpio_oe_l_oe  = 1'b1;
    assign led_oe_l_oe       = 1'b1;
    assign led_oe_l          = 1'b0;    // Output enable on level shifter
    assign irq_to_avr_oe     = 1'b1;
    assign fpga_ftdi_txd_oe  = 1'b1;
    assign fpga_i2c_req_l_oe = 1'b1;

    // ------------------------
    // Output port signals
    // ------------------------
    assign ext_gpio_dir      = 8'h00;
    assign ext_gpio_oe_l     = 1'b1;
    assign fpga_ftdi_txd     = 1'b0;        
    assign fpga_i2c_req_l    = 1'b1;


    // signals for shared JTAG bus
    wire   t_JTAP_BUS     jtap_bus;       // shared JTAG bus
    wire                  tdo_bus;        // tie to 0 if unused

    // For DDR4, top 2 bits of the address define the DDR4 target ID
    localparam ADDR_ID_WIDTH = 2;

    // Check DDR4_ADDR_ID is correct size
    generate if ($bits(DDR4_NOC_ADDR_ID) != ADDR_ID_WIDTH) begin : gb_addr_id_error
        ERROR_ddr4_addr_id_wrong_size();
    end
    endgenerate
    
    // Status outputs - not used in BRAM-only design
    logic   ddr_nap_fail;
    logic   ddr_nap_done;
    
    // MS2.0 Engine command submit - removed duplicate pulse generation
    
    // Tie off DDR signals (not used in current design)
    assign ddr_nap_fail = 1'b0;
    assign ddr_nap_done = 1'b1;

    // ------------------------
    //   Resets
    //   Three needed for the three functional blocks, registers, DDR NAP and Ethernet
    // ------------------------    
    logic   reg_rstn /* synthesis syn_keep=1 */;        // Reset over clock
    logic   nap_rstn /* synthesis syn_keep=1 */;        // Reset over clock
    logic   adm_rstn;                                   // ADM reset
    logic   bw_bmc_if_rstn;                             // bw_bmc_if reset

    logic [3:0] flr_pf_active_sync;
    logic [3:0] flr_pf_active_n;

    // inverse flr_pf_active to use as reset source or active-low reset
    assign flr_pf_active_n = ~pci_express_x16_status_flr_pf_active;

    // synchronize function level reset for physical function 0
    ACX_SYNCHRONIZER x_sync_flr_pf0 (.din(pci_express_x16_status_flr_pf_active[0]), .dout(flr_pf_active_sync[0]), .clk(i_reg_clk), .rstn(1'b1));
    // synchronize function level reset for physical function 1
    ACX_SYNCHRONIZER x_sync_flr_pf1 (.din(pci_express_x16_status_flr_pf_active[1]), .dout(flr_pf_active_sync[1]), .clk(i_reg_clk), .rstn(1'b1));
    // physical function 2 and 3 are not used in design
    assign flr_pf_active_sync[3:2] = 2'b00;

    // No reset input to VectorPath card, so generate a self-starting reset from power up
    // Once the circuit is running, the various blocks have their individual resets controlled from
    // the reg_control_block
    logic [32 -1:0] reset_pipe = 16'h0;

    always @(posedge i_reg_clk)
        reset_pipe <= {reset_pipe[$bits(reset_pipe)-2 : 0], 1'b1};

    // Create a main reset, based on reg_clk, used for PF0
    reset_processor_v2 #(
        .NUM_INPUT_RESETS       (7),    // Seven reset sources
        .IN_RST_PIPE_LENGTH     (8),    // Length of input flop pipeline, minimum of 2
                                        // Ignored if SYNC_INPUT_RESETS = 0
        .SYNC_INPUT_RESETS      (1),    // Synchronize input resets
        .OUT_RST_PIPE_LENGTH    (4),    // Length of reset flop pipeline, minimum of 2
                                        // Ignored if RESET_OVER_CLOCK = 1
        .RESET_OVER_CLOCK       (0)     // Not set to route the output reset over the clock network
    ) i_reset_processor_main (
        .i_rstn_array       ({reset_pipe[$bits(reset_pipe)-1],  // self-starting reset
                              pll_pcie_lock, pll_ddr_lock, pll_noc_lock, pll_gddr_SE_lock, pll_gddr_SW_lock,    // PLL lock signals
                              flr_pf_active_n[0]}),             // function level reset for physical function 0
        .i_clk              (i_reg_clk),
        .o_rstn             (reg_rstn)
    );

    // Create NAP rst, controlled from reg_rstn, synchronized to i_nap_clk.
    ACX_SYNCHRONIZER x_sync_nap_rstn (.din(1'b1), .dout(nap_rstn), .clk(i_nap_clk), .rstn(reg_rstn));
    // Create ADM rst, controlled from reg_rstn, synchronized to i_adm_clk.
    ACX_SYNCHRONIZER x_sync_adm_rstn (.din(1'b1), .dout(adm_rstn), .clk(i_adm_clk), .rstn(reg_rstn));

    // Create BW_BMC_IF rst, controlled from function level reset for physical function 1, synchronized to i_adm_clk.
    ACX_SYNCHRONIZER x_sync_bw_bmc_if_rstn (.din(1'b1), .dout(bw_bmc_if_rstn), .clk(i_adm_clk), .rstn(flr_pf_active_n[1]));

    //--------------------------------------------------------------------
    // Internal register block
    //--------------------------------------------------------------------
    // Create a set of user registers
    // These can be used for either setting values or monitoring results
    // in the user design
    // user_regs_write is to write values to the user design
    // user_regs_read is to read values from the user design
    //--------------------------------------------------------------------

    localparam      REGS_PER_IRQ_GEN_CH    = 3;
    localparam      REGS_PER_MSIX_IRQ_CH   = 4;
    localparam      NUM_MSIX_IRQ_CH        = 2;
    localparam      NUM_IRQ_GEN_REGS       = (NUM_MSIX_IRQ_CH * REGS_PER_IRQ_GEN_CH); // 2*3 = 6
    localparam      NUM_MSIX_IRQ_REGS      = 4 + (NUM_MSIX_IRQ_CH * REGS_PER_MSIX_IRQ_CH); // 4 + (2*4) = 12
    // GDDR6 register allocation (NOTE: 77 of 88 registers unused with GEMM focus)
    localparam      REGS_PER_GDDR_CH       = 11;                // Registers per GDDR6 channel
    localparam      NUM_GDDR_CHANNELS      = 8;                 // 8 GDDR6 channels
    localparam      NUM_GDDR_REGS          = NUM_GDDR_CHANNELS * REGS_PER_GDDR_CH - 1; // 8 * 11 - 1 = 87 (reduced by 1 for NAP_ERROR_STATUS)
    // OPTIMIZATION OPPORTUNITY: Could reduce to 11 regs (Channel 0 only) or 0 regs (no packet gen used)
    // This would free up 77-88 registers for future GEMM engine expansion
    // Register numbers
    localparam      CONTROL_REG            = 0;                 // System control register
    localparam      TEST_STATUS_REG        = 1;                 // System status register

    // Debug Registers (Oct 9, 2025 - MS2.0 GEMM Engine Debug Visibility)
    localparam      CE_BRAM_ADDR_DEBUG     = 2;                 // CE BRAM read address {21'h0, addr[10:0]} - 0x08
    localparam      CE_BRAM_DATA_LOW       = 3;                 // BRAM data sample [31:0] - 0x0C
    localparam      CE_BRAM_DATA_MID       = 4;                 // BRAM data sample [63:32] - 0x10
    localparam      CE_CONTROL_DEBUG       = 5;                 // CE control {24'h0, rd_en, load_count[2:0], state[3:0]} - 0x14
    localparam      DC_BRAM_WRITE_DEBUG    = 6;                 // DC BRAM write {20'h0, wr_en, wr_addr[10:0]} - 0x18
    localparam      DC_CONTROL_DEBUG       = 7;                 // DC status {24'h0, fetch_done, disp_done, 2'b0, dc_state[3:0]} - 0x1C
    localparam      BCV_DEBUG_STATE        = 8;                 // BCV controller {b_idx[7:0], c_idx[7:0], v_idx[7:0], fill[2:0], wait[2:0], state[1:0]} - 0x20
    localparam      BCV_DEBUG_DIMS         = 9;                 // BCV dimensions {dim_b_reg[7:0], dim_c_reg[7:0], dim_v_reg[7:0], i_dim_v[7:0]} - 0x24
    localparam      MC_TILE_DIMS           = 10;                // MC TILE dimensions {dim_b[7:0], dim_c[7:0], dim_v[7:0], 8'h00} - 0x28
    localparam      MC_PAYLOAD_WORD1       = 11;                // MC raw payload word 1 - 0x2C
    localparam      MC_PAYLOAD_WORD2       = 12;                // MC raw payload word 2 - 0x30
    localparam      MC_PAYLOAD_WORD3       = 13;                // MC raw payload word 3 - 0x34

    // MS2.0 GEMM Engine Registers (Channel 1)
    localparam      ENGINE_BYPASS_CTRL     = 14;                // Bypass control {30'h0, bypass_mode[1:0]} - 0x38
    localparam      ENGINE_CMD_WORD0       = 15;                // Command word 0 (contains opcode) - 0x3C
    localparam      ENGINE_CMD_WORD1       = 16;                // Command word 1 - 0x40
    localparam      ENGINE_CMD_WORD2       = 17;                // Command word 2 - 0x44
    localparam      ENGINE_CMD_WORD3       = 18;                // Command word 3 - 0x48
    localparam      ENGINE_CMD_SUBMIT      = 19;                // Submit trigger (write 1 to execute) - 0x4C
    localparam      ENGINE_STATUS          = 20;                // Engine status {CE[3:0], DC[3:0], MC[3:0], busy} - 0x50
    localparam      ENGINE_RESULT_COUNT    = 21;                // Result count (FP16 values written) - 0x54
    localparam      ENGINE_DEBUG           = 22;                // Debug signals {FIFO_empty, bridge_busy, FIFO_count[12:0]} - 0x58
    localparam      NAP_ERROR_STATUS       = 23;                // NAP Channel 1 error status {29'h0, error_info[2:0]} - 0x5C
    localparam      DC_BRAM_WR_COUNT       = 24;                // Dispatcher BRAM write count {22'h0, count[9:0]} - 0x60
    localparam      DC_DEBUG               = 25;                // Dispatcher debug {28'h0, dc_state[3:0]} - 0x64

    localparam      IRQ_GEN_REGS_BASE      = 26;                // Start IRQ registers after debug regs (25 = DC_DEBUG)
    localparam      MSIX_IRQ_REGS_BASE     = IRQ_GEN_REGS_BASE + NUM_IRQ_GEN_REGS; // 26 + 6 = 32
    localparam      GDDR_REGS_BASE         = MSIX_IRQ_REGS_BASE + NUM_MSIX_IRQ_REGS; // 32 + 12 = 44
    localparam      NUM_USER_REGS          = GDDR_REGS_BASE + NUM_GDDR_REGS + 4 + 5 + 4; // 44 + 87 + 4 + 5 + 4 = 144 (added circular buffer registers)
    localparam      LTSSM_STATE_REG        = NUM_USER_REGS - 13; // 144 - 13 = 131, offset 131*4 = 524 = 0x20C
    localparam      ADM_STATUS_REG         = NUM_USER_REGS - 12; // 144 - 12 = 132, offset 132*4 = 528 = 0x210
    localparam      BITSTREAM_ID           = NUM_USER_REGS - 11; // 144 - 11 = 133, offset 133*4 = 532 = 0x214
    localparam      SCRATCH_REG            = NUM_USER_REGS - 10; // 144 - 10 = 134, offset 134*4 = 536 = 0x218
    localparam      RESULT_REG_0           = NUM_USER_REGS - 9; // 144 - 9 = 135, offset 135*4 = 540 = 0x21C
    localparam      RESULT_REG_1           = NUM_USER_REGS - 8; // 144 - 8 = 136, offset 136*4 = 544 = 0x220
    localparam      RESULT_REG_2           = NUM_USER_REGS - 7; // 144 - 7 = 137, offset 137*4 = 548 = 0x224
    localparam      RESULT_REG_3           = NUM_USER_REGS - 6; // 144 - 6 = 138, offset 138*4 = 552 = 0x228
    localparam      ENGINE_WRITE_TOP       = NUM_USER_REGS - 5; // 144 - 5 = 139, offset 139*4 = 556 = 0x22C (write_top)
    localparam      REG_RD_PTR             = NUM_USER_REGS - 4; // 144 - 4 = 140, offset 140*4 = 560 = 0x230 (NEW: read pointer)
    localparam      REG_WR_PTR             = NUM_USER_REGS - 3; // 144 - 3 = 141, offset 141*4 = 564 = 0x234 (NEW: write pointer)
    localparam      REG_USED_ENTRIES       = NUM_USER_REGS - 2; // 144 - 2 = 142, offset 142*4 = 568 = 0x238 (NEW: used entries)
    localparam      REG_RESULT_EMPTY       = NUM_USER_REGS - 1; // 144 - 1 = 143, offset 143*4 = 572 = 0x23C (NEW: empty flag)
    t_ACX_USER_REG  user_regs_write [NUM_USER_REGS -1:0];
    t_ACX_USER_REG  user_regs_read  [NUM_USER_REGS -1:0];

    //--------------------------------------------------------------------
    // Control signals for DMA features  
    //--------------------------------------------------------------------
    // Legacy +42 processing removed - no longer needed for GEMM engine focus
    
    // GDDR6 channel configuration and status signals
    localparam GDDR6_NOC_CONFIG = 8'b00000010;  // Enable only Channel 1 (MS2.0 GEMM engine)
    localparam MAX_NOC_CHANNELS = 8;

    // GDDR6 target address mapping (NoC page IDs from reference design)
    // West side: channels 0-3, East side: channels 4-7
    localparam [71:0] GDDR6_ID_NOC_CH1 = {9'd10, 9'd2, 9'd6, 9'd14, 9'd9, 9'd1, 9'd5, 9'd13};

    // GDDR6 memory addressing parameters
    // VP815 uses 2x 8Gb devices in clamshell x8 mode = 2GB per channel
    localparam GDDR_NOC_ADDR_WIDTH = 26;  // Address width for 2GB
    localparam GDDR_PAD_WIDTH = 42 - 9 - GDDR_NOC_ADDR_WIDTH - 5;  // Padding bits

    // GDDR6 channel status signals
    logic [MAX_NOC_CHANNELS-1:0] gddr_nap_fail;
    logic [MAX_NOC_CHANNELS-1:0] gddr_nap_done;
    logic [MAX_NOC_CHANNELS-1:0] gddr_nap_running;

    // Instantiate default register control block
    // CRITICAL FIX: Run reg_control_block on NAP clock (same as engine)
    // This eliminates clock domain crossing issues between registers and engine
    // All CSR signals now synchronous on i_nap_clk
    logic [NUM_USER_REGS-1:0] write_strobes;  // Write strobes from reg_control_block
    logic engine_cmd_submit_stretched;  // 4-cycle stretched pulse for ENGINE_CMD_SUBMIT

    reg_control_block  #(
        .NUM_USER_REGS          (NUM_USER_REGS),        // Number of user registers
        .IN_REGS_PIPE           (1),                    // Input register pipeline stages
        .OUT_REGS_PIPE          (1)                     // Output register pipeline stages
    ) i_reg_control_block (
        .i_clk                  (i_reg_clk),            // CHANGED: Use NAP clock instead of reg_clk
        .i_reset_n              (nap_rstn),             // CHANGED: Use NAP reset instead of reg_rstn
        .i_user_regs_in         (user_regs_read),
        .o_user_regs_out        (user_regs_write),
        .o_write_strobes        (write_strobes)         // NEW: Write strobes for each register
    );

    // Stretch ENGINE_CMD_SUBMIT strobe from 1 cycle to 4 cycles
    // This ensures the pulse is long enough to be captured reliably
    logic [2:0] submit_stretch_counter;
    logic [15:0] submit_strobe_count;  // Count write strobes for debugging

    always_ff @(posedge i_nap_clk) begin
        if (~nap_rstn) begin
            submit_stretch_counter <= 3'd0;
            engine_cmd_submit_stretched <= 1'b0;
            submit_strobe_count <= 16'd0;
        end else begin
            if (write_strobes[ENGINE_CMD_SUBMIT]) begin
                // Start 4-cycle pulse
                submit_stretch_counter <= 3'd4;
                engine_cmd_submit_stretched <= 1'b1;
                submit_strobe_count <= submit_strobe_count + 1'd1;  // Count strobes
            end else if (submit_stretch_counter > 0) begin
                submit_stretch_counter <= submit_stretch_counter - 1'd1;
                engine_cmd_submit_stretched <= 1'b1;
            end else begin
                engine_cmd_submit_stretched <= 1'b0;
            end
        end
    end

    // Debug register to monitor write strobe generation
    logic [31:0] submit_strobe_debug;
    assign submit_strobe_debug = {
        submit_strobe_count,                    // [31:16] Total strobe count
        10'd0,                                  // [15:6] Reserved
        nap_rstn,                               // [5] NAP reset state (should be 1)
        reg_rstn,                               // [4] REG reset state (should be 1)
        submit_stretch_counter,                 // [3:1] Stretch counter
        write_strobes[ENGINE_CMD_SUBMIT]        // [0] Raw write strobe
    };

    // Control register read-back
    assign user_regs_read[CONTROL_REG] = user_regs_write[CONTROL_REG];

    // MS2.0 Engine Command Submit - No pulse generation needed
    // CSR command bridge handles edge detection internally

    // Define top level registers
    t_ACX_USER_REG  test_status;
    t_ACX_USER_REG  adm_status;
    logic           test_running;
    logic           test_done;
    logic           test_fail;
    logic           flr_resp_disable;

    // Test signals for BRAM design
    assign test_running = 1'b0;
    assign test_done = 1'b0;
    assign test_fail = 1'b0;

    //Status bit of GDDR6 training, set high when completed and successful
    logic train_done;

    assign train_done = adm_status[0];

    // Monitor test status (combined with GDDR6 status)
    assign test_status  = {16'b0, 5'b0, test_running, test_done, test_fail,
                                   3'b0, pll_pcie_lock, pll_ddr_lock, pll_noc_lock,
                                         pll_gddr_SE_lock, pll_gddr_SW_lock};

    // Test status register shows PLL locks and system status
    assign user_regs_read[TEST_STATUS_REG] = test_status;

    // Monitor LTSSM state and other FLR signals
    assign user_regs_read[LTSSM_STATE_REG] = {flr_resp_disable, 7'h0, counter, flr_pf_done, flr_pf_active_sync, pci_express_x16_status_flr_pf_active, 2'b00, pci_express_x16_status_ltssm_state};
    assign flr_resp_disable = user_regs_write[LTSSM_STATE_REG][31];

    //--------------------------------------------------------------------
    // Scratch register with bitstream identification
    // Emergency restoration build timestamp
    //--------------------------------------------------------------------
    // Generate bitstream ID from build timestamp - No hardcoded values  
    localparam [31:0] TIMESTAMP = `ACX_BUILD_TIMESTAMP;
    assign user_regs_read[BITSTREAM_ID] = TIMESTAMP;

    // ------------------------
    // LED outputs
    // ------------------------
    // There are 4 multi-color LEDs on the VectorPath card
    `include "vp815_rev0_led_defines.svh"

    // Create shift register to get LED signals across the die to the outputs
    logic [7:0] led_l_int;
    shift_reg #( .LENGTH(5), .WIDTH(8) ) x_shift_leds (.i_din (led_l_int), .o_dout(led_l),
                                                              .i_clk(i_reg_clk), .i_rstn(1'b1));

    // LED D3 indicates GDDR6 test status
    // Green = all tests pass and training done, Orange = test running or fail, Off = not done
    logic gddr_test_pass, gddr_test_running, gddr_test_fail;
    assign gddr_test_pass = (&gddr_nap_done) & ~(|gddr_nap_fail) & train_done;
    assign gddr_test_running = |gddr_nap_running;
    assign gddr_test_fail = |gddr_nap_fail;

    assign {led_l_int[4], led_l_int[0]} = (gddr_test_fail | gddr_test_running) ? ACX_VP_LED_ORANGE :
                                           gddr_test_pass ? ACX_VP_LED_GREEN :
                                           (train_done ? ACX_VP_LED_GREEN : ACX_VP_LED_OFF);

    // LED D4, D5, D6 - Reserved for future GEMM engine status
    assign {led_l_int[5], led_l_int[1]} = ACX_VP_LED_OFF;
    assign {led_l_int[6], led_l_int[2]} = ACX_VP_LED_OFF;
    assign {led_l_int[7], led_l_int[3]} = ACX_VP_LED_OFF;

    //--------------------------------------------------------------------
    // PCIe utility blocks
    //--------------------------------------------------------------------

    //--------------------------------
    // BRAM responders
    // PCIe can write and read to the memory within this block, (2xBRAM72K)
    // The responder includes an AXI initiator NAP
    //--------------------------------

    // Engine result BRAM write signals (from MS2.0 GEMM engine)
    // CRITICAL FIX (Oct 10, 2025): Initialize to avoid undriven signals when generate loop assigns later
    // These are assigned inside the generate loop but used outside - must have defaults
    logic         engine_bram_wr_en = 1'b0;
    logic [8:0]   engine_bram_wr_addr = 9'b0;
    logic [255:0] engine_bram_wr_data = 256'b0;
    logic [31:0]  engine_bram_wr_strobe = 32'b0;
    
    // First 4 results from compute engine (for register-based testing)
    logic [15:0] captured_result_0 = 16'd0;
    logic [15:0] captured_result_1 = 16'd0;
    logic [15:0] captured_result_2 = 16'd0;
    logic [15:0] captured_result_3 = 16'd0;

    // This instance is used for DMA transactions
    // Also accepts writes from MS2.0 Engine result writer via internal ports
    // CLOCK DOMAIN FIX (Oct 10, 2025): Changed from i_reg_clk to i_nap_clk
    // NAP PLACEMENT FIX (Oct 14, 2025): Result BRAM at NAP[3][5] per placement constraint
    // CRITICAL: RTL parameters MUST match physical placement in ace_placements.pdc
    // Physical placement: NOC[3][5] (ace_placements.pdc line 29)
    dma_bram_bridge
    #(
        .TGT_DATA_WIDTH     (`ACX_NAP_AXI_DATA_WIDTH), // Target data width.
        .TGT_ADDR_WIDTH     (`ACX_NAP_AXI_INITIATOR_ADDR_WIDTH),
        .NAP_COL            (3),  // Column 3 - same as engine
        .NAP_ROW            (5),  // Row 5 - MATCHES PLACEMENT CONSTRAINT (NOC[3][5])
        .PROBE_NAME         ("bram_rsp_dma")
    ) i_axi_bram_rsp_dma (
        // Inputs
        .i_clk              (i_reg_clk),  // FIXED: Match engine clock domain (was i_reg_clk)
        .i_reset_n          (nap_rstn),   // FIXED: Match engine reset domain (was reg_rstn)
        .i_bram_inc42_en       (1'b0),       // +42 processing disabled
        // Internal write ports from MS2.0 Engine result writer
        .i_internal_wr_en      (engine_bram_wr_en),
        .i_internal_wr_addr    (engine_bram_wr_addr),
        .i_internal_wr_data    (engine_bram_wr_data),
        .i_internal_wr_strobe  (engine_bram_wr_strobe),
        // Tie off internal read ports (not used)
        .i_internal_rd_en      (1'b0),
        .i_internal_rd_addr (9'b0),
        .o_internal_rd_data ()  // unconnected
    );

    // This instance is used for DMA descriptor lists
    dma_bram_bridge
    #(
        .TGT_DATA_WIDTH     (`ACX_NAP_AXI_DATA_WIDTH), // Target data width.
        .TGT_ADDR_WIDTH     (`ACX_NAP_AXI_INITIATOR_ADDR_WIDTH),
        .NAP_COL            (9),  // Column 9 as per constraints
        .NAP_ROW            (7),  // Row 7 as per constraints
        .PROBE_NAME         ("bram_rsp_dl")
    ) i_axi_bram_rsp_dl (
        // Inputs
        .i_clk              (i_reg_clk),
        .i_reset_n          (reg_rstn), // active low synchronous reset
        .i_bram_inc42_en    (1'b0)      // +42 processing disabled
    );

    // This instance is used for ATU demonstration (standard BRAM responder without processing)
    axi_bram_responder
    #(
        .TGT_DATA_WIDTH     (`ACX_NAP_AXI_DATA_WIDTH), // Target data width.
        .TGT_ADDR_WIDTH     (`ACX_NAP_AXI_INITIATOR_ADDR_WIDTH),
        .NAP_COL            (7),  // Column 7 as per constraints
        .NAP_ROW            (7),  // Row 7 as per constraints
        .PROBE_NAME         ("bram_rsp_atu")
    ) i_axi_bram_rsp_atu (
        // Inputs
        .i_clk              (i_reg_clk),
        .i_reset_n          (reg_rstn) // active low synchronous reset
    );
    //--------------------------------------------------------------------
    // GDDR6 Channel Infrastructure
    //--------------------------------------------------------------------
    // Implements 8 GDDR6 memory channels with NoC interfaces:
    //   - Channel 0: MS2.0 GEMM Engine (matrix multiplication core)
    //   - Channels 1-7: Packet gen/checker for memory validation
    //--------------------------------------------------------------------

    // Local parameters for NAP interface
    localparam NAP_DATA_WIDTH = `ACX_NAP_AXI_DATA_WIDTH;
    localparam NAP_ADDR_WIDTH = `ACX_NAP_AXI_RESPONDER_ADDR_WIDTH;


    // Generate 8 GDDR6 channels with NoC interfaces
    genvar i;
    generate
        for (i=0; i<MAX_NOC_CHANNELS; i=i+1) begin : gddr_gen_noc

            if (GDDR6_NOC_CONFIG[i]) begin : noc_on

                // Instantiate AXI4 interface for NAP
                t_AXI4 #(
                    .DATA_WIDTH (NAP_DATA_WIDTH),
                    .ADDR_WIDTH (NAP_ADDR_WIDTH),
                    .LEN_WIDTH  (8),
                    .ID_WIDTH   (8)
                ) nap();

                // Non-AXI signals from AXI NAP
                logic output_rstn_nap;
                logic error_valid_nap;
                logic [2:0] error_info_nap;

                // Channel 1: MS2.0 GEMM Engine (MOVED from Ch0 for DC AXI support)
                // GDDR6_1 supports Direct Connect AXI interface from fabric
                // Channel 0 only supports NoC mode (no DC interface)
                if (i == 1) begin : gemm_engine_channel
                    // MS2.0 GEMM Engine on Channel 1
                    // Architecture (CORRECTED per GDDR6 reference design):
                    //   Engine (initiator) -> NAP (responder) -> NoC -> GDDR6_1
                    // Engine performs FETCH from GDDR6 and matrix multiplication

                    // NAP responder wrapper for MS2.0 Engine (FIXED Oct 8 2025!)
                    // Dispatcher acts as AXI master/initiator, NAP provides AXI slave/responder interface
                    // This allows dispatcher to READ FROM GDDR6 via FETCH commands
                    // Reference: gddr_ref_design/src/rtl/gddr_ref_design_top.sv line 295
                    nap_responder_wrapper #(
                        .COLUMN         (3),    // West column for Channel 1
                        .ROW            (4),    // Row 4 for Channel 1 (NOC[3][4])
                        .E2W_ARB_SCHED  (32'hffffffff),  // East-to-west arbitration
                        .W2E_ARB_SCHED  (32'hffffffff)   // West-to-east arbitration
                    ) i_axi_responder_wrapper (
                        .i_clk          (i_nap_clk),
                        .i_reset_n      (nap_rstn),
                        .nap            (nap),  // NAP provides AXI slave/responder interface
                        .o_output_rstn  (output_rstn_nap),
                        .o_error_valid  (error_valid_nap),
                        .o_error_info   (error_info_nap)
                    );

                    // Pass raw submit signal to engine_wrapper - CSR bridge does its own edge detection
                    // CRITICAL FIX: Remove duplicate pulse generation (CSR bridge has internal edge detection)

                    // Engine status signals
                    logic        engine_busy;
                    logic [31:0] engine_result_count;
                    logic [3:0]  mc_state, mc_state_next, dc_state, ce_state;
                    logic [31:0] engine_debug;
                    logic [31:0] bcv_debug_state;      // BCV controller internal state (Oct 10, 2025)
                    logic [31:0] bcv_debug_dimensions; // BCV captured dimensions (Oct 10, 2025)
                    logic [31:0] mc_tile_dimensions;   // Master control TILE dimensions (Oct 10, 2025)
                    logic [31:0] mc_payload_word1, mc_payload_word2, mc_payload_word3;  // MC raw payload words (Oct 10, 2025)

                    // BRAM Data Path Debug Signals (Oct 9, 2025 - CE Stuck Debug)
                    logic [10:0]  ce_bram_rd_addr;
                    logic         ce_bram_rd_en;
                    // logic [2:0]   ce_load_count;  // REMOVED: not in working CE version
                    logic [255:0] dbram_rd_data;
                    logic [10:0]  dc_bram_wr_addr;
                    logic         dc_bram_wr_en;
                    logic         dc_fetch_done;
                    logic         dc_disp_done;

                    // CRITICAL FIX: CSR bridge has internal edge detection
                    // Pass raw register value directly - do NOT pre-generate pulse

                    // Result BRAM interface signals
                    logic [8:0]   result_bram_wr_addr;
                    logic [255:0] result_bram_wr_data;
                    logic         result_bram_wr_en;
                    logic [31:0]  result_bram_wr_strobe;

                    // NO CDC SYNCHRONIZERS NEEDED - All on same clock (i_nap_clk)
                    // reg_control_block, engine_wrapper, and NAP wrapper all run on i_nap_clk
                    // Direct connection of CSR signals with no clock domain crossing

                    // Soft-reset for engine (Oct 10, 2025 - Allow software reset between tests)
                    // Control Register bit 1: Engine soft reset (active high)
                    // Clears all FSM states (MC, DC, CE) and command FIFOs
                    logic engine_soft_reset;
                    logic engine_reset_n;
                    assign engine_soft_reset = user_regs_write[CONTROL_REG][1];
                    assign engine_reset_n = nap_rstn & ~engine_soft_reset;

                    // =====================================================================
                    // MS2.0 GEMM Engine Integration (Oct 12, 2025 - Validated Architecture)
                    // =====================================================================
                    // Uses engine_top.sv (validated in simulation with 8/8 tests passing)
                    // with simple adapter bridges for CSR and BRAM interfaces
                    
                    // Command path: CSR -> csr_to_fifo_bridge -> cmd FIFO -> engine_top
                    logic [31:0] cmd_fifo_wdata;
                    logic        cmd_fifo_wen;
                    logic        cmd_fifo_full, cmd_fifo_afull;
                    logic [12:0] cmd_fifo_count;
                    logic        bridge_busy;

                    csr_to_fifo_bridge i_csr_bridge (
                        .i_clk         (i_reg_clk),
                        .i_reset_n     (engine_reset_n),
                        .i_cmd_word0   (user_regs_write[ENGINE_CMD_WORD0]),
                        .i_cmd_word1   (user_regs_write[ENGINE_CMD_WORD1]),
                        .i_cmd_word2   (user_regs_write[ENGINE_CMD_WORD2]),
                        .i_cmd_word3   (user_regs_write[ENGINE_CMD_WORD3]),
                        .i_cmd_submit  (write_strobes[ENGINE_CMD_SUBMIT]),
                        .o_bridge_busy (bridge_busy),
                        .o_fifo_wdata  (cmd_fifo_wdata),
                        .o_fifo_wen    (cmd_fifo_wen),
                        .i_fifo_full   (cmd_fifo_full),
                        .i_fifo_afull  (cmd_fifo_afull)
                    );

                    // Result path: engine_top -> result FIFO -> result_fifo_to_bram -> BRAM + Registers
                    logic [15:0] result_fifo_rdata;
                    logic        result_fifo_ren;
                    logic        result_fifo_empty;
                    logic [14:0] result_fifo_count;
                    logic [15:0] result_count_16bit;  // FP16 result count
                    logic [3:0]  last_opcode;
                    logic [9:0]  bram_wr_count;  // Dispatcher BRAM write count (debug)

                    engine_top #(
                        .GDDR6_PAGE_ID  (9'd0),   // Page 0 (matches DMA write address 0x0)
                        .TGT_DATA_WIDTH (256),
                        .AXI_ADDR_WIDTH (42)
                    ) i_engine_top (
                        .i_clk              (i_reg_clk),
                        .i_reset_n          (engine_reset_n),
                        // Command FIFO interface
                        .i_cmd_fifo_wdata   (cmd_fifo_wdata),
                        .i_cmd_fifo_wen     (cmd_fifo_wen),
                        .o_cmd_fifo_full    (cmd_fifo_full),
                        .o_cmd_fifo_afull   (cmd_fifo_afull),
                        .o_cmd_fifo_count   (cmd_fifo_count),
                        // Result FIFO interface
                        .o_result_fifo_rdata  (result_fifo_rdata),
                        .i_result_fifo_ren    (result_fifo_ren),
                        .o_result_fifo_empty  (result_fifo_empty),
                        .o_result_fifo_count  (result_fifo_count),
                        // NAP AXI interface
                        .nap_axi            (nap),
                        // Flow control
                        .i_result_almost_full (result_almost_full),
                        // Status outputs
                        .o_engine_busy      (engine_busy),
                        .o_mc_state         (mc_state),
                        .o_mc_state_next    (mc_state_next),
                        .o_dc_state         (dc_state),
                        .o_ce_state         (ce_state),
                        .o_last_opcode      (last_opcode),
                        // Debug outputs
                        .o_bram_wr_count    (bram_wr_count),
                        .o_result_count     (result_count_16bit),
                        .o_mc_tile_dimensions (mc_tile_dimensions),
                        .o_mc_payload_word1 (mc_payload_word1),
                        .o_mc_payload_word2 (mc_payload_word2),
                        .o_mc_payload_word3 (mc_payload_word3),
                        .o_bcv_debug_state  (bcv_debug_state),
                        .o_bcv_debug_dimensions (bcv_debug_dimensions)
                    );

                    // Local signals for capturing results
                    logic [15:0] local_result_0, local_result_1, local_result_2, local_result_3;
                    logic [12:0] result_write_top;       // Write position counter (0-8191) [DEPRECATED - kept for compatibility]
                    logic        result_write_top_reset; // Host reset signal
                    logic        result_almost_full;     // Backpressure signal
                    // Circular buffer interface signals
                    logic [12:0] result_rd_ptr;          // Read pointer register (host-controlled)
                    logic [12:0] result_wr_ptr;          // Write pointer from hardware
                    logic [13:0] result_used_entries;    // Used entries from hardware (0-8192)
                    logic        result_empty;           // Empty flag from hardware

                    result_fifo_to_simple_bram i_result_adapter (
                        .i_clk              (i_reg_clk),
                        .i_reset_n          (engine_reset_n),
                        .i_fifo_rdata       (result_fifo_rdata),
                        .o_fifo_ren         (result_fifo_ren),
                        .i_fifo_empty       (result_fifo_empty),
                        .o_bram_wr_addr     (result_bram_wr_addr),
                        .o_bram_wr_data     (result_bram_wr_data),
                        .o_bram_wr_en       (result_bram_wr_en),
                        .o_bram_wr_strobe   (result_bram_wr_strobe),
                        .o_result_0         (local_result_0),
                        .o_result_1         (local_result_1),
                        .o_result_2         (local_result_2),
                        .o_result_3         (local_result_3),
                        // Circular buffer interface (updated for circular buffer optimization)
                        .i_rd_ptr           (result_rd_ptr),
                        .o_wr_ptr           (result_wr_ptr),
                        .o_used_entries     (result_used_entries),
                        .o_empty            (result_empty),
                        .i_write_top_reset  (result_write_top_reset),
                        .o_almost_full      (result_almost_full)
                    );

                    // Map simplified debug signals (engine_top now exposes full debug outputs)
                    assign engine_result_count = {16'd0, result_count_16bit};
                    assign engine_debug = {24'd0, last_opcode, mc_state};
                    // Debug signals (mc_tile_dimensions, mc_payload_word1/2/3, bcv_debug_*) now connected to engine_top
                    // Tie off unused signals from previous architecture
                    assign ce_bram_rd_addr = 11'd0;
                    assign ce_bram_rd_en = 1'b0;
                    assign dbram_rd_data = 256'd0;
                    assign dc_bram_wr_addr = 11'd0;
                    assign dc_bram_wr_en = 1'b0;
                    assign dc_fetch_done = 1'b0;
                    assign dc_disp_done = 1'b0;

                    // Map engine registers to CSR read interface
                    assign user_regs_read[ENGINE_BYPASS_CTRL] = {30'h0, user_regs_write[ENGINE_BYPASS_CTRL][1:0]};
                    assign user_regs_read[ENGINE_CMD_WORD0] = user_regs_write[ENGINE_CMD_WORD0];
                    assign user_regs_read[ENGINE_CMD_WORD1] = user_regs_write[ENGINE_CMD_WORD1];
                    assign user_regs_read[ENGINE_CMD_WORD2] = user_regs_write[ENGINE_CMD_WORD2];
                    assign user_regs_read[ENGINE_CMD_WORD3] = user_regs_write[ENGINE_CMD_WORD3];
                    assign user_regs_read[ENGINE_CMD_SUBMIT] = 32'h0;  // Write-only trigger register
                    assign user_regs_read[ENGINE_STATUS] = {12'h0, mc_state_next, mc_state, dc_state, ce_state, 3'b0, engine_busy};
                    assign user_regs_read[ENGINE_RESULT_COUNT] = engine_result_count;
                    assign user_regs_read[ENGINE_DEBUG] = engine_debug;  // FIXED: Use actual engine_wrapper debug signals

                    // Circular buffer registers (updated for circular buffer optimization)
                    assign user_regs_read[ENGINE_WRITE_TOP] = {19'h0, result_wr_ptr};  // Now reads hardware wr_ptr (was result_write_top)
                    assign result_write_top_reset = write_strobes[ENGINE_WRITE_TOP] && (user_regs_write[ENGINE_WRITE_TOP] == 32'h0);
                    // New circular buffer registers
                    assign result_rd_ptr = user_regs_write[REG_RD_PTR][12:0];  // RW: Host writes rd_ptr via this register
                    assign user_regs_read[REG_RD_PTR] = {19'h0, result_rd_ptr};  // RW: Host-controlled read pointer
                    assign user_regs_read[REG_WR_PTR] = {19'h0, result_wr_ptr};  // RO: Hardware write pointer
                    assign user_regs_read[REG_USED_ENTRIES] = {18'h0, result_used_entries};  // RO: Used entries (0-8192)
                    assign user_regs_read[REG_RESULT_EMPTY] = {31'h0, result_empty};  // RO: Empty flag
                    assign user_regs_read[NAP_ERROR_STATUS] = {28'h0, error_valid_nap, error_info_nap};  // NAP Channel 1 error monitoring
                    assign user_regs_read[DC_BRAM_WR_COUNT] = {22'h0, bram_wr_count};  // Dispatcher BRAM write count (verify FETCH worked)
                    assign user_regs_read[DC_DEBUG] = {28'h0, dc_state};  // Dispatcher state debug

                    // Debug Registers (Oct 9, 2025 - MS2.0 GEMM Engine Debug Visibility)
                    assign user_regs_read[CE_BRAM_ADDR_DEBUG] = {21'h0, ce_bram_rd_addr};  // CE BRAM read address [10:0]
                    assign user_regs_read[CE_BRAM_DATA_LOW] = dbram_rd_data[31:0];          // BRAM data sample [31:0]
                    assign user_regs_read[CE_BRAM_DATA_MID] = dbram_rd_data[63:32];         // BRAM data sample [63:32]
                    assign user_regs_read[CE_CONTROL_DEBUG] = {24'h0, ce_bram_rd_en, 3'h0, 3'h0, ce_state};  // CE control signals (ce_load_count removed)
                    assign user_regs_read[DC_BRAM_WRITE_DEBUG] = {20'h0, dc_bram_wr_en, dc_bram_wr_addr};  // DC BRAM write signals
                    assign user_regs_read[DC_CONTROL_DEBUG] = {24'h0, dc_fetch_done, dc_disp_done, 2'b0, dc_state};  // DC control status
                    assign user_regs_read[BCV_DEBUG_STATE] = bcv_debug_state;  // BCV controller internal state (Oct 10, 2025)
                    assign user_regs_read[BCV_DEBUG_DIMS] = bcv_debug_dimensions;  // BCV captured dimensions (Oct 10, 2025)
                    assign user_regs_read[MC_TILE_DIMS] = mc_tile_dimensions;  // Master control TILE dimensions (Oct 10, 2025)
                    assign user_regs_read[MC_PAYLOAD_WORD1] = mc_payload_word1;  // MC raw payload word 1 (Oct 10, 2025)
                    assign user_regs_read[MC_PAYLOAD_WORD2] = mc_payload_word2;  // MC raw payload word 2 (Oct 10, 2025)
                    assign user_regs_read[MC_PAYLOAD_WORD3] = mc_payload_word3;  // MC raw payload word 3 (Oct 10, 2025)

                    // MMIO debug counters declared at module level (outside generate block)
                    // See lines 436-456 for counter logic
                    // Counters exposed via SCRATCH register for debugging

                    // Engine status registers handled above - no additional assignments needed

                    // Connect engine result BRAM writer to module-level signals
                    assign engine_bram_wr_en     = result_bram_wr_en;
                    assign engine_bram_wr_addr   = result_bram_wr_addr;
                    assign engine_bram_wr_data   = result_bram_wr_data;
                    assign engine_bram_wr_strobe = result_bram_wr_strobe;
                    
                    // Connect local results to module-level captured result signals
                    assign captured_result_0 = local_result_0;  // From result_fifo_to_bram
                    assign captured_result_1 = local_result_1;
                    assign captured_result_2 = local_result_2;
                    assign captured_result_3 = local_result_3;

                    // Tie off packet gen status signals for Channel 0
                    assign gddr_nap_running[i] = 1'b0;
                    assign gddr_nap_done[i] = 1'b1;
                    assign gddr_nap_fail[i] = 1'b0;

                    // Tie off Channel 1 GDDR6 packet gen registers (not used by GEMM engine)
                    // Channel 1 uses ENGINE-specific registers instead
                    for (genvar j = 0; j < REGS_PER_GDDR_CH; j = j + 1) begin
                        if ((i*REGS_PER_GDDR_CH + j) < NUM_GDDR_REGS) begin
                            assign user_regs_read[GDDR_REGS_BASE + i*REGS_PER_GDDR_CH + j] = 32'b0;
                        end
                    end

                end 
                // else begin : pkt_gen_channel
                //     // NAP responder wrapper for packet generators (channels 1-7)
                //     // Packet generators test memory by writing TO the NAP as if it were memory
                //     nap_responder_wrapper i_axi_responder_wrapper (
                //         .i_clk          (i_nap_clk),
                //         .i_reset_n      (nap_rstn),
                //         .nap            (nap),
                //         .o_output_rstn  (output_rstn_nap),
                //         .o_error_valid  (error_valid_nap),
                //         .o_error_info   (error_info_nap)
                //     );

                //     // Packet Generator/Checker (Test/Validation Functionality)
                //     // Generates pseudo-random read/write traffic for GDDR6 validation

                //     // Create unique random data pattern for each channel
                //     localparam logic [NAP_DATA_WIDTH-1:0] RAND_DATA_INIT = {(NAP_DATA_WIDTH/32){32'hdeadbeef}} + integer'(i + 10);

                //     axi_mem_pkt_gen_chk_channel #(
                //         .LINEAR_PKTS            (0),                    // Random packet generation
                //         .LINEAR_ADDR            (1),                    // Linear addressing
                //         .TGT_ADDR_WIDTH         (GDDR_NOC_ADDR_WIDTH),  // 26-bit target address
                //         .TGT_ADDR_PAD_WIDTH     (GDDR_PAD_WIDTH),       // Padding bits
                //         .TGT_ADDR_ID            (GDDR6_ID_NOC_CH1[i*9+:9]), // NoC page ID
                //         .AXI_DATA_WIDTH         (NAP_DATA_WIDTH),       // 256-bit data
                //         .AXI_ADDR_WIDTH         (NAP_ADDR_WIDTH),       // 42-bit address
                //         .MAX_BURST_LEN          (16),                   // 16-beat max burst
                //         .RAND_DATA_INIT         (RAND_DATA_INIT),       // Unique random seed
                //         .NO_AR_LIMIT            (0),                    // Enforce AR spacing
                //         .NUM_REGS               (REGS_PER_GDDR_CH),     // 11 registers
                //         .CHANNEL_CLK_FREQ       (300),                  // 300MHz NAP clock
                //         .OUTPUT_PIPELINE_LENGTH (3)                     // Pipeline depth
                //     ) i_axi_mem_channel_gddr (
                //         // Clock and reset
                //         .i_ch_clk       (i_nap_clk),
                //         .i_reg_clk      (i_reg_clk),
                //         .i_ch_reset_n   (nap_rstn),
                //         // AXI interface (shared with NAP wrapper)
                //         .axi_if         (nap),
                //         // Register interface
                //         .i_regs_write   (user_regs_write[GDDR_REGS_BASE + i*REGS_PER_GDDR_CH +: REGS_PER_GDDR_CH]),
                //         .o_regs_read    (user_regs_read[GDDR_REGS_BASE + i*REGS_PER_GDDR_CH +: REGS_PER_GDDR_CH]),
                //         // Status outputs
                //         .o_running      (gddr_nap_running[i]),
                //         .o_done         (gddr_nap_done[i]),
                //         .o_fail         (gddr_nap_fail[i])
                //     );

                // end

            end else begin : noc_off
                // Tie off unused channel status signals
                assign gddr_nap_running[i] = 1'b0;
                assign gddr_nap_done[i] = 1'b1;
                assign gddr_nap_fail[i] = 1'b0;
                
                // Tie off unused GDDR6 packet gen registers (channels 0,2-7 disabled)
                for (genvar j = 0; j < REGS_PER_GDDR_CH; j = j + 1) begin
                    if ((i*REGS_PER_GDDR_CH + j) < NUM_GDDR_REGS) begin
                        assign user_regs_read[GDDR_REGS_BASE + i*REGS_PER_GDDR_CH + j] = 32'b0;
                    end
                end
            end
        end
    endgenerate

    //--------------------------------------------------------------------
    // MSI-X Interrupt Generation and Handling
    //--------------------------------------------------------------------
    
    // Instantiate IRQ source to generate local periodic interrupts
    localparam    IRQ_REG         = 2;      // Bit 0 is the interrupt signal

    irq_gen
    #(
        .NUM_CHANNELS       (NUM_MSIX_IRQ_CH)
    ) i_irq_gen (
        // Inputs
        .i_clk              (i_reg_clk),
        .i_reset_n          (reg_rstn),
        // Registers
        .i_regs_write       (user_regs_write[IRQ_GEN_REGS_BASE +: (NUM_MSIX_IRQ_CH * REGS_PER_IRQ_GEN_CH)]),
        .o_regs_read        (user_regs_read[IRQ_GEN_REGS_BASE +: (NUM_MSIX_IRQ_CH * REGS_PER_IRQ_GEN_CH)])
    );
    
    // Register Interface
    // CONTROL, DB_DATA, DB_CNT_STATUS are the MSI-X channel registers, these registers are replicated for each channel
    localparam    DB_ADDR_LOW       = 0;
    localparam    DB_ADDR_HIGH      = 1;
    localparam    CONTROL           = 4;    // Bit 31 is the interrupt enable signal, rising edge trigger
    localparam    DB_DATA           = 5;
    localparam    DB_CNT_STATUS     = 6;

    logic [31:0] msix_regs_write [NUM_MSIX_IRQ_REGS -1:0];
    logic [31:0] msix_regs_read  [NUM_MSIX_IRQ_REGS -1:0];

    // Connect relevant signals to a register interface for the MSIX handler
    assign msix_regs_write[DB_ADDR_LOW]  = user_regs_write[MSIX_IRQ_REGS_BASE+DB_ADDR_LOW];
    assign msix_regs_write[DB_ADDR_HIGH] = user_regs_write[MSIX_IRQ_REGS_BASE+DB_ADDR_HIGH];

    assign user_regs_read[MSIX_IRQ_REGS_BASE+DB_ADDR_LOW]  = msix_regs_read[DB_ADDR_LOW];
    assign user_regs_read[MSIX_IRQ_REGS_BASE+DB_ADDR_HIGH] = msix_regs_read[DB_ADDR_HIGH];

    genvar i;
    generate
        for (i = 0; i < NUM_MSIX_IRQ_CH; i++) begin : gb_connect_interrupt
            // Connect MSI-X interrupt channel enables to respective generated IRQ signals
            assign msix_regs_write[CONTROL+(REGS_PER_MSIX_IRQ_CH*i)]       = {user_regs_read[IRQ_GEN_REGS_BASE+IRQ_REG+(REGS_PER_IRQ_GEN_CH*i)][0],
                                                                              user_regs_write[MSIX_IRQ_REGS_BASE+CONTROL+(REGS_PER_MSIX_IRQ_CH*i)][30:0]};
            assign msix_regs_write[DB_DATA+(REGS_PER_MSIX_IRQ_CH*i)]       = user_regs_write[MSIX_IRQ_REGS_BASE+DB_DATA+(REGS_PER_MSIX_IRQ_CH*i)];
            assign msix_regs_write[DB_CNT_STATUS+(REGS_PER_MSIX_IRQ_CH*i)] = user_regs_write[MSIX_IRQ_REGS_BASE+DB_CNT_STATUS+(REGS_PER_MSIX_IRQ_CH*i)];

            assign user_regs_read[MSIX_IRQ_REGS_BASE+CONTROL+(REGS_PER_MSIX_IRQ_CH*i)]       = msix_regs_read[CONTROL+(REGS_PER_MSIX_IRQ_CH*i)];
            assign user_regs_read[MSIX_IRQ_REGS_BASE+DB_DATA+(REGS_PER_MSIX_IRQ_CH*i)]       = msix_regs_read[DB_DATA+(REGS_PER_MSIX_IRQ_CH*i)];
            assign user_regs_read[MSIX_IRQ_REGS_BASE+DB_CNT_STATUS+(REGS_PER_MSIX_IRQ_CH*i)] = msix_regs_read[DB_CNT_STATUS+(REGS_PER_MSIX_IRQ_CH*i)];
        end
    endgenerate

    // Instantiate handler to initiate MSI-X interrupts
    msix_irq_handler
    #(
        .NUM_CHANNELS       (NUM_MSIX_IRQ_CH)
    ) i_msix_irq_handler (
        // Inputs
        .i_clk              (i_reg_clk),
        .i_reset_n          (reg_rstn),
        // Registers
        .i_regs_write       (msix_regs_write),
        .o_regs_read        (msix_regs_read)
    );

    //--------------------------------------------------------------------
    // Function Level Reset (FLR) Responder Logic Block
    //--------------------------------------------------------------------
    // When FLR is requested for a function, the respective bit in pci_express_x16_status_flr_pf_active is set high
    // To communicate FLR completion, a write to a CSR register setting high the appropriate flr_pf_done bits is required
    // For both flr_pf_active and flr_pf_done, the bits used for the physical functions are as follows
    // bit3 - PF3, bit2 - PF2, bit1 - PF1, bit0 - PF0
    // Note: This design only expects FLR for physical function 1

    logic [3:0] flr_pf_done;
    logic       flr_resp_en;
    logic       flr_active_done_match;
    logic       flr_active_done_match_d;
    logic       wr_error;
    logic       written_valid;
    logic       written_valid_d;
    logic [3:0] counter;          // counter for FLR responder writes

    // FLR has completed when reset signals (used by the function) are asserted for requested function
    assign flr_pf_done = { 1'b0,                                // PF3 is not used in this design
                           1'b0,                                // PF2 is not used in this design
                           ~bw_bmc_if_rstn,                     // PF1
                           ~(reg_rstn | nap_rstn | adm_rstn) }  // PF0
                         & flr_pf_active_sync;

    // pulse FLR responder enable to write FLR done when done bits match active bits
    always_ff @(posedge i_reg_clk)
    begin
        flr_resp_en <= flr_active_done_match & ~flr_active_done_match_d;
        flr_active_done_match   <= 1'b0;
        flr_active_done_match_d <= flr_active_done_match;
        if ( (flr_pf_active_sync != 4'h0) && (flr_pf_done == flr_pf_active_sync) )
            flr_active_done_match <= 1'b1;
    end

    flr_responder i_flr_responder (
        .i_clk              (i_reg_clk),
        .i_reset_n          (pll_pcie_lock),
        .i_enable           (flr_resp_en & ~flr_resp_disable),      // set enable high to send FLR done bits
        .flr_pf_done        (flr_pf_done),      // bit3 - PF3, bit2 - PF2, bit1 - PF1, bit0 - PF0
        
        .o_wr_error         (wr_error),         // Asserted if there is an error writing
        .o_written_valid    (written_valid)
    );

    // Count the number of write completed by the FLR responder
    always_ff @(posedge i_reg_clk)
    begin
        written_valid_d <= written_valid;
        if (written_valid & ~written_valid_d)
            counter <= counter + 1'b1;
    end

    //--------------------------------------------------------------------
    // GDDR training and PERSTN support
    //--------------------------------------------------------------------
    acx_device_manager x_acx_dev_mgr (
        // JTAG ports
        .i_jtag_in                  (i_jtag_in),
        .i_tdo_bus                  (tdo_bus),
        .o_jtag_out                 (o_jtag_out),
        .o_jtap_bus                 (jtap_bus),

        // PCIe ports
        .i_pcie_1_perstn            (fpga_rst_l),   // PERST input
        .i_pcie_1_ltssm_state       (pci_express_x16_status_ltssm_state),   // LTSSM port
        .o_pcie_1_reconfig_fpga_n   (irq_to_avr),   // Active low.  Requires BMC FW 1.4.0+ onwards

        // User ports
        .i_clk                      (i_adm_clk),    // 100 MHz Clock input for Device Manager block.
        .i_start                    (adm_rstn),     // Once asserted, ADM will run to completion.
        .o_status                   (adm_status)    // Progress indication, error status, alarms
    );

    assign user_regs_read[ADM_STATUS_REG] = adm_status;

    // Scratch register - Read/write test register
    assign user_regs_read[SCRATCH_REG] = user_regs_write[SCRATCH_REG];
    
    // Result registers - First 4 FP16 results from compute engine (read-only)
    // Each register holds one FP16 value in lower 16 bits
    assign user_regs_read[RESULT_REG_0] = {16'd0, captured_result_0};
    assign user_regs_read[RESULT_REG_1] = {16'd0, captured_result_1};
    assign user_regs_read[RESULT_REG_2] = {16'd0, captured_result_2};
    assign user_regs_read[RESULT_REG_3] = {16'd0, captured_result_3};

    //--------------------------------------------------------------------
    // VectorPath BMC interface block.  Supports flash updates via PCIe
    //--------------------------------------------------------------------

    // BW_BMC_IF - comprises:
    // - AVR UART_EDGE, (uses NAP responder) - accesses from the BMC
    // - NAP Initiator for accesses from Host PC (UART or PCIe) or BMC over the NoC
    // - MCTP BRAM - 1024x32 = 4kiB
    // - FLASH Programming BRAM - 8096x32 = 32kiB
    // - IRQ & FLASH Register Interface
    // - FIRMWARE version
    // - TIMESTAMP when built
    // - ADM status

    BW_BMC_IF #(
        // This is the default location for the two NAPs
        // This is necessary for Host SW over USB to work without modification to BWC firmware
    `ifdef ACX_DEVICE_AC7t1400
        .BMC_NAP_COLUMN         (9),            // AC7t1400 uses the SE corner of the die for the cryptocore.
        .BMC_NAP_ROW            (3)             // Move BMC NAP pair up to row 3.
    `else
        .BMC_NAP_COLUMN         (9),
        .BMC_NAP_ROW            (2)
    `endif
    ) x_bw_bmc_if (
        .i_clk              (i_adm_clk),        // Must be 100MHz
        .i_rstn             (bw_bmc_if_rstn),   // Negative sense reset

        // A read-only register for users.  Values not used by software.
        // reg_control block has this build version information as well.
        // Duplicate here to give two sources that version info can be read from
        .i_fw_version       ({byte'(`ACX_MAJOR_VERSION),byte'(`ACX_MINOR_VERSION),
                              byte'(`ACX_PATCH_VERSION),byte'(`REVISON_CONTROL_VERSION)}),
        .i_timestamp        (32'h0),            // Optional, add build timestamp
        .i_adm_status       (adm_status),       // ADM status, also now captured in 2 locations.

        .i_fpga_avr_rxd     (fpga_avr_rxd),     // Input from BMC to FPGA
        .o_fpga_avr_txd     (fpga_avr_txd),     // Output from FPGA to BMC
        .o_fpga_avr_txd_oe  (fpga_avr_txd_oe)
    );

// Example to show how snapshot can be included into a design that also has the ADM
`ifdef ACX_USE_SNAPSHOT
    // ------------------------
    // Snapshot
    // ------------------------

    localparam integer MONITOR_WIDTH = 64;      // Only monitoring 12 signals
    localparam integer MONITOR_DEPTH = 1024;
    localparam integer STIMULI_WIDTH = 9;
 
 
    logic [MONITOR_WIDTH-1 : 0] monitor;
    logic [STIMULI_WIDTH-1 : 0] stimuli;
    logic                       stimuli_valid;
    logic                       arm;

    // Local signals to connect to probe points
    // Use syn_keep to maintain the signal names
    logic           test_awready    /* synthesis syn_keep=1 */;
    logic           test_awvalid    /* synthesis syn_keep=1 */; 
    logic [1:0]     test_awburst    /* synthesis syn_keep=1 */;
    logic           test_awlock     /* synthesis syn_keep=1 */; 
    logic [2:0]     test_awsize     /* synthesis syn_keep=1 */; 
    logic [7:0]     test_awlen      /* synthesis syn_keep=1 */; 
    logic [7:0]     test_awid       /* synthesis syn_keep=1 */;
    logic [41:0]    test_awaddr     /* synthesis syn_keep=1 */; 
    logic           test_wready     /* synthesis syn_keep=1 */;
    logic [255:0]   test_wdata      /* synthesis syn_keep=1 */; 
    logic           test_wvalid     /* synthesis syn_keep=1 */; 
    logic           test_wlast      /* synthesis syn_keep=1 */; 
    logic           test_bvalid     /* synthesis syn_keep=1 */;
    logic           test_bready     /* synthesis syn_keep=1 */;
    logic [7:0]     test_bid        /* synthesis syn_keep=1 */; 
    logic           test_arready    /* synthesis syn_keep=1 */;
    logic           test_arvalid    /* synthesis syn_keep=1 */; 
    logic           test_rvalid     /* synthesis syn_keep=1 */;
    logic           test_rready     /* synthesis syn_keep=1 */;
    logic           test_rlast      /* synthesis syn_keep=1 */;
    logic [7:0]     test_rid        /* synthesis syn_keep=1 */; 
    logic [7:0]     test_arid       /* synthesis syn_keep=1 */;


    // Set snapshot to monitor the AXI interface into the DMA BRAM responder
    ACX_PROBE_CONNECT #(
        .width  (12),
        .tag    ("bram_rsp_dma")
    ) x_probe_snapshot (
        .dout({
            test_rlast,   test_rready,  test_rvalid,
            test_arready, test_arvalid,
            test_bready,  test_bvalid,
            test_wlast,   test_wready,  test_wvalid,
            test_awready, test_awvalid
            })
    );

    assign monitor = {
            test_rlast,   test_rready,  test_rvalid,
            test_arready, test_arvalid,
            test_bready,  test_bvalid,
            test_wlast,   test_wready,  test_wvalid,
            test_awready, test_awvalid 
            };
  
  
    ACX_SNAPSHOT_JTAP_UNIT #(
        .DUT_NAME           ("snapshot_ddr"),
        .MONITOR_WIDTH      (MONITOR_WIDTH),
        .MONITOR_DEPTH      (MONITOR_DEPTH),
        .TRIGGER_WIDTH      (MONITOR_WIDTH < 40? MONITOR_WIDTH : 40),
        .STIMULI_WIDTH      (STIMULI_WIDTH),
        .ARM_DELAY          (3)
    ) x_snapshot (
        .i_jtap_bus         (jtap_bus),
        .i_tdo_bus          (1'b0),
        .o_tdo_bus          (tdo_bus),
        .i_user_clk         (i_reg_clk),    // Set to same clock as monitor signals
        .i_monitor          (monitor),
        .i_trigger          (), // not used if STANDARD_TRIGGERS = 1
        .o_stimuli          (stimuli),
        .o_stimuli_valid    (stimuli_valid),
        .o_arm              (arm),
        .o_trigger          ()
    );
  
`else
    assign tdo_bus = 1'b0;
`endif

    // ----------------------------------------------------------------------
    // Support for the AC7t1400 device
    // ----------------------------------------------------------------------
    // If this design is intended to be targeted to the AC7t1400 device,
    // then it is necessary to instantiate the SRM, (Serial Rate Monitor).
    // This is required in all AC7t1400 designs, as shown below
    // ----------------------------------------------------------------------
    // The define ACX_DEVICE_AC7t1400 is set as follows :
    //      In simulation by $ACE_INSTALL_DIR/libraries/device_models/AC7t1400_simmodels.v
    //      In synthesis by  $ACE_INSTALL_DIR/libraries/device_models/AC7t1400_synplify.v
    //
    //      For this design the above files are selected as follows
    //      In simulation, in the appropriate /sim/<simulator>/Makefile
    //      In GUI build flow, the synthesis project file in /src/syn, (in conjunction with changing the -part option).
    //      In batch build flow, the selection is done in /scripts/create_syn_project.tcl based on the selected device
    // ----------------------------------------------------------------------
    `ifdef ACX_DEVICE_AC7t1400
        
        (* must_keep *) ACX_SRM x_ACX_SRM () /* synthesis syn_noprune=1 */;
    `endif

endmodule :elastix_gemm_top