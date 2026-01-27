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
    localparam      DMA_CMD_CNT            = 15;                // DMA command count (number of commands in BRAM) - 0x3C
    localparam      DMA_CMD_VALID          = 16;                // DMA command valid (host writes 1 to start) - 0x40
    localparam      DMA_CMD_RD_ADDR        = 17;                // DMA command read address (debug, read-only) - 0x44
    localparam      DMA_CMD_RESERVED       = 18;                // Reserved - 0x48
    localparam      ENGINE_CMD_SUBMIT      = 19;                // Submit trigger (legacy, may be removed) - 0x4C
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
        .i_clk                  (i_reg_clk),
        .i_reset_n              (reg_rstn),
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

    // Engine result BRAM write signals (from 2D GEMM engine)
    // Assigned directly from engine_top_2d outputs
    logic         engine_bram_wr_en;
    logic [8:0]   engine_bram_wr_addr;
    logic [255:0] engine_bram_wr_data;
    logic [31:0]  engine_bram_wr_strobe;
    
    // =========================================================================
    // Pipeline Probe Signals (LEGACY - from single-row engine_top)
    // =========================================================================
    // NOTE: These are not driven by engine_top_2d - kept for compatibility
    // with existing register interface. Values will remain at 0.
    logic [15:0] probe_disp_data = 16'd0;
    logic        probe_disp_valid = 1'b0;
    logic [15:0] probe_rowbram_data = 16'd0;
    logic        probe_rowbram_valid = 1'b0;
    logic [23:0] probe_fp24_data = 24'd0;
    logic        probe_fp24_valid = 1'b0;
    logic [15:0] probe_fp16_data = 16'd0;
    logic        probe_fp16_valid = 1'b0;

    // =========================================================================
    // Probe Capture Registers (LEGACY - values will remain at 0)
    // =========================================================================
    logic [15:0] captured_probe_0 = 16'd0;
    logic [15:0] captured_probe_1 = 16'd0;
    logic [23:0] captured_probe_2 = 24'd0;
    logic [15:0] captured_probe_3 = 16'd0;

    always_ff @(posedge i_reg_clk or negedge reg_rstn) begin
        if (!reg_rstn) begin
            captured_probe_0 <= 16'd0;
            captured_probe_1 <= 16'd0;
            captured_probe_2 <= 24'd0;
            captured_probe_3 <= 16'd0;
        end else begin
            if (probe_disp_valid)    captured_probe_0 <= probe_disp_data;
            if (probe_rowbram_valid) captured_probe_1 <= probe_rowbram_data;
            if (probe_fp24_valid)    captured_probe_2 <= probe_fp24_data;
            if (probe_fp16_valid)    captured_probe_3 <= probe_fp16_data;
        end
    end

    // DMA Data Out BRAM - Result buffer for host DMA read-back
    // CRITICAL: RTL parameters MUST match physical placement in ace_placements.pdc
    // Physical placement: NOC[3][5]
    dma_bram_bridge
    #(
        .TGT_DATA_WIDTH     (`ACX_NAP_AXI_DATA_WIDTH),
        .TGT_ADDR_WIDTH     (`ACX_NAP_AXI_INITIATOR_ADDR_WIDTH),
        .NAP_COL            (3),
        .NAP_ROW            (5),
        .PROBE_NAME         ("dma_data_out_bram")
    ) i_dma_data_out_bram (
        .i_clk              (i_reg_clk),
        .i_reset_n          (reg_rstn),
        // Internal write ports from engine result writer
        .i_internal_wr_en      (engine_bram_wr_en),
        .i_internal_wr_addr    (engine_bram_wr_addr),
        .i_internal_wr_data    (engine_bram_wr_data),
        .i_internal_wr_strobe  (engine_bram_wr_strobe),
        // Internal read ports (not used)
        .i_internal_rd_en      (1'b0),
        .i_internal_rd_addr    (9'b0),
        .o_internal_rd_data    ()
    );

    // DMA Command In BRAM - Command buffer for host DMA write, engine read
    // CRITICAL: RTL parameters MUST match physical placement in ace_placements.pdc
    // Physical placement: NOC[3][6]
    dma_bram_bridge
    #(
        .TGT_DATA_WIDTH     (`ACX_NAP_AXI_DATA_WIDTH),
        .TGT_ADDR_WIDTH     (`ACX_NAP_AXI_INITIATOR_ADDR_WIDTH),
        .NAP_COL            (3),
        .NAP_ROW            (6),
        .PROBE_NAME         ("dma_cmd_in_bram")
    ) i_dma_cmd_in_bram (
        .i_clk              (i_reg_clk),
        .i_reset_n          (reg_rstn),
        // Internal write ports (not used - host writes via DMA)
        .i_internal_wr_en      (1'b0),
        .i_internal_wr_addr    (9'b0),
        .i_internal_wr_data    (256'b0),
        .i_internal_wr_strobe  (32'b0),
        // Internal read ports - connected to cmd_bram_fifo_bridge
        .i_internal_rd_en      (cmd_bram_rd_en),
        .i_internal_rd_addr    (cmd_bram_rd_addr),
        .o_internal_rd_data    (cmd_bram_rd_data)
    );

    // NOTE: cmd_bram_fifo_bridge has been moved inside engine_top_2d
    // The engine now directly reads from the external BRAM and handles the
    // BRAM-to-FIFO bridging internally, simplifying this top-level module.

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
        // Internal ports (not used - tied off)
        .i_internal_rd_en   (1'b0),
        .i_internal_rd_addr (9'b0),
        .o_internal_rd_data (),
        .i_internal_wr_en   (1'b0),
        .i_internal_wr_addr (9'b0),
        .i_internal_wr_data (256'b0),
        .i_internal_wr_strobe(32'b0)
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
    // 2D Multi-Row GEMM Engine Infrastructure
    //--------------------------------------------------------------------
    // Implements 16 GDDR6 channels with NoC interfaces for 2D GEMM array:
    //   - 16 NAP responders (one per GDDR6 channel/row)
    //   - engine_top_2d with 16 AXI initiator interfaces
    //   - Result adapter with internal FIFO -> BRAM write interface
    //--------------------------------------------------------------------

    // Local parameters for NAP interface
    localparam NAP_DATA_WIDTH = `ACX_NAP_AXI_DATA_WIDTH;
    localparam NAP_ADDR_WIDTH = `ACX_NAP_AXI_RESPONDER_ADDR_WIDTH;
    localparam NUM_ROWS_2D = 16;  // 16 rows in 2D array

    // NAP placement mapping arrays (column/row per GDDR6 channel)
    // -------------------------------------------------------------------------
    // OPTIMIZATION: Place NAPs closest to target GDDR controllers for lowest latency
    //   - West side (rows 0-7): NOC column 1 (closest to west-edge GDDR0-3)
    //   - East side (rows 8-15): NOC column 10 (closest to east-edge GDDR4-7)
    //
    // Reference: GDDR6_NAP_GUIDE.md, Section "Physical Layout":
    //   "Columns 1-5: West side of device (closer to GDDR0-3)"
    //   "Columns 6-10: East side of device (closer to GDDR4-7)"
    //
    // Reference: Speedster7t GDDR6 Reference Design Guide (RD017):
    //   "NAP locations should be chosen to be adjacent to the target GDDR6 subsystem"
    //
    // NOTE: NoC rows 9-10 do not exist on device - valid range is 1-8
    // -------------------------------------------------------------------------
    localparam int NAP_COL [0:15] = '{1, 1, 1, 1, 1, 1, 1, 1, 10, 10, 10, 10, 10, 10, 10, 10};
    localparam int NAP_ROW [0:15] = '{1, 2, 3, 4, 5, 6, 7, 8, 1, 2, 3, 4, 5, 6, 7, 8};


    // =====================================================================
    // 16 AXI Interface Array for 2D GEMM Engine
    // =====================================================================
    // Declare interface array at module level for engine_top_2d connection
    t_AXI4 #(
        .DATA_WIDTH (NAP_DATA_WIDTH),
        .ADDR_WIDTH (NAP_ADDR_WIDTH),
        .LEN_WIDTH  (8),
        .ID_WIDTH   (8)
    ) gddr_nap_if [NUM_ROWS_2D-1:0] ();

    // =====================================================================
    // 16 NAP Responders for 2D GEMM Engine (one per row/GDDR6 channel)
    // =====================================================================
    generate
        for (genvar r = 0; r < NUM_ROWS_2D; r++) begin : gen_gddr_nap
            // Non-AXI signals from NAP
            logic output_rstn_nap;
            logic error_valid_nap;
            logic [2:0] error_info_nap;

            // NAP responder wrapper - placement determined by ace_placements.pdc
            nap_responder_wrapper #(
                .COLUMN         (NAP_COL[r]),
                .ROW            (NAP_ROW[r]),
                .E2W_ARB_SCHED  (32'hffffffff),
                .W2E_ARB_SCHED  (32'hffffffff)
            ) i_nap_responder (
                .i_clk          (i_nap_clk),
                .i_reset_n      (nap_rstn),
                .nap            (gddr_nap_if[r]),
                .o_output_rstn  (output_rstn_nap),
                .o_error_valid  (error_valid_nap),
                .o_error_info   (error_info_nap)
            );
        end
    endgenerate

    // =====================================================================
    // 2D GEMM Engine Instance
    // =====================================================================
    // Engine status signals
    logic        engine_busy;
    logic [3:0]  mc_state_2d, rc_state_2d;

    // Debug signals from engine_top_2d
    logic [15:0] dbg_ce_ack_matmul;      // Per-row CE ACK bits (captured in MC)
    logic [15:0] dbg_dc_ack_fetch;       // Per-row DC ACK bits (captured in MC)
    logic        dbg_cmd_valid;          // MC has valid command
    logic        dbg_matmul_en_pulse;    // MATMUL enable pulse
    logic [3:0]  dbg_ce_state_row0;      // CE state for row 0
    logic [3:0]  dbg_dc_state_row0;      // DC state for row 0

    // Soft-reset for engine
    logic engine_soft_reset;
    logic engine_rstn;
    assign engine_soft_reset = user_regs_write[CONTROL_REG][1];
    assign engine_rstn = reg_rstn & ~engine_soft_reset;

    // Command BRAM-to-engine interface signals
    // BRAM read interface (engine reads from dma_cmd_in_bram)
    logic        cmd_bram_rd_en;
    logic [8:0]  cmd_bram_rd_addr;
    logic [255:0] cmd_bram_rd_data;

    // Command control signals (from engine bridge)
    logic        cmd_bram_bridge_busy;
    logic        cmd_valid_clr;
    logic [12:0] cmd_fifo_count;  // Internal FIFO count from engine (debug)

    // DMA_CMD_VALID register with auto-clear support
    logic        dma_cmd_valid_reg;
    always_ff @(posedge i_reg_clk) begin
        if (~reg_rstn) begin
            dma_cmd_valid_reg <= 1'b0;
        end else if (cmd_valid_clr) begin
            // Bridge finished - auto-clear
            dma_cmd_valid_reg <= 1'b0;
        end else if (write_strobes[DMA_CMD_VALID]) begin
            // Host write
            dma_cmd_valid_reg <= user_regs_write[DMA_CMD_VALID][0];
        end
    end


    // BRAM write interface from engine (connected to dma_bram_bridge)
    logic         engine_2d_bram_wr_en;
    logic [8:0]   engine_2d_bram_wr_addr;
    logic [255:0] engine_2d_bram_wr_data;
    logic [31:0]  engine_2d_bram_wr_strobe;

    // 2D GEMM Engine with 16 AXI interfaces
    // Note: Interface arrays require individual connections for each element
    localparam int ENGINE_NUM_MLPS = 2;
    localparam int ENGINE_NUM_COLS = ENGINE_NUM_MLPS * 2;  // 4 columns

    engine_top_2d #(
        .NUM_MLPS     (ENGINE_NUM_MLPS),
        .STACK_DEPTH  (4),
        .NUM_ROWS     (NUM_ROWS_2D),
        .NUM_COLS     (ENGINE_NUM_COLS),
        .MAN_WIDTH    (256),
        .EXP_WIDTH    (8),
        .BRAM_DEPTH   (512)
    ) i_engine_top_2d (
        .i_clk              (i_reg_clk),
        .i_reset_n          (engine_rstn),

        // Command BRAM Read Interface (direct to dma_cmd_in_bram)
        .i_cmd_bram_rd_data (cmd_bram_rd_data),
        .o_cmd_bram_rd_en   (cmd_bram_rd_en),
        .o_cmd_bram_rd_addr (cmd_bram_rd_addr),

        // Command Control Interface (from host registers)
        .i_cmd_cnt          (user_regs_write[DMA_CMD_CNT]),
        .i_cmd_valid        (dma_cmd_valid_reg),
        .o_cmd_valid_clr    (cmd_valid_clr),
        .o_cmd_bridge_busy  (cmd_bram_bridge_busy),
        .o_cmd_fifo_count   (cmd_fifo_count),

        // 16 AXI interfaces to NAPs
        .axi_ddr_if         (gddr_nap_if),

        // BRAM Write Interface (direct to dma_bram_bridge)
        .o_bram_wr_en       (engine_2d_bram_wr_en),
        .o_bram_wr_addr     (engine_2d_bram_wr_addr),
        .o_bram_wr_data     (engine_2d_bram_wr_data),
        .o_bram_wr_strobe   (engine_2d_bram_wr_strobe),

        // Status outputs
        .o_engine_busy      (engine_busy),
        .o_mc_state         (mc_state_2d),
        .o_rc_state         (rc_state_2d),

        // Debug outputs
        .o_dbg_ce_ack_matmul    (dbg_ce_ack_matmul),
        .o_dbg_dc_ack_fetch     (dbg_dc_ack_fetch),
        .o_dbg_cmd_valid        (dbg_cmd_valid),
        .o_dbg_matmul_en_pulse  (dbg_matmul_en_pulse),
        .o_dbg_ce_state_row0    (dbg_ce_state_row0),
        .o_dbg_dc_state_row0    (dbg_dc_state_row0)
    );

    // Connect engine BRAM writer to module-level signals
    assign engine_bram_wr_en     = engine_2d_bram_wr_en;
    assign engine_bram_wr_addr   = engine_2d_bram_wr_addr;
    assign engine_bram_wr_data   = engine_2d_bram_wr_data;
    assign engine_bram_wr_strobe = engine_2d_bram_wr_strobe;

    // =====================================================================
    // CSR Register Mappings for 2D Engine
    // =====================================================================
    // Engine command registers (read-back)
    assign user_regs_read[ENGINE_BYPASS_CTRL] = {30'h0, user_regs_write[ENGINE_BYPASS_CTRL][1:0]};
    // DMA Command registers
    assign user_regs_read[DMA_CMD_CNT] = user_regs_write[DMA_CMD_CNT];  // Read-back count
    assign user_regs_read[DMA_CMD_VALID] = {31'h0, dma_cmd_valid_reg};  // Current valid state
    assign user_regs_read[DMA_CMD_RD_ADDR] = {23'h0, cmd_bram_rd_addr};  // Debug: current read address
    assign user_regs_read[DMA_CMD_RESERVED] = 32'h0;  // Reserved
    assign user_regs_read[ENGINE_CMD_SUBMIT] = 32'h0;  // Legacy, write-only

    // Engine status: {reserved[12], reserved[4], mc_state[4], rc_state[4], reserved[4], busy[1]}
    assign user_regs_read[ENGINE_STATUS] = {12'h0, 4'h0, mc_state_2d, rc_state_2d, 3'b0, engine_busy};
    assign user_regs_read[ENGINE_RESULT_COUNT] = 32'h0;  // TODO: Add result counter to engine_top_2d
    // ENGINE_DEBUG: {bridge_busy, reserved[2], FIFO_empty, rc_state[3:0], mc_state[3:0], FIFO_count[12:0], 3'b0}
    assign user_regs_read[ENGINE_DEBUG] = {cmd_bram_bridge_busy, 2'b0,
                                           cmd_fifo_count == 13'd0,  // empty
                                           rc_state_2d, mc_state_2d, 
                                           cmd_fifo_count, 3'b0};

    // Circular buffer interface registers (simplified for 2D engine)
    assign user_regs_read[ENGINE_WRITE_TOP] = {23'h0, engine_2d_bram_wr_addr};
    assign user_regs_read[REG_RD_PTR] = user_regs_write[REG_RD_PTR];  // Host-controlled read pointer
    assign user_regs_read[REG_WR_PTR] = {23'h0, engine_2d_bram_wr_addr};
    assign user_regs_read[REG_USED_ENTRIES] = 32'h0;  // TODO: Add tracking
    assign user_regs_read[REG_RESULT_EMPTY] = {31'h0, ~engine_busy};  // Empty when not busy

    // NAP error status (aggregate across all 16 NAPs)
    assign user_regs_read[NAP_ERROR_STATUS] = 32'h0;  // TODO: Aggregate NAP errors
    assign user_regs_read[DC_BRAM_WR_COUNT] = 32'h0;  // TODO: Add debug counter
    assign user_regs_read[DC_DEBUG] = {28'h0, 4'h0};  // TODO: Add DC state

    // =========================================================================
    // Debug Registers for Hardware Debugging
    // =========================================================================
    // CE_BRAM_ADDR_DEBUG (0x08): ACK status from MC
    //   [31:16] = dbg_ce_ack_matmul[15:0] - Per-row CE MATMUL ACK (captured in MC)
    //   [15:0]  = dbg_dc_ack_fetch[15:0]  - Per-row DC FETCH ACK (captured in MC)
    assign user_regs_read[CE_BRAM_ADDR_DEBUG] = {dbg_ce_ack_matmul, dbg_dc_ack_fetch};

    // CE_BRAM_DATA_LOW (0x0C): FSM states overview
    //   [31:24] = reserved
    //   [23]    = dbg_cmd_valid      - MC has valid command
    //   [22]    = dbg_matmul_en_pulse - MATMUL enable pulse active
    //   [21:20] = reserved
    //   [19:16] = mc_state_2d        - Master Control state
    //   [15:12] = rc_state_2d        - Result Collector state
    //   [11:8]  = dbg_ce_state_row0  - Compute Engine state (row 0)
    //   [7:4]   = dbg_dc_state_row0  - Dispatcher Control state (row 0)
    //   [3:0]   = reserved
    assign user_regs_read[CE_BRAM_DATA_LOW] = {8'h0, dbg_cmd_valid, dbg_matmul_en_pulse, 2'b0,
                                                mc_state_2d, rc_state_2d,
                                                dbg_ce_state_row0, dbg_dc_state_row0, 4'h0};

    // CE_BRAM_DATA_MID (0x10): Reserved for future per-row CE states
    assign user_regs_read[CE_BRAM_DATA_MID] = 32'h0;

    // CE_CONTROL_DEBUG (0x14): Reserved for future per-row DC states
    assign user_regs_read[CE_CONTROL_DEBUG] = 32'h0;

    // Remaining debug registers - reserved for future use
    assign user_regs_read[DC_BRAM_WRITE_DEBUG] = 32'h0;
    assign user_regs_read[DC_CONTROL_DEBUG] = 32'h0;
    assign user_regs_read[BCV_DEBUG_STATE] = 32'h0;
    assign user_regs_read[BCV_DEBUG_DIMS] = 32'h0;
    assign user_regs_read[MC_TILE_DIMS] = 32'h0;
    assign user_regs_read[MC_PAYLOAD_WORD1] = 32'h0;
    assign user_regs_read[MC_PAYLOAD_WORD2] = 32'h0;
    assign user_regs_read[MC_PAYLOAD_WORD3] = 32'h0;

    // Tie off GDDR6 channel status signals (2D engine handles internally)
    assign gddr_nap_running = 8'h0;
    assign gddr_nap_done = 8'hff;
    assign gddr_nap_fail = 8'h0;

    // Tie off GDDR6 packet gen registers (not used in 2D engine)
    generate
        for (genvar i = 0; i < MAX_NOC_CHANNELS; i++) begin : gen_gddr_regs_tieoff
            for (genvar j = 0; j < REGS_PER_GDDR_CH; j++) begin : gen_gddr_reg
                if ((i*REGS_PER_GDDR_CH + j) < NUM_GDDR_REGS) begin : gen_valid_reg
                    assign user_regs_read[GDDR_REGS_BASE + i*REGS_PER_GDDR_CH + j] = 32'b0;
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
    
    // Pipeline Probe Registers (read-only) - Debug pipeline stages
    // REG_0: dispatcher_bram data (FETCH output)
    // REG_1: row_bram data (DISPATCH output)
    // REG_2: FP24 compute result (MLP output, lower 24 bits)
    // REG_3: FP16 final result (after conversion)
    assign user_regs_read[RESULT_REG_0] = {16'd0, captured_probe_0};  // disp_bram[15:0]
    assign user_regs_read[RESULT_REG_1] = {16'd0, captured_probe_1};  // row_bram[15:0]
    assign user_regs_read[RESULT_REG_2] = {8'd0, captured_probe_2};   // FP24[23:0]
    assign user_regs_read[RESULT_REG_3] = {16'd0, captured_probe_3};  // FP16[15:0]

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
        .tag    ("dma_data_out_bram")
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