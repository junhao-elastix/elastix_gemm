//////////////////////////////////////
// ACE GENERATED SYSTEMVERILOG FILE
// Generated on: 2025.11.13 at 11:48:13 PST
// By:           ACE 10.3.1
// From file:    /home/dev/Dev/elastix_gemm/gemm/src/acxip/acx_device_manager.acxip
// For Property: output.systemverilog_file
//
// IP                  : Speedster7t AC7t1500 Device Manager
// Configuration Name  : acx_device_manager
//

// Set the Verilog included files search path to:
//       $ACE_INSTALL_DIR/libraries
//  Details of setting the search path is given in:
//       $ACE_INSTALL_DIR/libraries/README.pdf
`include "speedster7t/macros/ACX_DEVICE_MANAGER.svp"

//////////////////////////////////////
// Speedster7t AC7t1500 Device Manager Wrapper User Model
//////////////////////////////////////

`timescale 1 ps / 1 ps
module acx_device_manager
  (

   // JTAG Interface

   input wire t_JTAG_INPUT i_jtag_in,                 // Should be connected to top-level ports with the same declaration
   input wire i_tdo_bus,                 // Pass-through the JTAG bus to connect to Snapshot. If not used, this input should be tied to 1'b0
   output wire t_JTAG_OUTPUT o_jtag_out,                // Should be connected to top-level ports with the same declaration
   output wire t_JTAP_BUS o_jtap_bus,                // Pass-through of the JTAG bus to connect to Snapshot (or other JTAG components)

   // PERSTN and Hot Reset Interface

   input wire [5:0] i_pcie_1_ltssm_state,      // Must be connected to the corresponding DCI GPIO pins is ENABLE_PCIE_1_HOT_RSTN  or ENABLE_PCIE_1_GEN2_DEEMPH is set
   input wire i_pcie_1_perstn,           // For designs with PCIe (on AC7t1500), this pin must be driven by a PERSTN GPIO pin, and ENABLE_PCIE_1_PERSTN must be set to 1, otherwise enumeration will not happen.
   output wire o_pcie_1_reconfig_fpga_n,  // This active-low output signals to the board manager that the FPGA must be reprogrammed. This requires board support (VP has it), and that the bitstream is stored in flash memory. This output is only enabled if both ENABLE_PCIE_0_HOT_RSTN  and ENABLE_PCIE_RECONFIG_FPGA are set, otherwise this output will be 1.

   // User Design

   input wire i_clk,                     // 100 MHz Clock input for Device Manager block.
   input wire i_start,                   // A high input starts the Device Manager. In most cases this signal is simply tied to 1'b1, but it can also be tied to a PLL lock signal if necessary.
   output wire [31:0] o_status                   // Progress indication, error status, alarms.  See User Guide documentation for details
  );

   wire [1023:0] not_used;


  ACX_DEVICE_MANAGER #
  (
  .ENABLE_PCIE_1_GEN2_DEEMPH(0),             // Enable PCIE_1 Gen2 De-emphasis Support
  .ENABLE_PCIE_0_GEN2_DEEMPH(0),             // Enable PCIE_0 Gen2 De-emphasis Support
  .ENABLE_PCIE_RECONFIG_FPGA(1),             // Enable FPGA Reconfiguration Pin Control
  .ENABLE_PCIE_0_PERSTN     (0),             // Enable PCIE_0 PERSTN Support
  .NAP_ROW                  (4'h4),          // NAP Row
  .ENABLE_PCIE_1_PERSTN     (1),             // Enable PCIE_1 PERSTN Support
  .NAP_COLUMN               (4'h6),          // NAP Column
  .ENABLE_PCIE_0_HOT_RSTN   (0),             // Enable PCIE_0 Hot Reset Support
  .ENABLE_PCIE_0_DBI_GATEWAY(0),             // Enable PCIE_0 DBI Gateway
  .ENABLE_PCIE_1_DBI_GATEWAY(1),             // Enable PCIE_1 DBI Gateway
  .ENABLE_PCIE_1_HOT_RSTN   (1)              // Enable PCIE_1 Hot Reset Support
  )
  x_dev_mgr
  (

   // JTAG Interface

   .i_jtag_in (i_jtag_in),                 // Should be connected to top-level ports with the same declaration
   .i_tdo_bus (i_tdo_bus),                 // Pass-through the JTAG bus to connect to Snapshot. If not used, this input should be tied to 1'b0
   .o_jtag_out (o_jtag_out),                // Should be connected to top-level ports with the same declaration
   .o_jtap_bus (o_jtap_bus),                // Pass-through of the JTAG bus to connect to Snapshot (or other JTAG components)

   // PERSTN and Hot Reset Interface

   .i_pcie_0_ltssm_state (6'h0),      // Must be connected to the corresponding DCI GPIO pins is ENABLE_PCIE_0_HOT_RSTN  or ENABLE_PCIE_0_GEN2_DEEMPH is set
   .i_pcie_0_perstn (1'h0),           // For designs with PCIe (on AC7t1500), this pin must be driven by a PERSTN GPIO pin, and ENABLE_PCIE_0_PERSTN must be set to 1, otherwise enumeration will not happen.
   .i_pcie_1_ltssm_state (i_pcie_1_ltssm_state),      // Must be connected to the corresponding DCI GPIO pins is ENABLE_PCIE_1_HOT_RSTN  or ENABLE_PCIE_1_GEN2_DEEMPH is set
   .i_pcie_1_perstn (i_pcie_1_perstn),           // For designs with PCIe (on AC7t1500), this pin must be driven by a PERSTN GPIO pin, and ENABLE_PCIE_1_PERSTN must be set to 1, otherwise enumeration will not happen.
   .o_pcie_0_reconfig_fpga_n (),  // This active-low output signals to the board manager that the FPGA must be reprogrammed. This requires board support (VP has it), and that the bitstream is stored in flash memory. This output is only enabled if both ENABLE_PCIE_0_HOT_RSTN  and ENABLE_PCIE_RECONFIG_FPGA are set, otherwise this output will be 1.
   .o_pcie_1_reconfig_fpga_n (o_pcie_1_reconfig_fpga_n),  // This active-low output signals to the board manager that the FPGA must be reprogrammed. This requires board support (VP has it), and that the bitstream is stored in flash memory. This output is only enabled if both ENABLE_PCIE_0_HOT_RSTN  and ENABLE_PCIE_RECONFIG_FPGA are set, otherwise this output will be 1.

   // User Design

   .i_clk (i_clk),                     // 100 MHz Clock input for Device Manager block.
   .i_start (i_start),                   // A high input starts the Device Manager. In most cases this signal is simply tied to 1'b1, but it can also be tied to a PLL lock signal if necessary.
   .o_serdes_status (),           // Serdes status.  See User Guide documentation for details
   .o_status (o_status)                   // Progress indication, error status, alarms.  See User Guide documentation for details
  );

endmodule  // acx_device_manager

//////////////////////////////////////
// End Speedster7t AC7t1500 Device Manager Wrapper User Model
//////////////////////////////////////
