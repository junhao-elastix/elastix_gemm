//////////////////////////////////////
// ACE GENERATED VERILOG INCLUDE FILE
// Generated on: 2025.10.28 at 20:44:42 PDT
// By: ACE 10.3.1
// From project: elastix_gemm_top
//////////////////////////////////////
// IO Ring Simulation Defines Include File
// 
// This file must be included in your compilation
// prior to the Device Simulation Model (DSM) being compiled
//////////////////////////////////////


//////////////////////////////////////
// Switch to set SystemVerilog Direct Connect
// Interfaces in DSM to Monitor-Only Mode.
// This is required when using the IO Designer
// generated user design port bindings file.
//////////////////////////////////////
  `define ACX_ENABLE_DCI_MONITOR_MODE = 1;

//////////////////////////////////////
// Clock Selects in each IP
//////////////////////////////////////

//////////////////////////////////////
// GDDR6_0:
  // Ref clock
  `define ACX_GDDR6_0_REF_CLK_SEL = 17;
  // NoC clock
  `define ACX_GDDR6_0_NOC_CLK_SEL = 17;

//////////////////////////////////////
// GDDR6_1:
  // Ref clock
  `define ACX_GDDR6_1_REF_CLK_SEL = 17;
  // NoC clock
  `define ACX_GDDR6_1_NOC_CLK_SEL = 17;

//////////////////////////////////////
// GDDR6_2:
  // Ref clock
  `define ACX_GDDR6_2_REF_CLK_SEL = 17;
  // NoC clock
  `define ACX_GDDR6_2_NOC_CLK_SEL = 17;

//////////////////////////////////////
// GDDR6_3:
  // Ref clock
  `define ACX_GDDR6_3_REF_CLK_SEL = 17;
  // NoC clock
  `define ACX_GDDR6_3_NOC_CLK_SEL = 17;

//////////////////////////////////////
// GDDR6_4:
  // Ref clock
  `define ACX_GDDR6_4_REF_CLK_SEL = 0;
  // NoC clock
  `define ACX_GDDR6_4_NOC_CLK_SEL = 0;

//////////////////////////////////////
// GDDR6_5:
  // Ref clock
  `define ACX_GDDR6_5_REF_CLK_SEL = 0;
  // NoC clock
  `define ACX_GDDR6_5_NOC_CLK_SEL = 0;

//////////////////////////////////////
// GDDR6_6:
  // Ref clock
  `define ACX_GDDR6_6_REF_CLK_SEL = 0;
  // NoC clock
  `define ACX_GDDR6_6_NOC_CLK_SEL = 0;

//////////////////////////////////////
// GDDR6_7:
  // Ref clock
  `define ACX_GDDR6_7_REF_CLK_SEL = 0;
  // NoC clock
  `define ACX_GDDR6_7_NOC_CLK_SEL = 0;

//////////////////////////////////////
// DDR4:
  // Ref clock
  `define ACX_DDR4_REF_CLK_SEL = 0;
  // NoC clock
  `define ACX_DDR4_NOC_CLK_SEL = 0;
  // DC clock not used

//////////////////////////////////////
// PCIE_1:
  // AUX clock
  `define ACX_PCIE_1_AUX_CLK_SEL = 16;
  // Master clock
  `define ACX_PCIE_1_MASTER_CLK_SEL = 16;
  // Slave clock
  `define ACX_PCIE_1_SLAVE_CLK_SEL = 16;

//////////////////////////////////////
// NoC:
  // NoC Ref clock
  `define ENOC_CLK_SEL = 15;

//////////////////////////////////////
// Reset Selects in each IP
//////////////////////////////////////

//////////////////////////////////////
// DDR4:
  `define ACX_DDR4_RST_SEL = 26;

//////////////////////////////////////
// GDDR6_0:
  `define ACX_GDDR6_0_RST_SEL = 16;

//////////////////////////////////////
// GDDR6_1:
  `define ACX_GDDR6_1_RST_SEL = 17;

//////////////////////////////////////
// GDDR6_2:
  `define ACX_GDDR6_2_RST_SEL = 18;

//////////////////////////////////////
// GDDR6_3:
  `define ACX_GDDR6_3_RST_SEL = 19;

//////////////////////////////////////
// GDDR6_4:
  `define ACX_GDDR6_4_RST_SEL = 20;

//////////////////////////////////////
// GDDR6_5:
  `define ACX_GDDR6_5_RST_SEL = 21;

//////////////////////////////////////
// GDDR6_6:
  `define ACX_GDDR6_6_RST_SEL = 22;

//////////////////////////////////////
// GDDR6_7:
  `define ACX_GDDR6_7_RST_SEL = 23;

//////////////////////////////////////
// PCIE_1:
  `define ACX_PCIE_1_RST_SEL = 15;

//////////////////////////////////////
// CLKIO_NE:
  `define ACX_CLKIO_NE_RST_SEL = 3;

//////////////////////////////////////
// CLKIO_NW:
  `define ACX_CLKIO_NW_RST_SEL = 2;

//////////////////////////////////////
// CLKIO_SE:
  `define ACX_CLKIO_SE_RST_SEL = 1;

//////////////////////////////////////
// CLKIO_SW:
  `define ACX_CLKIO_SW_RST_SEL = 0;

//////////////////////////////////////
// GPIO_N_B0:
  `define ACX_GPIO_N_B0_RST_SEL = 27;

//////////////////////////////////////
// GPIO_N_B1:
  `define ACX_GPIO_N_B1_RST_SEL = 27;

//////////////////////////////////////
// GPIO_N_B2:
  `define ACX_GPIO_N_B2_RST_SEL = 27;

//////////////////////////////////////
// GPIO_S_B0:
  `define ACX_GPIO_S_B0_RST_SEL = 27;

//////////////////////////////////////
// GPIO_S_B1:
  `define ACX_GPIO_S_B1_RST_SEL = 27;

//////////////////////////////////////
// GPIO_S_B2:
  `define ACX_GPIO_S_B2_RST_SEL = 27;

//////////////////////////////////////
// End IO Ring Simulation Defines Include File
//////////////////////////////////////
