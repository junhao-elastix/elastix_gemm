//////////////////////////////////////
// ACE GENERATED VERILOG INCLUDE FILE
// Generated on: 2025.10.28 at 01:41:28 PDT
// By: ACE 10.3.1
// From project: elastix_gemm_top
//////////////////////////////////////
// IO Ring Simulation Configuration Include File
// 
// This file must be included in your testbench
// after you instantiate the Device Simulation Model (DSM)
//////////////////////////////////////

//////////////////////////////////////
// Clocks
//////////////////////////////////////
// Global clocks driven from NW corner
`ifndef ACX_CLK_NW_FULL
`ACX_DEVICE_NAME.clocks.global_clk_nw.set_global_clocks({'d5000,'d0,'d0,'d0,'d0,'d0,'d0,'d0,'d0,'d0,'d0,'d0,'d0,'d0,'d0,'d0,'d5000,'d0,'d0,'d0,'d0,'d0,'d0,'d0,'d0,'d0,'d0,'d0,'d0,'d0,'d0,'d0});
`endif

// Global clocks driven from NE corner
`ifndef ACX_CLK_NE_FULL
`ACX_DEVICE_NAME.clocks.global_clk_ne.set_global_clocks({'d5000,'d0,'d0,'d0,'d0,'d0,'d0,'d0,'d0,'d0,'d0,'d0,'d0,'d0,'d0,'d1000,'d5000,'d0,'d0,'d0,'d0,'d0,'d0,'d0,'d0,'d0,'d0,'d0,'d0,'d0,'d0,'d1000});
`endif

// Global clocks driven from SE corner
`ifndef ACX_CLK_SE_FULL
`ACX_DEVICE_NAME.clocks.global_clk_se.set_global_clocks({'d5000,'d0,'d0,'d0,'d0,'d0,'d0,'d0,'d0,'d0,'d0,'d0,'d0,'d0,'d0,'d1000,'d5000,'d0,'d0,'d0,'d0,'d0,'d0,'d0,'d0,'d0,'d0,'d0,'d0,'d0,'d0,'d1000});
`endif

// Global clocks driven from SW corner
`ifndef ACX_CLK_SW_FULL
`ACX_DEVICE_NAME.clocks.global_clk_sw.set_global_clocks({'d5000,'d0,'d0,'d0,'d0,'d0,'d0,'d0,'d0,'d0,'d0,'d10000,'d5000,'d10000,'d1000,'d1250,'d5000,'d0,'d0,'d0,'d0,'d0,'d0,'d0,'d0,'d0,'d0,'d10000,'d5000,'d10000,'d1000,'d1250});
`endif


//////////////////////////////////////
// Config file loading for Cycle Accurate sims
// This is only applicable when using the FCU BFM
//////////////////////////////////////
`ifndef ACX_FCU_FULL
  `ifdef ACX_PCIE_1_FULL
    `ACX_DEVICE_NAME.fcu.configure( {`ACX_IORING_SIM_FILES_PATH, "elastix_gemm_top_ioring_bitstream0_PCIE_1_fast_sim.txt"}, "full");
  `endif
  `ifdef ACX_CLK_NW_FULL
    `ACX_DEVICE_NAME.fcu.configure( {`ACX_IORING_SIM_FILES_PATH, "elastix_gemm_top_ioring_bitstream0_QCM_NW.txt"}, "full");
  `endif
  `ifdef ACX_CLK_NW_FULL
    `ACX_DEVICE_NAME.fcu.configure( {`ACX_IORING_SIM_FILES_PATH, "elastix_gemm_top_ioring_bitstream0_CLKIO_NW.txt"}, "full");
  `endif
  `ifdef ACX_CLK_NE_FULL
    `ACX_DEVICE_NAME.fcu.configure( {`ACX_IORING_SIM_FILES_PATH, "elastix_gemm_top_ioring_bitstream0_QCM_NE.txt"}, "full");
  `endif
  `ifdef ACX_CLK_NE_FULL
    `ACX_DEVICE_NAME.fcu.configure( {`ACX_IORING_SIM_FILES_PATH, "elastix_gemm_top_ioring_bitstream0_CLKIO_NE.txt"}, "full");
  `endif
  `ifdef ACX_CLK_NE_FULL
    `ACX_DEVICE_NAME.fcu.configure( {`ACX_IORING_SIM_FILES_PATH, "elastix_gemm_top_ioring_bitstream0_PLL_NE_2.txt"}, "full");
  `endif
  `ifdef ACX_CLK_SE_FULL
    `ACX_DEVICE_NAME.fcu.configure( {`ACX_IORING_SIM_FILES_PATH, "elastix_gemm_top_ioring_bitstream0_QCM_SE.txt"}, "full");
  `endif
  `ifdef ACX_CLK_SE_FULL
    `ACX_DEVICE_NAME.fcu.configure( {`ACX_IORING_SIM_FILES_PATH, "elastix_gemm_top_ioring_bitstream0_CLKIO_SE.txt"}, "full");
  `endif
  `ifdef ACX_CLK_SE_FULL
    `ACX_DEVICE_NAME.fcu.configure( {`ACX_IORING_SIM_FILES_PATH, "elastix_gemm_top_ioring_bitstream0_PLL_SE_0.txt"}, "full");
  `endif
  `ifdef ACX_CLK_SW_FULL
    `ACX_DEVICE_NAME.fcu.configure( {`ACX_IORING_SIM_FILES_PATH, "elastix_gemm_top_ioring_bitstream0_QCM_SW.txt"}, "full");
  `endif
  `ifdef ACX_CLK_SW_FULL
    `ACX_DEVICE_NAME.fcu.configure( {`ACX_IORING_SIM_FILES_PATH, "elastix_gemm_top_ioring_bitstream0_CLKIO_SW.txt"}, "full");
  `endif
  `ifdef ACX_CLK_SW_FULL
    `ACX_DEVICE_NAME.fcu.configure( {`ACX_IORING_SIM_FILES_PATH, "elastix_gemm_top_ioring_bitstream0_PLL_SW_0.txt"}, "full");
  `endif
  `ifdef ACX_CLK_SW_FULL
    `ACX_DEVICE_NAME.fcu.configure( {`ACX_IORING_SIM_FILES_PATH, "elastix_gemm_top_ioring_bitstream0_PLL_SW_1.txt"}, "full");
  `endif
  `ifdef ACX_CLK_SW_FULL
    `ACX_DEVICE_NAME.fcu.configure( {`ACX_IORING_SIM_FILES_PATH, "elastix_gemm_top_ioring_bitstream0_PLL_SW_3.txt"}, "full");
  `endif
  `ifdef ACX_ENOC_RTL_INCLUDE
    `ACX_DEVICE_NAME.fcu.configure( {`ACX_IORING_SIM_FILES_PATH, "elastix_gemm_top_ioring_bitstream0_NOC.txt"}, "full");
  `endif
  `ifdef ACX_DDR4_FULL
    `ACX_DEVICE_NAME.fcu.configure( {`ACX_IORING_SIM_FILES_PATH, "elastix_gemm_top_ioring_bitstream1_DDR4.txt"}, "full");
  `endif
fork
  `ifdef ACX_GDDR6_0_FULL
    `ACX_DEVICE_NAME.fcu.configure( {`ACX_IORING_SIM_FILES_PATH, "elastix_gemm_top_ioring_bitstream1_GDDR6_0.txt"}, "full");
  `endif
  `ifdef ACX_GDDR6_1_FULL
    `ACX_DEVICE_NAME.fcu.configure( {`ACX_IORING_SIM_FILES_PATH, "elastix_gemm_top_ioring_bitstream1_GDDR6_1.txt"}, "full");
  `endif
  `ifdef ACX_GDDR6_2_FULL
    `ACX_DEVICE_NAME.fcu.configure( {`ACX_IORING_SIM_FILES_PATH, "elastix_gemm_top_ioring_bitstream1_GDDR6_2.txt"}, "full");
  `endif
  `ifdef ACX_GDDR6_3_FULL
    `ACX_DEVICE_NAME.fcu.configure( {`ACX_IORING_SIM_FILES_PATH, "elastix_gemm_top_ioring_bitstream1_GDDR6_3.txt"}, "full");
  `endif
  `ifdef ACX_GDDR6_4_FULL
    `ACX_DEVICE_NAME.fcu.configure( {`ACX_IORING_SIM_FILES_PATH, "elastix_gemm_top_ioring_bitstream1_GDDR6_4.txt"}, "full");
  `endif
  `ifdef ACX_GDDR6_5_FULL
    `ACX_DEVICE_NAME.fcu.configure( {`ACX_IORING_SIM_FILES_PATH, "elastix_gemm_top_ioring_bitstream1_GDDR6_5.txt"}, "full");
  `endif
  `ifdef ACX_GDDR6_6_FULL
    `ACX_DEVICE_NAME.fcu.configure( {`ACX_IORING_SIM_FILES_PATH, "elastix_gemm_top_ioring_bitstream1_GDDR6_6.txt"}, "full");
  `endif
  `ifdef ACX_GDDR6_7_FULL
    `ACX_DEVICE_NAME.fcu.configure( {`ACX_IORING_SIM_FILES_PATH, "elastix_gemm_top_ioring_bitstream1_GDDR6_7.txt"}, "full");
  `endif
join
  `ifdef ACX_GPIO_S_FULL
    `ACX_DEVICE_NAME.fcu.configure( {`ACX_IORING_SIM_FILES_PATH, "elastix_gemm_top_ioring_bitstream1_GPIO_S_B0.txt"}, "full");
  `endif
  `ifdef ACX_GPIO_S_FULL
    `ACX_DEVICE_NAME.fcu.configure( {`ACX_IORING_SIM_FILES_PATH, "elastix_gemm_top_ioring_bitstream1_GPIO_S_B1.txt"}, "full");
  `endif
  `ifdef ACX_GPIO_S_FULL
    `ACX_DEVICE_NAME.fcu.configure( {`ACX_IORING_SIM_FILES_PATH, "elastix_gemm_top_ioring_bitstream1_GPIO_S_B2.txt"}, "full");
  `endif
  `ifdef ACX_GPIO_N_FULL
    `ACX_DEVICE_NAME.fcu.configure( {`ACX_IORING_SIM_FILES_PATH, "elastix_gemm_top_ioring_bitstream1_GPIO_N_B0.txt"}, "full");
  `endif
  `ifdef ACX_GPIO_N_FULL
    `ACX_DEVICE_NAME.fcu.configure( {`ACX_IORING_SIM_FILES_PATH, "elastix_gemm_top_ioring_bitstream1_GPIO_N_B1.txt"}, "full");
  `endif
  `ifdef ACX_GPIO_N_FULL
    `ACX_DEVICE_NAME.fcu.configure( {`ACX_IORING_SIM_FILES_PATH, "elastix_gemm_top_ioring_bitstream1_GPIO_N_B2.txt"}, "full");
  `endif
`endif

//////////////////////////////////////
// End IO Ring Simulation Configuration Include File
//////////////////////////////////////
