# This file is public domain, it can be freely copied without restrictions.
# SPDX-License-Identifier: CC0-1.0
from __future__ import annotations


import cocotb
from cocotb.clock import Clock
from cocotb.triggers import  RisingEdge, with_timeout

from sim_utils.axi_driver import AXI4Driver, AXI4Response


@cocotb.test()
async def test_axi_driver_through_noc(dut):
    """Test basic AXI read and write operations through Achronix NoC"""

    # Setup clock
    clock = Clock(dut.i_clk, 10, unit="ns")  # 100MHz
    cocotb.start_soon(clock.start())
    dut.i_reset_n.value = 0
    await clock.cycles(5)
    dut.i_reset_n.value = 1
    await clock.cycles(5)

    # Initialize AXI driver
    axi_driver = AXI4Driver(
        axi_interface=dut.ext_axi_if,
        clock=dut.i_clk,
    )
    await axi_driver.initialize()

    NAP_ACCESS = 0b0001000
    NAP_COL = 1
    NAP_ROW = 1
    address_prefix = (NAP_ACCESS << 35) | ((NAP_COL-1) << 31) | ((NAP_ROW-1) << 28)

    # Wait for FCU to initialize
    await with_timeout(RisingEdge(dut.chip_ready), 500, "us")
    cocotb.log.info("FCU initialized and ready")

    await clock.cycles(10)

    # Example 1: Single word write
    cocotb.log.info("=== Example 1: Single Word Write ===")
    write_addr = address_prefix + 0x0
    write_data = 0xDEADBEEF

    response = await axi_driver.write_single(write_addr, write_data)
    assert response == AXI4Response.OKAY, f"Write to address 0x{write_addr:08x} failed"
    await clock.cycles(10)  # Wait for write to complete
    assert dut.o_user_regs_out[0].value == write_data, f"DUT register mismatch: expected {write_data}, got {dut.o_user.regs_out[0].value}"
    # Example 2: Single word read
    cocotb.log.info("=== Example 2: Single Word Read ===")
    user_data = 0x12345678
    dut.i_user_regs_in[0].value = user_data  # Set expected read data in DUT input register
    axi_read_data = await axi_driver.read_single(write_addr)
    cocotb.log.info(f"Read data: 0x{axi_read_data:08x}")

    # # Verify readback through NoC
    assert axi_read_data == user_data, f"Data mismatch: wrote 0x{user_data:08x}, read 0x{axi_read_data:08x}"

    cocotb.log.info("✓ Single word write/read verified")


