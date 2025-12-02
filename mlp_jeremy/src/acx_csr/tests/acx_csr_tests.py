# This file is public domain, it can be freely copied without restrictions.
# SPDX-License-Identifier: CC0-1.0
from __future__ import annotations

import logging
import cocotb
from cocotb.clock import Clock

from sim_utils.axi_driver import AXI4Driver, AXI4Response


@cocotb.test()
async def test_axi_driver_user_regs_unaligned(dut):
    """Test unaligned write / read of user registers via AXI CSR interface."""
    log = logging.getLogger("AXI4DriverTest")
    log.setLevel(logging.INFO)
    log.info("Hello")

    num_regs = dut.NUM_USER_REGS.value.to_signed()
    log.info(f"Number of user regs: {num_regs}")

    # Setup clock
    clock = Clock(dut.i_clk, 10, unit="ns")  # 100MHz
    cocotb.start_soon(clock.start())
    dut.i_reset_n.value = 0
    await clock.cycles(5)
    dut.i_reset_n.value = 1

    # Initialize AXI driver
    axi_driver = AXI4Driver(
        axi_interface=dut.axi_main_if,
        clock=dut.i_clk,
    )

    await axi_driver.initialize()
    await clock.cycles(5)

    write_vals = []
    read_vals = []
    # Set input regs and prepare write values
    for i in range(num_regs):
        write_vals.append(i + 1)
        read_vals.append(0x1337c0de + i)
        dut.i_user_regs_in[i].value = read_vals[-1]
    # Write to user regs
    for i in range(num_regs):
        cocotb.log.info(f"Writing 0x{write_vals[i]:08x} to user reg {i}")
        # Note: unaligned
        response = await axi_driver.write_single(i * 4, write_vals[i])
        assert response == AXI4Response.OKAY, f"Write to reg {i} failed"

    # Read back user regs and verify
    for i in range(num_regs):
        cocotb.log.info(f"Reading from user reg {i}")
        read_data = await axi_driver.read_single(i * 4)
        # Extract unaligned word
        word_shift = i % 8
        read_data = (read_data >> (word_shift*32)) & 0xFFFFFFFF
        cocotb.log.info(f"Read data: 0x{read_data:08x}")
        assert read_data == read_vals[i], f"Data mismatch at reg {i}: expected 0x{read_vals[i]:08x}, got 0x{read_data:08x}"
        assert dut.o_user_regs_out[i].value == write_vals[i], f"DUT register mismatch at reg {i}: expected 0x{write_vals[i]:08x}, got 0x{dut.o_user_regs_out[i].value:08x}"

    await clock.cycles(10)

    # reg_control_block.sv doesn't support bursting - will only set first word
    write_vals = [0xdeadbeef, 0xcafebabe, 0x8badf00d, 0xfeedface]
    await axi_driver.write_burst(0, write_vals)
    await clock.cycles(5)

    # Burst crossing a 4KB boundary - should raise error
    try:
        await axi_driver.write_burst(0xFFF0, [0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8])
        assert False, "Expected AXI4DriverError for burst crossing 4KB boundary"
    except Exception as e:
        cocotb.log.info(f"Caught expected exception: {e}")
    