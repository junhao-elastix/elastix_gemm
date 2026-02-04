"""
Cocotb unit tests for gfp16_extract module.

Tests GFP16 field extraction:
- Exponent extraction
- Signed mantissa extraction
- Zero detection
"""

import sys
from pathlib import Path

import cocotb
from cocotb.triggers import Timer

# Add golden_models to path
golden_path = Path(__file__).resolve().parents[2] / "golden_models"
if str(golden_path) not in sys.path:
    sys.path.insert(0, str(golden_path))

from gfp16_to_gfp8_golden import gfp16_extract_hw, pack_gfp16, to_signed, to_unsigned, GFP16Format, GFP16


def get_dut_params(dut):
    """Extract DUT parameters."""
    return {
        'GFP16_TOTAL_BITS': int(dut.GFP16_TOTAL_BITS.value),
        'GFP16_EXP_BITS': int(dut.GFP16_EXP_BITS.value),
        'GFP16_MAN_BITS': int(dut.GFP16_MAN_BITS.value),
        'IN_ELEMENTS': int(dut.IN_ELEMENTS.value),
    }


async def drive_and_check(dut, gfp16_data: list[int]):
    """Drive inputs and check outputs against golden."""
    params = get_dut_params(dut)
    in_elements = params['IN_ELEMENTS']
    man_bits = params['GFP16_MAN_BITS']
    exp_bits = params['GFP16_EXP_BITS']

    # Pad inputs
    while len(gfp16_data) < in_elements:
        gfp16_data.append(0)

    # Drive inputs
    for i in range(in_elements):
        dut.i_gfp16_data[i].value = gfp16_data[i]

    # Wait for combinational logic
    await Timer(1, units='ns')

    # Get golden results
    fmt = GFP16Format(exp_bits=exp_bits, man_bits=man_bits)
    g_exps, g_mans, g_is_zeros = gfp16_extract_hw(gfp16_data[:in_elements], fmt)

    # Check outputs
    for i in range(in_elements):
        dut_exp = int(dut.o_exps[i].value)
        dut_man = int(dut.o_mans[i].value.signed_integer)
        dut_is_zero = int(dut.o_is_zero[i].value)

        assert dut_exp == g_exps[i], \
            f"Element {i} exp mismatch: got {dut_exp}, expected {g_exps[i]}"
        assert dut_man == g_mans[i], \
            f"Element {i} man mismatch: got {dut_man}, expected {g_mans[i]}"
        assert dut_is_zero == int(g_is_zeros[i]), \
            f"Element {i} is_zero mismatch: got {dut_is_zero}, expected {g_is_zeros[i]}"


@cocotb.test()
async def test_zero_input(dut):
    """Test extraction of all zeros."""
    await drive_and_check(dut, [0, 0, 0, 0])
    dut._log.info("PASS: test_zero_input")


@cocotb.test()
async def test_positive_values(dut):
    """Test extraction of positive mantissa values."""
    data = [
        pack_gfp16(exp=15, man_signed=512),
        pack_gfp16(exp=10, man_signed=100),
        pack_gfp16(exp=5, man_signed=50),
    ]
    await drive_and_check(dut, data)
    dut._log.info("PASS: test_positive_values")


@cocotb.test()
async def test_negative_values(dut):
    """Test extraction of negative mantissa values (2's complement)."""
    data = [
        pack_gfp16(exp=15, man_signed=-512),
        pack_gfp16(exp=10, man_signed=-100),
        pack_gfp16(exp=5, man_signed=-1),
    ]
    await drive_and_check(dut, data)
    dut._log.info("PASS: test_negative_values")


@cocotb.test()
async def test_max_positive(dut):
    """Test maximum positive mantissa (+1023 in 11-bit signed)."""
    data = [pack_gfp16(exp=31, man_signed=1023)]
    await drive_and_check(dut, data)
    dut._log.info("PASS: test_max_positive")


@cocotb.test()
async def test_max_negative(dut):
    """Test maximum negative mantissa (-1024 in 11-bit signed)."""
    data = [pack_gfp16(exp=31, man_signed=-1024)]
    await drive_and_check(dut, data)
    dut._log.info("PASS: test_max_negative")


@cocotb.test()
async def test_mixed_values(dut):
    """Test mix of positive, negative, and zero values."""
    data = [
        pack_gfp16(exp=15, man_signed=512),
        pack_gfp16(exp=15, man_signed=-512),
        pack_gfp16(exp=0, man_signed=0),
        pack_gfp16(exp=10, man_signed=-100),
        pack_gfp16(exp=20, man_signed=200),
        pack_gfp16(exp=0, man_signed=0),
    ]
    await drive_and_check(dut, data)
    dut._log.info("PASS: test_mixed_values")


@cocotb.test()
async def test_all_exponent_values(dut):
    """Test all possible exponent values (0-31)."""
    for exp in [0, 1, 15, 30, 31]:
        data = [pack_gfp16(exp=exp, man_signed=100 if exp > 0 else 0)]
        await drive_and_check(dut, data)
    dut._log.info("PASS: test_all_exponent_values")
