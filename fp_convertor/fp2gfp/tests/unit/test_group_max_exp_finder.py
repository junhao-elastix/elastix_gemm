"""
Cocotb unit tests for group_max_exp_finder module.

Tests streaming max exponent accumulation for GFP16 format:
- Single word groups
- Multi-word groups
- Last word handling
- Padding handling
- Backpressure
"""

import sys
from pathlib import Path

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer

# Add golden_models to path
golden_path = Path(__file__).resolve().parents[2] / "golden_models"
if str(golden_path) not in sys.path:
    sys.path.insert(0, str(golden_path))

from gfp16_to_gfp8_golden import group_max_exp_finder_hw, to_unsigned


def get_dut_params(dut):
    """Extract DUT parameters."""
    return {
        'EXP_WIDTH': int(dut.EXP_WIDTH.value),
        'IN_ELEMENTS': int(dut.IN_ELEMENTS.value),
        'GROUP_WORDS': int(dut.GROUP_WORDS.value),
        'MAN_BITS': int(dut.MAN_BITS.value),
    }


async def reset_dut(dut):
    """Reset the DUT."""
    dut.reset_i.value = 1
    dut.v_i.value = 0
    dut.ready_i.value = 1
    for i in range(int(dut.IN_ELEMENTS.value)):
        dut.exps_i[i].value = 0
        dut.mans_i[i].value = 0
        dut.is_zero_i[i].value = 1
    dut.pad_i.value = 0
    dut.last_i.value = 0

    await RisingEdge(dut.clk_i)
    await RisingEdge(dut.clk_i)
    dut.reset_i.value = 0
    await RisingEdge(dut.clk_i)


async def send_word(dut, exps, mans, is_zeros, pad=0, last=False, wait_ready=True):
    """Send a single word to the DUT."""
    params = get_dut_params(dut)
    in_elements = params['IN_ELEMENTS']
    man_bits = params['MAN_BITS']

    # Pad inputs
    while len(exps) < in_elements:
        exps.append(0)
        mans.append(0)
        is_zeros.append(True)

    # Wait for ready if requested
    if wait_ready:
        while int(dut.ready_o.value) == 0:
            await RisingEdge(dut.clk_i)

    # Drive inputs
    dut.v_i.value = 1
    dut.pad_i.value = pad
    dut.last_i.value = int(last)

    for i in range(in_elements):
        dut.exps_i[i].value = exps[i]
        dut.mans_i[i].value = to_unsigned(mans[i], man_bits)
        dut.is_zero_i[i].value = int(is_zeros[i])

    await RisingEdge(dut.clk_i)
    dut.v_i.value = 0


async def wait_for_output(dut, timeout_cycles=100):
    """Wait for valid output."""
    for _ in range(timeout_cycles):
        if int(dut.v_o.value) == 1:
            return True
        await RisingEdge(dut.clk_i)
    return False


@cocotb.test()
async def test_single_word_group(dut):
    """Test single-word group (GROUP_WORDS=1 equivalent via last_i)."""
    clock = Clock(dut.clk_i, 10, units="ns")
    cocotb.start_soon(clock.start())

    await reset_dut(dut)

    # GFP16: 5-bit exponent (0-31), 11-bit signed mantissa
    exps = [15, 14, 13]
    mans = [512, 256, 128]  # Positive signed mantissas
    is_zeros = [False, False, False]

    # Golden reference
    g_max_exp = group_max_exp_finder_hw(exps, is_zeros, pad=0)

    await send_word(dut, exps, mans, is_zeros, last=True)

    assert await wait_for_output(dut), "Timeout waiting for output"

    assert int(dut.max_exp_o.value) == g_max_exp, \
        f"Expected max_exp={g_max_exp}, got {int(dut.max_exp_o.value)}"
    assert int(dut.group_last_o.value) == 1, "group_last should be set"

    dut._log.info("PASS: test_single_word_group")


@cocotb.test()
async def test_multi_word_stream(dut):
    """Test multiple words - each produces its own max_exp (no accumulation)."""
    clock = Clock(dut.clk_i, 10, units="ns")
    cocotb.start_soon(clock.start())

    await reset_dut(dut)

    # Word 1: max_exp = 14
    exps1 = [14, 13, 12]
    mans1 = [512, 256, 128]
    is_zeros1 = [False, False, False]

    # Word 2: max_exp = 16
    exps2 = [16, 15, 14]
    mans2 = [512, 256, 128]
    is_zeros2 = [False, False, False]

    # Send word 1
    await send_word(dut, exps1, mans1, is_zeros1, last=False)
    assert await wait_for_output(dut), "Timeout waiting for word 1 output"
    assert int(dut.max_exp_o.value) == 14, \
        f"Word 1: Expected max_exp=14, got {int(dut.max_exp_o.value)}"

    dut.ready_i.value = 1
    await RisingEdge(dut.clk_i)

    # Send word 2
    await send_word(dut, exps2, mans2, is_zeros2, last=True)
    assert await wait_for_output(dut), "Timeout waiting for word 2 output"
    assert int(dut.max_exp_o.value) == 16, \
        f"Word 2: Expected max_exp=16, got {int(dut.max_exp_o.value)}"

    dut._log.info("PASS: test_multi_word_stream")


@cocotb.test()
async def test_all_zeros(dut):
    """Test group with all zeros."""
    clock = Clock(dut.clk_i, 10, units="ns")
    cocotb.start_soon(clock.start())

    await reset_dut(dut)

    exps = [0, 0, 0, 0]
    mans = [0, 0, 0, 0]
    is_zeros = [True, True, True, True]

    await send_word(dut, exps, mans, is_zeros, last=True)
    assert await wait_for_output(dut), "Timeout"

    assert int(dut.max_exp_o.value) == 0, "All zeros should give max_exp=0"

    dut._log.info("PASS: test_all_zeros")


@cocotb.test()
async def test_mixed_zeros_nonzeros(dut):
    """Test mix of zero and non-zero elements."""
    clock = Clock(dut.clk_i, 10, units="ns")
    cocotb.start_soon(clock.start())

    await reset_dut(dut)

    # Non-zero elements have exponents, zero elements should be ignored
    exps = [20, 0, 15, 0]
    mans = [512, 0, 256, 0]
    is_zeros = [False, True, False, True]

    g_max_exp = group_max_exp_finder_hw(exps, is_zeros, pad=0)

    await send_word(dut, exps, mans, is_zeros, last=True)
    assert await wait_for_output(dut), "Timeout"

    assert int(dut.max_exp_o.value) == g_max_exp, \
        f"Expected max_exp={g_max_exp}, got {int(dut.max_exp_o.value)}"

    dut._log.info("PASS: test_mixed_zeros_nonzeros")


@cocotb.test()
async def test_negative_mantissas(dut):
    """Test that negative mantissas don't affect max exp calculation."""
    clock = Clock(dut.clk_i, 10, units="ns")
    cocotb.start_soon(clock.start())

    await reset_dut(dut)

    # Negative mantissas (2's complement)
    exps = [15, 14, 13]
    mans = [-512, -256, -128]  # Negative values
    is_zeros = [False, False, False]

    g_max_exp = group_max_exp_finder_hw(exps, is_zeros, pad=0)

    await send_word(dut, exps, mans, is_zeros, last=True)
    assert await wait_for_output(dut), "Timeout"

    assert int(dut.max_exp_o.value) == g_max_exp, \
        f"Expected max_exp={g_max_exp}, got {int(dut.max_exp_o.value)}"

    dut._log.info("PASS: test_negative_mantissas")


@cocotb.test()
async def test_padding(dut):
    """Test that padded elements are ignored."""
    clock = Clock(dut.clk_i, 10, units="ns")
    cocotb.start_soon(clock.start())

    await reset_dut(dut)

    params = get_dut_params(dut)
    in_elements = params['IN_ELEMENTS']

    # With pad=2 and IN_ELEMENTS=8, valid are indices 0-5, padded are 6-7
    pad = 2
    # Valid elements have low exponents, padded elements have high exponents
    exps = [15, 14, 10, 10, 10, 10, 31, 31]  # 31s at indices 6,7 (padded)
    mans = [512] * in_elements
    is_zeros = [False] * in_elements

    g_max_exp = group_max_exp_finder_hw(exps[:in_elements-pad], is_zeros[:in_elements-pad], pad=0)

    await send_word(dut, exps, mans, is_zeros, pad=pad, last=True)
    assert await wait_for_output(dut), "Timeout"

    # Should ignore padded elements (31s), max should be 15
    assert int(dut.max_exp_o.value) == g_max_exp, \
        f"Padded elements should be ignored, expected {g_max_exp}, got {int(dut.max_exp_o.value)}"

    dut._log.info("PASS: test_padding")


@cocotb.test()
async def test_backpressure(dut):
    """Test backpressure handling."""
    clock = Clock(dut.clk_i, 10, units="ns")
    cocotb.start_soon(clock.start())

    await reset_dut(dut)

    # Deassert ready to create backpressure
    dut.ready_i.value = 0

    exps = [15]
    mans = [512]
    is_zeros = [False]

    await send_word(dut, exps, mans, is_zeros, last=True, wait_ready=True)

    # Output should be valid but held
    await Timer(50, units='ns')

    # Now release backpressure
    dut.ready_i.value = 1
    await RisingEdge(dut.clk_i)

    # Should see output
    assert await wait_for_output(dut, timeout_cycles=5), "Output not released after backpressure"

    dut._log.info("PASS: test_backpressure")


@cocotb.test()
async def test_consecutive_groups(dut):
    """Test multiple consecutive groups."""
    clock = Clock(dut.clk_i, 10, units="ns")
    cocotb.start_soon(clock.start())

    await reset_dut(dut)

    # Group 1: max_exp = 15
    await send_word(dut, [15], [512], [False], last=True)
    assert await wait_for_output(dut), "Timeout on group 1"
    assert int(dut.max_exp_o.value) == 15

    dut.ready_i.value = 1
    await RisingEdge(dut.clk_i)

    # Group 2: max_exp = 20
    await send_word(dut, [20], [512], [False], last=True)
    assert await wait_for_output(dut), "Timeout on group 2"
    assert int(dut.max_exp_o.value) == 20

    dut._log.info("PASS: test_consecutive_groups")
