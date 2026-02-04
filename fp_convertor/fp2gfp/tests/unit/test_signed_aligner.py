"""
Cocotb unit tests for signed_aligner module.

Tests signed mantissa alignment with arithmetic right shift:
- No shift needed
- Shift by various amounts
- Sign preservation (negative values)
- Complete underflow
- Round bit capture
"""

import sys
from pathlib import Path

import cocotb
from cocotb.triggers import Timer

# Add golden_models to path
golden_path = Path(__file__).resolve().parents[2] / "golden_models"
if str(golden_path) not in sys.path:
    sys.path.insert(0, str(golden_path))

from gfp16_to_gfp8_golden import signed_aligner_hw, to_signed, to_unsigned


def get_dut_params(dut):
    """Extract DUT parameters."""
    return {
        'EXP_BITS': int(dut.EXP_BITS.value),
        'MAN_BITS': int(dut.MAN_BITS.value),
        'IN_ELEMENTS': int(dut.IN_ELEMENTS.value),
    }


async def drive_and_check(dut, exps, mans, is_zeros, max_exp):
    """Drive inputs and check outputs against golden."""
    params = get_dut_params(dut)
    in_elements = params['IN_ELEMENTS']
    man_bits = params['MAN_BITS']

    # Pad inputs
    while len(exps) < in_elements:
        exps.append(0)
        mans.append(0)
        is_zeros.append(True)

    # Drive inputs
    for i in range(in_elements):
        dut.i_exps[i].value = exps[i]
        dut.i_mans[i].value = to_unsigned(mans[i], man_bits)
        dut.i_is_zero[i].value = int(is_zeros[i])
    dut.i_max_exp.value = max_exp

    # Wait for combinational logic
    await Timer(1, units='ns')

    # Get golden results
    g_aligned, g_round = signed_aligner_hw(exps, mans, is_zeros, max_exp, man_bits)

    # Check outputs
    for i in range(len(exps)):
        if i >= in_elements:
            break
        dut_aligned = int(dut.o_aligned_mans[i].value.signed_integer)
        dut_round = int(dut.o_round_bits[i].value)

        assert dut_aligned == g_aligned[i], \
            f"Element {i} aligned mismatch: got {dut_aligned}, expected {g_aligned[i]}"
        assert dut_round == g_round[i], \
            f"Element {i} round bit mismatch: got {dut_round}, expected {g_round[i]}"


@cocotb.test()
async def test_no_shift(dut):
    """Test when element exp equals max exp (no shift)."""
    exps = [15, 15, 15]
    mans = [512, -512, 100]
    is_zeros = [False, False, False]
    max_exp = 15
    await drive_and_check(dut, exps, mans, is_zeros, max_exp)
    dut._log.info("PASS: test_no_shift")


@cocotb.test()
async def test_shift_by_one(dut):
    """Test shift by 1 position."""
    exps = [14]
    mans = [512]  # Binary: 01000000000, after >>1: 00100000000 = 256
    is_zeros = [False]
    max_exp = 15
    await drive_and_check(dut, exps, mans, is_zeros, max_exp)
    dut._log.info("PASS: test_shift_by_one")


@cocotb.test()
async def test_shift_negative(dut):
    """Test arithmetic shift preserves negative sign."""
    exps = [13]
    mans = [-512]  # Negative value
    is_zeros = [False]
    max_exp = 15  # Shift by 2
    await drive_and_check(dut, exps, mans, is_zeros, max_exp)

    # Verify the result is still negative
    dut_aligned = int(dut.o_aligned_mans[0].value.signed_integer)
    assert dut_aligned < 0, f"Expected negative, got {dut_aligned}"
    dut._log.info("PASS: test_shift_negative")


@cocotb.test()
async def test_complete_underflow(dut):
    """Test shift amount >= mantissa width (complete underflow)."""
    params = get_dut_params(dut)
    man_bits = params['MAN_BITS']

    exps = [0]
    mans = [100]
    is_zeros = [False]
    max_exp = man_bits + 5  # Shift by more than mantissa width
    await drive_and_check(dut, exps, mans, is_zeros, max_exp)
    dut._log.info("PASS: test_complete_underflow")


@cocotb.test()
async def test_round_bit_capture(dut):
    """Test that round bit captures first discarded bit."""
    # Value with bit pattern that will produce round bit = 1
    exps = [14]
    mans = [3]  # Binary: 00000000011, shift by 1 -> discards 1
    is_zeros = [False]
    max_exp = 15  # Shift by 1
    await drive_and_check(dut, exps, mans, is_zeros, max_exp)

    dut_round = int(dut.o_round_bits[0].value)
    assert dut_round == 1, f"Expected round bit=1, got {dut_round}"
    dut._log.info("PASS: test_round_bit_capture")


@cocotb.test()
async def test_zero_element(dut):
    """Test zero element passes through as zero."""
    exps = [15]
    mans = [999]  # Non-zero mantissa but marked as zero
    is_zeros = [True]
    max_exp = 15
    await drive_and_check(dut, exps, mans, is_zeros, max_exp)

    dut_aligned = int(dut.o_aligned_mans[0].value.signed_integer)
    assert dut_aligned == 0, f"Zero element should be 0, got {dut_aligned}"
    dut._log.info("PASS: test_zero_element")


@cocotb.test()
async def test_mixed_elements(dut):
    """Test mix of shifts, signs, and zeros."""
    exps = [15, 14, 13, 0]
    mans = [512, -256, 100, 0]
    is_zeros = [False, False, False, True]
    max_exp = 15
    await drive_and_check(dut, exps, mans, is_zeros, max_exp)
    dut._log.info("PASS: test_mixed_elements")
