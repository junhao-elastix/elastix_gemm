"""
Cocotb unit tests for gfp8_quantizer module.

Tests signed mantissa quantization from 11-bit to 8-bit:
- Basic quantization (positive/negative)
- Rounding behavior
- Saturation (overflow/underflow)
- Zero handling
"""

import sys
from pathlib import Path

import cocotb
from cocotb.triggers import Timer

# Add golden_models to path
golden_path = Path(__file__).resolve().parents[2] / "golden_models"
if str(golden_path) not in sys.path:
    sys.path.insert(0, str(golden_path))

from gfp16_to_gfp8_golden import gfp8_quantizer_hw, to_signed, to_unsigned


def get_dut_params(dut):
    """Extract DUT parameters."""
    return {
        'IN_MAN_BITS': int(dut.IN_MAN_BITS.value),
        'OUT_MAN_BITS': int(dut.OUT_MAN_BITS.value),
        'IN_ELEMENTS': int(dut.IN_ELEMENTS.value),
    }


async def drive_and_check(dut, aligned_mans, round_bits, is_zeros):
    """Drive inputs and check outputs against golden."""
    params = get_dut_params(dut)
    in_elements = params['IN_ELEMENTS']
    in_man_bits = params['IN_MAN_BITS']
    out_man_bits = params['OUT_MAN_BITS']

    # Pad inputs
    while len(aligned_mans) < in_elements:
        aligned_mans.append(0)
        round_bits.append(0)
        is_zeros.append(True)

    # Drive inputs
    for i in range(in_elements):
        dut.i_aligned_mans[i].value = to_unsigned(aligned_mans[i], in_man_bits)
        dut.i_round_bits[i].value = round_bits[i]
        dut.i_is_zero[i].value = int(is_zeros[i])

    # Wait for combinational logic
    await Timer(1, units='ns')

    # Get golden results
    g_mans = gfp8_quantizer_hw(aligned_mans, round_bits, is_zeros, in_man_bits, out_man_bits)

    # Check outputs
    for i in range(len(aligned_mans)):
        if i >= in_elements:
            break
        dut_man = int(dut.o_gfp8_mans[i].value.signed_integer)
        expected = to_signed(g_mans[i], out_man_bits) if g_mans[i] >= 128 else g_mans[i]

        # Golden returns unsigned representation, convert to signed for comparison
        expected_signed = to_signed(g_mans[i], out_man_bits)

        assert dut_man == expected_signed, \
            f"Element {i} mismatch: got {dut_man}, expected {expected_signed}"


@cocotb.test()
async def test_positive_quantize(dut):
    """Test basic positive value quantization."""
    # 11-bit positive: 512 (0b01000000000)
    # Shift by 3: 512 >> 3 = 64
    aligned_mans = [512, 256, 128]
    round_bits = [0, 0, 0]
    is_zeros = [False, False, False]
    await drive_and_check(dut, aligned_mans, round_bits, is_zeros)
    dut._log.info("PASS: test_positive_quantize")


@cocotb.test()
async def test_negative_quantize(dut):
    """Test basic negative value quantization."""
    # Negative values should remain negative after quantization
    aligned_mans = [-512, -256, -128]
    round_bits = [0, 0, 0]
    is_zeros = [False, False, False]
    await drive_and_check(dut, aligned_mans, round_bits, is_zeros)

    # Verify outputs are negative
    for i in range(3):
        dut_man = int(dut.o_gfp8_mans[i].value.signed_integer)
        assert dut_man < 0, f"Element {i} should be negative, got {dut_man}"

    dut._log.info("PASS: test_negative_quantize")


@cocotb.test()
async def test_rounding_positive(dut):
    """Test rounding for positive values."""
    # With round bit = 1, value should round up
    aligned_mans = [7]  # 7 >> 3 = 0, but with rounding: (7+4) >> 3 = 1
    round_bits = [1]
    is_zeros = [False]
    await drive_and_check(dut, aligned_mans, round_bits, is_zeros)
    dut._log.info("PASS: test_rounding_positive")


@cocotb.test()
async def test_saturation_positive(dut):
    """Test positive overflow saturation."""
    # Max 11-bit signed positive = 1023
    # If aligned value is near max, quantization may saturate to 127
    aligned_mans = [1023]  # Max positive
    round_bits = [1]  # With rounding may cause overflow
    is_zeros = [False]
    await drive_and_check(dut, aligned_mans, round_bits, is_zeros)

    dut_man = int(dut.o_gfp8_mans[0].value.signed_integer)
    assert dut_man <= 127, f"Should saturate to max 127, got {dut_man}"
    dut._log.info("PASS: test_saturation_positive")


@cocotb.test()
async def test_saturation_negative(dut):
    """Test negative underflow saturation."""
    # Min 11-bit signed = -1024
    # Quantization should saturate to -128
    aligned_mans = [-1024]
    round_bits = [0]
    is_zeros = [False]
    await drive_and_check(dut, aligned_mans, round_bits, is_zeros)

    dut_man = int(dut.o_gfp8_mans[0].value.signed_integer)
    assert dut_man >= -128, f"Should saturate to min -128, got {dut_man}"
    dut._log.info("PASS: test_saturation_negative")


@cocotb.test()
async def test_zero_element(dut):
    """Test zero element passes through as zero."""
    aligned_mans = [512]  # Non-zero value but marked as zero
    round_bits = [1]
    is_zeros = [True]
    await drive_and_check(dut, aligned_mans, round_bits, is_zeros)

    dut_man = int(dut.o_gfp8_mans[0].value.signed_integer)
    assert dut_man == 0, f"Zero element should be 0, got {dut_man}"
    dut._log.info("PASS: test_zero_element")


@cocotb.test()
async def test_small_values(dut):
    """Test small values that don't need saturation."""
    # Small values: -4, 0, 4 in 11-bit
    # After >> 3: -1, 0, 0 (or with rounding: -1, 0, 1)
    aligned_mans = [-8, 0, 8]
    round_bits = [0, 0, 0]
    is_zeros = [False, False, False]
    await drive_and_check(dut, aligned_mans, round_bits, is_zeros)
    dut._log.info("PASS: test_small_values")


@cocotb.test()
async def test_mixed_values(dut):
    """Test mix of positive, negative, and zero values."""
    aligned_mans = [512, -512, 0, 100, -100]
    round_bits = [0, 0, 0, 1, 1]
    is_zeros = [False, False, True, False, False]
    await drive_and_check(dut, aligned_mans, round_bits, is_zeros)
    dut._log.info("PASS: test_mixed_values")
