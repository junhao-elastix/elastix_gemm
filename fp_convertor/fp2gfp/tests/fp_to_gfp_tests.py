"""
Cocotb testbench for fp_to_gfp module.

Tests FP to GFP conversion against Python golden reference (hw_golden.py).
Uses bitarray-based reference model for hardware-accurate comparison.
"""

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ClockCycles
import struct
import random
import math
from pathlib import Path
import sys

# Add py/ directory for hw_golden imports
py_path = Path(__file__).resolve().parent.parent / "golden_models"
if str(py_path) not in sys.path:
    sys.path.insert(0, str(py_path))

from hw_golden import (
    IEEEFormat,
    GFPFormat,
    IEEE_FP32,
    IEEE_FP16,
    IEEE_BF16,
    IEEE_FORMATS,
    fp_to_gfp_1d_hw,
    float_to_bitarray,
    bitarray_to_float,
    ba_to_int,
    ba_to_signed_int,
)


def get_dut_format(dut) -> tuple[IEEEFormat, GFPFormat]:
    """Extract format parameters from DUT."""
    fp_total_bits = int(dut.FP_TOTAL_BITS.value)
    fp_exp_bits = int(dut.FP_EXP_BITS.value)
    fp_man_bits = int(dut.FP_MAN_BITS.value)
    fp_bias = int(dut.FP_BIAS.value)
    gfp_man_bits = int(dut.GFP_MAN_BITS.value)
    gfp_exp_bits = int(dut.GFP_EXP_BITS.value)
    group_size = int(dut.GROUP_SIZE.value)

    # Identify IEEE format
    if fp_total_bits == 32:
        ieee_fmt = IEEE_FP32
    elif fp_total_bits == 16 and fp_exp_bits == 5:
        ieee_fmt = IEEE_FP16
    elif fp_total_bits == 16 and fp_exp_bits == 8:
        ieee_fmt = IEEE_BF16
    else:
        # Custom format
        ieee_fmt = IEEEFormat(
            name=f"fp{fp_total_bits}",
            total_bits=fp_total_bits,
            exp_bits=fp_exp_bits,
            mantissa_bits=fp_man_bits,
            bias=fp_bias,
        )

    gfp_fmt = GFPFormat(gfp_man_bits, gfp_exp_bits, group_size)

    return ieee_fmt, gfp_fmt


def float_to_fp_bits(val: float, fmt: IEEEFormat) -> int:
    """Convert Python float to FP integer bits."""
    if fmt.name == "fp32":
        packed = struct.pack('>f', val)
        return struct.unpack('>I', packed)[0]
    elif fmt.name == "fp16":
        packed = struct.pack('>e', val)
        return struct.unpack('>H', packed)[0]
    elif fmt.name == "bf16":
        packed = struct.pack('>f', val)
        bits32 = struct.unpack('>I', packed)[0]
        return bits32 >> 16
    else:
        raise ValueError(f"Unknown format: {fmt.name}")


def fp_bits_to_float(bits: int, fmt: IEEEFormat) -> float:
    """Convert FP integer bits to Python float."""
    if fmt.name == "fp32":
        packed = struct.pack('>I', bits)
        return struct.unpack('>f', packed)[0]
    elif fmt.name == "fp16":
        packed = struct.pack('>H', bits)
        return struct.unpack('>e', packed)[0]
    elif fmt.name == "bf16":
        bits32 = bits << 16
        packed = struct.pack('>I', bits32)
        return struct.unpack('>f', packed)[0]
    else:
        raise ValueError(f"Unknown format: {fmt.name}")


class FpToGfpTB:
    """Testbench helper class for fp_to_gfp module."""

    def __init__(self, dut):
        self.dut = dut
        self.ieee_fmt, self.gfp_fmt = get_dut_format(dut)
        self.group_size = self.gfp_fmt.group_size

    async def reset(self):
        """Reset the DUT."""
        self.dut.i_reset_n.value = 0
        self.dut.i_valid.value = 0
        self.dut.i_ready.value = 1
        self.dut.i_fp_data.value = 0
        await ClockCycles(self.dut.i_clk, 5)
        self.dut.i_reset_n.value = 1
        await ClockCycles(self.dut.i_clk, 2)

    async def send_group(self, fp_values: list[float]) -> tuple[list[int], int]:
        """
        Send a group of FP values and collect GFP output.

        Args:
            fp_values: List of GROUP_SIZE float values

        Returns:
            (mantissas, exponent): GFP output
        """
        assert len(fp_values) == self.group_size

        # Pack FP values into input data
        input_data = 0
        for i, val in enumerate(fp_values):
            bits = float_to_fp_bits(val, self.ieee_fmt)
            input_data |= bits << (i * self.ieee_fmt.total_bits)

        # Send input
        self.dut.i_fp_data.value = input_data
        self.dut.i_valid.value = 1
        await RisingEdge(self.dut.i_clk)
        self.dut.i_valid.value = 0

        # Wait for output valid (pipeline latency)
        for _ in range(10):
            await RisingEdge(self.dut.i_clk)
            if self.dut.o_valid.value == 1:
                break
        else:
            raise TimeoutError("Output valid not asserted")

        # Extract outputs
        mantissas = []
        raw_mantissa = int(self.dut.o_gfp_mantissa.value)
        for i in range(self.group_size):
            man_bits = (raw_mantissa >> (i * self.gfp_fmt.mantissa_bits)) & ((1 << self.gfp_fmt.mantissa_bits) - 1)
            # Convert to signed
            if man_bits >= (1 << (self.gfp_fmt.mantissa_bits - 1)):
                man_bits -= (1 << self.gfp_fmt.mantissa_bits)
            mantissas.append(man_bits)

        exponent = int(self.dut.o_gfp_exponent.value)

        return mantissas, exponent


@cocotb.test()
async def test_all_zeros(dut):
    """Test with all zero inputs."""
    tb = FpToGfpTB(dut)

    clock = Clock(dut.i_clk, 10, units="ns")
    cocotb.start_soon(clock.start())

    await tb.reset()

    fp_values = [0.0] * tb.group_size
    mantissas, exponent = await tb.send_group(fp_values)

    cocotb.log.info(f"Input: all zeros")
    cocotb.log.info(f"Output mantissas: {mantissas}")
    cocotb.log.info(f"Output exponent: {exponent}")

    # All mantissas should be zero
    assert all(m == 0 for m in mantissas), f"Expected all zeros, got {mantissas}"
    assert exponent == 0, f"Expected exponent 0, got {exponent}"

    cocotb.log.info("TEST PASSED: All zeros")


@cocotb.test()
async def test_all_ones(dut):
    """Test with all 1.0 inputs."""
    tb = FpToGfpTB(dut)

    clock = Clock(dut.i_clk, 10, units="ns")
    cocotb.start_soon(clock.start())

    await tb.reset()

    fp_values = [1.0] * tb.group_size

    # Get golden reference
    input_bits = [float_to_bitarray(f, tb.ieee_fmt) for f in fp_values]
    gold_mantissas, gold_exponents = fp_to_gfp_1d_hw(input_bits, tb.ieee_fmt, tb.gfp_fmt)
    gold_man = [ba_to_signed_int(m) for m in gold_mantissas[0]]
    gold_exp = ba_to_int(gold_exponents[0])

    # Run DUT
    mantissas, exponent = await tb.send_group(fp_values)

    cocotb.log.info(f"Input: all 1.0")
    cocotb.log.info(f"DUT mantissas: {mantissas}")
    cocotb.log.info(f"DUT exponent:  {exponent}")
    cocotb.log.info(f"Golden mantissas: {gold_man}")
    cocotb.log.info(f"Golden exponent:  {gold_exp}")

    # Compare
    assert mantissas == gold_man, f"Mantissa mismatch: DUT={mantissas}, Golden={gold_man}"
    assert exponent == gold_exp, f"Exponent mismatch: DUT={exponent}, Golden={gold_exp}"

    cocotb.log.info("TEST PASSED: All ones")


@cocotb.test()
async def test_mixed_values(dut):
    """Test with mixed positive values."""
    tb = FpToGfpTB(dut)

    clock = Clock(dut.i_clk, 10, units="ns")
    cocotb.start_soon(clock.start())

    await tb.reset()

    # Generate test values: 1, 2, 3, ..., group_size
    fp_values = [float(i + 1) for i in range(tb.group_size)]

    # Get golden reference
    input_bits = [float_to_bitarray(f, tb.ieee_fmt) for f in fp_values]
    gold_mantissas, gold_exponents = fp_to_gfp_1d_hw(input_bits, tb.ieee_fmt, tb.gfp_fmt)
    gold_man = [ba_to_signed_int(m) for m in gold_mantissas[0]]
    gold_exp = ba_to_int(gold_exponents[0])

    # Run DUT
    mantissas, exponent = await tb.send_group(fp_values)

    cocotb.log.info(f"Input: {fp_values}")
    cocotb.log.info(f"DUT mantissas: {mantissas}")
    cocotb.log.info(f"DUT exponent:  {exponent}")
    cocotb.log.info(f"Golden mantissas: {gold_man}")
    cocotb.log.info(f"Golden exponent:  {gold_exp}")

    # Compare
    assert mantissas == gold_man, f"Mantissa mismatch: DUT={mantissas}, Golden={gold_man}"
    assert exponent == gold_exp, f"Exponent mismatch: DUT={exponent}, Golden={gold_exp}"

    cocotb.log.info("TEST PASSED: Mixed values")


@cocotb.test()
async def test_negative_values(dut):
    """Test with negative values."""
    tb = FpToGfpTB(dut)

    clock = Clock(dut.i_clk, 10, units="ns")
    cocotb.start_soon(clock.start())

    await tb.reset()

    # Mix of positive and negative
    fp_values = [(-1.0) ** i * (i + 1) for i in range(tb.group_size)]

    # Get golden reference
    input_bits = [float_to_bitarray(f, tb.ieee_fmt) for f in fp_values]
    gold_mantissas, gold_exponents = fp_to_gfp_1d_hw(input_bits, tb.ieee_fmt, tb.gfp_fmt)
    gold_man = [ba_to_signed_int(m) for m in gold_mantissas[0]]
    gold_exp = ba_to_int(gold_exponents[0])

    # Run DUT
    mantissas, exponent = await tb.send_group(fp_values)

    cocotb.log.info(f"Input: {fp_values}")
    cocotb.log.info(f"DUT mantissas: {mantissas}")
    cocotb.log.info(f"DUT exponent:  {exponent}")
    cocotb.log.info(f"Golden mantissas: {gold_man}")
    cocotb.log.info(f"Golden exponent:  {gold_exp}")

    # Compare
    assert mantissas == gold_man, f"Mantissa mismatch: DUT={mantissas}, Golden={gold_man}"
    assert exponent == gold_exp, f"Exponent mismatch: DUT={exponent}, Golden={gold_exp}"

    cocotb.log.info("TEST PASSED: Negative values")


@cocotb.test()
async def test_random_values(dut):
    """Test with random values."""
    tb = FpToGfpTB(dut)

    clock = Clock(dut.i_clk, 10, units="ns")
    cocotb.start_soon(clock.start())

    await tb.reset()

    # Use fixed seed for reproducibility
    random.seed(42)

    # Generate random values with std=1.0
    fp_values = [random.gauss(0, 1.0) for _ in range(tb.group_size)]

    # Round-trip through FP format to get exact stored values
    fp_values = [fp_bits_to_float(float_to_fp_bits(f, tb.ieee_fmt), tb.ieee_fmt) for f in fp_values]

    # Get golden reference
    input_bits = [float_to_bitarray(f, tb.ieee_fmt) for f in fp_values]
    gold_mantissas, gold_exponents = fp_to_gfp_1d_hw(input_bits, tb.ieee_fmt, tb.gfp_fmt)
    gold_man = [ba_to_signed_int(m) for m in gold_mantissas[0]]
    gold_exp = ba_to_int(gold_exponents[0])

    # Run DUT
    mantissas, exponent = await tb.send_group(fp_values)

    cocotb.log.info(f"Input (random): {[f'{v:.4f}' for v in fp_values]}")
    cocotb.log.info(f"DUT mantissas: {mantissas}")
    cocotb.log.info(f"DUT exponent:  {exponent}")
    cocotb.log.info(f"Golden mantissas: {gold_man}")
    cocotb.log.info(f"Golden exponent:  {gold_exp}")

    # Compare
    assert mantissas == gold_man, f"Mantissa mismatch: DUT={mantissas}, Golden={gold_man}"
    assert exponent == gold_exp, f"Exponent mismatch: DUT={exponent}, Golden={gold_exp}"

    cocotb.log.info("TEST PASSED: Random values")


@cocotb.test()
async def test_large_values(dut):
    """Test with large magnitude values."""
    tb = FpToGfpTB(dut)

    clock = Clock(dut.i_clk, 10, units="ns")
    cocotb.start_soon(clock.start())

    await tb.reset()

    # Large values (100-1000 range)
    fp_values = [100.0 * (i + 1) for i in range(tb.group_size)]

    # Round-trip
    fp_values = [fp_bits_to_float(float_to_fp_bits(f, tb.ieee_fmt), tb.ieee_fmt) for f in fp_values]

    # Get golden reference
    input_bits = [float_to_bitarray(f, tb.ieee_fmt) for f in fp_values]
    gold_mantissas, gold_exponents = fp_to_gfp_1d_hw(input_bits, tb.ieee_fmt, tb.gfp_fmt)
    gold_man = [ba_to_signed_int(m) for m in gold_mantissas[0]]
    gold_exp = ba_to_int(gold_exponents[0])

    # Run DUT
    mantissas, exponent = await tb.send_group(fp_values)

    cocotb.log.info(f"Input (large): {fp_values}")
    cocotb.log.info(f"DUT mantissas: {mantissas}")
    cocotb.log.info(f"DUT exponent:  {exponent}")
    cocotb.log.info(f"Golden mantissas: {gold_man}")
    cocotb.log.info(f"Golden exponent:  {gold_exp}")

    # Compare
    assert mantissas == gold_man, f"Mantissa mismatch: DUT={mantissas}, Golden={gold_man}"
    assert exponent == gold_exp, f"Exponent mismatch: DUT={exponent}, Golden={gold_exp}"

    cocotb.log.info("TEST PASSED: Large values")


@cocotb.test()
async def test_small_values(dut):
    """Test with small magnitude values."""
    tb = FpToGfpTB(dut)

    clock = Clock(dut.i_clk, 10, units="ns")
    cocotb.start_soon(clock.start())

    await tb.reset()

    # Small values (0.001 - 0.01 range)
    fp_values = [0.001 * (i + 1) for i in range(tb.group_size)]

    # Round-trip
    fp_values = [fp_bits_to_float(float_to_fp_bits(f, tb.ieee_fmt), tb.ieee_fmt) for f in fp_values]

    # Get golden reference
    input_bits = [float_to_bitarray(f, tb.ieee_fmt) for f in fp_values]
    gold_mantissas, gold_exponents = fp_to_gfp_1d_hw(input_bits, tb.ieee_fmt, tb.gfp_fmt)
    gold_man = [ba_to_signed_int(m) for m in gold_mantissas[0]]
    gold_exp = ba_to_int(gold_exponents[0])

    # Run DUT
    mantissas, exponent = await tb.send_group(fp_values)

    cocotb.log.info(f"Input (small): {[f'{v:.6f}' for v in fp_values]}")
    cocotb.log.info(f"DUT mantissas: {mantissas}")
    cocotb.log.info(f"DUT exponent:  {exponent}")
    cocotb.log.info(f"Golden mantissas: {gold_man}")
    cocotb.log.info(f"Golden exponent:  {gold_exp}")

    # Compare
    assert mantissas == gold_man, f"Mantissa mismatch: DUT={mantissas}, Golden={gold_man}"
    assert exponent == gold_exp, f"Exponent mismatch: DUT={exponent}, Golden={gold_exp}"

    cocotb.log.info("TEST PASSED: Small values")


@cocotb.test()
async def test_multiple_groups(dut):
    """Test multiple consecutive groups."""
    tb = FpToGfpTB(dut)

    clock = Clock(dut.i_clk, 10, units="ns")
    cocotb.start_soon(clock.start())

    await tb.reset()

    num_groups = 4
    errors = 0

    for g in range(num_groups):
        random.seed(100 + g)
        fp_values = [random.gauss(0, 1.0) for _ in range(tb.group_size)]
        fp_values = [fp_bits_to_float(float_to_fp_bits(f, tb.ieee_fmt), tb.ieee_fmt) for f in fp_values]

        # Get golden
        input_bits = [float_to_bitarray(f, tb.ieee_fmt) for f in fp_values]
        gold_mantissas, gold_exponents = fp_to_gfp_1d_hw(input_bits, tb.ieee_fmt, tb.gfp_fmt)
        gold_man = [ba_to_signed_int(m) for m in gold_mantissas[0]]
        gold_exp = ba_to_int(gold_exponents[0])

        # Run DUT
        mantissas, exponent = await tb.send_group(fp_values)

        if mantissas != gold_man or exponent != gold_exp:
            cocotb.log.error(f"Group {g} mismatch:")
            cocotb.log.error(f"  DUT: man={mantissas}, exp={exponent}")
            cocotb.log.error(f"  Golden: man={gold_man}, exp={gold_exp}")
            errors += 1
        else:
            cocotb.log.info(f"Group {g}: OK")

    assert errors == 0, f"Failed {errors}/{num_groups} groups"
    cocotb.log.info(f"TEST PASSED: Multiple groups ({num_groups} groups)")
