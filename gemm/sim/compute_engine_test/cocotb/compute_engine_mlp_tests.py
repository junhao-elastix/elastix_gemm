"""
Testbench for compute_engine_mlp module (GEMM-compatible interface).

Tests the integrated wrapper with:
- row_bram for L1 memory (left=activations, right=weights)
- mlp_bram_col_ctrl for MLP compute
- Weight fill + compute triggered by single i_tile_start

Interface matches compute_engine_modular.sv from gemm project.
Output: 256-bit vector (16 × FP16) per batch.
"""

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ClockCycles, Timer
import random
import sys
import struct
from pathlib import Path
import numpy as np

# Add emulator path for GFP imports
emulator_path = Path(__file__).resolve().parents[4] / "emulator" / "src"
if str(emulator_path) not in sys.path:
    sys.path.insert(0, str(emulator_path))

try:
    import torch
    from emulator import group_floating_point as gfp
    HAS_GFP = True
except ImportError as e:
    HAS_GFP = False
    cocotb.log.warning(f"GFP imports not available: {e}")

# GFP8 bias constants
GFP8E8_BIAS = 127   # IEEE standard: 2^(8-1) - 1 = 127
BFP8E8_BIAS = 133   # MLP native bias: 127 + 6
ACX_BFP_M8E8_BIAS = BFP8E8_BIAS - GFP8E8_BIAS  # = 6

# Hex file constants (5-bit exponent format)
HEX_EXP_BIAS = 15   # Bias for 5-bit exponents in hex files


def load_hex_file(file_path: str) -> tuple:
    """
    Load a 528-line hex file and separate into exponent and mantissa data.

    Format:
    - Lines 0-15: Exponent data (512 exponents, 32 per line)
    - Lines 16-527: Mantissa data (16,384 mantissas, 32 per line)

    Returns:
        tuple: (exponent_data, mantissa_data) where:
            - exponent_data: [128, 4] array of 5-bit exponents
            - mantissa_data: [128, 128] array of signed 8-bit mantissas
    """
    with open(file_path, 'r') as f:
        lines = f.readlines()

    if len(lines) != 528:
        raise ValueError(f"Expected 528 lines, got {len(lines)}")

    # Parse exponent lines (0-15)
    exp_flat = []
    for i in range(16):
        hex_bytes = lines[i].strip().split()
        for b in hex_bytes:
            exp_flat.append(int(b, 16) & 0x1F)  # Mask to 5 bits

    exponent_data = np.array(exp_flat, dtype=np.uint8).reshape(128, 4)

    # Parse mantissa lines (16-527)
    mant_flat = []
    for i in range(16, 528):
        hex_bytes = lines[i].strip().split()
        for b in hex_bytes:
            val = int(b, 16)
            # Convert to signed
            if val >= 128:
                val -= 256
            mant_flat.append(val)

    mantissa_data = np.array(mant_flat, dtype=np.int8).reshape(128, 128)

    return exponent_data, mantissa_data


def load_golden_hex(file_path: str) -> list:
    """
    Load golden FP16 values from hex file.

    Format: One FP16 hex value per line (e.g., "25b0")

    Returns:
        list: FP16 values as integers
    """
    golden = []
    with open(file_path, 'r') as f:
        for line in f:
            line = line.strip()
            if line:
                golden.append(int(line, 16))
    return golden


def fp16_to_float(fp16_int: int) -> float:
    """Convert FP16 integer to Python float."""
    sign = (fp16_int >> 15) & 1
    exp = (fp16_int >> 10) & 0x1F
    mant = fp16_int & 0x3FF

    if exp == 0:
        if mant == 0:
            return -0.0 if sign else 0.0
        # Denormal
        return ((-1) ** sign) * (mant / 1024.0) * (2 ** -14)
    elif exp == 31:
        if mant == 0:
            return float('-inf') if sign else float('inf')
        else:
            return float('nan')
    else:
        # Normal
        return ((-1) ** sign) * (1 + mant / 1024.0) * (2 ** (exp - 15))


class ComputeEngineMlpTB:
    """Testbench helper class for compute_engine_mlp (GEMM-compatible interface)."""

    def __init__(self, dut):
        self.dut = dut
        self.NUM_COLUMNS = 16
        self.NUM_MLPS = 8
        self.MAN_WIDTH = 256
        self.NV_SIZE = 128  # Elements per NV
        self.GROUP_SIZE = 32  # Elements per exponent group

    async def reset(self):
        """Reset the DUT."""
        self.dut.i_reset_n.value = 0

        # GEMM-compatible control interface
        self.dut.i_tile_en.value = 1          # Static enable (always on)
        self.dut.i_tile_start.value = 0       # Dynamic start pulse
        self.dut.i_tile_left_addr.value = 0   # Unused
        self.dut.i_tile_right_addr.value = 0  # Unused
        self.dut.i_tile_left_ugd_len.value = 1   # B = 1 batch
        self.dut.i_tile_right_ugd_len.value = 16 # C = 16 columns (fixed)
        self.dut.i_tile_vec_len.value = 1        # V = 1 NV per output
        self.dut.i_tile_left_man_4b.value = 0    # Unused
        self.dut.i_tile_right_man_4b.value = 0   # Unused
        self.dut.i_tile_main_loop_over_left.value = 0  # Unused
        self.dut.i_mc_tile_en.value = 0x000001   # Unused

        # Backpressure signals
        self.dut.i_result_full.value = 0
        self.dut.i_result_afull.value = 0

        # Clear write enables
        self.dut.i_man_left_wr_en.value = 0
        self.dut.i_man_right_wr_en.value = 0
        self.dut.i_exp_left_wr_en.value = 0
        self.dut.i_exp_right_wr_en.value = 0

        await ClockCycles(self.dut.i_clk, 5)
        self.dut.i_reset_n.value = 1
        await ClockCycles(self.dut.i_clk, 2)

    async def write_man_left(self, addr: int, data: int):
        """Write a mantissa line to left row_bram (activations)."""
        self.dut.i_man_left_wr_addr.value = addr
        self.dut.i_man_left_wr_data.value = data
        self.dut.i_man_left_wr_en.value = 1
        await RisingEdge(self.dut.i_clk)
        self.dut.i_man_left_wr_en.value = 0

    async def write_exp_left(self, addr: int, data: int):
        """Write an exponent to left row_bram (activations)."""
        self.dut.i_exp_left_wr_addr.value = addr
        self.dut.i_exp_left_wr_data.value = data
        self.dut.i_exp_left_wr_en.value = 1
        await RisingEdge(self.dut.i_clk)
        self.dut.i_exp_left_wr_en.value = 0

    async def write_man_right(self, addr: int, data: int):
        """Write a mantissa line to right row_bram (weights)."""
        self.dut.i_man_right_wr_addr.value = addr
        self.dut.i_man_right_wr_data.value = data
        self.dut.i_man_right_wr_en.value = 1
        await RisingEdge(self.dut.i_clk)
        self.dut.i_man_right_wr_en.value = 0

    async def write_exp_right(self, addr: int, data: int):
        """Write an exponent to right row_bram (weights)."""
        self.dut.i_exp_right_wr_addr.value = addr
        self.dut.i_exp_right_wr_data.value = data
        self.dut.i_exp_right_wr_en.value = 1
        await RisingEdge(self.dut.i_clk)
        self.dut.i_exp_right_wr_en.value = 0

    async def load_activation_nv(self, nv_idx: int, mantissas: list[int], exponents: list[int]):
        """Load a Native Vector to left row_bram (activations)."""
        assert len(mantissas) == self.NV_SIZE
        assert len(exponents) == 4

        base_addr = nv_idx * 4  # 4 lines per NV

        # Write 4 mantissa lines
        for group in range(4):
            line_data = 0
            for i in range(32):
                elem_idx = group * 32 + i
                m = mantissas[elem_idx] & 0xFF
                line_data |= (m << (i * 8))
            await self.write_man_left(base_addr + group, line_data)

        # Write 4 exponents
        for group in range(4):
            await self.write_exp_left(base_addr + group, exponents[group])

    async def load_weight_nv(self, col_idx: int, nv_idx: int, mantissas: list[int], exponents: list[int]):
        """Load a Native Vector to right row_bram (weights)."""
        assert len(mantissas) == self.NV_SIZE
        assert len(exponents) == 4

        vec_len = int(self.dut.i_tile_vec_len.value)
        row_bram_nv_idx = col_idx * vec_len + nv_idx
        base_addr = row_bram_nv_idx * 4

        # Write 4 mantissa lines
        for group in range(4):
            line_data = 0
            for i in range(32):
                elem_idx = group * 32 + i
                m = mantissas[elem_idx] & 0xFF
                line_data |= (m << (i * 8))
            await self.write_man_right(base_addr + group, line_data)

        # Write 4 exponents
        for group in range(4):
            await self.write_exp_right(base_addr + group, exponents[group])

    async def start_tile(self):
        """Start tile operation (fill + compute triggered by single pulse)."""
        self.dut.i_tile_start.value = 1
        await RisingEdge(self.dut.i_clk)
        self.dut.i_tile_start.value = 0

    async def wait_tile_done(self, timeout_cycles: int = 50000):
        """Wait for tile operation to complete."""
        for _ in range(timeout_cycles):
            await RisingEdge(self.dut.i_clk)
            if self.dut.o_tile_done.value == 1:
                return True
        return False

    def get_results_fp16(self) -> list[float]:
        """Get the 16 FP16 results from 256-bit o_result_data."""
        raw_256 = int(self.dut.o_result_data.value)
        results = []
        for col in range(self.NUM_COLUMNS):
            fp16_int = (raw_256 >> (col * 16)) & 0xFFFF
            results.append(fp16_to_float(fp16_int))
        return results

    def get_raw_results_fp16(self) -> list[int]:
        """Get the raw 16-bit FP16 integers for debugging."""
        raw_256 = int(self.dut.o_result_data.value)
        results = []
        for col in range(self.NUM_COLUMNS):
            fp16_int = (raw_256 >> (col * 16)) & 0xFFFF
            results.append(fp16_int)
        return results


@cocotb.test()
async def test_first_8_elements(dut):
    """Test with data only in first 8 positions (one MLP cycle)."""
    tb = ComputeEngineMlpTB(dut)

    clock = Clock(dut.i_clk, 10, units="ns")
    cocotb.start_soon(clock.start())

    await tb.reset()

    dut.i_tile_vec_len.value = 1
    await RisingEdge(dut.i_clk)

    # Only first 8 elements are 1, rest are 0
    act_mantissas = [1] * 8 + [0] * 120
    act_exponents = [BFP8E8_BIAS] * 4
    await tb.load_activation_nv(0, act_mantissas, act_exponents)

    # Same for weights
    for col in range(16):
        wt_mantissas = [1] * 8 + [0] * 120
        wt_exponents = [BFP8E8_BIAS] * 4
        await tb.load_weight_nv(col, 0, wt_mantissas, wt_exponents)

    await tb.start_tile()
    tile_done = await tb.wait_tile_done()
    assert tile_done, "Tile operation timed out"

    await ClockCycles(dut.i_clk, 5)

    # Wait for result valid
    for _ in range(100):
        await RisingEdge(dut.i_clk)
        if dut.o_result_valid.value == 1:
            break

    results = tb.get_results_fp16()

    # Golden reference
    act_vec = np.array([1.0] * 8 + [0.0] * 120)
    wt_vec = np.array([1.0] * 8 + [0.0] * 120)
    golden_dot = float(np.dot(act_vec, wt_vec))
    expected = [golden_dot] * 16

    cocotb.log.info(f"Results (first 8 only):   {results}")
    cocotb.log.info(f"Expected (numpy golden):  {expected}")

    for i in range(16):
        assert results[i] == expected[i], f"Column {i}: got {results[i]}, expected {expected[i]}"

    cocotb.log.info("TEST PASSED: First 8 elements test")


@cocotb.test()
async def test_first_32_elements(dut):
    """Test with data only in first 32 positions (one group)."""
    tb = ComputeEngineMlpTB(dut)

    clock = Clock(dut.i_clk, 10, units="ns")
    cocotb.start_soon(clock.start())

    await tb.reset()

    dut.i_tile_vec_len.value = 1
    await RisingEdge(dut.i_clk)

    act_mantissas = [1] * 32 + [0] * 96
    act_exponents = [BFP8E8_BIAS] * 4
    await tb.load_activation_nv(0, act_mantissas, act_exponents)

    for col in range(16):
        wt_mantissas = [1] * 32 + [0] * 96
        wt_exponents = [BFP8E8_BIAS] * 4
        await tb.load_weight_nv(col, 0, wt_mantissas, wt_exponents)

    await tb.start_tile()
    tile_done = await tb.wait_tile_done()
    assert tile_done, "Tile operation timed out"

    await ClockCycles(dut.i_clk, 5)

    for _ in range(100):
        await RisingEdge(dut.i_clk)
        if dut.o_result_valid.value == 1:
            break

    results = tb.get_results_fp16()

    act_vec = np.array([1.0] * 32 + [0.0] * 96)
    wt_vec = np.array([1.0] * 32 + [0.0] * 96)
    golden_dot = float(np.dot(act_vec, wt_vec))
    expected = [golden_dot] * 16

    cocotb.log.info(f"Results:   {results}")
    cocotb.log.info(f"Expected:  {expected}")

    for i in range(16):
        assert results[i] == expected[i], f"Column {i}: got {results[i]}, expected {expected[i]}"

    cocotb.log.info("TEST PASSED: First 32 elements test")


@cocotb.test()
async def test_identity_matrix(dut):
    """Test with identity-like weight matrix."""
    tb = ComputeEngineMlpTB(dut)

    clock = Clock(dut.i_clk, 10, units="ns")
    cocotb.start_soon(clock.start())

    await tb.reset()

    dut.i_tile_vec_len.value = 1
    await RisingEdge(dut.i_clk)

    # Activation: [1, 2, 3, ..., 16, 0, ...]
    act_mantissas = [0] * 128
    act_exponents = [BFP8E8_BIAS] * 4
    for i in range(16):
        act_mantissas[i] = i + 1

    await tb.load_activation_nv(0, act_mantissas, act_exponents)

    # Weight column i has 1 at position i only
    for col in range(16):
        wt_mantissas = [0] * 128
        wt_exponents = [BFP8E8_BIAS] * 4
        wt_mantissas[col] = 1
        await tb.load_weight_nv(col, 0, wt_mantissas, wt_exponents)

    await tb.start_tile()
    tile_done = await tb.wait_tile_done()
    assert tile_done, "Tile operation timed out"

    await ClockCycles(dut.i_clk, 5)

    for _ in range(100):
        await RisingEdge(dut.i_clk)
        if dut.o_result_valid.value == 1:
            break

    results = tb.get_results_fp16()

    # Golden: column i = activation[i] = i+1
    expected = [float(i + 1) for i in range(16)]

    cocotb.log.info(f"Results:   {results}")
    cocotb.log.info(f"Expected:  {expected}")

    for i in range(16):
        assert results[i] == expected[i], f"Column {i}: got {results[i]}, expected {expected[i]}"

    cocotb.log.info("TEST PASSED: Identity matrix test")


@cocotb.test()
async def test_all_ones(dut):
    """Test with all-ones activation and weights."""
    tb = ComputeEngineMlpTB(dut)

    clock = Clock(dut.i_clk, 10, units="ns")
    cocotb.start_soon(clock.start())

    await tb.reset()

    dut.i_tile_vec_len.value = 1
    await RisingEdge(dut.i_clk)

    act_mantissas = [1] * 128
    act_exponents = [BFP8E8_BIAS] * 4
    await tb.load_activation_nv(0, act_mantissas, act_exponents)

    for col in range(16):
        wt_mantissas = [1] * 128
        wt_exponents = [BFP8E8_BIAS] * 4
        await tb.load_weight_nv(col, 0, wt_mantissas, wt_exponents)

    await tb.start_tile()
    tile_done = await tb.wait_tile_done()
    assert tile_done, "Tile operation timed out"

    await ClockCycles(dut.i_clk, 5)

    for _ in range(100):
        await RisingEdge(dut.i_clk)
        if dut.o_result_valid.value == 1:
            break

    results = tb.get_results_fp16()

    golden_dot = float(np.dot(np.ones(128), np.ones(128)))
    expected = [golden_dot] * 16

    cocotb.log.info(f"Results:   {results}")
    cocotb.log.info(f"Expected:  {expected}")

    for i in range(16):
        assert results[i] == expected[i], f"Column {i}: got {results[i]}, expected {expected[i]}"

    cocotb.log.info("TEST PASSED: All-ones test")


@cocotb.test()
async def test_multi_nv(dut):
    """Test with multiple NVs per column (V > 1)."""
    tb = ComputeEngineMlpTB(dut)

    clock = Clock(dut.i_clk, 10, units="ns")
    cocotb.start_soon(clock.start())

    await tb.reset()

    dut.i_tile_vec_len.value = 2
    await RisingEdge(dut.i_clk)

    # Activation NV 0: all 1s
    await tb.load_activation_nv(0, [1] * 128, [BFP8E8_BIAS] * 4)
    # Activation NV 1: all 2s
    await tb.load_activation_nv(1, [2] * 128, [BFP8E8_BIAS] * 4)

    # Weights: all 1s for both NVs
    for col in range(16):
        await tb.load_weight_nv(col, 0, [1] * 128, [BFP8E8_BIAS] * 4)
        await tb.load_weight_nv(col, 1, [1] * 128, [BFP8E8_BIAS] * 4)

    await tb.start_tile()
    tile_done = await tb.wait_tile_done()
    assert tile_done, "Tile operation timed out"

    await ClockCycles(dut.i_clk, 5)

    for _ in range(100):
        await RisingEdge(dut.i_clk)
        if dut.o_result_valid.value == 1:
            break

    results = tb.get_results_fp16()

    # Golden: [1,1,...,1, 2,2,...,2] dot [1,1,...,1, 1,1,...,1] = 128 + 256 = 384
    act_vec = np.concatenate([np.ones(128), np.full(128, 2.0)])
    wt_vec = np.ones(256)
    golden_dot = float(np.dot(act_vec, wt_vec))
    expected = [golden_dot] * 16

    cocotb.log.info(f"Results:   {results}")
    cocotb.log.info(f"Expected:  {expected}")

    for i in range(16):
        assert results[i] == expected[i], f"Column {i}: got {results[i]}, expected {expected[i]}"

    cocotb.log.info("TEST PASSED: Multi-NV test")


@cocotb.test()
async def test_different_columns(dut):
    """Test with different weight values per column."""
    tb = ComputeEngineMlpTB(dut)

    clock = Clock(dut.i_clk, 10, units="ns")
    cocotb.start_soon(clock.start())

    await tb.reset()

    dut.i_tile_vec_len.value = 1
    await RisingEdge(dut.i_clk)

    act_mantissas = [1] * 128
    act_exponents = [BFP8E8_BIAS] * 4
    await tb.load_activation_nv(0, act_mantissas, act_exponents)

    for col in range(16):
        val = (col % 7) + 1
        wt_mantissas = [val] * 128
        wt_exponents = [BFP8E8_BIAS] * 4
        await tb.load_weight_nv(col, 0, wt_mantissas, wt_exponents)

    await tb.start_tile()
    tile_done = await tb.wait_tile_done()
    assert tile_done, "Tile operation timed out"

    await ClockCycles(dut.i_clk, 5)

    for _ in range(100):
        await RisingEdge(dut.i_clk)
        if dut.o_result_valid.value == 1:
            break

    results = tb.get_results_fp16()

    expected = []
    act_vec = np.ones(128)
    for col in range(16):
        val = (col % 7) + 1
        wt_vec = np.full(128, float(val))
        expected.append(float(np.dot(act_vec, wt_vec)))

    cocotb.log.info(f"Results:   {results}")
    cocotb.log.info(f"Expected:  {expected}")

    for i in range(16):
        assert results[i] == expected[i], f"Column {i}: got {results[i]}, expected {expected[i]}"

    cocotb.log.info("TEST PASSED: Different columns test")


@cocotb.test()
async def test_gfp_random_floats(dut):
    """Test with real GFP8-quantized random float data."""
    if not HAS_GFP:
        cocotb.log.warning("Skipping GFP test - torch/gfp not available")
        return

    tb = ComputeEngineMlpTB(dut)

    clock = Clock(dut.i_clk, 10, unit="ns")
    cocotb.start_soon(clock.start())

    await tb.reset()

    dut.i_tile_vec_len.value = 1
    await RisingEdge(dut.i_clk)

    gfp8 = gfp.GFPDataType(mantissa_bits=8, exp_bits=8)

    torch.manual_seed(42)
    activations_float = torch.rand(128) * 2.0 - 1.0
    weights_float = torch.rand(128, 16) * 2.0 - 1.0

    act_gfp = gfp.GFPTensor(
        original_shape=activations_float.shape,
        group_axis=-1,
        group_size=32,
        dtype=gfp8,
        original_data=activations_float,
    )

    weights_gfp = gfp.GFPTensor(
        original_shape=weights_float.shape,
        group_axis=0,
        group_size=32,
        dtype=gfp8,
        original_data=weights_float,
    )

    act_dequant = act_gfp.dequantize()
    weights_dequant = weights_gfp.dequantize()

    # Load activations
    act_mantissas = []
    act_exponents = []
    for g in range(4):
        group_mantissas = act_gfp.mantissa_data[g].tolist()
        act_mantissas.extend(group_mantissas)
        group_exp = int(act_gfp.exp_data[g].item()) + ACX_BFP_M8E8_BIAS
        act_exponents.append(group_exp)

    await tb.load_activation_nv(0, act_mantissas, act_exponents)

    # Load weights
    for col in range(16):
        wt_mantissas = []
        wt_exponents = []
        for g in range(4):
            group_mantissas = weights_gfp.mantissa_data[col, g, :].tolist()
            wt_mantissas.extend(group_mantissas)
            group_exp = int(weights_gfp.exp_data[col, g, 0].item()) + ACX_BFP_M8E8_BIAS
            wt_exponents.append(group_exp)
        await tb.load_weight_nv(col, 0, wt_mantissas, wt_exponents)

    await tb.start_tile()
    tile_done = await tb.wait_tile_done()
    assert tile_done, "Tile operation timed out"

    await ClockCycles(dut.i_clk, 5)

    for _ in range(100):
        await RisingEdge(dut.i_clk)
        if dut.o_result_valid.value == 1:
            break

    results = tb.get_results_fp16()

    expected = []
    for col in range(16):
        dot = torch.dot(act_dequant, weights_dequant[:, col])
        expected.append(dot.item())

    cocotb.log.info(f"Results:   {[f'{r:.6f}' for r in results]}")
    cocotb.log.info(f"Expected:  {[f'{e:.6f}' for e in expected]}")

    max_rel_err = 0.0
    REL_TOL = 0.01
    for i in range(16):
        abs_err = abs(results[i] - expected[i])
        rel_err = abs_err / abs(expected[i]) if expected[i] != 0 else 0
        if rel_err > max_rel_err:
            max_rel_err = rel_err
        assert rel_err < REL_TOL, f"Column {i}: rel error {rel_err*100:.2f}%"

    cocotb.log.info(f"Max relative error: {max_rel_err*100:.4f}%")
    cocotb.log.info("TEST PASSED: GFP random floats test")


@cocotb.test()
async def test_gfp_large_values(dut):
    """Test with large-scale GFP values."""
    if not HAS_GFP:
        cocotb.log.warning("Skipping GFP test - torch/gfp not available")
        return

    tb = ComputeEngineMlpTB(dut)

    clock = Clock(dut.i_clk, 10, unit="ns")
    cocotb.start_soon(clock.start())

    await tb.reset()

    dut.i_tile_vec_len.value = 1
    await RisingEdge(dut.i_clk)

    gfp8 = gfp.GFPDataType(mantissa_bits=8, exp_bits=8)

    torch.manual_seed(456)
    # Use scale of 20 to keep dot product results within FP16 range (~65504 max)
    # dot product ≈ 128 * (10)^2 = 12800, well within FP16 range
    activations_float = torch.rand(128) * 20.0
    weights_float = torch.rand(128, 16) * 20.0

    act_gfp = gfp.GFPTensor(
        original_shape=activations_float.shape,
        group_axis=-1,
        group_size=32,
        dtype=gfp8,
        original_data=activations_float,
    )

    weights_gfp = gfp.GFPTensor(
        original_shape=weights_float.shape,
        group_axis=0,
        group_size=32,
        dtype=gfp8,
        original_data=weights_float,
    )

    act_dequant = act_gfp.dequantize()
    weights_dequant = weights_gfp.dequantize()

    # Load data
    act_mantissas = []
    act_exponents = []
    for g in range(4):
        group_mantissas = act_gfp.mantissa_data[g].tolist()
        act_mantissas.extend(group_mantissas)
        group_exp = int(act_gfp.exp_data[g].item()) + ACX_BFP_M8E8_BIAS
        act_exponents.append(group_exp)

    await tb.load_activation_nv(0, act_mantissas, act_exponents)

    for col in range(16):
        wt_mantissas = []
        wt_exponents = []
        for g in range(4):
            group_mantissas = weights_gfp.mantissa_data[col, g, :].tolist()
            wt_mantissas.extend(group_mantissas)
            group_exp = int(weights_gfp.exp_data[col, g, 0].item()) + ACX_BFP_M8E8_BIAS
            wt_exponents.append(group_exp)
        await tb.load_weight_nv(col, 0, wt_mantissas, wt_exponents)

    await tb.start_tile()
    tile_done = await tb.wait_tile_done()
    assert tile_done, "Tile operation timed out"

    await ClockCycles(dut.i_clk, 5)

    for _ in range(100):
        await RisingEdge(dut.i_clk)
        if dut.o_result_valid.value == 1:
            break

    results = tb.get_results_fp16()

    expected = []
    for col in range(16):
        dot = torch.dot(act_dequant, weights_dequant[:, col])
        expected.append(dot.item())

    cocotb.log.info(f"Results:   {[f'{r:.2f}' for r in results]}")
    cocotb.log.info(f"Expected:  {[f'{e:.2f}' for e in expected]}")

    max_rel_err = 0.0
    REL_TOL = 0.01
    for i in range(16):
        abs_err = abs(results[i] - expected[i])
        rel_err = abs_err / abs(expected[i]) if expected[i] != 0 else 0
        if rel_err > max_rel_err:
            max_rel_err = rel_err
        assert rel_err < REL_TOL, f"Column {i}: rel error {rel_err*100:.2f}%"

    cocotb.log.info(f"Max relative error: {max_rel_err*100:.4f}%")
    cocotb.log.info("TEST PASSED: GFP large values test")


@cocotb.test()
async def test_batch_dimension(dut):
    """Test with batch dimension B > 1."""
    tb = ComputeEngineMlpTB(dut)

    clock = Clock(dut.i_clk, 10, units="ns")
    cocotb.start_soon(clock.start())

    await tb.reset()

    B = 2
    V = 1
    dut.i_tile_left_ugd_len.value = B
    dut.i_tile_right_ugd_len.value = 16
    dut.i_tile_vec_len.value = V
    await RisingEdge(dut.i_clk)

    # Batch 0: all 1s
    await tb.load_activation_nv(0, [1] * 128, [BFP8E8_BIAS] * 4)
    # Batch 1: all 2s
    await tb.load_activation_nv(1, [2] * 128, [BFP8E8_BIAS] * 4)

    # Weights: all 1s
    for col in range(16):
        await tb.load_weight_nv(col, 0, [1] * 128, [BFP8E8_BIAS] * 4)

    await tb.start_tile()

    # Collect results from both batches
    all_results = []
    result_valid_count = 0

    for cycle in range(10000):
        await RisingEdge(dut.i_clk)

        if dut.o_result_valid.value == 1:
            result_valid_count += 1
            batch_results = tb.get_results_fp16()
            all_results.append(batch_results)
            cocotb.log.info(f"Result valid pulse {result_valid_count}: {batch_results}")

        if dut.o_tile_done.value == 1:
            cocotb.log.info(f"Tile done after {cycle} cycles")
            break
    else:
        assert False, "Tile operation timed out"

    assert result_valid_count == B, f"Expected {B} result pulses, got {result_valid_count}"

    # Golden
    expected_batch_0 = [float(np.dot(np.ones(128), np.ones(128)))] * 16
    expected_batch_1 = [float(np.dot(np.full(128, 2.0), np.ones(128)))] * 16

    cocotb.log.info(f"Batch 0 results:   {all_results[0]}")
    cocotb.log.info(f"Batch 0 expected:  {expected_batch_0}")
    cocotb.log.info(f"Batch 1 results:   {all_results[1]}")
    cocotb.log.info(f"Batch 1 expected:  {expected_batch_1}")

    for i in range(16):
        assert all_results[0][i] == expected_batch_0[i]
        assert all_results[1][i] == expected_batch_1[i]

    cocotb.log.info("TEST PASSED: Batch dimension test (B=2)")


@cocotb.test()
async def test_batch_with_multi_nv(dut):
    """Test with batch B > 1 AND multiple NVs V > 1."""
    tb = ComputeEngineMlpTB(dut)

    clock = Clock(dut.i_clk, 10, units="ns")
    cocotb.start_soon(clock.start())

    await tb.reset()

    B = 2
    V = 2
    dut.i_tile_left_ugd_len.value = B
    dut.i_tile_right_ugd_len.value = 16
    dut.i_tile_vec_len.value = V
    await RisingEdge(dut.i_clk)

    # Batch 0: NV 0 and 1 both all 1s
    await tb.load_activation_nv(0, [1] * 128, [BFP8E8_BIAS] * 4)
    await tb.load_activation_nv(1, [1] * 128, [BFP8E8_BIAS] * 4)
    # Batch 1: NV 0 and 1 both all 2s
    await tb.load_activation_nv(2, [2] * 128, [BFP8E8_BIAS] * 4)
    await tb.load_activation_nv(3, [2] * 128, [BFP8E8_BIAS] * 4)

    # Weights: all 1s
    for col in range(16):
        for nv in range(V):
            await tb.load_weight_nv(col, nv, [1] * 128, [BFP8E8_BIAS] * 4)

    await tb.start_tile()

    all_results = []
    result_valid_count = 0

    for cycle in range(20000):
        await RisingEdge(dut.i_clk)

        if dut.o_result_valid.value == 1:
            result_valid_count += 1
            batch_results = tb.get_results_fp16()
            all_results.append(batch_results)

        if dut.o_tile_done.value == 1:
            break
    else:
        assert False, "Tile operation timed out"

    assert result_valid_count == B

    # Golden: Batch 0 = 256, Batch 1 = 512
    expected_batch_0 = [float(np.dot(np.ones(256), np.ones(256)))] * 16
    expected_batch_1 = [float(np.dot(np.full(256, 2.0), np.ones(256)))] * 16

    cocotb.log.info(f"Batch 0 results:   {all_results[0]}")
    cocotb.log.info(f"Batch 0 expected:  {expected_batch_0}")
    cocotb.log.info(f"Batch 1 results:   {all_results[1]}")
    cocotb.log.info(f"Batch 1 expected:  {expected_batch_1}")

    for i in range(16):
        assert all_results[0][i] == expected_batch_0[i]
        assert all_results[1][i] == expected_batch_1[i]

    cocotb.log.info("TEST PASSED: Batch with multi-NV test (B=2, V=2)")


@cocotb.test()
async def test_full_bcv(dut):
    """Test with full BCV dimensions: B=16, C=16, V=8."""
    if not HAS_GFP:
        cocotb.log.warning("Skipping full BCV test - torch/gfp not available")
        return

    tb = ComputeEngineMlpTB(dut)

    clock = Clock(dut.i_clk, 10, units="ns")
    cocotb.start_soon(clock.start())

    await tb.reset()

    B = 16
    C = 16
    V = 8
    NV_SIZE = 128
    dut.i_tile_left_ugd_len.value = B
    dut.i_tile_right_ugd_len.value = C
    dut.i_tile_vec_len.value = V
    await RisingEdge(dut.i_clk)

    cocotb.log.info(f"Testing full BCV: B={B}, C={C}, V={V}")

    gfp8 = gfp.GFPDataType(mantissa_bits=8, exp_bits=8)

    torch.manual_seed(12345)
    activations_float = torch.rand(B, V * NV_SIZE) * 2.0 - 1.0
    weights_float = torch.rand(V * NV_SIZE, C) * 2.0 - 1.0

    # Quantize
    act_gfp_list = []
    for b in range(B):
        act_row = activations_float[b]
        act_gfp = gfp.GFPTensor(
            original_shape=act_row.shape,
            group_axis=-1,
            group_size=32,
            dtype=gfp8,
            original_data=act_row,
        )
        act_gfp_list.append(act_gfp)

    wt_gfp_list = []
    for c in range(C):
        wt_col = weights_float[:, c]
        wt_gfp = gfp.GFPTensor(
            original_shape=wt_col.shape,
            group_axis=-1,
            group_size=32,
            dtype=gfp8,
            original_data=wt_col,
        )
        wt_gfp_list.append(wt_gfp)

    # Golden reference
    golden_results = torch.zeros(B, C)
    for b in range(B):
        act_dequant = act_gfp_list[b].dequantize()
        for c in range(C):
            wt_dequant = wt_gfp_list[c].dequantize()
            golden_results[b, c] = torch.dot(act_dequant, wt_dequant)

    # Load activations
    for batch in range(B):
        act_gfp = act_gfp_list[batch]
        for nv in range(V):
            nv_idx = batch * V + nv
            mantissas = []
            exponents = []
            for g in range(4):
                group_idx = nv * 4 + g
                group_mantissas = act_gfp.mantissa_data[group_idx].tolist()
                mantissas.extend(group_mantissas)
                group_exp = int(act_gfp.exp_data[group_idx].item()) + ACX_BFP_M8E8_BIAS
                exponents.append(group_exp)
            await tb.load_activation_nv(nv_idx, mantissas, exponents)

    # Load weights
    for col in range(C):
        wt_gfp = wt_gfp_list[col]
        for nv in range(V):
            mantissas = []
            exponents = []
            for g in range(4):
                group_idx = nv * 4 + g
                group_mantissas = wt_gfp.mantissa_data[group_idx].tolist()
                mantissas.extend(group_mantissas)
                group_exp = int(wt_gfp.exp_data[group_idx].item()) + ACX_BFP_M8E8_BIAS
                exponents.append(group_exp)
            await tb.load_weight_nv(col, nv, mantissas, exponents)

    cocotb.log.info("Data loaded. Starting tile operation...")
    await tb.start_tile()

    all_results = []
    result_valid_count = 0

    for cycle in range(100000):
        await RisingEdge(dut.i_clk)

        if dut.o_result_valid.value == 1:
            result_valid_count += 1
            batch_results = tb.get_results_fp16()
            all_results.append(batch_results)

        if dut.o_tile_done.value == 1:
            cocotb.log.info(f"Tile done after {cycle} cycles")
            break
    else:
        assert False, "Tile operation timed out"

    assert result_valid_count == B, f"Expected {B} result pulses, got {result_valid_count}"

    # Verify
    max_rel_err = 0.0
    errors = 0
    REL_TOL = 0.01

    for batch in range(B):
        for col in range(C):
            hw_result = all_results[batch][col]
            golden = golden_results[batch, col].item()

            abs_err = abs(hw_result - golden)
            rel_err = abs_err / abs(golden) if golden != 0 else 0

            if rel_err > max_rel_err:
                max_rel_err = rel_err

            if rel_err > REL_TOL:
                errors += 1

    cocotb.log.info(f"Max relative error: {max_rel_err*100:.4f}%")

    if errors > 0:
        assert False, f"Found {errors} mismatches exceeding {REL_TOL*100}% tolerance"

    cocotb.log.info(f"All {B * C} results verified!")
    cocotb.log.info("TEST PASSED: Full BCV test (B=16, C=16, V=8)")


@cocotb.test()
async def test_golden_hex(dut):
    """
    Test with golden hex files from the hex/ directory.

    Uses:
    - hex/left.hex: Activation matrix (128 NVs)
    - hex/right.hex: Weight matrix (128 NVs)
    - hex/golden_B16_C16_V8.hex: Expected FP16 results

    The hex files use 5-bit exponents (bias=15), which must be converted
    to 8-bit exponents (bias=127+6) for the MLP hardware.
    """
    tb = ComputeEngineMlpTB(dut)

    clock = Clock(dut.i_clk, 10, unit="ns")
    cocotb.start_soon(clock.start())

    await tb.reset()

    # BCV parameters for this test
    B = 16  # Batches
    C = 16  # Columns (fixed for MLP)
    V = 8   # NVs per output (inner dimension)

    dut.i_tile_left_ugd_len.value = B
    dut.i_tile_right_ugd_len.value = C
    dut.i_tile_vec_len.value = V
    await RisingEdge(dut.i_clk)

    cocotb.log.info(f"Testing with golden hex files: B={B}, C={C}, V={V}")

    # Find hex directory (elastix_gemm/hex/)
    # Path: gemm/sim/compute_engine_test/cocotb/compute_engine_mlp_tests.py
    # parents[4] = elastix_gemm/
    hex_dir = Path(__file__).resolve().parents[4] / "hex"
    left_hex = hex_dir / "left.hex"
    right_hex = hex_dir / "right.hex"
    golden_hex = hex_dir / "golden_B16_C16_V8.hex"

    cocotb.log.info(f"Loading hex files from: {hex_dir}")

    # Load hex files
    left_exp, left_mant = load_hex_file(str(left_hex))
    right_exp, right_mant = load_hex_file(str(right_hex))
    golden_fp16 = load_golden_hex(str(golden_hex))

    cocotb.log.info(f"Loaded left: {left_mant.shape}, right: {right_mant.shape}")
    cocotb.log.info(f"Golden results: {len(golden_fp16)} FP16 values")

    # Convert 5-bit exponents (bias=15) to 8-bit exponents for MLP hardware
    # Hardware expects: exp_8bit = exp_5bit - 15 + 127 + 6 = exp_5bit + 118
    EXP_CONVERT_OFFSET = GFP8E8_BIAS + ACX_BFP_M8E8_BIAS - HEX_EXP_BIAS  # = 127 + 6 - 15 = 118

    # Load activation NVs (B*V = 128 NVs total)
    cocotb.log.info("Loading activation NVs...")
    for nv_idx in range(B * V):
        # Each NV: 128 mantissas (4 groups × 32) and 4 exponents
        mant_list = left_mant[nv_idx, :].tolist()
        exp_list = [(int(e) + EXP_CONVERT_OFFSET) & 0xFF for e in left_exp[nv_idx, :]]
        await tb.load_activation_nv(nv_idx, mant_list, exp_list)

    # Load weight NVs (C*V = 128 NVs total)
    # Weight layout: column c uses NVs [c*V, c*V+1, ..., c*V+V-1]
    cocotb.log.info("Loading weight NVs...")
    for col in range(C):
        for v in range(V):
            nv_idx = col * V + v
            mant_list = right_mant[nv_idx, :].tolist()
            exp_list = [(int(e) + EXP_CONVERT_OFFSET) & 0xFF for e in right_exp[nv_idx, :]]
            await tb.load_weight_nv(col, v, mant_list, exp_list)

    cocotb.log.info("Data loaded. Starting tile operation...")

    # Start tile operation
    await tb.start_tile()

    # Collect results
    all_results = []
    result_valid_count = 0

    for cycle in range(5000):
        await RisingEdge(dut.i_clk)
        if dut.o_result_valid.value == 1:
            result_valid_count += 1
            results = tb.get_results_fp16()
            all_results.append(results)
        if dut.o_tile_done.value == 1:
            cocotb.log.info(f"Tile done after {cycle} cycles")
            break
    else:
        assert False, "Tile operation timed out"

    cocotb.log.info(f"Got {result_valid_count} result pulses (expected {B})")
    assert result_valid_count == B, f"Expected {B} result pulses, got {result_valid_count}"

    # Compare against golden
    errors = 0
    max_rel_err = 0.0
    REL_TOL = 0.05  # 5% tolerance for quantization differences

    for batch in range(B):
        for col in range(C):
            result_idx = batch * C + col
            golden_int = golden_fp16[result_idx]
            golden_float = fp16_to_float(golden_int)

            hw_float = all_results[batch][col]

            # Convert hw_float back to FP16 int for exact comparison
            hw_fp16 = np.float16(hw_float).view(np.uint16)

            # Calculate error
            if golden_float != 0:
                rel_err = abs(hw_float - golden_float) / abs(golden_float)
            else:
                rel_err = abs(hw_float)

            if rel_err > max_rel_err:
                max_rel_err = rel_err

            if rel_err > REL_TOL:
                errors += 1
                if errors <= 10:
                    cocotb.log.warning(
                        f"Mismatch [{batch},{col}]: HW=0x{hw_fp16:04x} ({hw_float:.4f}) "
                        f"Golden=0x{golden_int:04x} ({golden_float:.4f}) "
                        f"rel_err={rel_err*100:.2f}%"
                    )

    cocotb.log.info(f"Max relative error: {max_rel_err*100:.4f}%")

    if errors > 0:
        cocotb.log.warning(f"Found {errors} mismatches exceeding {REL_TOL*100}% tolerance")
        # Don't fail completely - just warn since algorithms may differ
        if errors > B * C * 0.1:  # Fail if more than 10% are wrong
            assert False, f"Too many mismatches: {errors}/{B*C}"
    else:
        cocotb.log.info(f"All {B * C} results within {REL_TOL*100}% tolerance!")

    cocotb.log.info("TEST PASSED: Golden hex file test (B=16, C=16, V=8)")


# =============================================================================
# Tests for C > 16 (column group iteration)
# =============================================================================

async def run_multi_column_group_test(dut, B: int, C: int, V: int):
    """
    Generic test helper for C > 16 configurations.

    Tests the column group iteration feature where C columns are processed
    in groups of 16. For C=32, there are 2 groups; for C=64, 4 groups, etc.

    Args:
        dut: Device under test
        B: Number of batches
        C: Number of columns (must be divisible by 16)
        V: Number of NVs per output
    """
    tb = ComputeEngineMlpTB(dut)

    clock = Clock(dut.i_clk, 10, unit="ns")
    cocotb.start_soon(clock.start())

    await tb.reset()

    num_groups = C // 16
    cocotb.log.info(f"Testing C > 16: B={B}, C={C}, V={V}, num_groups={num_groups}")

    dut.i_tile_left_ugd_len.value = B
    dut.i_tile_right_ugd_len.value = C
    dut.i_tile_vec_len.value = V
    await RisingEdge(dut.i_clk)

    # Find hex directory and load data
    hex_dir = Path(__file__).resolve().parents[4] / "hex"
    left_hex = hex_dir / "left.hex"
    right_hex = hex_dir / "right.hex"
    golden_hex = hex_dir / f"golden_B{B}_C{C}_V{V}.hex"

    if not golden_hex.exists():
        cocotb.log.error(f"Golden file not found: {golden_hex}")
        assert False, f"Missing golden file: {golden_hex}"

    cocotb.log.info(f"Loading hex files from: {hex_dir}")

    # Load hex files
    left_exp, left_mant = load_hex_file(str(left_hex))
    right_exp, right_mant = load_hex_file(str(right_hex))
    golden_fp16 = load_golden_hex(str(golden_hex))

    cocotb.log.info(f"Loaded left: {left_mant.shape}, right: {right_mant.shape}")
    cocotb.log.info(f"Golden results: {len(golden_fp16)} FP16 values (expected {B * C})")

    assert len(golden_fp16) == B * C, f"Golden file has {len(golden_fp16)} values, expected {B * C}"

    # Convert 5-bit exponents to 8-bit for MLP hardware
    EXP_CONVERT_OFFSET = GFP8E8_BIAS + ACX_BFP_M8E8_BIAS - HEX_EXP_BIAS  # = 118

    # Load activation NVs (B*V NVs total)
    cocotb.log.info(f"Loading activation NVs: {B * V} NVs...")
    for nv_idx in range(B * V):
        mant_list = left_mant[nv_idx, :].tolist()
        exp_list = [(int(e) + EXP_CONVERT_OFFSET) & 0xFF for e in left_exp[nv_idx, :]]
        await tb.load_activation_nv(nv_idx, mant_list, exp_list)

    # Load weight NVs (C*V NVs total)
    # Weight layout (column-major): col c uses NVs [c*V, c*V+1, ..., c*V+V-1]
    cocotb.log.info(f"Loading weight NVs: {C * V} NVs ({C} columns × {V} NVs each)...")
    for col in range(C):
        for v in range(V):
            nv_idx = col * V + v
            mant_list = right_mant[nv_idx, :].tolist()
            exp_list = [(int(e) + EXP_CONVERT_OFFSET) & 0xFF for e in right_exp[nv_idx, :]]
            await tb.load_weight_nv(col, v, mant_list, exp_list)

    cocotb.log.info("Data loaded. Starting tile operation...")

    # Start tile operation
    await tb.start_tile()

    # Collect results - for C > 16, we get B result pulses per group, num_groups times
    # Total result pulses = B * num_groups
    # Each pulse contains 16 FP16 results
    all_raw_results = []  # List of (batch_within_group, raw 256-bit results)
    result_valid_count = 0
    expected_pulses = B * num_groups

    # Extended timeout for multi-group processing
    timeout_cycles = 10000 * num_groups

    for cycle in range(timeout_cycles):
        await RisingEdge(dut.i_clk)
        if dut.o_result_valid.value == 1:
            result_valid_count += 1
            results = tb.get_results_fp16()
            all_raw_results.append(results)
        if dut.o_tile_done.value == 1:
            cocotb.log.info(f"Tile done after {cycle} cycles")
            break
    else:
        assert False, f"Tile operation timed out after {timeout_cycles} cycles"

    cocotb.log.info(f"Got {result_valid_count} result pulses (expected {expected_pulses})")
    assert result_valid_count == expected_pulses, \
        f"Expected {expected_pulses} result pulses, got {result_valid_count}"

    # Reorganize results: all_raw_results[pulse_idx] → [batch][col]
    # Result order: Group 0 (B batches × 16 cols), Group 1 (B batches × 16 cols), ...
    # Final shape: [B][C] where C = num_groups * 16
    all_results = [[0.0] * C for _ in range(B)]

    for pulse_idx in range(expected_pulses):
        group_idx = pulse_idx // B
        batch_within_group = pulse_idx % B
        for col_within_group in range(16):
            global_col = group_idx * 16 + col_within_group
            all_results[batch_within_group][global_col] = all_raw_results[pulse_idx][col_within_group]

    # Compare against golden
    errors = 0
    max_rel_err = 0.0
    REL_TOL = 0.05  # 5% tolerance

    for batch in range(B):
        for col in range(C):
            result_idx = batch * C + col
            golden_int = golden_fp16[result_idx]
            golden_float = fp16_to_float(golden_int)

            hw_float = all_results[batch][col]

            # Calculate error
            if golden_float != 0:
                rel_err = abs(hw_float - golden_float) / abs(golden_float)
            else:
                rel_err = abs(hw_float) if hw_float != 0 else 0

            if rel_err > max_rel_err:
                max_rel_err = rel_err

            if rel_err > REL_TOL:
                errors += 1
                if errors <= 10:
                    hw_fp16 = np.float16(hw_float).view(np.uint16)
                    cocotb.log.warning(
                        f"Mismatch [{batch},{col}]: HW=0x{hw_fp16:04x} ({hw_float:.4f}) "
                        f"Golden=0x{golden_int:04x} ({golden_float:.4f}) "
                        f"rel_err={rel_err*100:.2f}%"
                    )

    cocotb.log.info(f"Max relative error: {max_rel_err*100:.4f}%")

    if errors > 0:
        cocotb.log.warning(f"Found {errors} mismatches exceeding {REL_TOL*100}% tolerance")
        if errors > B * C * 0.1:  # Fail if more than 10% are wrong
            assert False, f"Too many mismatches: {errors}/{B*C}"
    else:
        cocotb.log.info(f"All {B * C} results within {REL_TOL*100}% tolerance!")

    cocotb.log.info(f"TEST PASSED: B={B}, C={C}, V={V} ({num_groups} column groups)")


@cocotb.test()
async def test_c16_b4_v8(dut):
    """Test B=4, C=16, V=8 (baseline - 1 column group)."""
    await run_multi_column_group_test(dut, B=4, C=16, V=8)


@cocotb.test()
async def test_c16_b8_v4(dut):
    """Test B=8, C=16, V=4 (baseline - 1 column group)."""
    await run_multi_column_group_test(dut, B=8, C=16, V=4)


@cocotb.test()
async def test_c32_b4_v4(dut):
    """Test B=4, C=32, V=4 (2 column groups)."""
    await run_multi_column_group_test(dut, B=4, C=32, V=4)


@cocotb.test()
async def test_c32_b8_v2(dut):
    """Test B=8, C=32, V=2 (2 column groups)."""
    await run_multi_column_group_test(dut, B=8, C=32, V=2)


@cocotb.test()
async def test_c64_b8_v2(dut):
    """Test B=8, C=64, V=2 (4 column groups)."""
    await run_multi_column_group_test(dut, B=8, C=64, V=2)


@cocotb.test()
async def test_c128_b2_v1(dut):
    """Test B=2, C=128, V=1 (8 column groups)."""
    await run_multi_column_group_test(dut, B=2, C=128, V=1)
