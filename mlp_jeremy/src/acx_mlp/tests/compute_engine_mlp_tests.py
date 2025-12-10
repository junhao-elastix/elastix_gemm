"""
Testbench for compute_engine_mlp module.

Tests the integrated wrapper with:
- row_bram for L1 memory (left=activations, right=weights)
- mlp_bram_col_ctrl for MLP compute
- Weight fill controller
- Compute controller

Test case: 1×128 × 128×16 matrix multiplication
- Activation vector: 1×128 (128 elements, 1 NV)
- Weight matrix: 128×16 (128 rows, 16 columns)
- Result: 1×16 (16 elements)
"""

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ClockCycles, Timer
import random
import sys
from pathlib import Path
import numpy as np

# Add emulator path for GFP imports
# Path: tests -> acx_mlp -> src -> mlp_jeremy -> elastix_gemm (4 parents up)
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

from sim_utils.build_misc import int_to_float24

# GFP8 bias constants (from acx_mlp_tests_nv.py)
GFP8E8_BIAS = 127   # IEEE standard: 2^(8-1) - 1 = 127
BFP8E8_BIAS = 133   # MLP native bias: 127 + 6 (mantissa format offset)
ACX_BFP_M8E8_BIAS = BFP8E8_BIAS - GFP8E8_BIAS  # = 6


class ComputeEngineMlpTB:
    """Testbench helper class for compute_engine_mlp."""

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
        self.dut.i_start_fill.value = 0
        self.dut.i_start_compute.value = 0
        # BCV configuration defaults
        self.dut.i_left_ugd_len.value = 1   # B = 1 batch (backward compatible)
        self.dut.i_right_ugd_len.value = 16  # C = 16 columns (fixed for MLP)
        self.dut.i_vec_len.value = 1         # V = 1 NV per output

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
        """Load a Native Vector to left row_bram (activations).

        Args:
            nv_idx: NV index (0-127)
            mantissas: List of 128 8-bit mantissa values
            exponents: List of 4 8-bit exponent values (one per 32-element group)
        """
        assert len(mantissas) == self.NV_SIZE, f"Expected {self.NV_SIZE} mantissas, got {len(mantissas)}"
        assert len(exponents) == 4, f"Expected 4 exponents, got {len(exponents)}"

        base_addr = nv_idx * 4  # 4 lines per NV

        # Write 4 mantissa lines (32 elements each = 256 bits)
        for group in range(4):
            line_data = 0
            for i in range(32):
                elem_idx = group * 32 + i
                # Convert signed to unsigned 8-bit
                m = mantissas[elem_idx] & 0xFF
                line_data |= (m << (i * 8))

            addr = base_addr + group
            await self.write_man_left(addr, line_data)

        # Write 4 exponents (one per line/group)
        for group in range(4):
            addr = base_addr + group
            await self.write_exp_left(addr, exponents[group])

    async def load_weight_nv(self, col_idx: int, nv_idx: int, mantissas: list[int], exponents: list[int]):
        """Load a Native Vector to right row_bram (weights).

        Args:
            col_idx: Column index (0-15)
            nv_idx: NV index within column (0 to vec_len-1)
            mantissas: List of 128 8-bit mantissa values
            exponents: List of 4 8-bit exponent values
        """
        assert len(mantissas) == self.NV_SIZE, f"Expected {self.NV_SIZE} mantissas, got {len(mantissas)}"
        assert len(exponents) == 4, f"Expected 4 exponents, got {len(exponents)}"

        # Calculate NV index in row_bram (column-major: col * vec_len + nv_idx)
        vec_len = int(self.dut.i_vec_len.value)
        row_bram_nv_idx = col_idx * vec_len + nv_idx
        base_addr = row_bram_nv_idx * 4  # 4 lines per NV

        # Debug for first column
        if col_idx == 0 and nv_idx == 0:
            cocotb.log.info(f"Loading weight NV to col={col_idx}, base_addr={base_addr}")
            cocotb.log.info(f"  Mantissas[0:8]: {mantissas[0:8]}")
            cocotb.log.info(f"  Mantissas[32:40]: {mantissas[32:40]}")
            cocotb.log.info(f"  Mantissas[64:72]: {mantissas[64:72]}")
            cocotb.log.info(f"  Mantissas[96:104]: {mantissas[96:104]}")
            cocotb.log.info(f"  Exponents: {exponents}")

        # Write 4 mantissa lines
        for group in range(4):
            line_data = 0
            for i in range(32):
                elem_idx = group * 32 + i
                m = mantissas[elem_idx] & 0xFF
                line_data |= (m << (i * 8))

            addr = base_addr + group

            # Debug for first column
            if col_idx == 0 and nv_idx == 0:
                # Print full 256-bit value
                cocotb.log.info(f"  Writing group {group} to addr {addr}: full 256-bit = 0x{line_data:064x}")

            await self.write_man_right(addr, line_data)

        # Write 4 exponents
        for group in range(4):
            addr = base_addr + group
            await self.write_exp_right(addr, exponents[group])

    async def start_fill(self):
        """Start the weight fill phase."""
        self.dut.i_start_fill.value = 1
        await RisingEdge(self.dut.i_clk)
        self.dut.i_start_fill.value = 0

    async def wait_fill_done(self, timeout_cycles: int = 10000):
        """Wait for weight fill to complete."""
        for _ in range(timeout_cycles):
            await RisingEdge(self.dut.i_clk)
            if self.dut.o_fill_done.value == 1:
                return True
        return False

    async def start_compute(self):
        """Start the compute phase."""
        self.dut.i_start_compute.value = 1
        await RisingEdge(self.dut.i_clk)
        self.dut.i_start_compute.value = 0

    async def wait_compute_done(self, timeout_cycles: int = 10000):
        """Wait for compute to complete."""
        for _ in range(timeout_cycles):
            await RisingEdge(self.dut.i_clk)
            if self.dut.o_compute_done.value == 1:
                return True
        return False

    def get_results(self) -> list[float]:
        """Get the 16 FP24 results from the compute."""
        results = []
        for col in range(self.NUM_COLUMNS):
            # o_result is 24-bit, convert to FP24 float
            raw_val = int(self.dut.o_result[col].value)
            results.append(int_to_float24(raw_val))
        return results

    def get_raw_results(self) -> list[int]:
        """Get the raw 24-bit integer results for debugging."""
        results = []
        for col in range(self.NUM_COLUMNS):
            raw_val = int(self.dut.o_result[col].value)
            results.append(raw_val)
        return results


@cocotb.test()
async def test_first_8_elements(dut):
    """Test with data only in first 8 positions (one MLP cycle).

    This isolates whether the issue is with multi-cycle accumulation.
    """
    tb = ComputeEngineMlpTB(dut)

    clock = Clock(dut.i_clk, 10, units="ns")
    cocotb.start_soon(clock.start())

    await tb.reset()

    dut.i_vec_len.value = 1
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

    await tb.start_fill()
    fill_done = await tb.wait_fill_done()
    assert fill_done, "Fill timed out"

    await ClockCycles(dut.i_clk, 5)

    await tb.start_compute()
    compute_done = await tb.wait_compute_done()
    assert compute_done, "Compute timed out"

    await ClockCycles(dut.i_clk, 5)

    results = tb.get_results()

    # Compute golden reference using numpy
    # Activation and weights are both [1,1,1,1,1,1,1,1,0,0,...,0]
    act_vec = np.array([1.0] * 8 + [0.0] * 120)
    wt_vec = np.array([1.0] * 8 + [0.0] * 120)
    golden_dot = float(np.dot(act_vec, wt_vec))
    expected = [golden_dot] * 16

    cocotb.log.info(f"Results (first 8 only):   {results}")
    cocotb.log.info(f"Expected (numpy golden):  {expected}")

    for i in range(16):
        assert results[i] == expected[i], f"Column {i}: got {results[i]}, expected {expected[i]}"

    cocotb.log.info("TEST PASSED: First 8 elements test (numpy golden verified)")


@cocotb.test()
async def test_first_32_elements(dut):
    """Test with data only in first 32 positions (4 MLP cycles = 1 group).

    This checks if exactly one exponent group (32 elements) is working.
    """
    tb = ComputeEngineMlpTB(dut)

    clock = Clock(dut.i_clk, 10, units="ns")
    cocotb.start_soon(clock.start())

    await tb.reset()

    dut.i_vec_len.value = 1
    await RisingEdge(dut.i_clk)

    # Only first 32 elements are 1, rest are 0
    act_mantissas = [1] * 32 + [0] * 96
    act_exponents = [BFP8E8_BIAS] * 4
    await tb.load_activation_nv(0, act_mantissas, act_exponents)

    # Same for weights
    for col in range(16):
        wt_mantissas = [1] * 32 + [0] * 96
        wt_exponents = [BFP8E8_BIAS] * 4
        await tb.load_weight_nv(col, 0, wt_mantissas, wt_exponents)

    await tb.start_fill()
    fill_done = await tb.wait_fill_done()
    assert fill_done, "Fill timed out"

    await ClockCycles(dut.i_clk, 5)

    await tb.start_compute()
    compute_done = await tb.wait_compute_done()
    assert compute_done, "Compute timed out"

    await ClockCycles(dut.i_clk, 5)

    results = tb.get_results()

    # Compute golden reference using numpy
    act_vec = np.array([1.0] * 32 + [0.0] * 96)
    wt_vec = np.array([1.0] * 32 + [0.0] * 96)
    golden_dot = float(np.dot(act_vec, wt_vec))
    expected = [golden_dot] * 16

    cocotb.log.info(f"Results (first 32 only):   {results}")
    cocotb.log.info(f"Expected (numpy golden):   {expected}")

    for i in range(16):
        assert results[i] == expected[i], f"Column {i}: got {results[i]}, expected {expected[i]}"

    cocotb.log.info("TEST PASSED: First 32 elements test (numpy golden verified)")


@cocotb.test()
async def test_identity_matrix(dut):
    """Test with identity-like weight matrix.

    Activation: [1, 0, 0, ..., 0] repeated for 128 elements (actually just 1 in position 0)
    Weights: Each column has 1 in a different position
    Expected: Each output should equal the corresponding activation element
    """
    tb = ComputeEngineMlpTB(dut)

    # Start clock
    clock = Clock(dut.i_clk, 10, units="ns")
    cocotb.start_soon(clock.start())

    # Reset
    await tb.reset()

    # Configure for 1 NV per column (vec_len = 1)
    dut.i_vec_len.value = 1
    await RisingEdge(dut.i_clk)

    # Create activation vector: [1, 2, 3, ..., 16, 0, 0, ..., 0]
    # Only first 16 elements are non-zero
    act_mantissas = [0] * 128
    act_exponents = [BFP8E8_BIAS] * 4  # All exponents = 133 (scale = 1)
    for i in range(16):
        act_mantissas[i] = i + 1  # Values 1-16

    # Load activation NV to left row_bram
    await tb.load_activation_nv(0, act_mantissas, act_exponents)

    # Create weight matrix: identity-like (one-hot in first 16 positions)
    # Column i has weight[i] = 1, all others = 0
    for col in range(16):
        wt_mantissas = [0] * 128
        wt_exponents = [BFP8E8_BIAS] * 4
        wt_mantissas[col] = 1  # One-hot at position col

        await tb.load_weight_nv(col, 0, wt_mantissas, wt_exponents)

    cocotb.log.info("Starting weight fill phase...")

    # Debug: Check row_bram internal signals before fill
    try:
        # Try to access row_bram's NV index and output
        rb = dut.u_row_bram
        cocotb.log.info(f"  row_bram nv_right_rd_idx: {int(rb.i_nv_right_rd_idx.value)}")
        # Check the packed NV that will be sent
        ce = dut
        nv_packed = int(ce.nv_right_man_packed.value)
        cocotb.log.info(f"  nv_right_man_packed (first 256 bits): 0x{(nv_packed & ((1<<256)-1)):064x}")
    except Exception as e:
        cocotb.log.info(f"  Could not access internal signals: {e}")

    # Start weight fill
    await tb.start_fill()

    # Wait for fill to complete
    fill_done = await tb.wait_fill_done()
    assert fill_done, "Weight fill timed out"

    cocotb.log.info("Weight fill complete. Starting compute phase...")

    # Wait a few cycles
    await ClockCycles(dut.i_clk, 5)

    # Start compute
    await tb.start_compute()

    # Wait for compute to complete
    compute_done = await tb.wait_compute_done()
    assert compute_done, "Compute timed out"

    cocotb.log.info("Compute complete. Checking results...")

    # Wait for results to be valid
    await ClockCycles(dut.i_clk, 5)

    # Get results
    results = tb.get_results()
    raw_results = tb.get_raw_results()

    # Compute golden reference using numpy
    # Activation: [1, 2, 3, ..., 16, 0, 0, ..., 0]
    # Weights: Column i has weight[i] = 1, all others = 0
    act_vec = np.zeros(128)
    for i in range(16):
        act_vec[i] = i + 1

    expected = []
    for col in range(16):
        wt_vec = np.zeros(128)
        wt_vec[col] = 1.0  # One-hot at position col
        expected.append(float(np.dot(act_vec, wt_vec)))

    cocotb.log.info(f"Raw results (hex): {[hex(r) for r in raw_results]}")
    cocotb.log.info(f"Results:   {results}")
    cocotb.log.info(f"Expected (numpy golden):  {expected}")

    # Verify
    for i in range(16):
        assert results[i] == expected[i], f"Column {i}: got {results[i]}, expected {expected[i]}"

    cocotb.log.info("TEST PASSED: Identity matrix test (numpy golden verified)")


@cocotb.test()
async def test_all_ones(dut):
    """Test with all-ones activation and all-ones weights.

    Activation: [1, 1, 1, ..., 1] (128 ones)
    Weights: All columns have all 1s
    Expected: Each output = 128 (sum of 128 ones)
    """
    tb = ComputeEngineMlpTB(dut)

    # Start clock
    clock = Clock(dut.i_clk, 10, units="ns")
    cocotb.start_soon(clock.start())

    # Reset
    await tb.reset()

    # Configure for 1 NV per column
    dut.i_vec_len.value = 1
    await RisingEdge(dut.i_clk)

    # All-ones activation
    act_mantissas = [1] * 128
    act_exponents = [BFP8E8_BIAS] * 4

    await tb.load_activation_nv(0, act_mantissas, act_exponents)

    # All-ones weights for all columns
    for col in range(16):
        wt_mantissas = [1] * 128
        wt_exponents = [BFP8E8_BIAS] * 4
        await tb.load_weight_nv(col, 0, wt_mantissas, wt_exponents)

    cocotb.log.info("Starting weight fill phase...")
    await tb.start_fill()

    fill_done = await tb.wait_fill_done()
    assert fill_done, "Weight fill timed out"

    cocotb.log.info("Weight fill complete. Starting compute phase...")
    await tb.start_compute()

    compute_done = await tb.wait_compute_done()
    assert compute_done, "Compute timed out"

    cocotb.log.info("Compute complete. Checking results...")
    await ClockCycles(dut.i_clk, 5)

    results = tb.get_results()

    # Compute golden reference using numpy
    act_vec = np.ones(128)
    wt_vec = np.ones(128)
    golden_dot = float(np.dot(act_vec, wt_vec))
    expected = [golden_dot] * 16

    cocotb.log.info(f"Results:   {results}")
    cocotb.log.info(f"Expected (numpy golden):  {expected}")

    for i in range(16):
        assert results[i] == expected[i], f"Column {i}: got {results[i]}, expected {expected[i]}"

    cocotb.log.info("TEST PASSED: All-ones test (numpy golden verified)")


@cocotb.test()
async def test_multi_nv(dut):
    """Test with multiple NVs per column (vec_len > 1).

    Activation: 2 NVs, each with values
    Weights: 2 NVs per column
    Expected: Sum of two dot products
    """
    tb = ComputeEngineMlpTB(dut)

    # Start clock
    clock = Clock(dut.i_clk, 10, units="ns")
    cocotb.start_soon(clock.start())

    # Reset
    await tb.reset()

    # Configure for 2 NVs per column
    dut.i_vec_len.value = 2
    await RisingEdge(dut.i_clk)

    # Activation NV 0: all 1s
    act_mantissas_0 = [1] * 128
    act_exponents_0 = [BFP8E8_BIAS] * 4
    await tb.load_activation_nv(0, act_mantissas_0, act_exponents_0)

    # Activation NV 1: all 2s
    act_mantissas_1 = [2] * 128
    act_exponents_1 = [BFP8E8_BIAS] * 4
    await tb.load_activation_nv(1, act_mantissas_1, act_exponents_1)

    # Weights: Column i has all 1s in NV 0 and all 1s in NV 1
    # Expected result: sum of (128 * 1) + (128 * 2) = 128 + 256 = 384
    for col in range(16):
        # NV 0 for this column
        wt_mantissas_0 = [1] * 128
        wt_exponents_0 = [BFP8E8_BIAS] * 4
        await tb.load_weight_nv(col, 0, wt_mantissas_0, wt_exponents_0)

        # NV 1 for this column
        wt_mantissas_1 = [1] * 128
        wt_exponents_1 = [BFP8E8_BIAS] * 4
        await tb.load_weight_nv(col, 1, wt_mantissas_1, wt_exponents_1)

    cocotb.log.info("Starting weight fill phase (2 NVs per column)...")
    await tb.start_fill()

    fill_done = await tb.wait_fill_done()
    assert fill_done, "Weight fill timed out"

    cocotb.log.info("Weight fill complete. Starting compute phase...")
    await ClockCycles(dut.i_clk, 5)

    await tb.start_compute()

    compute_done = await tb.wait_compute_done()
    assert compute_done, "Compute timed out"

    cocotb.log.info("Compute complete. Checking results...")
    await ClockCycles(dut.i_clk, 5)

    results = tb.get_results()

    # Compute golden reference using numpy
    # Concatenate NVs: act = [1,1,...,1, 2,2,...,2] (256 elements)
    # Weights: [1,1,...,1, 1,1,...,1] (256 elements)
    act_vec = np.concatenate([np.ones(128), np.full(128, 2.0)])
    wt_vec = np.ones(256)
    golden_dot = float(np.dot(act_vec, wt_vec))
    expected = [golden_dot] * 16

    cocotb.log.info(f"Results:   {results}")
    cocotb.log.info(f"Expected (numpy golden):  {expected}")

    for i in range(16):
        assert results[i] == expected[i], f"Column {i}: got {results[i]}, expected {expected[i]}"

    cocotb.log.info("TEST PASSED: Multi-NV test (numpy golden verified)")


@cocotb.test()
async def test_different_columns(dut):
    """Test with different weight values per column.

    Activation: all 1s
    Weights: Column i has all (i+1)s
    Expected: Column i outputs 128 * (i+1)
    """
    tb = ComputeEngineMlpTB(dut)

    # Start clock
    clock = Clock(dut.i_clk, 10, units="ns")
    cocotb.start_soon(clock.start())

    # Reset
    await tb.reset()

    # Configure for 1 NV per column
    dut.i_vec_len.value = 1
    await RisingEdge(dut.i_clk)

    # All-ones activation
    act_mantissas = [1] * 128
    act_exponents = [BFP8E8_BIAS] * 4
    await tb.load_activation_nv(0, act_mantissas, act_exponents)

    # Different weights per column
    for col in range(16):
        # Limit mantissa to 7 to avoid overflow issues (7 * 128 = 896 < 32768)
        val = (col % 7) + 1
        wt_mantissas = [val] * 128
        wt_exponents = [BFP8E8_BIAS] * 4
        await tb.load_weight_nv(col, 0, wt_mantissas, wt_exponents)

    cocotb.log.info("Starting weight fill phase...")
    await tb.start_fill()

    fill_done = await tb.wait_fill_done()
    assert fill_done, "Weight fill timed out"

    cocotb.log.info("Weight fill complete. Starting compute phase...")
    await ClockCycles(dut.i_clk, 5)

    await tb.start_compute()

    compute_done = await tb.wait_compute_done()
    assert compute_done, "Compute timed out"

    cocotb.log.info("Compute complete. Checking results...")
    await ClockCycles(dut.i_clk, 5)

    results = tb.get_results()

    # Compute golden reference using numpy
    act_vec = np.ones(128)
    expected = []
    for col in range(16):
        val = (col % 7) + 1
        wt_vec = np.full(128, float(val))
        expected.append(float(np.dot(act_vec, wt_vec)))

    cocotb.log.info(f"Results:   {results}")
    cocotb.log.info(f"Expected (numpy golden):  {expected}")

    for i in range(16):
        assert results[i] == expected[i], f"Column {i}: got {results[i]}, expected {expected[i]}"

    cocotb.log.info("TEST PASSED: Different columns test (numpy golden verified)")


@cocotb.test()
async def test_gfp_random_floats(dut):
    """Test with real GFP8-quantized random float data.

    This test uses the emulator's GFP quantization to:
    1. Generate random float activations and weights
    2. Quantize them to GFP8 format (8-bit mantissa, 8-bit exponent)
    3. Load the quantized values into the hardware
    4. Compare hardware results with Python golden reference

    This validates the full GFP pipeline including:
    - Quantization precision
    - Exponent handling across groups
    - Accumulation accuracy
    """
    if not HAS_GFP:
        cocotb.log.warning("Skipping GFP test - torch/gfp not available")
        return

    tb = ComputeEngineMlpTB(dut)

    # Start clock
    clock = Clock(dut.i_clk, 10, unit="ns")
    cocotb.start_soon(clock.start())

    # Reset
    await tb.reset()

    # Configure for 1 NV per column
    dut.i_vec_len.value = 1
    await RisingEdge(dut.i_clk)

    # Create GFP8 data type
    gfp8 = gfp.GFPDataType(mantissa_bits=8, exp_bits=8)

    # Generate random float data with reproducible seed
    torch.manual_seed(42)
    activations_float = torch.rand(128) * 2.0 - 1.0  # [-1, 1]
    weights_float = torch.rand(128, 16) * 2.0 - 1.0  # [-1, 1]

    cocotb.log.info(f"Activation range: [{activations_float.min():.4f}, {activations_float.max():.4f}]")
    cocotb.log.info(f"Weight range: [{weights_float.min():.4f}, {weights_float.max():.4f}]")

    # Quantize activations with group_size=32 (4 groups for NV format)
    act_gfp = gfp.GFPTensor(
        original_shape=activations_float.shape,
        group_axis=-1,
        group_size=32,
        dtype=gfp8,
        original_data=activations_float,
    )

    # Quantize weights with group_size=32 along rows
    weights_gfp = gfp.GFPTensor(
        original_shape=weights_float.shape,
        group_axis=0,
        group_size=32,
        dtype=gfp8,
        original_data=weights_float,
    )

    # Dequantize for golden reference calculation
    act_dequant = act_gfp.dequantize()
    weights_dequant = weights_gfp.dequantize()

    cocotb.log.info(f"Act dequant range: [{act_dequant.min():.4f}, {act_dequant.max():.4f}]")
    cocotb.log.info(f"Weights dequant range: [{weights_dequant.min():.4f}, {weights_dequant.max():.4f}]")

    # Load activations to left row_bram (NV index 0)
    act_mantissas = []
    act_exponents = []
    for g in range(4):
        # Act GFP has shape [groups, elements] = [4, 32]
        group_mantissas = act_gfp.mantissa_data[g].tolist()
        act_mantissas.extend(group_mantissas)
        # Convert GFP exponent to BFP8 exponent (+6 offset)
        group_exp = int(act_gfp.exp_data[g].item()) + ACX_BFP_M8E8_BIAS
        act_exponents.append(group_exp)

    cocotb.log.info(f"Act mantissa range: [{min(act_mantissas)}, {max(act_mantissas)}]")
    cocotb.log.info(f"Act exponents (BFP8): {act_exponents}")

    await tb.load_activation_nv(0, act_mantissas, act_exponents)

    # Load weights to right row_bram (16 columns, 1 NV each)
    for col in range(16):
        wt_mantissas = []
        wt_exponents = []
        for g in range(4):
            # Weights GFP has shape [columns, groups, elements] = [16, 4, 32]
            group_mantissas = weights_gfp.mantissa_data[col, g, :].tolist()
            wt_mantissas.extend(group_mantissas)
            group_exp = int(weights_gfp.exp_data[col, g, 0].item()) + ACX_BFP_M8E8_BIAS
            wt_exponents.append(group_exp)
        await tb.load_weight_nv(col, 0, wt_mantissas, wt_exponents)

    cocotb.log.info("Data loaded. Starting weight fill phase...")
    await tb.start_fill()

    fill_done = await tb.wait_fill_done()
    assert fill_done, "Weight fill timed out"

    cocotb.log.info("Weight fill complete. Starting compute phase...")
    await tb.start_compute()

    compute_done = await tb.wait_compute_done()
    assert compute_done, "Compute timed out"

    cocotb.log.info("Compute complete. Checking results...")
    await ClockCycles(dut.i_clk, 5)

    # Get hardware results
    results = tb.get_results()

    # Calculate golden reference using dequantized values
    expected = []
    for col in range(16):
        dot = torch.dot(act_dequant, weights_dequant[:, col])
        expected.append(dot.item())

    cocotb.log.info(f"Results:   {[f'{r:.6f}' for r in results]}")
    cocotb.log.info(f"Expected:  {[f'{e:.6f}' for e in expected]}")

    # Calculate errors
    max_abs_err = 0.0
    max_rel_err = 0.0
    for i in range(16):
        abs_err = abs(results[i] - expected[i])
        rel_err = abs_err / abs(expected[i]) if expected[i] != 0 else 0
        if abs_err > max_abs_err:
            max_abs_err = abs_err
        if rel_err > max_rel_err:
            max_rel_err = rel_err
            max_rel_col = i

    cocotb.log.info(f"Max absolute error: {max_abs_err:.6f}")
    cocotb.log.info(f"Max relative error: {max_rel_err*100:.4f}% (col {max_rel_col})")

    # GFP quantization + FP24 rounding introduces some error
    # Use 1% relative tolerance (observed max ~0.01%)
    REL_TOL = 0.01
    for i in range(16):
        abs_err = abs(results[i] - expected[i])
        rel_err = abs_err / abs(expected[i]) if expected[i] != 0 else 0
        assert rel_err < REL_TOL, f"Column {i}: rel error {rel_err*100:.2f}% > {REL_TOL*100}% (got {results[i]:.6f}, expected {expected[i]:.6f})"

    cocotb.log.info("TEST PASSED: GFP random floats test")


@cocotb.test()
async def test_gfp_large_values(dut):
    """Test with large-scale GFP values to verify exponent handling.

    Tests values in range [0, 1000] to exercise:
    - Large exponent values
    - Exponent variation between groups
    - Numerical stability with large accumulations
    """
    if not HAS_GFP:
        cocotb.log.warning("Skipping GFP test - torch/gfp not available")
        return

    tb = ComputeEngineMlpTB(dut)

    # Start clock
    clock = Clock(dut.i_clk, 10, unit="ns")
    cocotb.start_soon(clock.start())

    # Reset
    await tb.reset()

    # Configure for 1 NV per column
    dut.i_vec_len.value = 1
    await RisingEdge(dut.i_clk)

    # Create GFP8 data type
    gfp8 = gfp.GFPDataType(mantissa_bits=8, exp_bits=8)

    # Generate large-scale float data
    torch.manual_seed(456)
    activations_float = torch.rand(128) * 1000.0  # [0, 1000]
    weights_float = torch.rand(128, 16) * 1000.0  # [0, 1000]

    cocotb.log.info(f"Activation range: [{activations_float.min():.2f}, {activations_float.max():.2f}]")
    cocotb.log.info(f"Weight range: [{weights_float.min():.2f}, {weights_float.max():.2f}]")

    # Quantize
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

    # Dequantize for golden reference
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

    cocotb.log.info(f"Act exponents (BFP8): {act_exponents} (large values need higher exponents)")

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

    cocotb.log.info("Data loaded. Starting weight fill phase...")
    await tb.start_fill()

    fill_done = await tb.wait_fill_done()
    assert fill_done, "Weight fill timed out"

    cocotb.log.info("Weight fill complete. Starting compute phase...")
    await tb.start_compute()

    compute_done = await tb.wait_compute_done()
    assert compute_done, "Compute timed out"

    cocotb.log.info("Compute complete. Checking results...")
    await ClockCycles(dut.i_clk, 5)

    # Get hardware results
    results = tb.get_results()

    # Calculate golden reference
    expected = []
    for col in range(16):
        dot = torch.dot(act_dequant, weights_dequant[:, col])
        expected.append(dot.item())

    cocotb.log.info(f"Results:   {[f'{r:.2f}' for r in results]}")
    cocotb.log.info(f"Expected:  {[f'{e:.2f}' for e in expected]}")

    # Calculate errors
    max_abs_err = 0.0
    max_rel_err = 0.0
    for i in range(16):
        abs_err = abs(results[i] - expected[i])
        rel_err = abs_err / abs(expected[i]) if expected[i] != 0 else 0
        if abs_err > max_abs_err:
            max_abs_err = abs_err
        if rel_err > max_rel_err:
            max_rel_err = rel_err
            max_rel_col = i

    cocotb.log.info(f"Max absolute error: {max_abs_err:.2f}")
    cocotb.log.info(f"Max relative error: {max_rel_err*100:.4f}% (col {max_rel_col})")

    # Large values have higher absolute error but should maintain relative accuracy
    REL_TOL = 0.01
    for i in range(16):
        abs_err = abs(results[i] - expected[i])
        rel_err = abs_err / abs(expected[i]) if expected[i] != 0 else 0
        assert rel_err < REL_TOL, f"Column {i}: rel error {rel_err*100:.2f}% > {REL_TOL*100}% (got {results[i]:.2f}, expected {expected[i]:.2f})"

    cocotb.log.info("TEST PASSED: GFP large values test")


@cocotb.test()
async def test_batch_dimension(dut):
    """Test with batch dimension B > 1.

    Tests the BCV loop with:
    - B = 2 batches (left_ugd_len)
    - C = 16 columns (fixed)
    - V = 1 NV per output

    Activation: 2 NVs (one per batch)
      - Batch 0: all 1s
      - Batch 1: all 2s
    Weights: 16 columns, each with all 1s

    Expected:
      - Batch 0 output: 128 * 1 * 1 = 128 for all 16 columns
      - Batch 1 output: 128 * 2 * 1 = 256 for all 16 columns
      - Total: 2 result pulses, 32 results total
    """
    tb = ComputeEngineMlpTB(dut)

    # Start clock
    clock = Clock(dut.i_clk, 10, units="ns")
    cocotb.start_soon(clock.start())

    # Reset
    await tb.reset()

    # Configure for batch dimension
    B = 2   # 2 batches
    V = 1   # 1 NV per output
    dut.i_left_ugd_len.value = B
    dut.i_right_ugd_len.value = 16  # Fixed C=16
    dut.i_vec_len.value = V
    await RisingEdge(dut.i_clk)

    cocotb.log.info(f"Testing batch dimension: B={B}, C=16, V={V}")

    # Load activation NVs (B=2 batches, V=1 each)
    # Batch 0: all 1s (NV index 0)
    act_mantissas_0 = [1] * 128
    act_exponents_0 = [BFP8E8_BIAS] * 4
    await tb.load_activation_nv(0, act_mantissas_0, act_exponents_0)

    # Batch 1: all 2s (NV index 1)
    act_mantissas_1 = [2] * 128
    act_exponents_1 = [BFP8E8_BIAS] * 4
    await tb.load_activation_nv(1, act_mantissas_1, act_exponents_1)

    # Load weights (16 columns, 1 NV each, all 1s)
    for col in range(16):
        wt_mantissas = [1] * 128
        wt_exponents = [BFP8E8_BIAS] * 4
        await tb.load_weight_nv(col, 0, wt_mantissas, wt_exponents)

    cocotb.log.info("Data loaded. Starting weight fill phase...")
    await tb.start_fill()

    fill_done = await tb.wait_fill_done()
    assert fill_done, "Weight fill timed out"

    cocotb.log.info("Weight fill complete. Starting compute phase...")
    await ClockCycles(dut.i_clk, 5)

    await tb.start_compute()

    # Collect results from both batches
    all_results = []
    result_valid_count = 0

    for cycle in range(10000):
        await RisingEdge(dut.i_clk)

        # Check for result valid
        if dut.o_result_valid.value == 1:
            result_valid_count += 1
            batch_results = tb.get_results()
            all_results.append(batch_results)
            cocotb.log.info(f"Result valid pulse {result_valid_count}: {batch_results}")

        # Check for compute done
        if dut.o_compute_done.value == 1:
            cocotb.log.info(f"Compute done after {cycle} cycles")
            break
    else:
        assert False, "Compute timed out"

    # Verify we got B result pulses
    assert result_valid_count == B, f"Expected {B} result pulses, got {result_valid_count}"

    # Compute golden reference using numpy
    # Batch 0: act = [1,1,...,1] (128 elements), weight = [1,1,...,1] (128 elements)
    act_batch_0 = np.ones(128)
    wt_vec = np.ones(128)
    golden_batch_0 = float(np.dot(act_batch_0, wt_vec))
    expected_batch_0 = [golden_batch_0] * 16

    # Batch 1: act = [2,2,...,2] (128 elements), weight = [1,1,...,1] (128 elements)
    act_batch_1 = np.full(128, 2.0)
    golden_batch_1 = float(np.dot(act_batch_1, wt_vec))
    expected_batch_1 = [golden_batch_1] * 16

    cocotb.log.info(f"Batch 0 results:   {all_results[0]}")
    cocotb.log.info(f"Batch 0 expected (numpy golden):  {expected_batch_0}")
    cocotb.log.info(f"Batch 1 results:   {all_results[1]}")
    cocotb.log.info(f"Batch 1 expected (numpy golden):  {expected_batch_1}")

    for i in range(16):
        assert all_results[0][i] == expected_batch_0[i], \
            f"Batch 0, Column {i}: got {all_results[0][i]}, expected {expected_batch_0[i]}"
        assert all_results[1][i] == expected_batch_1[i], \
            f"Batch 1, Column {i}: got {all_results[1][i]}, expected {expected_batch_1[i]}"

    cocotb.log.info("TEST PASSED: Batch dimension test (B=2) (numpy golden verified)")


@cocotb.test()
async def test_batch_with_multi_nv(dut):
    """Test with batch dimension B > 1 AND multiple NVs per output (V > 1).

    Tests the BCV loop with:
    - B = 2 batches
    - C = 16 columns (fixed)
    - V = 2 NVs per output

    Memory layout:
    - Left (activations): B * V = 4 NVs total
      - Batch 0, NV 0: all 1s (index 0)
      - Batch 0, NV 1: all 1s (index 1)
      - Batch 1, NV 0: all 2s (index 2)
      - Batch 1, NV 1: all 2s (index 3)
    - Right (weights): C * V = 32 NVs total

    Expected:
      - Batch 0 output: (1*1)*128 + (1*1)*128 = 256 per column
      - Batch 1 output: (2*1)*128 + (2*1)*128 = 512 per column
    """
    tb = ComputeEngineMlpTB(dut)

    # Start clock
    clock = Clock(dut.i_clk, 10, units="ns")
    cocotb.start_soon(clock.start())

    # Reset
    await tb.reset()

    # Configure for batch + multi-NV
    B = 2   # 2 batches
    V = 2   # 2 NVs per output
    dut.i_left_ugd_len.value = B
    dut.i_right_ugd_len.value = 16  # Fixed C=16
    dut.i_vec_len.value = V
    await RisingEdge(dut.i_clk)

    cocotb.log.info(f"Testing batch + multi-NV: B={B}, C=16, V={V}")

    # Load activation NVs
    # NV index = batch * V + nv_within_batch
    # Batch 0, NV 0 (index 0): all 1s
    await tb.load_activation_nv(0, [1] * 128, [BFP8E8_BIAS] * 4)
    # Batch 0, NV 1 (index 1): all 1s
    await tb.load_activation_nv(1, [1] * 128, [BFP8E8_BIAS] * 4)
    # Batch 1, NV 0 (index 2): all 2s
    await tb.load_activation_nv(2, [2] * 128, [BFP8E8_BIAS] * 4)
    # Batch 1, NV 1 (index 3): all 2s
    await tb.load_activation_nv(3, [2] * 128, [BFP8E8_BIAS] * 4)

    # Load weights (16 columns, 2 NVs each, all 1s)
    for col in range(16):
        for nv in range(V):
            wt_mantissas = [1] * 128
            wt_exponents = [BFP8E8_BIAS] * 4
            await tb.load_weight_nv(col, nv, wt_mantissas, wt_exponents)

    cocotb.log.info("Data loaded. Starting weight fill phase...")
    await tb.start_fill()

    fill_done = await tb.wait_fill_done()
    assert fill_done, "Weight fill timed out"

    cocotb.log.info("Weight fill complete. Starting compute phase...")
    await ClockCycles(dut.i_clk, 5)

    await tb.start_compute()

    # Collect results from both batches
    all_results = []
    result_valid_count = 0

    for cycle in range(20000):  # Longer timeout for more computation
        await RisingEdge(dut.i_clk)

        if dut.o_result_valid.value == 1:
            result_valid_count += 1
            batch_results = tb.get_results()
            all_results.append(batch_results)
            cocotb.log.info(f"Result valid pulse {result_valid_count}: {batch_results}")

        if dut.o_compute_done.value == 1:
            cocotb.log.info(f"Compute done after {cycle} cycles")
            break
    else:
        assert False, "Compute timed out"

    # Verify we got B result pulses
    assert result_valid_count == B, f"Expected {B} result pulses, got {result_valid_count}"

    # Compute golden reference using numpy
    # Batch 0: act = [1,1,...,1, 1,1,...,1] (256 elements), weight = [1,1,...,1] (256 elements)
    # V=2 NVs, each with 128 elements
    act_batch_0 = np.ones(256)  # NV0 and NV1 both all 1s
    wt_vec = np.ones(256)       # 2 NVs of weights, all 1s
    golden_batch_0 = float(np.dot(act_batch_0, wt_vec))
    expected_batch_0 = [golden_batch_0] * 16

    # Batch 1: act = [2,2,...,2, 2,2,...,2] (256 elements), weight = [1,1,...,1] (256 elements)
    act_batch_1 = np.full(256, 2.0)  # NV0 and NV1 both all 2s
    golden_batch_1 = float(np.dot(act_batch_1, wt_vec))
    expected_batch_1 = [golden_batch_1] * 16

    cocotb.log.info(f"Batch 0 results:   {all_results[0]}")
    cocotb.log.info(f"Batch 0 expected (numpy golden):  {expected_batch_0}")
    cocotb.log.info(f"Batch 1 results:   {all_results[1]}")
    cocotb.log.info(f"Batch 1 expected (numpy golden):  {expected_batch_1}")

    for i in range(16):
        assert all_results[0][i] == expected_batch_0[i], \
            f"Batch 0, Column {i}: got {all_results[0][i]}, expected {expected_batch_0[i]}"
        assert all_results[1][i] == expected_batch_1[i], \
            f"Batch 1, Column {i}: got {all_results[1][i]}, expected {expected_batch_1[i]}"

    cocotb.log.info("TEST PASSED: Batch with multi-NV test (B=2, V=2) (numpy golden verified)")


@cocotb.test()
async def test_full_bcv(dut):
    """Test with full BCV dimensions: B=16, C=16, V=8 using GFP golden reference.

    This is a comprehensive test with:
    - B = 16 batches
    - C = 16 columns (fixed)
    - V = 8 NVs per output

    Memory layout:
    - Left (activations): B * V = 128 NVs total, shape [B, V*128] = [16, 1024]
    - Right (weights): C * V = 128 NVs total, shape [V*128, C] = [1024, 16]

    Golden reference is computed using Python matrix multiplication on
    dequantized GFP values, matching hardware computation exactly.
    """
    if not HAS_GFP:
        cocotb.log.warning("Skipping full BCV test - torch/gfp not available")
        return

    tb = ComputeEngineMlpTB(dut)

    # Start clock
    clock = Clock(dut.i_clk, 10, units="ns")
    cocotb.start_soon(clock.start())

    # Reset
    await tb.reset()

    # Configure for full BCV
    B = 16  # 16 batches
    C = 16  # 16 columns (fixed)
    V = 8   # 8 NVs per output
    NV_SIZE = 128  # Elements per NV
    dut.i_left_ugd_len.value = B
    dut.i_right_ugd_len.value = C
    dut.i_vec_len.value = V
    await RisingEdge(dut.i_clk)

    cocotb.log.info(f"Testing full BCV: B={B}, C={C}, V={V}")
    cocotb.log.info(f"  Left NVs: {B * V} = {B}*{V}")
    cocotb.log.info(f"  Right NVs: {C * V} = {C}*{V}")
    cocotb.log.info(f"  Total outputs: {B * C} = {B}*{C}")

    # Create GFP8 data type
    gfp8 = gfp.GFPDataType(mantissa_bits=8, exp_bits=8)

    # Generate random float data
    torch.manual_seed(12345)
    # Activations: [B, V*NV_SIZE] = [16, 1024]
    activations_float = torch.rand(B, V * NV_SIZE) * 2.0 - 1.0  # [-1, 1]
    # Weights: [V*NV_SIZE, C] = [1024, 16]
    weights_float = torch.rand(V * NV_SIZE, C) * 2.0 - 1.0  # [-1, 1]

    cocotb.log.info(f"Activation shape: {activations_float.shape}, range: [{activations_float.min():.4f}, {activations_float.max():.4f}]")
    cocotb.log.info(f"Weight shape: {weights_float.shape}, range: [{weights_float.min():.4f}, {weights_float.max():.4f}]")

    # Quantize activations - each batch row separately, grouped along inner dimension
    # Shape: [B, V*NV_SIZE] -> quantize along axis=1 with group_size=32
    act_gfp_list = []
    for b in range(B):
        act_row = activations_float[b]  # [V*NV_SIZE]
        act_gfp = gfp.GFPTensor(
            original_shape=act_row.shape,
            group_axis=-1,
            group_size=32,
            dtype=gfp8,
            original_data=act_row,
        )
        act_gfp_list.append(act_gfp)

    # Quantize weights - each column separately, grouped along rows
    # Shape: [V*NV_SIZE, C] -> for each column, quantize along axis=0 with group_size=32
    wt_gfp_list = []
    for c in range(C):
        wt_col = weights_float[:, c]  # [V*NV_SIZE]
        wt_gfp = gfp.GFPTensor(
            original_shape=wt_col.shape,
            group_axis=-1,
            group_size=32,
            dtype=gfp8,
            original_data=wt_col,
        )
        wt_gfp_list.append(wt_gfp)

    # Compute golden reference using dequantized values
    # For each batch b and column c: result[b,c] = dot(act_dequant[b], wt_dequant[:,c])
    golden_results = torch.zeros(B, C)
    for b in range(B):
        act_dequant = act_gfp_list[b].dequantize()  # [V*NV_SIZE]
        for c in range(C):
            wt_dequant = wt_gfp_list[c].dequantize()  # [V*NV_SIZE]
            golden_results[b, c] = torch.dot(act_dequant, wt_dequant)

    cocotb.log.info(f"Golden results shape: {golden_results.shape}")
    cocotb.log.info(f"Golden results range: [{golden_results.min():.4f}, {golden_results.max():.4f}]")

    # Load activation NVs to hardware
    # NV index = batch * V + nv_within_batch
    for batch in range(B):
        act_gfp = act_gfp_list[batch]
        # act_gfp.mantissa_data shape: [num_groups, 32] where num_groups = V*NV_SIZE/32 = V*4
        # act_gfp.exp_data shape: [num_groups]
        for nv in range(V):
            nv_idx = batch * V + nv
            mantissas = []
            exponents = []
            # Each NV has 4 groups (128 elements / 32 per group)
            for g in range(4):
                group_idx = nv * 4 + g
                group_mantissas = act_gfp.mantissa_data[group_idx].tolist()
                mantissas.extend(group_mantissas)
                group_exp = int(act_gfp.exp_data[group_idx].item()) + ACX_BFP_M8E8_BIAS
                exponents.append(group_exp)
            await tb.load_activation_nv(nv_idx, mantissas, exponents)
        if batch % 4 == 0:
            cocotb.log.info(f"  Loaded activation batch {batch}")

    # Load weight NVs to hardware
    # Weight NV index for col c, nv v: col * V + v (column-major in row_bram)
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
        if col % 4 == 0:
            cocotb.log.info(f"  Loaded weight column {col}")

    cocotb.log.info("Data loaded. Starting weight fill phase...")
    await tb.start_fill()

    fill_done = await tb.wait_fill_done(timeout_cycles=50000)
    assert fill_done, "Weight fill timed out"

    cocotb.log.info("Weight fill complete. Starting compute phase...")
    await ClockCycles(dut.i_clk, 5)

    await tb.start_compute()

    # Collect results from all batches
    all_results = []
    result_valid_count = 0

    for cycle in range(100000):  # Long timeout for large computation
        await RisingEdge(dut.i_clk)

        if dut.o_result_valid.value == 1:
            result_valid_count += 1
            batch_results = tb.get_results()
            all_results.append(batch_results)
            if result_valid_count <= 2 or result_valid_count > B - 2:
                cocotb.log.info(f"Result valid pulse {result_valid_count}: {[f'{r:.4f}' for r in batch_results[:4]]}...")

        if dut.o_compute_done.value == 1:
            cocotb.log.info(f"Compute done after {cycle} cycles")
            break
    else:
        assert False, "Compute timed out"

    # Verify we got B result pulses
    assert result_valid_count == B, f"Expected {B} result pulses, got {result_valid_count}"

    # Verify results against golden reference
    cocotb.log.info("Verifying hardware results against Python golden reference...")

    # Debug: Print first few batches comparison
    cocotb.log.info("=== Detailed comparison (first 2 batches) ===")
    for batch in range(min(2, B)):
        hw_row = all_results[batch][:4]
        golden_row = [golden_results[batch, c].item() for c in range(4)]
        cocotb.log.info(f"Batch {batch} HW:     {[f'{x:.4f}' for x in hw_row]}")
        cocotb.log.info(f"Batch {batch} Golden: {[f'{x:.4f}' for x in golden_row]}")

    max_abs_err = 0.0
    max_rel_err = 0.0
    errors = 0

    for batch in range(B):
        for col in range(C):
            hw_result = all_results[batch][col]
            golden = golden_results[batch, col].item()

            abs_err = abs(hw_result - golden)
            rel_err = abs_err / abs(golden) if golden != 0 else 0

            if abs_err > max_abs_err:
                max_abs_err = abs_err
            if rel_err > max_rel_err:
                max_rel_err = rel_err
                max_rel_batch = batch
                max_rel_col = col

            # Use 1% relative tolerance for GFP quantization + FP24 rounding
            REL_TOL = 0.01
            if rel_err > REL_TOL:
                if errors < 5:
                    cocotb.log.error(f"Batch {batch}, Col {col}: HW={hw_result:.6f}, Golden={golden:.6f}, RelErr={rel_err*100:.2f}%")
                errors += 1

    cocotb.log.info(f"Max absolute error: {max_abs_err:.6f}")
    cocotb.log.info(f"Max relative error: {max_rel_err*100:.4f}% (batch {max_rel_batch}, col {max_rel_col})")

    if errors > 0:
        cocotb.log.error(f"Total errors: {errors} / {B * C}")
        assert False, f"Found {errors} mismatches exceeding {REL_TOL*100}% tolerance"

    cocotb.log.info(f"All {B * C} results verified against golden reference!")
    cocotb.log.info("TEST PASSED: Full BCV test (B=16, C=16, V=8) with GFP golden verification")
