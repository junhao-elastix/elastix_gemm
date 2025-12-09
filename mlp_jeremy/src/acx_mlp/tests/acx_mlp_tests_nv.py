"""
Testbench for mlp_bram_col_ctrl.sv - Native Vector Weight Loading & Compute

Validates the MLP BRAM Column Controller with:
  1. Native Vector weight loading (16 NVs to 16 columns)
  2. Native Vector activation streaming with automatic control signal generation
  3. Vector-matrix multiplication: [1×128] × [128×16] = [1×16]

Native Vector Format:
    - 128 mantissas (8-bit each) = 1024 bits
    - 4 exponents (8-bit each), one per 32 elements = 32 bits
    - Elements 0-31 share exp[7:0], 32-63 share exp[15:8], etc.
"""

from __future__ import annotations

from typing import Any
import math
import torch

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge

from emulator import group_floating_point as gfp
from sim_utils.build_misc import int_to_float24

# GFP8 bias constants
GFP8E8_BIAS = 127   # IEEE standard: 2^(8-1) - 1 = 127
BFP8E8_BIAS = 133   # MLP native bias: 127 + 6 (mantissa format offset)
ACX_BFP_M8E8_BIAS = BFP8E8_BIAS - GFP8E8_BIAS  # = 6


def pack_bytes_lsb(byte_list: list[int]) -> int:
    """Pack a list of bytes into a single integer. byte[0] is LSB.

    For 128-element mantissa arrays where element 0 should map to bits [7:0].

    Args:
        byte_list: list of bytes to pack

    Returns:
        Packed integer.
    """
    result = 0
    for i, byte in enumerate(byte_list):
        # Handle signed bytes (convert to unsigned)
        byte_unsigned = byte & 0xFF
        result |= byte_unsigned << (i * 8)
    return result


def pack_bytes_msb(byte_list: list[int]) -> int:
    """Pack a list of bytes into a single integer. byte[0] is MSB.

    For 8-element arrays (like din) where the reference testbench uses MSB-first.

    Args:
        byte_list: list of bytes to pack

    Returns:
        Packed integer.
    """
    result = 0
    for i, byte in enumerate(reversed(byte_list)):
        # Handle signed bytes (convert to unsigned)
        byte_unsigned = byte & 0xFF
        result |= byte_unsigned << (i * 8)
    return result


class MLPBramColCtrlTestbench:
    """Test harness for MLP BRAM Column Controller with Native Vector support"""

    def __init__(self, dut):
        self.dut = dut
        self.NUM_MLPS = int(dut.NUM_MLPS.value) if hasattr(dut, 'NUM_MLPS') else 8
        self.NUM_COLS = self.NUM_MLPS * 2  # 2 banks per MLP = 16 columns
        self.CLK_PERIOD = 10  # 100MHz in ns

        cocotb.log.info(f"Testbench initialized for {self.NUM_MLPS} MLPs ({self.NUM_COLS} columns)")

    async def setup_clock(self):
        """Setup the clock for the DUT"""
        self.clock = Clock(self.dut.clk, self.CLK_PERIOD, unit="ns")
        cocotb.start_soon(self.clock.start())
        cocotb.log.debug(f"Clock setup: {self.CLK_PERIOD}ns period")

    async def reset_system(self):
        """Reset the system"""
        cocotb.log.debug("Resetting system...")

        # Initialize all signals
        self.dut.rstn.value = 0
        self.dut.i_wt_valid.value = 0
        self.dut.i_nv_right_man.value = 0
        self.dut.i_nv_right_exp.value = 0
        self.dut.i_col_sel.value = 0
        self.dut.i_act_valid.value = 0
        self.dut.i_nv_left_man.value = 0
        self.dut.i_nv_left_exp.value = 0
        self.dut.i_new_dot.value = 0
        self.dut.i_dout_ready.value = 1

        # Hold reset for 5 cycles
        await self.clock.cycles(5)

        # Release reset and let system stabilize
        self.dut.rstn.value = 1
        await self.clock.cycles(10)

        cocotb.log.debug("Reset complete")

    async def load_native_vector_to_column(self, col_idx: int,
                                           mantissas: list[int],
                                           exponents: list[int]):
        """Load one Native Vector (128 elements) to a specific column.

        Args:
            col_idx: Target column index (0-15)
            mantissas: List of 128 mantissa values (8-bit each)
            exponents: List of 4 exponent values (8-bit each)
                       exp[0] for elements 0-31, exp[1] for 32-63, etc.
        """
        assert len(mantissas) == 128, f"Expected 128 mantissas, got {len(mantissas)}"
        assert len(exponents) == 4, f"Expected 4 exponents, got {len(exponents)}"
        assert 0 <= col_idx < self.NUM_COLS, f"Column index {col_idx} out of range"

        # Pack mantissas into 1024-bit value
        # Using LSB-first: element 0 at bits [7:0], element 1 at bits [15:8], etc.
        nv_man = pack_bytes_lsb(mantissas)

        # Pack exponents into 32-bit value
        # exp[0] for elements 0-31 at bits [7:0], exp[1] at bits [15:8], etc.
        nv_exp = pack_bytes_lsb(exponents)

        if col_idx == 0:  # Debug first column only
            cocotb.log.info(f"Loading NV to column {col_idx}")
            cocotb.log.info(f"  Mantissas[0:7]: {mantissas[0:8]}")
            cocotb.log.info(f"  Exponents: {exponents}")
            cocotb.log.info(f"  Packed nv_man (first 128 bits): 0x{(nv_man & ((1<<128)-1)):032x}")
            cocotb.log.info(f"  Packed nv_exp: 0x{nv_exp:08x}")

        # Wait for controller to be ready
        while self.dut.o_wt_ready.value != 1:
            await RisingEdge(self.dut.clk)

        # Apply weight data
        self.dut.i_nv_right_man.value = nv_man
        self.dut.i_nv_right_exp.value = nv_exp
        self.dut.i_col_sel.value = col_idx
        self.dut.i_wt_valid.value = 1

        await RisingEdge(self.dut.clk)

        # Deassert valid after one cycle (data is latched)
        self.dut.i_wt_valid.value = 0

        # Wait for loading to complete (16 cycles for WT_LOAD + 1 for WT_DONE)
        for cycle in range(18):
            await RisingEdge(self.dut.clk)
            # Debug first two cycles of first 4 columns to understand wraddr pattern
            if col_idx < 4 and cycle < 2:
                try:
                    wt_state = int(self.dut.wt_state_reg.value)
                    wraddr = int(self.dut.mlp_wraddr.value)
                    wren = int(self.dut.mlp_wren.value)
                    bram_din = int(self.dut.mlp_bram_din.value)
                    cocotb.log.info(f"  col{col_idx} WT cycle {cycle}: state={wt_state}, wraddr={wraddr}, wren=0x{wren:02x}, bram_din=0x{bram_din:018x}")
                except Exception as e:
                    cocotb.log.warning(f"  col{col_idx} WT cycle {cycle}: Could not read signals: {e}")

        cocotb.log.debug(f"Column {col_idx} loaded")

    async def load_weight_matrix(self, weights: torch.Tensor, exp_data: torch.Tensor = None):
        """Load a full 128×16 weight matrix into all columns.

        Args:
            weights: Tensor of shape (128, 16) - weight mantissas
            exp_data: Optional tensor of shape (4, 16) - exponents per column
                      If None, uses default BFP8E8_BIAS for all
        """
        assert weights.shape == (128, 16), f"Expected (128, 16), got {weights.shape}"

        for col_idx in range(16):
            mantissas = weights[:, col_idx].tolist()

            if exp_data is not None:
                exponents = exp_data[:, col_idx].tolist()
            else:
                # Default exponent = BFP8E8_BIAS for unit scale
                exponents = [BFP8E8_BIAS] * 4

            await self.load_native_vector_to_column(col_idx, mantissas, exponents)

    async def compute_with_activations(self, mantissas: list[int], exponents: list[int],
                                       new_dot: bool = True):
        """Submit activation NV and run compute phase.

        The controller automatically:
          - Streams din over 16 cycles
          - Generates ce, load, accumulate, rdaddr signals
          - Drains pipeline after streaming

        Args:
            mantissas: List of 128 activation mantissa values
            exponents: List of 4 exponent values
            new_dot: If True, reset accumulator (start new dot product)
        """
        assert len(mantissas) == 128, f"Expected 128 mantissas, got {len(mantissas)}"
        assert len(exponents) == 4, f"Expected 4 exponents, got {len(exponents)}"

        # Pack data using LSB-first (same as weight packing)
        nv_man = pack_bytes_lsb(mantissas)
        nv_exp = pack_bytes_lsb(exponents)

        cocotb.log.debug(f"Starting compute, new_dot={new_dot}")

        # Wait for activation ready
        while self.dut.o_act_ready.value != 1:
            await RisingEdge(self.dut.clk)

        # Apply activation data
        self.dut.i_nv_left_man.value = nv_man
        self.dut.i_nv_left_exp.value = nv_exp
        self.dut.i_new_dot.value = 1 if new_dot else 0
        self.dut.i_act_valid.value = 1

        await RisingEdge(self.dut.clk)

        # Deassert valid
        self.dut.i_act_valid.value = 0
        self.dut.i_new_dot.value = 0

        # Debug: check state AFTER the clock edge where i_act_valid was sampled
        comp_state_after_valid = int(self.dut.comp_state_reg.value)
        cocotb.log.info(f"After i_act_valid clock edge: comp_state={comp_state_after_valid}")

        # Wait one more cycle for FSM to transition (registered state update)
        await RisingEdge(self.dut.clk)
        comp_state_after_transition = int(self.dut.comp_state_reg.value)
        cocotb.log.info(f"After transition clock edge: comp_state={comp_state_after_transition}")

        # Wait for compute to complete (16 stream cycles + drain cycles)
        # Monitor o_dout_valid to know when results are ready
        # Note: o_dout_valid is 1 when comp_state == COMP_IDLE, so we need to wait
        # for it to go LOW first (compute starts), then HIGH again (compute done)
        cycle = 0
        dout_valid = int(self.dut.o_dout_valid.value)
        comp_state = int(self.dut.comp_state_reg.value)
        wt_state = int(self.dut.wt_state_reg.value)
        is_loading = (wt_state == 1)  # WT_LOAD
        cocotb.log.info(f"Before compute wait: o_dout_valid={dout_valid}, comp_state={comp_state}, wt_state={wt_state}, is_loading={is_loading}")

        # If o_dout_valid is already high, we need to wait for it to go low first
        # (meaning compute has started), then wait for it to go high again
        if self.dut.o_dout_valid.value == 1:
            cocotb.log.info("o_dout_valid is already 1, waiting for it to go low (compute start)")
            # Wait for dout_valid to go low (compute started)
            for _ in range(5):  # Should happen within a few cycles
                await RisingEdge(self.dut.clk)
                if self.dut.o_dout_valid.value != 1:
                    break
                cycle += 1
            cocotb.log.info(f"o_dout_valid went low at cycle {cycle}")

        # Now wait for completion
        while self.dut.o_dout_valid.value != 1:
            await RisingEdge(self.dut.clk)
            if cycle < 5:  # Debug first few cycles
                try:
                    comp_state = int(self.dut.comp_state_reg.value)
                    comp_cnt = int(self.dut.comp_cycle_cnt.value)
                    din_val = int(self.dut.mlp_din.value)
                    rdaddr = int(self.dut.mlp_rdaddr.value)
                    ce = int(self.dut.mlp_ce.value)
                    load = int(self.dut.mlp_load.value)
                    accum = int(self.dut.mlp_accumulate.value)
                    # Try to read BRAM output
                    try:
                        bram_dout = int(self.dut.u_mlp_bram_col.mlp_col_base.bram_dout.value)
                        bram_str = f", bram_dout=0x{bram_dout:036x}"
                    except:
                        bram_str = ""
                    cocotb.log.info(f"  COMP cycle {cycle}: state={comp_state}, cnt={comp_cnt}, ce={ce}, load={load}, accum={accum}, rdaddr={rdaddr}, din=0x{din_val:018x}{bram_str}")
                except Exception as e:
                    cocotb.log.warning(f"  COMP cycle {cycle}: Could not read signals: {e}")
            cycle += 1

        cocotb.log.info(f"Compute complete after {cycle} cycles")
        # Extra debug: check MLP output after a few more cycles
        for extra in range(3):
            await RisingEdge(self.dut.clk)
            try:
                raw = int(self.dut.o_dout[0].value)
                ce = int(self.dut.mlp_ce.value)
                cocotb.log.info(f"  Extra cycle {extra}: o_dout[0]=0x{raw:018x}, ce={ce}")
            except Exception as e:
                pass

    def get_outputs(self) -> list[tuple[float, float]]:
        """Retrieve output dot products from DUT.

        Returns:
            List of (col_even_result, col_odd_result) tuples for each MLP.
            Index mapping:
              - results[mlp_idx][0] = column 2*mlp_idx result (even column, Bank CD)
              - results[mlp_idx][1] = column 2*mlp_idx+1 result (odd column, Bank AB)
        """
        results = []

        for mlp_index in range(self.NUM_MLPS):
            mlp_out = self.dut.o_dout[mlp_index].value
            # dout[23:0] = Bank CD result (even column)
            # dout[47:24] = Bank AB result (odd column)
            ed0 = int_to_float24(mlp_out[23:0].to_signed())  # Even column
            ed1 = int_to_float24(mlp_out[47:24].to_signed())  # Odd column
            results.append((ed0, ed1))

        return results

    def get_flat_outputs(self) -> list[float]:
        """Get outputs as flat list indexed by column (0-15).

        Returns:
            List of 16 float results, one per column.
        """
        paired = self.get_outputs()

        # Reorder to column order: [col0, col1, col2, ..., col15]
        result = [0.0] * 16
        for mlp_idx in range(self.NUM_MLPS):
            result[2*mlp_idx] = paired[mlp_idx][0]      # even column
            result[2*mlp_idx + 1] = paired[mlp_idx][1]  # odd column
        return result

    def verify_outputs(self, expected: list[float], rel_tol: float = 1e-3):
        """Verify DUT outputs against expected values.

        Args:
            expected: List of 16 expected dot product results (one per column)
            rel_tol: Relative tolerance for comparison
        """
        actual = self.get_flat_outputs()
        errors = 0

        for col_idx in range(16):
            exp = expected[col_idx]
            act = actual[col_idx]

            if not math.isclose(act, exp, rel_tol=rel_tol, abs_tol=rel_tol):
                cocotb.log.error(f"Column {col_idx} mismatch: expected {exp}, got {act}")
                errors += 1
            else:
                cocotb.log.debug(f"Column {col_idx} OK: expected {exp}, got {act}")

        assert errors == 0, f"{errors} columns failed verification"
        cocotb.log.info("All 16 column outputs verified successfully")


# =============================================================================
# Test Cases
# =============================================================================

@cocotb.test()
async def test_simple_identity(dut: Any) -> None:
    """Test with identity-like weights (all 1s) and simple activations."""
    tb = MLPBramColCtrlTestbench(dut)
    await tb.setup_clock()
    await tb.reset_system()

    # Create simple test data
    # Activations: all 1s (128 elements)
    act_mantissas = [1] * 128
    act_exponents = [BFP8E8_BIAS] * 4  # exp = 0 in IEEE (scale = 1.0)

    # Weights: all 1s (128×16)
    weight_mantissas = torch.ones((128, 16), dtype=torch.int32)

    # Load weights
    await tb.load_weight_matrix(weight_mantissas)

    # Debug: check some internal signals before compute
    cocotb.log.info(f"Before compute - wt_state: {dut.wt_state_reg.value}")
    cocotb.log.info(f"Before compute - comp_state: {dut.comp_state_reg.value}")
    cocotb.log.info(f"Before compute - o_act_ready: {dut.o_act_ready.value}")

    # Compute
    await tb.compute_with_activations(act_mantissas, act_exponents, new_dot=True)

    # Debug: check output raw values
    for i in range(8):
        raw = int(dut.o_dout[i].value)
        cocotb.log.info(f"MLP {i} raw output: 0x{raw:018x}")

    # Debug: check internal MLP signals for MLP 0
    try:
        mlp_col = dut.u_mlp_bram_col.mlp_col_base
        mlp = mlp_col.u_mlp_dot16_bfp8
        mlp_dout = int(mlp.mlp_dout.value)
        cocotb.log.info(f"MLP 0 internal mlp_dout: 0x{mlp_dout:018x}")
    except Exception as e:
        cocotb.log.warning(f"Could not read internal MLP signals: {e}")

    # Expected: dot(ones(128), ones(128)) = 128 for each column
    expected = [128.0] * 16
    actual = tb.get_flat_outputs()
    cocotb.log.info(f"test_simple_identity: expected={expected}")
    cocotb.log.info(f"test_simple_identity: actual={actual}")

    tb.verify_outputs(expected, rel_tol=0.01)


@cocotb.test()
async def test_column_identity(dut: Any) -> None:
    """Test that each column computes independently with different weights."""
    tb = MLPBramColCtrlTestbench(dut)
    await tb.setup_clock()
    await tb.reset_system()

    # Activations: all 1s
    act_mantissas = [1] * 128
    act_exponents = [BFP8E8_BIAS] * 4

    # Weights: column c has all (c+1) values
    # So column 0 = all 1s, column 1 = all 2s, ..., column 15 = all 16s
    weight_mantissas = torch.zeros((128, 16), dtype=torch.int32)
    for col in range(16):
        weight_mantissas[:, col] = col + 1

    await tb.load_weight_matrix(weight_mantissas)

    await tb.compute_with_activations(act_mantissas, act_exponents, new_dot=True)

    # Expected: column c = 128 * (c+1)
    expected = [128.0 * (c + 1) for c in range(16)]
    actual = tb.get_flat_outputs()
    cocotb.log.info(f"test_column_identity: expected={expected}")
    cocotb.log.info(f"test_column_identity: actual={actual}")

    tb.verify_outputs(expected, rel_tol=0.01)


@cocotb.test()
async def test_random_int_weights(dut: Any) -> None:
    """Test with random integer weights and activations."""
    tb = MLPBramColCtrlTestbench(dut)
    await tb.setup_clock()
    await tb.reset_system()

    # Generate random data
    torch.manual_seed(42)
    act_mantissas = torch.randint(0, 128, (128,), dtype=torch.int32).tolist()
    act_exponents = [BFP8E8_BIAS] * 4

    weight_mantissas = torch.randint(0, 128, (128, 16), dtype=torch.int32)

    # Load weights
    await tb.load_weight_matrix(weight_mantissas)

    # Compute
    await tb.compute_with_activations(act_mantissas, act_exponents, new_dot=True)

    # Calculate expected results
    act_tensor = torch.tensor(act_mantissas, dtype=torch.float32)
    expected = []
    for col in range(16):
        dot = torch.dot(act_tensor, weight_mantissas[:, col].float())
        expected.append(dot.item())

    # Tolerance based on accumulator precision
    tb.verify_outputs(expected, rel_tol=0.001)


@cocotb.test()
async def test_gfp_quantized(dut: Any) -> None:
    """Test with GFP8-quantized weights and activations."""
    tb = MLPBramColCtrlTestbench(dut)
    await tb.setup_clock()
    await tb.reset_system()

    gfp8 = gfp.GFPDataType(mantissa_bits=8, exp_bits=8)

    # Generate random float data
    torch.manual_seed(123)
    activations_float = torch.rand(128) * 2.0 - 1.0  # [-1, 1]
    weights_float = torch.rand(128, 16) * 2.0 - 1.0

    # Quantize activations with group_size=32 (for NV format with 4 exponents)
    act_gfp = gfp.GFPTensor.quantize_from_float(
        group_axis=-1,
        group_size=32,
        dtype=gfp8,
        original_data=activations_float,
    )

    # Quantize weights with group_size=32
    weights_gfp = gfp.GFPTensor.quantize_from_float(
        group_axis=0,
        group_size=32,
        dtype=gfp8,
        original_data=weights_float,
    )

    # Dequantize for golden reference
    act_dequant = act_gfp.dequantize()
    weights_dequant = weights_gfp.dequantize()

    # Load weights
    for col_idx in range(16):
        mantissas = []
        exponents = []
        for g in range(4):
            # GFP tensor shape: mantissa_data[columns, groups, elements] = [16, 4, 32]
            group_mantissas = weights_gfp.mantissa_data[col_idx, g, :].tolist()
            mantissas.extend(group_mantissas)
            group_exp = int(weights_gfp.exp_data[col_idx, g, 0].item()) + ACX_BFP_M8E8_BIAS
            exponents.append(group_exp)
        await tb.load_native_vector_to_column(col_idx, mantissas, exponents)

    # Prepare activations
    act_mantissas = []
    act_exponents = []
    for g in range(4):
        group_mantissas = act_gfp.mantissa_data[g].tolist()
        act_mantissas.extend(group_mantissas)
        group_exp = act_gfp.exp_data[g].item() + ACX_BFP_M8E8_BIAS
        act_exponents.append(group_exp)

    # Compute
    await tb.compute_with_activations(act_mantissas, act_exponents, new_dot=True)

    # Calculate expected results using dequantized values
    expected = []
    for col in range(16):
        dot = torch.dot(act_dequant, weights_dequant[:, col])
        expected.append(dot.item())

    cocotb.log.info(f"Expected results: {expected}")
    actual = tb.get_flat_outputs()
    cocotb.log.info(f"Actual results: {actual}")

    # GFP quantization introduces error, use looser tolerance
    tb.verify_outputs(expected, rel_tol=0.05)


@cocotb.test()
async def test_accumulation_across_batches(dut: Any) -> None:
    """Test accumulation across multiple activation batches (new_dot=False)."""
    tb = MLPBramColCtrlTestbench(dut)
    await tb.setup_clock()
    await tb.reset_system()

    # Simple weights: all 1s
    weight_mantissas = torch.ones((128, 16), dtype=torch.int32)
    await tb.load_weight_matrix(weight_mantissas)

    # First batch: all 1s -> result = 128
    act1 = [1] * 128
    exp1 = [BFP8E8_BIAS] * 4
    await tb.compute_with_activations(act1, exp1, new_dot=True)

    first_result = tb.get_flat_outputs()
    cocotb.log.info(f"After first batch: {first_result}")

    # Second batch: all 1s, accumulate -> result = 128 + 128 = 256
    act2 = [1] * 128
    exp2 = [BFP8E8_BIAS] * 4
    await tb.compute_with_activations(act2, exp2, new_dot=False)

    # Expected: 256 for each column (accumulated)
    expected = [256.0] * 16
    tb.verify_outputs(expected, rel_tol=0.01)


@cocotb.test()
async def test_large_scale_gfp(dut: Any) -> None:
    """Test with large-scale GFP values to verify exponent handling."""
    tb = MLPBramColCtrlTestbench(dut)
    await tb.setup_clock()
    await tb.reset_system()

    gfp8 = gfp.GFPDataType(mantissa_bits=8, exp_bits=8)

    # Generate data with large scale
    torch.manual_seed(456)
    activations_float = torch.rand(128) * 1000.0  # [0, 1000]
    weights_float = torch.rand(128, 16) * 1000.0

    # Quantize
    act_gfp = gfp.GFPTensor.quantize_from_float(
        group_axis=-1,
        group_size=32,
        dtype=gfp8,
        original_data=activations_float,
    )

    weights_gfp = gfp.GFPTensor.quantize_from_float(
        group_axis=0,
        group_size=32,
        dtype=gfp8,
        original_data=weights_float,
    )

    # Dequantize for golden reference
    act_dequant = act_gfp.dequantize()
    weights_dequant = weights_gfp.dequantize()

    # Load weights
    for col_idx in range(16):
        mantissas = []
        exponents = []
        for g in range(4):
            # GFP tensor shape: mantissa_data[columns, groups, elements] = [16, 4, 32]
            group_mantissas = weights_gfp.mantissa_data[col_idx, g, :].tolist()
            mantissas.extend(group_mantissas)
            group_exp = int(weights_gfp.exp_data[col_idx, g, 0].item()) + ACX_BFP_M8E8_BIAS
            exponents.append(group_exp)
        await tb.load_native_vector_to_column(col_idx, mantissas, exponents)

    # Prepare activations
    act_mantissas = []
    act_exponents = []
    for g in range(4):
        group_mantissas = act_gfp.mantissa_data[g].tolist()
        act_mantissas.extend(group_mantissas)
        group_exp = act_gfp.exp_data[g].item() + ACX_BFP_M8E8_BIAS
        act_exponents.append(group_exp)

    await tb.compute_with_activations(act_mantissas, act_exponents, new_dot=True)

    # Calculate expected
    expected = []
    for col in range(16):
        dot = torch.dot(act_dequant, weights_dequant[:, col])
        expected.append(dot.item())

    cocotb.log.info(f"Large scale expected: {expected}")
    actual = tb.get_flat_outputs()
    cocotb.log.info(f"Large scale actual: {actual}")

    tb.verify_outputs(expected, rel_tol=0.1)  # Looser tolerance for large values
