"""
Testbench for mlp_bram_col.sv

Validates the Achronix MLP+BRAM stack in dual 8x8 BFP8 dot-product mode.
"""

from __future__ import annotations

from typing import Any
import math
import torch

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import  RisingEdge

from emulator import group_floating_point as gfp
from sim_utils.build_misc import int_to_float24

GFP8E8_BIAS = 128
BFP8E8_BIAS = 133
ACX_BFP_M8E8_BIAS = BFP8E8_BIAS - GFP8E8_BIAS # Exponent bias compensation (GFP8 -> BFP8)


def pack_bytes(byte_list: list[int]) -> int:
    """Pack a list of bytes into a single integer. byte[0] is the most significant byte.

    Args:
        byte_list: list of bytes to pack.

    Returns:
        Packed integer.
    """
    result = 0
    for i, byte in enumerate(reversed(byte_list)):
        assert byte < 256, "Byte value out of range"
        result |= (byte & 0xFF) << (i * 8)
    return result

class MLPBramColTestbench:
    """Test harness for MLP BRAM Column module"""

    def __init__(self, dut):
        self.dut = dut
        self.NUM_MLPS = int(dut.NUM_MLPS.value) if hasattr(dut, 'NUM_MLPS') else 4
        self.CLK_PERIOD = 10  # 100MHz in ns

        # Test data storage
        self.activations = []
        cocotb.log.debug(f"Testbench initialized for {self.NUM_MLPS} MLPs")

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
        self.dut.ce.value = 1
        self.dut.din.value = 0
        self.dut.load.value = 0
        self.dut.accumulate.value = 0
        self.dut.bram_din.value = 0
        self.dut.wraddr.value = 0
        self.dut.wren.value = 0
        self.dut.rdaddr.value = 0

        # Hold reset for 5 cycles
        # await ClockCycles(self.dut.clk, 5)
        await self.clock.cycles(5)

        # Release reset and let system stabilize
        self.dut.rstn.value = 1
        await self.clock.cycles(10)

        cocotb.log.debug("Reset complete")

    async def write_bram_params(self, bram_offset: int, bank0_params: list[int],
                               bank1_params: list[int], mlp_mask: int = 0):
        """Write parameters to BRAM for specified MLPs

        Args:
            bram_offset: Base address for BRAM write
            bank0_params: 8 parameters for bank 0
            bank1_params: 8 parameters for bank 1
            mlp_mask: Bitmask indicating which MLPs to write to (default: all)
        """
        if (not mlp_mask):
            mlp_mask = (1 << self.NUM_MLPS) - 1  # Enable all MLPs

        if (len(bank0_params) == 8):
            exponent = BFP8E8_BIAS  # bfp_m8e8 bias (this does scale by factors of 2)
            bank1_params.insert(0, exponent)
            bank0_params.insert(0, exponent)
        else:
            assert len(bank0_params) == 9, "Each bank must have 8 parameters + 1 exponent"
        # Construct 72-bit parameter words
        # Each bank gets 8 parameters packed into 72 bits (8 bits each + padding)

        low_bank = pack_bytes(bank1_params)
        high_bank = pack_bytes(bank0_params)


        cocotb.log.debug(f"Writing BRAM offset {bram_offset}, mask 0x{mlp_mask:x}")
        cocotb.log.debug(f"Bank0 params: {bank0_params}")
        cocotb.log.debug(f"Bank1 params: {bank1_params}")
        cocotb.log.debug(f"Packed low_bank: 0x{low_bank:x}, high_bank: 0x{high_bank:x}")

        # Write low bank (first address)
        self.dut.bram_din.value = low_bank
        self.dut.wraddr.value = bram_offset
        self.dut.wren.value = mlp_mask
        await RisingEdge(self.dut.clk)

        # Write high bank (next address)
        self.dut.bram_din.value = high_bank
        self.dut.wraddr.value = bram_offset + 1
        self.dut.wren.value = mlp_mask
        await RisingEdge(self.dut.clk)

        # Disable write
        self.dut.wren.value = 0
        #await RisingEdge(self.dut.clk)

    async def load_weights(self, weights: torch.Tensor):
        """Load weights into BRAM for all MLPs

        Args:
            weights: Tensor of shape (2, num_params, NUM_MLPS)
        """
        num_params = weights.shape[1]
        assert weights.shape[0] == 2, "Weights tensor must have shape (2, num_params, NUM_MLPS)"
        assert weights.shape[2] == self.NUM_MLPS, f"Weights tensor must have NUM_MLPS={self.NUM_MLPS}"
        assert num_params % 8 == 0, "Number of parameters must be multiple of 8"

        num_bram_addresses = num_params // 8

        for mlp_index in range(self.NUM_MLPS):
            for bram_addr in range(num_bram_addresses):
                bank0_params = weights[0, bram_addr*8:(bram_addr+1)*8, mlp_index].tolist()
                bank1_params = weights[1, bram_addr*8:(bram_addr+1)*8, mlp_index].tolist()
                mlp_mask = 1 << mlp_index
                await self.write_bram_params(bram_addr*2, bank0_params, bank1_params, mlp_mask)

    async def load_gfp_weights(self, weights: gfp.GFPTensor):
        """Load weights into BRAM for all MLPs

        Args:
            weights: GFPTensor of shape (2, num_params, NUM_MLPS)
        """
        assert weights.group_size == 8, "Weights GFPTensor must have group size of 8"
        for mlp_index in range(self.NUM_MLPS):
            for g in range(weights.num_groups):
                mlp_m = weights.mantissa_data[:, :, g] # 8 mantissas * NUM_MLPS * 2 cols
                mlp_e = weights.exp_data[:, :, g] # 1 exponent * NUM_MLPS * 2 cols

                # load_from_gfp_group(w_gfp[:, :, g])
                bank0_params = mlp_m[0, mlp_index].tolist()
                bank1_params = mlp_m[1, mlp_index].tolist()
                bank0_exp = mlp_e[0, mlp_index].item() + ACX_BFP_M8E8_BIAS
                bank1_exp = mlp_e[1, mlp_index].item() + ACX_BFP_M8E8_BIAS
                bank0_params.insert(0, bank0_exp)
                bank1_params.insert(0, bank1_exp)
                cocotb.log.debug(f"Updated bram weights  {g}: {bank0_params}, {bank1_params}")

                await self.write_bram_params(g*2, bank0_params, bank1_params, 1 << mlp_index)

    def update_activations(self, activations: torch.Tensor):
        """Update activation vectors for multi-cycle tests

        Args:
            activations: Tensor of shape (num_params,)
        """
        num_params = activations.shape[0]
        assert num_params % 8 == 0, "Number of activation parameters must be multiple of 8"

        self.activations = []
        for a in torch.split(activations, 8):
            self.activations.append(a.tolist())

    def update_gfp_activations(self, activations: gfp.GFPTensor):
        """Update activation vector for single cycle test

        Args:
            a_mantissa: List of 8 mantissa values
            a_exponent: Exponent value
        """
        assert activations.group_size == 8, "Activation GFPTensor must have group size of 8"
        self.activations = []
        for g in range(activations.num_groups):
            act_m = activations.mantissa_data[g].tolist()
            act_e = activations.exp_data[g].item() + ACX_BFP_M8E8_BIAS  # bfp_m8e8 bias
            self.activations.append([act_e] + act_m)
            cocotb.log.debug(f"Updated activation group {g}: {self.activations[g]}")


    def apply_input_vector(self, inputs: list[int]):
        """Apply input vector to DIN

        Args:
            inputs: list of up to 9 input values (0-255)
        """
        if (len(inputs) == 8):
            inputs.insert(0, BFP8E8_BIAS)  # exponent = 1.0 in bfp_m8e8
        din_value = pack_bytes(inputs)

        self.dut.din.value = din_value
        cocotb.log.debug(f"Applied input vector: {inputs} -> 0x{din_value:x}")

    async def single_dot_product(self, inputs: list[int]):
        """Perform single dot product operation

        Args:
            inputs: list of 8 input values
        """
        self.dut.rdaddr.value = 0
        self.dut.accumulate.value = 0
        self.dut.load.value = 1
        self.dut.ce.value = 1

        # Allow for BRAM latency
        await RisingEdge(self.dut.clk)

        self.dut.load.value = 1
        self.apply_input_vector(inputs)

        # Allow for computation pipeline latency (typically 2-3 cycles)
        await self.clock.cycles(3)
        self.dut.ce.value = 0

    async def accumulate_dot_products(self, cycle_length: int = 0, new_dot: bool = True):
        """Perform accumulating dot product over multiple cycles

        Args:
            cycle_length: Number of cycles to accumulate over
            new_dot: Whether this is a new dot product (resets accumulator)
        """
        if (not cycle_length):
            cycle_length = len(self.activations)
        else:
            assert cycle_length <= len(self.activations), "cycle_length exceeds number of activation vectors"
        self.dut.rdaddr.value = 0
        self.dut.accumulate.value = 0
        self.dut.load.value = 0

        # Initial setup cycle
        await RisingEdge(self.dut.clk)
        self.dut.ce.value = 1

        # Process each activation vector
        for i in range(cycle_length):
            self.apply_input_vector(self.activations[i])

            # Update read address for next parameter set
            if i < cycle_length - 1:
                self.dut.rdaddr.value = i + 1

            # Enable accumulation after first cycle
            if i > 0:
                self.dut.accumulate.value = 1

            # Load accumulator with first valid result
            self.dut.load.value = 1 if ((i == 2) and new_dot) else 0

            await RisingEdge(self.dut.clk)

        # Reset control signals
        self.dut.rdaddr.value = 0
        self.dut.load.value = 0
        await RisingEdge(self.dut.clk)
        self.dut.accumulate.value = 0
        self.dut.ce.value = 0
        # One more cycle for last ce to propagate
        await RisingEdge(self.dut.clk)

    def get_outputs(self) -> list[tuple[float, float]]:
        """Retrieve output dot products from DUT

        Returns:
            tuple of two lists: (dot_product_bank0, dot_product_bank1)
        """
        results = []

        for mlp_index in range(self.NUM_MLPS):
            mlp_out = self.dut.dout[mlp_index].value
            ed0 = int_to_float24(mlp_out[23:0].to_signed())
            ed1 = int_to_float24(mlp_out[47:24].to_signed())
            results.append((ed0, ed1))

        return results

    def verify_outputs(self, expected: list[tuple[int | float, int | float]], rel_tol: float = 1e-5):
        """Verify DUT outputs against expected values

        Args:
            expected: list of expected (dot0, dot1) tuples for each MLP
        """
        actual = self.get_outputs()
        for mlp_index in range(self.NUM_MLPS):
            exp0, exp1 = expected[mlp_index]
            act0, act1 = actual[mlp_index]
            assert math.isclose(act0, exp0, rel_tol=rel_tol, abs_tol=rel_tol), f"MLP{mlp_index} dot0 mismatch: expected {exp0}, got {act0}"
            assert math.isclose(act1, exp1, rel_tol=rel_tol, abs_tol=rel_tol), f"MLP{mlp_index} dot1 mismatch: expected {exp1}, got {act1}"
        cocotb.log.debug("All outputs verified successfully")


# TODO: num_cycles = 2 doesn't work
@cocotb.test() #timeout_time=10, timeout_unit="ms")
@cocotb.parametrize(num_cycles=[3, 1, 7], batch_size=[1, 2, 3])
async def random_int_weights(dut: Any, num_cycles: int = 42, batch_size: int = 1) -> None:
    """Test w/ fixed exponent, random integer weights and activations over multiple cycles."""
    tb = MLPBramColTestbench(dut)
    NUM_MLPS = tb.NUM_MLPS
    await tb.setup_clock()
    await tb.reset_system()
    # Generate random weights for the batch, and load them into BRAM
    weights = torch.randint(-128, 127, (2, num_cycles*8, NUM_MLPS), dtype=torch.int32)
    await tb.load_weights(weights)
    for b in range(batch_size):
        activations = torch.randint(-128, 127, (num_cycles*8,), dtype=torch.int32)
        tb.update_activations(activations)
        expected = []
        for mlp_index in range(NUM_MLPS):
            dot0 = torch.matmul(activations, weights[0, :, mlp_index])
            dot1 = torch.matmul(activations, weights[1, :, mlp_index])
            expected.append((dot0.item(), dot1.item()))
        # Push activations and check results
        await tb.accumulate_dot_products(0, True)
        # Precision is limited by mantissa bits of output
        tb.verify_outputs(expected, rel_tol=(2.0 / 2**14))


#@cocotb.test()
async def random_gfp_weights(dut: Any, num_groups: int = 7, a_scale: float = 1.0, w_scale: float = 1.0 ) -> None:
    tb = MLPBramColTestbench(dut)
    await tb.setup_clock()
    await tb.reset_system()
    NUM_MLPS = tb.NUM_MLPS
    num_params = 8 * num_groups

    gfp8 = gfp.GFPDataType(mantissa_bits=8, exp_bits=8)
    assert gfp8.exp_bias == GFP8E8_BIAS, f"GFP8E8 bias mismatch: expected {GFP8E8_BIAS}, got {gfp8.exp_bias}"
    # torch.rand generates [0.0, 1.0)
    # scale_factor = 1000.0 
    bias = -0.5
    activations = a_scale * (torch.rand((num_params,)) + bias)
    weights = w_scale * (torch.rand((2, num_params, NUM_MLPS)) + bias)

    a_gfp = gfp.GFPTensor.quantize_from_float(
        group_axis=-1,
        group_size=8,
        dtype=gfp8,
        original_data=activations,
    )
    # It may be easier to generate seperate vectors for each MLP column
    w_gfp = gfp.GFPTensor.quantize_from_float(
        group_axis=-2,
        group_size=8,
        dtype=gfp8,
        original_data=weights,
    )

    a_quantized = a_gfp.dequantize()
    w_quantized = w_gfp.dequantize()

    # Calculate expected results
    expected = []
    for mlp_index in range(tb.NUM_MLPS):
        dot0 = torch.matmul(a_quantized, w_quantized[0, :, mlp_index])
        dot1 = torch.matmul(a_quantized, w_quantized[1, :, mlp_index])
        expected.append((dot0.item(), dot1.item()))

    assert a_gfp.mantissa_shape[0] == w_gfp.mantissa_shape[2], "Activation and weight group size mismatch"
    #num_groups = a_gfp.mantissa_shape[0]
    tb.update_gfp_activations(a_gfp)
    await tb.load_gfp_weights(w_gfp)
    await tb.accumulate_dot_products(num_groups, True)
    actual = tb.get_outputs()
    cocotb.log.debug(f"Expected results: {expected}")
    cocotb.log.debug(f"Actual results: {actual} tolerance: {num_groups / 2**14}")
    # Precision is limited by mantissa bits of MLP accumulators (and output conversion if fp16)
    tb.verify_outputs(expected, rel_tol=(num_groups / 2**14)) # TODO: bit accurate reference?
    await tb.clock.cycles(5)


@cocotb.test()
async def small_gfp_weights(dut: Any) -> None:
    await random_gfp_weights(dut, num_groups=7, a_scale=1e-5, w_scale=1e-5)

@cocotb.test()
async def big_gfp_weights(dut: Any) -> None:
    await random_gfp_weights(dut, num_groups=13, a_scale=1000.0, w_scale=1000.0)

@cocotb.test()
async def mixed_gfp_weights_big_a(dut: Any) -> None:
    await random_gfp_weights(dut, num_groups=13, a_scale=1000.0, w_scale=1e-5)

@cocotb.test()
async def mixed_gfp_weights_big_w(dut: Any) -> None:
    await random_gfp_weights(dut, num_groups=13, a_scale=1e-5, w_scale=1000.0)

@cocotb.test()
@cocotb.parametrize(
    groups=[7, 128],
    a_scale=[1e-3, 1.0, 1e3],
    w_scale=[1e-3, 1.0, 1e3]
)
async def sweep_gfp_scale(dut: Any, groups: int, a_scale: float, w_scale: float) -> None:
    await random_gfp_weights(dut, num_groups=groups, a_scale=a_scale, w_scale=w_scale)

# NOTE: *not efficient* for batches, we should stride over activiations first
#.  and collect partial products, before loading new weights
@cocotb.test() #timeout_time=10, timeout_unit="ms")
async def big_dot(dut: Any, num_params=16000) -> None:
    """Test accumulators with over 4096 parameters."""
    assert num_params % 8 == 0, "num_params must be padded to a multiple of 8"
    tb = MLPBramColTestbench(dut)
    await tb.setup_clock()
    await tb.reset_system()
    # Generate random weights for each column
    weights = torch.randint(-128, 127, (2, num_params, tb.NUM_MLPS), dtype=torch.int32)
    activations = torch.randint(-128, 127, (num_params,), dtype=torch.int32)
    # Calculate expected results
    expected = []
    for mlp_index in range(tb.NUM_MLPS):
        dot0 = torch.matmul(activations, weights[0, :, mlp_index])
        dot1 = torch.matmul(activations, weights[1, :, mlp_index])
        expected.append((dot0.item(), dot1.item()))

    # Split weights into chunks of 4096 parameters (512 BRAM addresses)
    chunk_size = 4096
    w_chunks = torch.split(weights, chunk_size, dim=1)
    a_chunks = torch.split(activations, chunk_size)
    first_chunk = True
    # Load chunks and accumulate
    for i, (act_chunk, weight_chunk) in enumerate(zip(a_chunks, w_chunks)):
        cocotb.log.info(f"Chunk {i}[{act_chunk.shape[0]} parameters]")
        tb.update_activations(act_chunk)
        await tb.load_weights(weight_chunk)
        await tb.accumulate_dot_products(0, first_chunk)
        first_chunk = False

    tb.verify_outputs(expected, rel_tol = (num_params / 8) / 2**15)

