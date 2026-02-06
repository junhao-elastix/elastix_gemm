"""
Cocotb integration tests for gfp_norm_quant module.

Tests end-to-end GFP11e5 → GFP8e5 normalize and quantize:
- Single word processing
- Backpressure handling
- Last word signaling
- Padding handling
"""

import sys
from pathlib import Path

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer, ClockCycles

# Add golden_models to path
golden_path = Path(__file__).resolve().parents[2] / "golden_models"
if str(golden_path) not in sys.path:
    sys.path.insert(0, str(golden_path))

from gfp11e5_to_gfp8e5_golden import gfp11e5_to_gfp8e5_hw, pack_gfp11e5, to_signed, GFP11e5, GFP8e5


async def reset_dut(dut):
    """Apply reset to DUT."""
    dut.reset_i.value = 1
    dut.valid_i.value = 0
    dut.ready_i.value = 1
    dut.ack_i.value = 0
    for i in range(int(dut.IN_ELEMENTS.value)):
        dut.data_i[i].value = 0
    dut.pad_i.value = 0
    dut.last_i.value = 0

    await ClockCycles(dut.clk_i, 5)
    dut.reset_i.value = 0
    await ClockCycles(dut.clk_i, 2)


async def send_word(dut, gfp11e5_data, pad=0, last=False):
    """Send a single word to the DUT."""
    in_elements = int(dut.IN_ELEMENTS.value)

    # Pad data to IN_ELEMENTS
    while len(gfp11e5_data) < in_elements:
        gfp11e5_data.append(0)

    # Wait for ready
    while dut.ready_o.value == 0:
        await RisingEdge(dut.clk_i)

    # Drive inputs
    dut.valid_i.value = 1
    for i in range(in_elements):
        dut.data_i[i].value = gfp11e5_data[i]
    dut.pad_i.value = pad
    dut.last_i.value = int(last)

    await RisingEdge(dut.clk_i)
    dut.valid_i.value = 0


async def receive_output(dut, timeout=100):
    """Receive output from DUT."""
    in_elements = int(dut.IN_ELEMENTS.value)

    # Wait for valid output
    for _ in range(timeout):
        await RisingEdge(dut.clk_i)
        if dut.valid_o.value == 1:
            # Capture output
            mantissas = []
            for i in range(in_elements):
                man = int(dut.mantissa_o[i].value.signed_integer)
                mantissas.append(man)
            exponent = int(dut.exponent_o.value)
            pad = int(dut.pad_o.value)
            last = int(dut.last_o.value)
            return mantissas, exponent, pad, last

    raise TimeoutError("No output received")


@cocotb.test()
async def test_single_word_positive(dut):
    """Test single word with positive values."""
    clock = Clock(dut.clk_i, 10, units="ns")
    cocotb.start_soon(clock.start())

    await reset_dut(dut)

    # Create test data: positive values with same exponent
    test_data = [
        pack_gfp11e5(exp=15, man_signed=512),
        pack_gfp11e5(exp=15, man_signed=256),
        pack_gfp11e5(exp=15, man_signed=128),
        pack_gfp11e5(exp=15, man_signed=64),
    ]

    # Get golden reference
    g_mans, g_exp = gfp11e5_to_gfp8e5_hw(test_data)

    # Send data
    await send_word(dut, test_data, pad=0, last=True)

    # Receive output
    mantissas, exponent, pad, last = await receive_output(dut)

    # Check exponent
    assert exponent == g_exp, f"Exponent mismatch: got {exponent}, expected {g_exp}"

    # Check mantissas (first 4 elements)
    for i in range(4):
        expected = to_signed(g_mans[i], GFP8e5.man_bits)
        assert mantissas[i] == expected, \
            f"Mantissa {i} mismatch: got {mantissas[i]}, expected {expected}"

    assert last == 1, "Last flag should be set"
    dut._log.info("PASS: test_single_word_positive")


@cocotb.test()
async def test_single_word_negative(dut):
    """Test single word with negative values."""
    clock = Clock(dut.clk_i, 10, units="ns")
    cocotb.start_soon(clock.start())

    await reset_dut(dut)

    # Create test data: negative values
    test_data = [
        pack_gfp11e5(exp=15, man_signed=-512),
        pack_gfp11e5(exp=15, man_signed=-256),
        pack_gfp11e5(exp=15, man_signed=-128),
        pack_gfp11e5(exp=15, man_signed=-64),
    ]

    # Get golden reference
    g_mans, g_exp = gfp11e5_to_gfp8e5_hw(test_data)

    # Send data
    await send_word(dut, test_data, pad=0, last=True)

    # Receive output
    mantissas, exponent, pad, last = await receive_output(dut)

    # Check exponent
    assert exponent == g_exp, f"Exponent mismatch: got {exponent}, expected {g_exp}"

    # Check mantissas are negative
    for i in range(4):
        expected = to_signed(g_mans[i], GFP8e5.man_bits)
        assert mantissas[i] == expected, \
            f"Mantissa {i} mismatch: got {mantissas[i]}, expected {expected}"
        assert mantissas[i] < 0, f"Mantissa {i} should be negative"

    dut._log.info("PASS: test_single_word_negative")


@cocotb.test()
async def test_mixed_exponents(dut):
    """Test values with different exponents requiring alignment."""
    clock = Clock(dut.clk_i, 10, units="ns")
    cocotb.start_soon(clock.start())

    await reset_dut(dut)

    # Create test data: mixed exponents
    test_data = [
        pack_gfp11e5(exp=15, man_signed=512),   # Max exp
        pack_gfp11e5(exp=14, man_signed=512),   # Shift by 1
        pack_gfp11e5(exp=13, man_signed=512),   # Shift by 2
        pack_gfp11e5(exp=12, man_signed=512),   # Shift by 3
    ]

    # Get golden reference
    g_mans, g_exp = gfp11e5_to_gfp8e5_hw(test_data)

    # Send data
    await send_word(dut, test_data, pad=0, last=True)

    # Receive output
    mantissas, exponent, pad, last = await receive_output(dut)

    # Check exponent is maximum
    assert exponent == 15, f"Exponent should be 15, got {exponent}"

    # Check mantissas
    for i in range(4):
        expected = to_signed(g_mans[i], GFP8e5.man_bits)
        assert mantissas[i] == expected, \
            f"Mantissa {i} mismatch: got {mantissas[i]}, expected {expected}"

    dut._log.info("PASS: test_mixed_exponents")


@cocotb.test()
async def test_with_zeros(dut):
    """Test handling of zero elements."""
    clock = Clock(dut.clk_i, 10, units="ns")
    cocotb.start_soon(clock.start())

    await reset_dut(dut)

    # Create test data: mix of zeros and non-zeros
    test_data = [
        pack_gfp11e5(exp=15, man_signed=512),
        pack_gfp11e5(exp=0, man_signed=0),      # Zero
        pack_gfp11e5(exp=15, man_signed=-256),
        pack_gfp11e5(exp=0, man_signed=0),      # Zero
    ]

    # Get golden reference
    g_mans, g_exp = gfp11e5_to_gfp8e5_hw(test_data)

    # Send data
    await send_word(dut, test_data, pad=0, last=True)

    # Receive output
    mantissas, exponent, pad, last = await receive_output(dut)

    # Check zeros are preserved
    assert mantissas[1] == 0, f"Element 1 should be zero, got {mantissas[1]}"
    assert mantissas[3] == 0, f"Element 3 should be zero, got {mantissas[3]}"

    dut._log.info("PASS: test_with_zeros")


@cocotb.test()
async def test_with_padding(dut):
    """Test handling of padding elements."""
    clock = Clock(dut.clk_i, 10, units="ns")
    cocotb.start_soon(clock.start())

    await reset_dut(dut)
    in_elements = int(dut.IN_ELEMENTS.value)

    # Create full test data array: 4 valid elements + padding zeros
    # Pad count (elements at end to ignore)
    pad_count = in_elements - 4

    test_data = [
        pack_gfp11e5(exp=10, man_signed=100),
        pack_gfp11e5(exp=10, man_signed=200),
        pack_gfp11e5(exp=10, man_signed=300),
        pack_gfp11e5(exp=10, man_signed=400),
    ]
    # Fill rest with zeros (padding)
    for _ in range(pad_count):
        test_data.append(pack_gfp11e5(exp=0, man_signed=0))

    # Get golden reference with padding
    g_mans, g_exp = gfp11e5_to_gfp8e5_hw(test_data, pad=pad_count)

    # Send data with padding
    await send_word(dut, test_data, pad=pad_count, last=True)

    # Receive output
    mantissas, exponent, pad, last = await receive_output(dut)

    # Verify pad is passed through
    assert pad == pad_count, f"Pad mismatch: got {pad}, expected {pad_count}"

    dut._log.info("PASS: test_with_padding")


@cocotb.test()
async def test_backpressure(dut):
    """Test backpressure handling."""
    clock = Clock(dut.clk_i, 10, units="ns")
    cocotb.start_soon(clock.start())

    await reset_dut(dut)

    # Create test data
    test_data = [pack_gfp11e5(exp=15, man_signed=i * 100) for i in range(4)]

    # Apply backpressure
    dut.ready_i.value = 0

    # Send data
    await send_word(dut, test_data, pad=0, last=True)

    # Wait a few cycles with backpressure
    await ClockCycles(dut.clk_i, 10)

    # Release backpressure
    dut.ready_i.value = 1

    # Now we should get output
    mantissas, exponent, pad, last = await receive_output(dut)

    assert last == 1, "Last flag should be set"
    dut._log.info("PASS: test_backpressure")


@cocotb.test()
async def test_continuous_stream(dut):
    """Test continuous streaming of multiple words."""
    clock = Clock(dut.clk_i, 10, units="ns")
    cocotb.start_soon(clock.start())

    await reset_dut(dut)

    # Send 3 words
    for word_idx in range(3):
        is_last = (word_idx == 2)
        test_data = [pack_gfp11e5(exp=10 + word_idx, man_signed=(i + 1) * 50) for i in range(4)]
        await send_word(dut, test_data, pad=0, last=is_last)

    # Receive all outputs
    received_count = 0
    for _ in range(3):
        try:
            mantissas, exponent, pad, last = await receive_output(dut, timeout=50)
            received_count += 1
            if last:
                break
        except TimeoutError:
            break

    # Should receive at least one output (depends on GROUP_WORDS parameter)
    assert received_count > 0, "Should receive at least one output"
    dut._log.info(f"PASS: test_continuous_stream (received {received_count} outputs)")


@cocotb.test()
async def test_e2e_accuracy_varied_exponents(dut):
    """
    E2E accuracy test: 8 vectors with varied exponents per element.
    Each element has a unique exponent to stress test alignment.
    Uses concurrent producer/consumer for true streaming behavior.
    """
    import random
    clock = Clock(dut.clk_i, 10, units="ns")
    cocotb.start_soon(clock.start())

    await reset_dut(dut)

    in_elements = int(dut.IN_ELEMENTS.value)
    num_vectors = 8

    # Seed for reproducibility
    random.seed(42)

    # Generate test vectors: each element has a different exponent
    all_test_data = []
    all_expected_mans = []
    all_expected_exps = []

    dut._log.info(f"Generating {num_vectors} vectors of {in_elements} GFP11e5 elements each")

    for vec_idx in range(num_vectors):
        test_data = []
        for elem_idx in range(in_elements):
            # Varied exponent: spread across range 5-25
            exp = 5 + (elem_idx + vec_idx * 3) % 21
            # Random signed mantissa: -500 to +500
            man = random.randint(-500, 500)
            packed = pack_gfp11e5(exp=exp, man_signed=man)
            test_data.append(packed)

        all_test_data.append(test_data)

        # Get expected output from golden model
        expected_mans, expected_exp = gfp11e5_to_gfp8e5_hw(test_data)
        expected_mans_signed = [to_signed(m, 8) for m in expected_mans]
        all_expected_mans.append(expected_mans_signed)
        all_expected_exps.append(expected_exp)

    # Shared state for results
    results = []
    producer_done = False

    async def producer():
        """Continuously send vectors."""
        nonlocal producer_done
        for vec_idx in range(num_vectors):
            is_last = (vec_idx == num_vectors - 1)
            await send_word(dut, all_test_data[vec_idx].copy(), pad=0, last=is_last)
        producer_done = True
        dut._log.info("Producer: all vectors sent")

    async def consumer():
        """Continuously drain outputs."""
        while len(results) < num_vectors:
            try:
                mantissas, exponent, pad, last = await receive_output(dut, timeout=500)
                results.append((mantissas, exponent, pad, last))
                if last:
                    break
            except TimeoutError:
                if producer_done:
                    dut._log.error(f"Consumer timeout after producer done, got {len(results)} results")
                    break
                # Keep waiting if producer still running
                continue
        dut._log.info(f"Consumer: received {len(results)} vectors")

    # Start both coroutines concurrently
    producer_task = cocotb.start_soon(producer())
    consumer_task = cocotb.start_soon(consumer())

    # Wait for both to complete
    await producer_task
    await consumer_task

    # Verify results
    total_elements = 0
    total_errors = 0
    max_error = 0

    for vec_idx, (mantissas, exponent, pad, last) in enumerate(results):
        # Check exponent
        expected_exp = all_expected_exps[vec_idx]
        if exponent != expected_exp:
            dut._log.warning(f"Vec {vec_idx}: exp mismatch: got {exponent}, expected {expected_exp}")

        # Check mantissas
        expected_mans = all_expected_mans[vec_idx]
        for i in range(min(len(mantissas), len(expected_mans))):
            total_elements += 1
            error = abs(mantissas[i] - expected_mans[i])
            if error > 0:
                total_errors += 1
                if error > max_error:
                    max_error = error
                if error > 1:  # Only log significant errors
                    dut._log.warning(f"Vec {vec_idx}, elem {i}: got {mantissas[i]}, expected {expected_mans[i]}, err={error}")

    # Report accuracy
    accuracy = (total_elements - total_errors) / total_elements * 100 if total_elements > 0 else 0
    dut._log.info(f"=" * 60)
    dut._log.info(f"E2E Accuracy Test Results (Concurrent Streaming):")
    dut._log.info(f"  Vectors processed: {len(results)}")
    dut._log.info(f"  Elements per vector: {in_elements}")
    dut._log.info(f"  Total elements: {total_elements}")
    dut._log.info(f"  Elements with errors: {total_errors}")
    dut._log.info(f"  Max error: {max_error}")
    dut._log.info(f"  Accuracy: {accuracy:.2f}%")
    dut._log.info(f"=" * 60)

    # Pass if 100% accurate (golden model should match exactly)
    assert len(results) == num_vectors, f"Expected {num_vectors} results, got {len(results)}"
    assert total_errors == 0, f"Found {total_errors} mismatches out of {total_elements} elements"
    dut._log.info(f"PASS: test_e2e_accuracy_varied_exponents (100% accurate)")
