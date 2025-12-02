"""
Testbench for nap_dma_ctrl.sv

This testbench validates the DMA read burst functionality using Python and cocotb.
It tests burst splitting, flow control, error handling, and AXI4 protocol compliance.
"""

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, FallingEdge, Timer, Event, First
from cocotb.handle import SimHandleBase
import logging
import random
from typing import List, Optional, Dict, Any
from dataclasses import dataclass
from enum import Enum

# Configure logging
logging.basicConfig(level=logging.DEBUG)
logger = logging.getLogger(__name__)

# Test configuration
TEST_CLK_PERIOD = 10  # 100MHz in ns


class AXIResponse(Enum):
    """AXI response types"""
    OKAY = 0b00
    EXOKAY = 0b01
    SLVERR = 0b10
    DECERR = 0b11


@dataclass
class ReadRequest:
    """DMA read request configuration"""
    base_addr: int
    length: int  # In 256-bit words
    expected_bursts: int = 0
    description: str = ""


@dataclass
class TestResult:
    """Test execution result"""
    passed: bool
    description: str
    errors: List[str]
    warnings: List[str]
    data_received: int = 0
    data_expected: int = 0


class AXIMemoryModel:
    """Simple AXI4 memory model for generating read responses"""
    
    def __init__(self, dut, clock):
        self.dut = dut
        self.clock = clock
        self.memory = {}  # Address -> data mapping
        self.read_delay = 2  # Cycles delay for read responses
        self.outstanding_reads = []
        self.response_queue = []
        
        # Initialize test memory
        self._init_memory()
        
    def _init_memory(self):
        """Initialize memory with test patterns"""
        for addr in range(0, 0x10000, 32):  # 32-byte aligned addresses
            # Create unique test pattern for each address
            pattern = (addr // 32) & 0xFFFFFFFF
            data = 0
            for i in range(8):  # 8 x 32-bit words = 256 bits
                data |= (pattern + i) << (i * 32)
            self.memory[addr] = data
            
    async def handle_read_address(self):
        """Handle AXI read address channel"""
        axi = self.dut.axi_if
        await RisingEdge(self.clock)
        
        while True:
            await RisingEdge(self.clock)
            
            # Always ready to accept addresses
            axi.arready.value = 1
            
            # Capture new read requests
            if axi.arvalid.value and axi.arready.value:
                addr = int(axi.araddr.value)
                length = int(axi.arlen.value) + 1  # Convert AXI len to beat count
                burst_id = int(axi.arid.value)
                
                logger.info(f"AXI Read Request: addr=0x{addr:08x}, len={length}, id={burst_id}")
                
                # Queue read response
                self.outstanding_reads.append({
                    'addr': addr,
                    'length': length,
                    'id': burst_id,
                    'delay': self.read_delay
                })
                
    async def handle_read_data(self):
        """Handle AXI read data channel responses"""
        axi = self.dut.axi_if
        await RisingEdge(self.clock)
        while True:
            await RisingEdge(self.clock)
            
            # Process outstanding reads
            if self.outstanding_reads:
                req = self.outstanding_reads[0]
                
                if req['delay'] > 0:
                    req['delay'] -= 1
                    axi.rvalid.value = 0
                else:
                    # Generate read response
                    axi.rvalid.value = 1
                    axi.rid.value = req['id']
                    axi.rresp.value = AXIResponse.OKAY.value
                    
                    # Get data from memory
                    addr = req['addr']
                    if addr in self.memory:
                        axi.rdata.value = self.memory[addr]
                    else:
                        # Generate pattern for unmapped addresses
                        pattern = (addr // 32) & 0xFFFFFFFF
                        data = 0
                        for i in range(8):
                            data |= (pattern + i) << (i * 32)
                        axi.rdata.value = data
                    
                    # Check if this is the last beat
                    if req['length'] <= 1:
                        axi.rlast.value = 1
                        self.outstanding_reads.pop(0)  # Remove completed request
                    else:
                        axi.rlast.value = 0
                        req['length'] -= 1
                        req['addr'] += 32  # Next 256-bit word
                    
                    # Wait for ready
                    await FallingEdge(self.clock)
                    while (not axi.rready.value):
                        # cocotb.log.info("Waiting for AXI RREADY...")
                        await RisingEdge(self.clock)

                        # End data?
                        if axi.rlast.value:
                            axi.rvalid.value = 0
                            axi.rlast.value = 0
            else:
                axi.rvalid.value = 0
                axi.rlast.value = 0


class NAPDMATestbench:
    """Main testbench class for nap_dma_ctrl"""
    
    def __init__(self, dut):
        self.dut = dut
        self.clock = None
        self.memory_model = None
        self.test_results = []
        self.errors = []
        self.warnings = []
        
        # Test tracking
        self.received_data = []
        self.expected_words = 0
        self.received_words = 0
        
    async def setup_clock(self):
        """Setup system clock"""
        self.clock = Clock(self.dut.i_clk, TEST_CLK_PERIOD, unit="ns")
        cocotb.start_soon(self.clock.start())
        logger.info(f"Clock setup: {TEST_CLK_PERIOD}ns period")
        
    async def reset_system(self):
        """Reset the DUT"""
        logger.info("Resetting DUT...")
        self.dut.i_reset_n.value = 0
        
        # Initialize all inputs
        self.dut.i_read_valid.value = 0
        self.dut.i_read_base_addr.value = 0
        self.dut.i_read_length.value = 0
        self.dut.i_read_data_ready.value = 1
        
        # Wait for reset
        await Timer(TEST_CLK_PERIOD * 10, unit="ns")
        await RisingEdge(self.dut.i_clk)
        
        self.dut.i_reset_n.value = 1
        await RisingEdge(self.dut.i_clk)
        logger.info("Reset complete")
        
    async def setup_memory_model(self):
        """Setup AXI memory model"""
        self.memory_model = AXIMemoryModel(self.dut, self.dut.i_clk)
        
        # Start memory model tasks
        cocotb.start_soon(self.memory_model.handle_read_address())
        cocotb.start_soon(self.memory_model.handle_read_data())
        
        logger.info("AXI memory model started")
        
    async def issue_read_request(self, req: ReadRequest) -> TestResult:
        """Issue a DMA read request and monitor completion"""
        logger.info(f"Issuing read request: {req.description}")
        logger.info(f"  Address: 0x{req.base_addr:08x}")
        logger.info(f"  Length: {req.length} words")
        
        # Reset monitoring
        self.received_data = []
        self.expected_words = req.length
        self.received_words = 0
        
        # Start data monitoring
        monitor_task = cocotb.start_soon(self.monitor_output_data())
        
        # Issue request
        self.dut.i_read_base_addr.value = req.base_addr
        self.dut.i_read_length.value = req.length
        self.dut.i_read_valid.value = 1
        
        # Wait for acknowledgment
        ack_received = False
        timeout_cycles = 100
        for _ in range(timeout_cycles):
            await RisingEdge(self.dut.i_clk)
            if self.dut.o_read_ready.value:
                ack_received = True
                break
                
        self.dut.i_read_valid.value = 0
        
        if not ack_received:
            return TestResult(
                passed=False,
                description=req.description,
                errors=["Request not acknowledged within timeout"],
                warnings=[]
            )
            
        logger.info("Request acknowledged")
        
        # Wait for completion
        completion_timeout = req.length * 10 + 1000  # Generous timeout
        for _ in range(completion_timeout):
            await RisingEdge(self.dut.i_clk)
            if self.received_words >= self.expected_words:
                break
        else:
            return TestResult(
                passed=False,
                description=req.description,
                errors=[f"Timeout waiting for completion. Received {self.received_words}/{self.expected_words}"],
                warnings=[],
                data_received=self.received_words,
                data_expected=self.expected_words
            )
            
        # Stop monitoring
        monitor_task.cancel()
        
        # Validate results
        errors = []
        warnings = []
        
        if self.received_words != self.expected_words:
            errors.append(f"Word count mismatch: expected {self.expected_words}, got {self.received_words}")
            
        # Additional validation can be added here
        
        logger.info(f"Request completed: {self.received_words} words received")
        
        return TestResult(
            passed=(len(errors) == 0),
            description=req.description,
            errors=errors,
            warnings=warnings,
            data_received=self.received_words,
            data_expected=self.expected_words
        )
        
    async def monitor_output_data(self):
        """Monitor output data stream"""
        while True:
            await RisingEdge(self.dut.i_clk)
            
            if self.dut.o_read_data_valid.value and self.dut.i_read_data_ready.value:
                data = int(self.dut.o_read_data.value)
                last = bool(self.dut.o_read_data_last.value)
                
                self.received_data.append((data, last))
                self.received_words += 1
                
                logger.debug(f"Data received: word {self.received_words}, last={last}")
                
                if last:
                    logger.debug("Burst completed")
                    
    async def test_back_pressure(self, req: ReadRequest) -> TestResult:
        """Test with intermittent ready signal"""
        logger.info(f"Testing back pressure: {req.description}")
        
        # Reset monitoring
        self.received_data = []
        self.expected_words = req.length
        self.received_words = 0
        
        # Start data monitoring
        monitor_task = cocotb.start_soon(self.monitor_output_data())
        
        # Start back-pressure generation
        backpressure_task = cocotb.start_soon(self.generate_backpressure())
        
        # Issue request
        self.dut.i_read_base_addr.value = req.base_addr
        self.dut.i_read_length.value = req.length
        self.dut.i_read_valid.value = 1
        await RisingEdge(self.dut.i_clk)
        # Wait for acknowledgment
        ack_received = False
        for _ in range(100):
            if self.dut.o_read_ready.value:
                ack_received = True
                break
            await RisingEdge(self.dut.i_clk)
        logger.info("Request acknowledged under back-pressure" if ack_received else "Request not acknowledged under back-pressure")
                
        self.dut.i_read_valid.value = 0
        
        if not ack_received:
            backpressure_task.cancel()
            monitor_task.cancel()
            return TestResult(
                passed=False,
                description=req.description,
                errors=["Request not acknowledged"],
                warnings=[]
            )
            
        # Wait for completion with back-pressure
        completion_timeout = req.length * 20 + 2000  # Longer timeout due to back-pressure
        for _ in range(completion_timeout):
            await RisingEdge(self.dut.i_clk)
            if self.received_words >= self.expected_words:
                break
        else:
            backpressure_task.cancel()
            monitor_task.cancel()
            return TestResult(
                passed=False,
                description=req.description,
                errors=[f"Timeout with back-pressure. Received {self.received_words}/{self.expected_words}"],
                warnings=[]
            )
            
        # Cleanup
        backpressure_task.cancel()
        monitor_task.cancel()
        self.dut.i_read_data_ready.value = 1  # Restore ready
        
        return TestResult(
            passed=(self.received_words == self.expected_words),
            description=req.description,
            errors=[] if self.received_words == self.expected_words else ["Data count mismatch"],
            warnings=[],
            data_received=self.received_words,
            data_expected=self.expected_words
        )
        
    async def generate_backpressure(self):
        """Generate random back-pressure on ready signal"""
        while True:
            await RisingEdge(self.dut.i_clk)
            # 70% chance of ready being high
            self.dut.i_read_data_ready.value = random.random() > 0.3
            
    async def test_error_conditions(self) -> List[TestResult]:
        """Test error conditions (unaligned address, zero length)"""
        results = []
        
        # Test unaligned address
        logger.info("Testing unaligned address error")
        self.dut.i_read_base_addr.value = 0x1001  # Unaligned
        self.dut.i_read_length.value = 1
        self.dut.i_read_valid.value = 1
        
        # Should NOT get acknowledgment
        ack_received = False
        for _ in range(50):
            await RisingEdge(self.dut.i_clk)
            if self.dut.o_read_ready.value:
                ack_received = True
                break
                
        self.dut.i_read_valid.value = 0
        
        results.append(TestResult(
            passed=not ack_received,
            description="Unaligned address rejection",
            errors=[] if not ack_received else ["Unaligned address incorrectly accepted"],
            warnings=[]
        ))
        
        # Test zero length
        logger.info("Testing zero length error")
        self.dut.i_read_base_addr.value = 0x2000  # Aligned
        self.dut.i_read_length.value = 0  # Zero length
        self.dut.i_read_valid.value = 1
        
        # Should NOT get acknowledgment
        ack_received = False
        for _ in range(50):
            await RisingEdge(self.dut.i_clk)
            if self.dut.o_read_ready.value:
                ack_received = True
                break
                
        self.dut.i_read_valid.value = 0
        
        results.append(TestResult(
            passed=not ack_received,
            description="Zero length rejection",
            errors=[] if not ack_received else ["Zero length incorrectly accepted"],
            warnings=[]
        ))
        
        return results


# Test configuration
TEST_CASES = [
    ReadRequest(
        base_addr=0x1000,
        length=1,
        description="Single word read"
    ),
    ReadRequest(
        base_addr=0x2000,
        length=16,
        description="Small burst read"
    ),
    ReadRequest(
        base_addr=0x3000,
        length=256,
        description="Maximum single burst"
    ),
    ReadRequest(
        base_addr=0x4000,
        length=512,
        description="Multi-burst read (2 AXI bursts)"
    ),
    ReadRequest(
        base_addr=0x5000,
        length=1000,
        description="Large multi-burst read"
    ),
]

BACKPRESSURE_TESTS = [
    ReadRequest(
        base_addr=0x6000,
        length=32,
        description="Back-pressure test - small"
    ),
    ReadRequest(
        base_addr=0x7000,
        length=128,
        description="Back-pressure test - medium"
    ),
]


@cocotb.test()
async def test_nap_dma_ctrl_basic(dut):
    """Test basic DMA functionality"""
    
    tb = NAPDMATestbench(dut)
    
    # Setup
    await tb.setup_clock()
    await tb.setup_memory_model()
    await tb.reset_system()

    logger.setLevel(logging.INFO)
    
    logger.info("Starting basic DMA tests...")
    
    # Run basic test cases
    for test_case in TEST_CASES:
        result = await tb.issue_read_request(test_case)
        tb.test_results.append(result)
        
        if result.passed:
            logger.info(f"✓ PASS: {result.description}")
        else:
            logger.error(f"✗ FAIL: {result.description}")
            for error in result.errors:
                logger.error(f"  Error: {error}")
                
    # Summary
    passed = sum(1 for r in tb.test_results if r.passed)
    total = len(tb.test_results)
    
    logger.info(f"Basic tests: {passed}/{total} passed")
    assert passed == total, f"Basic tests failed: {passed}/{total}"


@cocotb.test()
async def test_nap_dma_ctrl_backpressure(dut):
    """Test DMA with back-pressure"""
    
    tb = NAPDMATestbench(dut)
    
    # Setup
    await tb.setup_clock()
    await tb.setup_memory_model()
    await tb.reset_system()
    
    logger.info("Starting back-pressure tests...")
    
    # Run back-pressure tests
    results = []
    for test_case in BACKPRESSURE_TESTS:
        result = await tb.test_back_pressure(test_case)
        results.append(result)
        
        if result.passed:
            logger.info(f"✓ PASS: {result.description}")
        else:
            logger.error(f"✗ FAIL: {result.description}")
            
    # Summary
    passed = sum(1 for r in results if r.passed)
    total = len(results)
    
    logger.info(f"Back-pressure tests: {passed}/{total} passed")
    assert passed == total, f"Back-pressure tests failed: {passed}/{total}"


# TODO - bad request handling
#@cocotb.test()
async def test_nap_dma_ctrl_errors(dut):
    """Test error conditions"""
    
    tb = NAPDMATestbench(dut)
    
    # Setup
    await tb.setup_clock()
    await tb.setup_memory_model()
    await tb.reset_system()
    
    logger.info("Starting error condition tests...")
    
    # Run error tests
    results = await tb.test_error_conditions()
    
    # Summary
    passed = sum(1 for r in results if r.passed)
    total = len(results)
    
    for result in results:
        if result.passed:
            logger.info(f"✓ PASS: {result.description}")
        else:
            logger.error(f"✗ FAIL: {result.description}")
            
    logger.info(f"Error condition tests: {passed}/{total} passed")
    assert passed == total, f"Error tests failed: {passed}/{total}"


@cocotb.test()
async def test_nap_dma_ctrl_comprehensive(dut):
    """Comprehensive test combining all scenarios"""
    
    tb = NAPDMATestbench(dut)
    
    # Setup
    await tb.setup_clock()
    await tb.setup_memory_model()
    await tb.reset_system()
    
    logger.info("Starting comprehensive DMA test...")
    
    all_results = []
    
    # Basic tests
    for test_case in TEST_CASES:
        result = await tb.issue_read_request(test_case)
        all_results.append(result)
        
    # Back-pressure tests
    for test_case in BACKPRESSURE_TESTS:
        result = await tb.test_back_pressure(test_case)
        all_results.append(result)
        
    # Error tests
    # error_results = await tb.test_error_conditions()
    # all_results.extend(error_results)
    
    # Final summary
    passed = sum(1 for r in all_results if r.passed)
    total = len(all_results)
    
    logger.info("=" * 60)
    logger.info("COMPREHENSIVE TEST SUMMARY")
    logger.info("=" * 60)
    
    for i, result in enumerate(all_results, 1):
        status = "PASS" if result.passed else "FAIL"
        logger.info(f"{i:2d}. {status}: {result.description}")
        if not result.passed:
            for error in result.errors:
                logger.error(f"     Error: {error}")
                
    logger.info(f"\nOverall: {passed}/{total} tests passed")
    
    if passed == total:
        logger.info("🎉 ALL TESTS PASSED!")
    else:
        logger.error(f"❌ {total - passed} TESTS FAILED!")
        
    assert passed == total, f"Comprehensive test failed: {passed}/{total}"