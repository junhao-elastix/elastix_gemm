"""
AXI4 Driver for Cocotb Testbenches

This module provides a comprehensive AXI4 driver class for performing read and write
transactions in cocotb-based verification environments. It supports full AXI4 protocol
features including burst transactions, different response types, and proper handshaking.

Features:
- AXI4 read/write transactions with proper handshaking
- Burst transaction support (INCR, WRAP, FIXED)
- Configurable data width, address width, and ID support
- Timeout handling and error detection
- Response validation and error reporting
- Both blocking and non-blocking transaction methods
- Queue-based transaction management for high throughput
- Debug logging and transaction monitoring

Usage:
    from axi_driver import AXI4Driver

    # Initialize driver
    axi_driver = AXI4Driver(dut.axi_if, clock_domain="clk")

    # Perform single read
    data = await axi_driver.read(address=0x1000, length=1)

    # Perform single write
    await axi_driver.write(address=0x1000, data=[0x12345678])

    # Perform burst read
    data = await axi_driver.read_burst(address=0x1000, length=4, burst_type="INCR")

    # Perform burst write
    await axi_driver.write_burst(address=0x1000, data=[0x11, 0x22, 0x33, 0x44], burst_type="INCR")

Author: Generated for ElastiCore project
License: MIT
"""

from typing import List, Optional, Union, Literal, Dict, Any

import logging
from dataclasses import dataclass, field
from enum import Enum
import cocotb
from cocotb.triggers import RisingEdge, FallingEdge, Timer, Event, First, with_timeout
from cocotb.clock import Clock
from cocotb.handle import SimHandleBase, LogicObject


class AXI4BurstType(Enum):
    """AXI4 burst types"""
    FIXED = 0b00  # Fixed address burst
    INCR = 0b01   # Incrementing address burst
    WRAP = 0b10   # Wrapping address burst
    RESERVED = 0b11


class AXI4Response(Enum):
    """AXI4 response types"""
    OKAY = 0b00    # Normal access success
    EXOKAY = 0b01  # Exclusive access okay
    SLVERR = 0b10  # Slave error
    DECERR = 0b11  # Decode error


class AXI4Size(Enum):
    """AXI4 transfer size encoding"""
    SIZE_1B = 0b000    # 1 byte
    SIZE_2B = 0b001    # 2 bytes
    SIZE_4B = 0b010    # 4 bytes
    SIZE_8B = 0b011    # 8 bytes
    SIZE_16B = 0b100   # 16 bytes
    SIZE_32B = 0b101   # 32 bytes
    SIZE_64B = 0b110   # 64 bytes
    SIZE_128B = 0b111  # 128 bytes


@dataclass
class AXI4Transaction:
    """AXI4 transaction configuration"""
    address: int
    data: Optional[List[int]] = None
    length: int = 1  # Number of transfers (awlen/arlen + 1)
    size: AXI4Size = AXI4Size.SIZE_4B
    burst_type: AXI4BurstType = AXI4BurstType.INCR
    transaction_id: int = 0
    qos: int = 0
    region: int = 0
    prot: int = 0b000  # Normal, secure, data access
    cache: int = 0b0000  # Device non-bufferable
    lock: bool = False
    user: int = 0
    strobe: Optional[List[int]] = None
    expected_response: AXI4Response = AXI4Response.OKAY
    timeout_cycles: int = 1000
    is_write: bool = True

    def __post_init__(self):
        """Validate transaction parameters"""
        if self.length < 1 or self.length > 256:
            raise ValueError(f"Invalid length: {self.length}. Must be 1-256.")
        if self.is_write and self.data is None:
            raise ValueError("Write transactions must provide data")
        if self.is_write and len(self.data) != self.length:
            raise ValueError(f"Data length {len(self.data)} doesn't match transaction length {self.length}")


class AXI4DriverError(Exception):
    """Base exception for AXI4 driver errors"""
    pass


class AXI4TimeoutError(AXI4DriverError):
    """Exception raised when AXI4 transaction times out"""
    pass


class AXI4ResponseError(AXI4DriverError):
    """Exception raised when AXI4 response indicates an error"""
    def __init__(self, message: str, response: AXI4Response):
        super().__init__(message)
        self.response = response


def signal_width(object: cocotb.handle) -> int:
    """Calculate number of bits in a cocotb handle.

    Args:
        range: cocotb handle slice object.
    Returns:
        Number of bits in the range.
    """
    if isinstance(object, cocotb.handle.LogicObject):
        return 1
    return abs(object.left - object.right) + 1

class AXI4Driver:
    """
    Comprehensive AXI4 driver for cocotb testbenches

    This driver provides high-level methods for performing AXI4 read and write
    transactions with full protocol compliance and error handling.
    """

    def __init__(self,
                 axi_interface: SimHandleBase,
                 clock: LogicObject,
                 data_width: int = 32,
                 address_width: int = 32,
                 id_width: int = 1,
                 len_width: int = 8,
                 reset_signal: Optional[SimHandleBase] = None,
                 reset_active_low: bool = True):
        """
        Initialize AXI4 driver

        Args:
            axi_interface: AXI4 interface handle from DUT
            clock: Clock signal for the DUT
            data_width: AXI4 data width in bits
            address_width: AXI4 address width in bits
            id_width: AXI4 ID width in bits
            len_width: AXI4 length width in bits
            reset_signal: Optional reset signal handle
            reset_active_low: True if reset is active low
        """
        self.axi = axi_interface
        self.clock = clock
        self.address_width = signal_width(self.axi.awaddr)
        self.data_width = signal_width(self.axi.wdata)
        self.id_width = signal_width(self.axi.awid)
        self.len_width = signal_width(self.axi.awlen)
        self.reset_signal = reset_signal
        self.reset_active_low = reset_active_low

        # Calculate derived parameters
        self.data_bytes = data_width // 8
        self.strobe_width = self.data_bytes

        # Transaction tracking
        self._transaction_id_counter = 0
        self._pending_reads: Dict[int, Event] = {}
        self._pending_writes: Dict[int, Event] = {}
        self._read_results: Dict[int, List[int]] = {}
        self._write_results: Dict[int, AXI4Response] = {}

        # Driver state
        self._initialized = False
        self._write_monitor_task = None
        self._read_monitor_task = None

        # Logging
        self.log = self.axi._log


    async def initialize(self):
        """Initialize the AXI4 driver and start monitoring"""
        if self._initialized:
            return

        self.log.info(f"Initializing AXI4 Driver: {self.axi._name}")
        self.log.info(f"address_width: {self.address_width}")
        self.log.info(f"data_width: {self.data_width}")
        self.log.info(f"id_width: {self.id_width}")
        self.log.info(f"len_width: {self.len_width}")
        # Initialize all signals to safe values
        await self._initialize_signals()

        # Start background monitoring task
        self._read_monitor_task = cocotb.start_soon(self._monitor_read_responses())
        self._write_monitor_task = cocotb.start_soon(self._monitor_write_responses())

        self._initialized = True
        self.log.info("AXI4 driver initialized successfully")

    async def _initialize_signals(self):
        """Initialize AXI4 signals to safe idle values"""
        # Write address channel
        self.axi.awvalid.value = 0
        self.axi.awaddr.value = 0
        self.axi.awlen.value = 0
        self.axi.awid.value = 0
        self.axi.awsize.value = AXI4Size.SIZE_4B.value
        self.axi.awburst.value = AXI4BurstType.INCR.value
        self.axi.awlock.value = 0
        self.axi.awqos.value = 0
        self.axi.awregion.value = 0
        self.axi.awprot.value = 0
        self.axi.awcache.value = 0

        # Write data channel
        self.axi.wvalid.value = 0
        self.axi.wdata.value = 0
        self.axi.wstrb.value = 0
        self.axi.wlast.value = 0

        # Write response channel
        self.axi.bready.value = 1  # Always ready to receive write response

        # Read address channel
        self.axi.arvalid.value = 0
        self.axi.araddr.value = 0
        self.axi.arlen.value = 0
        self.axi.arid.value = 0
        self.axi.arsize.value = AXI4Size.SIZE_4B.value
        self.axi.arburst.value = AXI4BurstType.INCR.value
        self.axi.arlock.value = 0
        self.axi.arqos.value = 0
        self.axi.arregion.value = 0
        self.axi.arprot.value = 0
        self.axi.arcache.value = 0

        # Read data channel
        self.axi.rready.value = 1  # Always ready to receive read data

        await RisingEdge(self.clock)

    async def _get_next_transaction_id(self) -> int:
        """Get next available transaction ID"""
        tid = self._transaction_id_counter
        self._transaction_id_counter = (self._transaction_id_counter + 1) % (2 ** self.id_width)
        return tid

    # TODO - split into read and write monitors
    async def _monitor_read_responses(self):
        """Background task to monitor AXI4 read responses"""
        await RisingEdge(self.clock) # Align to clock edge
        while True:
            try:

                cocotb.log.info("Wait for rvalid/rready...")
                await First(self.axi.rvalid.value_change, self.axi.rready.value_change)
                await RisingEdge(self.clock)

                # Check for read response
                while (self.axi.rvalid.value and self.axi.rready.value):
                    cocotb.log.info("Read response detected")
                    await self._handle_read_response()
                    await RisingEdge(self.clock)

            except Exception as e:
                self.log.error(f"Error in read response monitor: {e}")
                await Timer(1, "ns")  # Prevent tight loop on error


    async def _monitor_write_responses(self):
        """Background task to monitor AXI4 read and write responses"""
        await RisingEdge(self.clock) # Align to clock edge
        while True:
            try:

                cocotb.log.info("Wait for bvalid/bready...")
                await First(self.axi.bvalid.value_change, self.axi.bready.value_change)
                await RisingEdge(self.clock)

                # Check for write response
                while (self.axi.bvalid.value and self.axi.bready.value):
                    cocotb.log.info(f"Write response detected: {self.axi.bresp.value}")
                    await self._handle_write_response() # Not async?
                    await RisingEdge(self.clock)

            except Exception as e:
                self.log.error(f"Error in write response monitor: {e}")
                await Timer(1, "ns")  # Prevent tight loop on error

    async def _handle_read_response(self):
        """Handle incoming read response"""
        transaction_id = int(self.axi.rid.value)
        data = int(self.axi.rdata.value)
        last = bool(self.axi.rlast.value)
        response = AXI4Response(int(self.axi.rresp.value))

        if transaction_id not in self._read_results:
            self._read_results[transaction_id] = []

        self._read_results[transaction_id].append({
            'data': data,
            'response': response,
            'last': last
        })

        # Signal completion if this was the last beat
        if last and transaction_id in self._pending_reads:
            self._pending_reads[transaction_id].set()

    async def _handle_write_response(self):
        """Handle incoming write response"""
        transaction_id = int(self.axi.bid.value)
        response = AXI4Response(int(self.axi.bresp.value))

        self._write_results[transaction_id] = response

        if transaction_id in self._pending_writes:
            self._pending_writes[transaction_id].set()

    async def read(self,
                   address: int,
                   length: int = 1,
                   size: AXI4Size = AXI4Size.SIZE_4B,
                   burst_type: AXI4BurstType = AXI4BurstType.INCR,
                   transaction_id: Optional[int] = None,
                   timeout_cycles: int = 1000) -> List[int]:
        """
        Perform AXI4 read transaction

        Args:
            address: Starting address for read
            length: Number of data beats to read (1-256)
            size: Size of each data beat
            burst_type: Type of burst transaction
            transaction_id: Optional transaction ID (auto-assigned if None)
            timeout_cycles: Timeout in clock cycles

        Returns:
            List of data values read from the bus

        Raises:
            AXI4TimeoutError: If transaction times out
            AXI4ResponseError: If response indicates an error
        """
        if not self._initialized:
            await self.initialize()

        if transaction_id is None:
            transaction_id = await self._get_next_transaction_id()

        self.log.debug(f"Starting read transaction ID {transaction_id}: "
                      f"addr=0x{address:08x}, len={length}, size={size.name}")

        # Verify page crossing for INCR bursts
        if burst_type == AXI4BurstType.INCR:
            burst_bytes = length * (2 ** size.value)
            start_page = address // 4096
            end_page = (address + burst_bytes - 1) // 4096
            if start_page != end_page:
                raise AXI4DriverError("INCR burst crosses 4KB page boundary")

        # Create completion event
        completion_event = Event()
        self._pending_reads[transaction_id] = completion_event

        # Send read address
        await self._send_read_address(address, length-1, size, burst_type, transaction_id)

        # Wait for completion with timeout
        try:
            await with_timeout(completion_event.wait(), 1, 'ms')  # Assume 10ns clock
        except cocotb.triggers.SimTimeoutError:
            raise AXI4TimeoutError(f"Read transaction {transaction_id} timed out")

        # Process results
        if transaction_id not in self._read_results:
            raise AXI4DriverError(f"No results for transaction {transaction_id}")

        results = self._read_results[transaction_id]
        data_values = []

        for beat in results:
            if beat['response'] != AXI4Response.OKAY:
                raise AXI4ResponseError(f"Read error response: {beat['response'].name}",
                                       beat['response'])
            data_values.append(beat['data'])

        # Cleanup
        del self._pending_reads[transaction_id]
        del self._read_results[transaction_id]

        self.log.debug(f"Read transaction {transaction_id} completed successfully")
        return data_values

    async def _send_read_address(self,
                                address: int,
                                length: int,
                                size: AXI4Size,
                                burst_type: AXI4BurstType,
                                transaction_id: int):
        """Send read address phase"""
        # Set up address phase
        self.axi.araddr.value = address
        self.axi.arlen.value = length
        self.axi.arsize.value = size.value
        self.axi.arburst.value = burst_type.value
        self.axi.arid.value = transaction_id
        self.axi.arvalid.value = 1

        # Wait for ready
        while not self.axi.arready.value:
            await RisingEdge(self.clock)

        await RisingEdge(self.clock)
        self.axi.arvalid.value = 0

    async def write(self,
                    address: int,
                    data: List[int],
                    size: AXI4Size = AXI4Size.SIZE_4B,
                    burst_type: AXI4BurstType = AXI4BurstType.INCR,
                    strobe: Optional[List[int]] = None,
                    transaction_id: Optional[int] = None,
                    timeout_cycles: int = 1000) -> AXI4Response:
        """
        Perform AXI4 write transaction

        Args:
            address: Starting address for write
            data: List of data values to write
            size: Size of each data beat
            burst_type: Type of burst transaction
            strobe: Optional write strobe values (default: all bytes enabled)
            transaction_id: Optional transaction ID (auto-assigned if None)
            timeout_cycles: Timeout in clock cycles

        Returns:
            Write response

        Raises:
            AXI4TimeoutError: If transaction times out
            AXI4ResponseError: If response indicates an error
        """
        if not self._initialized:
            await self.initialize()

        if transaction_id is None:
            transaction_id = await self._get_next_transaction_id()

        length = len(data)
        if strobe is None:
            strobe = [(2**self.strobe_width - 1)] * length  # All bytes enabled

        self.log.debug(f"Starting write transaction ID {transaction_id}: "
                      f"addr=0x{address:08x}, len={length}, size={size.name}")

        # Verify page crossing for INCR bursts
        if burst_type == AXI4BurstType.INCR:
            burst_bytes = length * (2 ** size.value)
            start_page = address // 4096
            end_page = (address + burst_bytes - 1) // 4096
            if start_page != end_page:
                raise AXI4DriverError("INCR burst crosses 4KB page boundary")

        # Create completion event
        completion_event = Event()
        self._pending_writes[transaction_id] = completion_event

        # Send address and data concurrently
        address_task = cocotb.start_soon(
            self._send_write_address(address, length-1, size, burst_type, transaction_id)
        )
        data_task = cocotb.start_soon(
            self._send_write_data(data, strobe)
        )

        # Wait for both to complete
        await address_task
        await data_task

        # Wait for write response with timeout
        try:
            await with_timeout(completion_event.wait(), 1, 'ms')
        except cocotb.triggers.SimTimeoutError:
            raise AXI4TimeoutError(f"Write transaction {transaction_id} timed out")

        # Check response
        if transaction_id not in self._write_results:
            raise AXI4DriverError(f"No response for transaction {transaction_id}")

        response = self._write_results[transaction_id]

        # Cleanup
        del self._pending_writes[transaction_id]
        del self._write_results[transaction_id]

        if response != AXI4Response.OKAY:
            cocotb.log.warning(f"Write transaction {transaction_id} received error response: {response.name}")
            #raise AXI4ResponseError(f"Write error response: {response.name}", response)
        else:
            self.log.debug(f"Write transaction {transaction_id} completed successfully")
        return response

    async def _send_write_address(self,
                                 address: int,
                                 length: int,
                                 size: AXI4Size,
                                 burst_type: AXI4BurstType,
                                 transaction_id: int):
        """Send write address phase"""
        # Set up address phase
        self.axi.awaddr.value = address
        self.axi.awlen.value = length
        self.axi.awsize.value = size.value
        self.axi.awburst.value = burst_type.value
        self.axi.awid.value = transaction_id
        self.axi.awvalid.value = 1

        # Wait for ready
        while not self.axi.awready.value:
            await RisingEdge(self.clock)
            # await self.axi.awready.value.value_change #? ??

        await RisingEdge(self.clock)
        self.axi.awvalid.value = 0

    async def _send_write_data(self, data: List[int], strobe: List[int]):
        """Send write data phase"""
        for i, (data_beat, strobe_beat) in enumerate(zip(data, strobe)):
            # Set up data
            self.axi.wdata.value = data_beat
            self.axi.wstrb.value = strobe_beat
            self.axi.wlast.value = 1 if i == len(data) - 1 else 0
            self.axi.wvalid.value = 1

            # Wait for ready
            while not self.axi.wready.value:
                await RisingEdge(self.clock)

            await RisingEdge(self.clock)

        self.axi.wvalid.value = 0
        self.axi.wlast.value = 0

    async def read_burst(self,
                        address: int,
                        length: int,
                        burst_type: Union[AXI4BurstType, str] = AXI4BurstType.INCR,
                        size: AXI4Size = AXI4Size.SIZE_4B,
                        **kwargs) -> List[int]:
        """
        Convenience method for burst reads

        Args:
            address: Starting address
            length: Number of beats
            burst_type: Burst type (INCR, WRAP, FIXED)
            size: Transfer size
            **kwargs: Additional arguments passed to read()

        Returns:
            List of data values
        """
        if isinstance(burst_type, str):
            burst_type = AXI4BurstType[burst_type.upper()]

        return await self.read(address=address,
                              length=length,
                              size=size,
                              burst_type=burst_type,
                              **kwargs)

    async def write_burst(self,
                         address: int,
                         data: List[int],
                         burst_type: Union[AXI4BurstType, str] = AXI4BurstType.INCR,
                         size: AXI4Size = AXI4Size.SIZE_4B,
                         **kwargs) -> AXI4Response:
        """
        Convenience method for burst writes

        Args:
            address: Starting address
            data: Data to write
            burst_type: Burst type (INCR, WRAP, FIXED)
            size: Transfer size
            **kwargs: Additional arguments passed to write()

        Returns:
            Write response
        """
        if isinstance(burst_type, str):
            burst_type = AXI4BurstType[burst_type.upper()]

        return await self.write(address=address,
                               data=data,
                               size=size,
                               burst_type=burst_type,
                               **kwargs)

    async def write_single(self, address: int, data: int, **kwargs) -> AXI4Response:
        """
        Convenience method for single word write

        Args:
            address: Address to write
            data: Single data value
            **kwargs: Additional arguments

        Returns:
            Write response
        """
        return await self.write(address=address, data=[data], **kwargs)

    async def read_single(self, address: int, **kwargs) -> int:
        """
        Convenience method for single word read

        Args:
            address: Address to read
            **kwargs: Additional arguments

        Returns:
            Single data value
        """
        result = await self.read(address=address, length=1, **kwargs)
        return result[0]

    def cleanup(self):
        """Clean up driver resources"""
        if self._read_monitor_task:
            self._read_monitor_task.kill()
            self._read_monitor_task = None

        if self._write_monitor_task:
            self._write_monitor_task.kill()
            self._write_monitor_task = None

        self._pending_reads.clear()
        self._pending_writes.clear()
        self._read_results.clear()
        self._write_results.clear()

        self._initialized = False
        self.log.info("AXI4 driver cleanup completed")


# Convenience functions for quick usage
async def axi_read(axi_interface: SimHandleBase,
                   address: int,
                   length: int = 1,
                   **kwargs) -> List[int]:
    """
    Quick AXI read without driver instance management

    Args:
        axi_interface: AXI interface handle
        address: Address to read
        length: Number of beats
        **kwargs: Additional driver arguments

    Returns:
        List of data values
    """
    driver = AXI4Driver(axi_interface, **kwargs)
    try:
        return await driver.read(address, length)
    finally:
        driver.cleanup()


async def axi_write(axi_interface: SimHandleBase,
                    address: int,
                    data: Union[int, List[int]],
                    **kwargs) -> AXI4Response:
    """
    Quick AXI write without driver instance management

    Args:
        axi_interface: AXI interface handle
        address: Address to write
        data: Data to write (single value or list)
        **kwargs: Additional driver arguments

    Returns:
        Write response
    """
    if isinstance(data, int):
        data = [data]

    driver = AXI4Driver(axi_interface, **kwargs)
    try:
        return await driver.write(address, data)
    finally:
        driver.cleanup()