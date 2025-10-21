# ACX_BRAM72K_SDP

## Logic Symbol
The ACX_BRAM72K_SDP block RAM primitive implements a 72-Kb simple dual-port (SDP) memory block with one write port and one read port. Each port can be independently configured with respect to bit-width. Both ports can be configured as any one of 512 × 144, 512 × 128, 1024 × 72, 1024 × 64, 2048 × 36, 2048 × 32, 4096 × 18, 4096 × 16, 8192 × 9, 8192 × 8, or 16384 × 4, (depth × data width). The read and write operations are both synchronous.

For higher performance operation, an additional output register can be enabled at the cost of an additional cycle of read latency.

When writing, there is one write enable bit (we[]) for each 8 or 9 bits of input data, depending on the byte_width parameter.

The initial value of the memory contents may be user-specified from either parameters or a memory initialization file.

A block diagram showing the data flow through the ECC modules, memories, and optional output registers is shown below.

## Parameters

| Parameter | Supported Values | Default Value | Description |
|-----------|------------------|---------------|-------------|
| read_width (1) | 4, 8, 9, 16, 18, 32, 36, 64, 72, 128, 144 | 72 | Data width of read port. Read port widths of 36 or narrower are not supported for write_width settings of 72 or 144. |
| write_width (1) | 4, 8, 9, 16, 18, 32, 36, 64, 72, 128, 144 | 72 | Data width of write port. |
| rdclk_polarity | "rise", "fall" | "rise" | Determines whether the rdclk signal uses the falling or rising edge: "rise" – rising edge. "fall" – falling edge. |
| wrclk_polarity | "rise", "fall" | "rise" | Determines whether the wrclk signal uses the falling or rising edge: "rise" – rising edge. "fall" – falling edge. |
| outreg_enable | 0, 1 | 0 | Determines whether the output register is enabled: 0 – disables the output register and results in a read latency of one cycle. 1 – enables the output register and results in a read latency of two cycles. |
| outreg_sr_assertion | "clocked", "unclocked" | "clocked" | Determines whether the assertion of the output register reset is synchronous or asynchronous with respect to the rdclk input. "clocked" – synchronous reset. The output register is reset upon the next rising edge of the clock when outreg_rstn is asserted. "unclocked" – asynchronous reset. The output register is reset immediately following the assertion of the outreg_rstn input. |
| byte_width (2) | 8, 9 | 9 | Determines whether the the we[] signal applies as 8-bit bytes or 9-bit bytes: The byte_width=8 setting is required for read_width and write_width settings of 4, 8, 16, 32, 64 or 128. The 144-bit din[] signal should be viewed as eighteen 8-bit bytes. During a write operation, we[17:0] selects which of the 8-bit bytes to be written, where we[0] implies that din[7:0] is written to memory, and we[17] implies that din[143:136] is written. The byte_width=9 setting is required for read_width and write_width settings of 9, 18 or 36. The 144-bit din[] signal should be viewed as sixteen 9-bit bytes. During a write operation, we[7:0] selects which of the lower 9-bit bytes to be written and we[16:9] selects which of the higher 9-bit bytes to be written, where we[0] implies that din[8:0] is written to memory, and we[16] implies that din[143:135] is written. In this mode, we[8] and we[17] are ignored. |
| mem_init_file | Path to HEX file | "" | Provides a mechanism to set the initial contents of the ACX_BRAM72K_SDP memory: If the mem_init_file parameter is defined, the BRAM is initialized with the values defined in the file pointed to by the mem_init_file parameter according to the format defined in Memory Initialization. If the mem_init_file is left at the default value of "", the initial contents are defined by the values of the initd_0 through initd_1023 parameters. If the memory initialization parameters and the mem_init_file parameters are not defined, the contents of the BRAM remain uninitialized. |
| initd_0–initd_1023 | 72 bit hex number | 72'hX | The initd_0 through initd_1023 parameters define the initial contents of the memory associated with dout[71:0] as defined in Memory Initialization. |
| ecc_encoder_enable | 0, 1 | 0 | Determines if the ECC encoder circuitry is enabled. A value of 1 is only supported for a write width of 64 or 128: 0 – disables the ECC encoder. 1 – enables the ECC encoder such that din[71:64] and din[143:136] are ignored and bits [71:64] and [143:136] of the memory array are populated with ECC bits. |
| ecc_decoder_enable | 0, 1 | 0 | Determines if the ECC decoder circuitry is enabled. A value of 1 is only supported for a read width of 64 or 128: 0 – disables the ECC decoder. 1 – enables the ECC decoder. |
| read_remap | 0, 1 | 0 | Enable read port to be remapped: 0 - disable remap. In byte_mode=8, the port presents up to 1024 locations. 1 - enable remap. With read_width=4, 8, 16, 32 or 64, when rdmsel=1'b1 and rdaddr[11]=1'b0, the port presents up to 1152 locations, reading the higher order data bits as extended memory address locations. See Advanced Modes for full details. |
| write_remap | 0, 1 | 0 | Enable write port to be remapped: 0 - disable remap. In byte_mode=8, the port presents up to 1024 locations. 1 - enable remap. With write_width=4, 8, 16, 32 or 64, when wrmsel=1'b1 and wraddr[11]=1'b0, the port presents up to 1152 locations, writing the extended memory address locations to the higher order data bits. See Advanced Modes for full details. |

Table Notes:
(1) Setting read_width or write_width to 128 or 144 consumes the adjacent MLP site by using it as a route-through to accommodate the transfer of wide data.
(2) Write and read port widths of 72 or 144 are allowed to use either 8 or 9.

## Ports

| Name | Direction | Description |
|------|-----------|-------------|
| wrclk | Input | Write clock input. Write operations are fully synchronous and occur upon the active edge of the wrclk clock input when wren is asserted. The active edge of wrclk is determined by the wrclk_polarity parameter. |
| wren | Input | Write port enable. Assert wren high to perform a write operation. |
| we[17:0] | Input | Write enable mask. There is one bit of we[] for each byte of din (byte width can be set to either 8 or 9 bits). Asserting each bit causes the corresponding byte of we[] din to be written to memory. When using 72-bit width or smaller, only the lower 9 bits must be connected. |
| wraddr[13:0] | Input | The wraddr signal determines which memory location is being written to. See the write port address and data bus mapping tables below for details. |
| wrmsel | Input | Write support for advanced modes. Used in conjunction with wraddr[11] to set the following modes, {wrmsel, wraddr[11]}: 1'b0, 1'bx – normal mode. BRAM write-side operation. 1'b1, 1'b0 – remap depth mode. 9-bit bytes remapped to 8-bit bytes. 1'b1, 1'b1 – reserved. See Advanced Modes for full details of the operation. |
| din[143:0] | Input | The din signal determines the data to write to the memory array during a write operation. See the write port address and data bus mapping tables below for details. |
| rdclk | Input | Read clock input. Read operations are fully synchronous and occur upon the active edge of the rdclk input when the rden signal is asserted. The active edge of rdclk is determined by the rdclk_polarity parameter. |
| rden | Input | Read port enable. Assert rden high to perform a read operation. |
| rdaddr[13:0] | Input | The rdaddr signal determines which memory location to read from. See the read port address and data bus mapping tables below for details. |
| rdmsel | Input | Read support for advanced modes. Used in conjunction with rdaddr[11] to set the following modes, {rdmsel, rdaddr[11]}: 1'b0, 1'bx – normal mode. BRAM read-side operation. 1'b1, 1'b0 – remap mode. 9-bit bytes remapped to 8-bit bytes. 1'b1, 1'b1 – reserved. See Advanced Modes for full details of the operation. |
| outlatch_rstn | Input | Output latch synchronous reset. When outlatch_rstn is asserted low, the value of the output latches are reset to 0. |
| outreg_rstn | Input | Output register synchronous reset. When outreg_rstn is asserted low, the value of the output registers are reset to 0. |
| outreg_ce | Input | Output register clock enable (active high). When outreg_enable=1, de-asserting outreg_ce causes the BRAM to keep the dout signal unchanged, independent of a read operation. When outreg_enable=0, input outreg_ce is ignored. |
| dout[143:0] | Output | Read port data output. For read operations, the dout output is updated with the memory contents addressed by rdaddr if the port enable rden is active. See the read port address and data bus mapping tables below for details. |
| sbit_error[1:0] (1) | Output | Single-bit error (active high). The sbit_error signal is asserted during a read operation when ecc_decoder_enable=1 and a single-bit error is detected. In this case, the corrected word is output on the dout pins. The memory contents are not corrected by the error correction circuitry. The sbit_error signal is aligned with the associated read data word. When using 64-bit width, only sbit_error[0] should be used. sbit_error[1] is unused. |
| dbit_error[1:0] (1) | Output | Dual-bit error (active high). The dbit_error signal is asserted during a read operation when ecc_decoder_enable=1 and two or more bit errors are detected. In the case of two or more bit errors, the uncorrected read data word is output on the dout pins. The dbit_error signal is aligned with the associated read data word. When using 64-bit width, only dbit_error[0] should be used. dbit_error[1] is unused. |

Table Notes:
(1) ECC modes are only applicable with read and write widths of 64 and 128 bits. In these modes, bits [71:64] and [143:136] of the memory array are used to store the ECC parity bits. If ECC is enabled with other read_width settings, the respective data input and output on these memory array bits are ignored. Please see ECC Modes of Operation for full details of ECC operation and configuration.

## Memory Organization and Data Input/Output Pin Assignments

### Supported Width Combinations

The ACX_BRAM72K_SDP block supports a variety of memory width combinations, as shown in the following table.

| Write Data Width | Read Data Width | | | | | | | | | | |
|------------------|---|---|---|---|---|---|---|---|---|---|---|
| | 144 | 72 | 36 | 18 | 9 | 128 | 64 | 32 | 16 | 8 | 4 |
| 144 | ✓ | (w)(1) | (w)(1) | (w)(1) | (w)(1) | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| 72 | | ✓ | ✓ | ✓ | ✓ | | ✓ | ✓ | ✓ | ✓ | ✓ |
| 36 | | | ✓ | ✓ | ✓ | | (r)(1) | ✓ | ✓ | ✓ | ✓ |
| 18 | | | | ✓ | ✓ | | (r)(1) | (r)(1) | ✓ | ✓ | ✓ |
| 9 | | | | | ✓ | | (r)(1) | (r)(1) | (r)(1) | ✓ | ✓ |
| 128 | | | | | | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| 64 | | | | | | | ✓ | ✓ | ✓ | ✓ | ✓ |
| 32 | | | | | | | | ✓ | ✓ | ✓ | ✓ |
| 16 | | | | | | | | | ✓ | ✓ | ✓ |
| 8 | | | | | | | | | | ✓ | ✓ |
| 4 | | | | | | | | | | | ✓ |

Table Notes:
(1) Requires remap mode:
(w) – write_remap=1'b1.
(r) – read_remap=1'b1.

### Write Data Port Usage

| Write Port Configuration | Data Input Assignment | Write Word Address Assignment |
|-------------------------|----------------------|------------------------------|
| 144 × 512 | din[143:0] <= user_din[143:0] | wraddr[13:5] <= user_wraddr[8:0] wraddr[4:0] <= 5'b0 |
| 128 × 512 | din[143:136] <= 8'b0 din[135:72] <= user_din[127:64] din[71:64] <= 8'b0 din[63:0] <= user_din[63:0] | wraddr[13:5] <= user_wraddr[8:0] wraddr[4:0] <= 5'b0 |
| 72 × 1024 | din[143:72] <= 72'b0 din[71:0] <= user_din[71:0] | wraddr[13:4] <= user_wraddr[9:0] wraddr[3:0] <= 4'b0 |
| 64 × 1024 | din[143:64] <= 80'b0 din[63:0] <= user_din[63:0] | wraddr[13:4] <= user_wraddr[9:0] wraddr[3:0] <= 4'b0 |
| 36 × 2048 | din[143:36] <= 108'b0 din[35:0] <= user_din[35:0] | wraddr[13:3] <= user_wraddr[10:0] wraddr[2:0] <= 3'b0 |
| 32 × 2048 | din[143:32] <= 112'b0 din[31:0] <= user_din[31:0] | wraddr[13:3] <= user_wraddr[10:0] wraddr[2:0] <= 3'b0 |
| 18 × 4096 | din[143:18] <= 126'b0 din[17:0] <= user_din[17:0] | wraddr[13:2] <= user_wraddr[11:0] wraddr[1:0] <= 2'b0 |
| 16 × 4096 | din[143:16] <= 128'b0 din[15:0] <= user_din[15:0] | wraddr[13:2] <= user_wraddr[11:0] wraddr[1:0] <= 2'b0 |
| 9 × 8192 | din[143:9] <= 135'b0 din[8:0] <= user_din[8:0] | wraddr[13:1] <= user_wraddr[12:0] raddr[0] <= 1'b0 |
| 8 × 8192 | din[143:8] <= 136'b0 din[7:0] <= user_din[7:0] | wraddr[13:1] <= user_wraddr[12:0] wraddr[0] <= 1'b0 |
| 4 × 16384 | din[143:4] <= 140'b0 din[3:0] <= user_din[3:0] | wraddr[13:0] <= user_wraddr[13:0] |

### Read Data Port Usage

| Read Port Configuration | Data Output Assignment | Read Word Address Assignment |
|------------------------|------------------------|-------------------------------|
| 144 × 512 | user_dout[143:0] <= dout[143:0] | rdaddr[13:5] <= user_rdaddr[8:0] rdaddr[4:0] <= 5'b0 |
| 128 × 512 | user_dout[127:64] <= dout[135:72] user_dout[63:0] <= dout[63:0] | rdaddr[13:5] <= user_rdaddr[8:0] rdaddr[4:0] <= 5'b0 |
| 72 × 1024 | user_dout[72:0] <= dout[72:0] | rdaddr[13:4] <= user_rdaddr[9:0] rdaddr[3:0] <= 4'b0 |
| 64 × 1024 | user_dout[63:0] <= dout[63:0] | rdaddr[13:4] <= user_rdaddr[9:0] rdaddr[3:0] <= 4'b0 |
| 36 × 2048 (1) | user_dout[35:0] <= dout[35:0] | rdaddr[13:3] <= user_rdaddr[10:0] rdaddr[2:0] <= 3'b0 |
| 32 × 2048 (1) | user_dout[31:0] <= dout[31:0] | rdaddr[13:3] <= user_rdaddr[10:0] rdaddr[2:0] <= 3'b0 |
| 18 × 4096 (1) | user_dout[17:0] <= dout[17:0] | rdaddr[13:2] <= user_rdaddr[11:0] rdaddr[1:0] <= 2'b0 |
| 16 × 4096 (1) | user_dout[15:0] <= dout[15:0] | rdaddr[13:2] <= user_rdaddr[11:0] rdaddr[1:0] <= 2'b0 |
| 9 × 8192 (1) | user_dout[8:0] <= dout[8:0] | rdaddr[13:1] <= user_rdaddr[12:0] rdaddr[0] <= 1'b0 |
| 8 × 8192 (1) | user_dout[7:0] <= dout[7:0] | rdaddr[13:1] <= user_rdaddr[12:0] rdaddr[0] <= 1'b0 |
| 4 × 16384 (1) | user_dout[3:0] <= dout[3:0] | rdaddr[13:0] <= user_rdaddr[13:0] |

Table Notes:
(1) Not supported for write_width setting of 72 or 144.

## Read and Write Operations

### Timing Options

The ACX_BRAM72K_SDP has two options for interface timing, controlled by the outreg_enable parameter:

- Latched mode – when outreg_enable=0, the port is in latched mode. In latched mode, the read address is registered and the stored data is latched into the output latches on the following clock cycle providing a read operation with one cycle of latency.

- Registered mode – when outreg_enable=1, the port is in registered mode. In registered mode, there is an additional register after the latch to support higher-frequency designs providing a read operation with two cycles of latency.

### Read Operation

Read operations are signaled by driving the rdaddr[] signal with the address to be read and asserting the rden signal. The requested read data arrives on the dout[] signal on the following clock cycle or the cycle after depending on the outreg_enable parameter value.

### ACX_BRAM72K_SDP Output Function Table for Latched Mode

| Operation | rdclk | outlatch_rstn | rden | dout[] |
|-----------|-------|---------------|------|--------|
| Hold | X | X | X | Hold previous value |
| Reset latch | ↑ | 0 | X | 0 |
| Hold | ↑ | 1 | 0 | Hold previous value |
| Read | ↑ | 1 | 1 | mem[rdaddr] |

Table Note:
Operation assumes rising-edge clock and active-high port enable.

### ACX_BRAM72K_SDP Output Function Table for Registered Mode

| Operation | rdclk | outreg_rstn | outregce | dout[] |
|-----------|-------|-------------|----------|--------|
| Hold | X | X | X | Previous dout[] |
| Reset Output | ↑ | 0 | 1 | 0 |
| Hold | ↑ | 1 | 0 | Previous dout[] |
| Update Output | ↑ | 1 | 1 | Registered from latch output |

Table Note:
Operation assumes active-high clock, output register clock enable, and output register reset.

### Write Operation

Write operations are signaled by asserting the wren signal. The value of the din[] signal is stored in the memory array at the address indicated by the wraddr[] signal on the next active clock edge.

### Simultaneous Memory Operations

Memory operations may be performed simultaneously from both sides of the memory. However, there is a restriction regarding memory collisions. A memory collision is defined as the condition where both ports access the same memory location(s) within the same clock cycle (both ports connected to the same clock), or within a fixed time window (if each port is connected to a different clock). If one of the ports is writing an address while the other port is reading the same address (qualified with overlapping write enables per bit), the write operation takes precedence, but the read data is invalid. The data may be reliably read on the next cycle if there is no longer a write collision.