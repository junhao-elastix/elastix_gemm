<!-- 3aff65d5-9c34-441e-a193-f19bfe0f2798 1e23456e-7f45-47fd-aef8-46cf0af9e4cd -->
# Optimize Fetcher AXI Read Burst Pipelining

## Current Implementation Analysis

**Current fetcher.sv behavior:**

- Issues AR request in `ST_FETCH_INIT`
- Waits for AR handshake before starting data transfer
- Issues next AR request only after RLAST of previous burst (lines 684-697)
- This creates a gap: must wait for RLAST before issuing next AR

**gddr_ref_design pattern (axi_pkt_gen):**

- 8-entry AWID FIFO tracks outstanding write transactions
- Can issue new AW request when `~awid_fifo_full` (even during active write)
- Enables true pipelining: AW for burst N+1 while burst N is still sending W data

## Optimization Strategy

### 1. Add ARID FIFO for Outstanding Transaction Tracking

**Location:** `fetcher.sv` lines 108-128 (add new signals after existing AXI control signals)

Add ARID FIFO similar to `axi_pkt_gen.sv` lines 320-382:

- 8-entry FIFO (sufficient for NoC latency)
- Track ARID values on AR handshake (`arvalid & arready`)
- Decrement on RLAST handshake (`rvalid & rready & rlast`)
- Generate `arid_fifo_full` and `arid_fifo_empty` flags

**Benefits:**

- Track multiple in-flight read transactions (up to 8 concurrent bursts)
- Enable pipelined AR requests

### 2. Pipeline AR Requests (Issue Before RLAST)

**Location:** `fetcher.sv` lines 669-713 (AR request control logic)

**Current logic:** Issues AR only on RLAST (line 684)

**New logic:** Issue AR requests continuously while:

- Not all lines fetched (`exp_lines_fetched_reg < 16` or `man_lines_fetched_reg < 511`)
- ARID FIFO not full (`~arid_fifo_full`)
- Not in IDLE state

**Key change:** Remove dependency on RLAST for AR request generation:

```systemverilog
// Instead of: if (rvalid && rready && rlast)
// Use: if (~arid_fifo_full && (exp_lines_fetched_reg < 16 || man_lines_fetched_reg < 511))
```

### 3. Simplify State Machine

**Location:** `fetcher.sv` lines 192-251 (state transition logic)

**Current:** `ST_FETCH_READ` → `ST_FETCH_READ_EXP` → `ST_FETCH_READ` → `ST_FETCH_READ_MAN` → `ST_FETCH_READ`

**Optimized:** Remove need to return to `ST_FETCH_READ` between bursts:

- Stay in `ST_FETCH_READ_EXP` or `ST_FETCH_READ_MAN` continuously
- Issue AR requests in parallel while receiving R data
- Transition to `ST_FETCH_READ_MAN` only when `exp_lines_fetched_reg >= 16`

**Benefits:**

- Eliminates state machine overhead between bursts
- Reduces latency by ~2 cycles per burst

### 4. ARID Generation and Tracking

**Location:** `fetcher.sv` line 721 (current: `arid = 8'hFE`)

**Current:** Fixed ARID value

**New:** Increment ARID for each AR request (similar to `axi_pkt_gen.sv` line 289):

```systemverilog
logic [7:0] arid_counter;
always_ff @(posedge i_clk) begin
    if (arvalid && arready) begin
        arid_counter <= arid_counter + 8'h1;
    end
end
```

Store ARID in FIFO on AR handshake, verify on RLAST (optional, for debugging)

## Implementation Details

### ARID FIFO Structure

```systemverilog
localparam ARID_FIFO_DEPTH_WIDTH = 3;  // 8 entries
logic [ARID_FIFO_DEPTH_WIDTH-1:0] arid_fifo_wr_ptr, arid_fifo_rd_ptr, arid_fifo_entries;
logic [7:0] arid_fifo [(2**ARID_FIFO_DEPTH_WIDTH)-1:0];
logic [7:0] arid_fifo_dout;

assign arid_fifo_wr = (axi_ddr_if.arvalid && axi_ddr_if.arready);
assign arid_fifo_rd = (axi_ddr_if.rvalid && axi_ddr_if.rready && axi_ddr_if.rlast);
```

### AR Request Logic Update

**Replace lines 676-698 with:**

```systemverilog
// Issue AR request when:
// 1. In active fetch phase (EXP or MAN)
// 2. ARID FIFO not full (allows pipelining)
// 3. More lines to fetch
if (state_reg == ST_FETCH_INIT) begin
    axi_ar_req_reg <= 1'b1;
end else if (axi_ddr_if.arvalid && axi_ddr_if.arready) begin
    axi_ar_req_reg <= 1'b0;  // Clear after handshake
end else begin
    // Pipelined AR requests: issue before RLAST
    if (~arid_fifo_full) begin
        if (state_reg == ST_FETCH_READ_EXP && exp_lines_fetched_reg < 15) begin
            axi_ar_req_reg <= 1'b1;
        end else if (state_reg == ST_FETCH_READ_MAN && man_lines_fetched_reg < 511) begin
            axi_ar_req_reg <= 1'b1;
        end
    end
end
```

## Expected Performance Improvement

**Current:** 33 bursts × ~17 cycles = ~561 cycles (with gaps)

**Optimized:** 33 bursts × ~16 cycles = ~528 cycles (no gaps)

**Savings:** ~33 cycles (~6% improvement)

**Additional benefits:**

- Eliminates inter-burst gaps completely
- Better utilizes NoC bandwidth
- Reduces latency for large transfers

## Testing Considerations

1. **Simulation validation:**

   - Verify AR requests issue continuously (no gaps)
   - Check ARID FIFO doesn't overflow
   - Ensure all 528 lines (16 exp + 512 man) fetched correctly

2. **Hardware validation:**

   - Compare fetch timing with performance instrumentation
   - Verify correct BRAM addressing for pipelined bursts
   - Test with different FETCH lengths

3. **Edge cases:**

   - ARID FIFO full condition (backpressure handling)
   - Transition from EXP to MAN phase
   - FETCH completion (all lines fetched)

## Files to Modify

- `gemm/src/rtl/fetcher.sv`: Add ARID FIFO, pipeline AR requests, simplify state machine
- No other files need changes (interface remains the same)

### To-dos

- [ ] Add ARID FIFO structure (8-entry) to track outstanding read transactions, similar to axi_pkt_gen AWID FIFO
- [ ] Modify AR request logic to issue requests continuously when ARID FIFO not full, removing dependency on RLAST
- [ ] Simplify state machine to eliminate ST_FETCH_READ transitions, allowing continuous AR requests during active fetch phases
- [ ] Add ARID counter that increments on each AR handshake for proper transaction tracking
- [ ] Validate pipelined AR requests in simulation, verify no gaps between bursts and correct line fetching