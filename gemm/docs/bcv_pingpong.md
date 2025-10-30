# BCV Controller Ping-Pong Architecture

## Overview
Dual state machine design for overlapped fill and compute operations using ping-pong buffering.

## Architecture

### Two Independent State Machines

**1. Fill State Machine (FSM_FILL)**
- States: `IDLE`, `FILL_BUFFER`
- Responsible for: Loading data from BRAM into PING or PONG buffers
- Duration: 5 cycles per buffer fill

**2. Compute State Machine (FSM_COMP)**
- States: `IDLE`, `COMPUTE_NV`, `ACCUM`, `RETURN`
- Responsible for: Running gfp8_nv_dot computation, accumulation, and result output
- Duration: 4 cycles (compute) + 1 cycle (accum) per V iteration

### Control Signals (Handshake Protocol)

```
filling_ping   : Fill FSM sets HIGH when filling PING, Compute FSM sets LOW when start computing ping
filling_pong   : Fill FSM sets HIGH when filling PONG, Compute FSM sets LOW when start computing pong
ping_ready     : Fill FSM sets HIGH when PING filled, Compute FSM sets LOW when ping consumed, compute finished
pong_ready     : Fill FSM sets HIGH when PONG filled, Compute FSM sets LOW when pong consumed, compute finished
```

### Initial Conditions
```
filling_ping = 0
filling_pong = 0
ping_ready   = 0
pong_ready   = 0
```

## Operation Flow

### Startup (V=0)
1. **External trigger** sets `filling_ping = 1`
2. Fill FSM fills PING buffer (5 cycles)
3. Fill FSM sets `ping_ready = 1`

### Steady State (V≥1)

#### Compute FSM Behavior
```
IDLE:
  - Check for (ping_ready OR pong_ready)
  - If ping_ready: Use PING buffer, start compute
  - If pong_ready: Use PONG buffer, start compute

COMPUTE_NV:
  - Compute on selected buffer (4 cycles)
  - On completion, move to ACCUM

ACCUM:
  - Clear the ready flag
    - If used PING: ping_ready = 0
    - If used PONG: pong_ready = 0
  - Accumulate result
  - Increment V counter
  - Return to IDLE, check for next ready buffer
```

#### Fill FSM Behavior
```
IDLE:
  - Check: (!filling_ping AND !pong_ready) → Start filling PONG, filling_pong high
  - Check: (!filling_pong AND !ping_ready) → Start filling PING, filling_ping high
  
FILL_BUFFER:
  - Fill target buffer (5 cycles)
  - On completion:
    - If filling PING: ping_ready = 1
    - If filling PONG: pong_ready = 1
```

### Example Timeline (V=0,1,2,3)

```
Time | Fill FSM          | Compute FSM       | Filling Ping | Ping Ready | Filling Pong | Pong Ready |
-----|-------------------|-------------------|--------------|------------|--------------|------------|
  0  | (trigger)         | IDLE              | 1            | 0          | 0            | 0          | 
 1-5 | FILL PING         | IDLE (waiting)    | 1            | 0          | 0            | 0          | 
  6  | IDLE              | IDLE              | 0            | 1          | 0            | 0          | 
  7  | FILL_PONG (start) | COMPUTE PING      | 0            | 1          | 1            | 0          | 
 8-11| FILL_PONG         | COMPUTE PING      | 0            | 0          | 1            | 0          | 
 12  | IDLE              | ACCUM             | 0            | 0          | 0            | 1          | 
 13  | FILL_PING (start) | COMPUTE PONG      | 1            | 0          | 0            | 1          | 
14-17| FILL_PING         | COMPUTE PONG      | 1            | 0          | 0            | 0          | 
 18  | IDLE              | ACCUM             | 0            | 1          | 0            | 0          | 
 19  | FILL_PONG (start) | COMPUTE PING      | 0            | 1          | 1            | 0          | 
...  | (continues)       | (continues)       | (alternates)

* Compute FSM clears ready flag after starting compute
```

### Termination (Last V iteration)

1. Compute FSM detects last V iteration
2. Compute FSM does NOT request next fill
3. Both FSMs return to IDLE
4. All flags return to 0

## Key Properties

### Producer-Consumer Pattern
- **Fill FSM = Producer**: Fills buffers, sets ready flags
- **Compute FSM = Consumer**: Consumes buffers, clears ready flags
- **Mutual Exclusion**: Only one buffer being filled at a time
- **Flow Control**: Fill waits if both ready flags are high (backpressure)

### Overlap Efficiency
- **V=0**: 5 (fill) + 4 (compute) + 1 (accum) = 10 cycles
- **V≥1**: Fill overlapped with compute = 5 cycles (if fill completes before compute)
- **Actual**: max(5 fill, 4 compute) + 1 accum = 5 + 1 = 6 cycles per V (after V=0)
- **Wait**: If compute finishes before fill (4 < 5), must wait 1 cycle

### Address Generation
- V index for fill: Use incremented V from loop control
- Each FSM tracks its own buffer target independently
- No need for complex v_idx+1 logic

## Implementation Notes

### State Variables
```systemverilog
// Fill FSM
typedef enum {FILL_IDLE, FILL_ACTIVE} fill_state_t;
fill_state_t fill_state;
logic fill_target;  // 0=PING, 1=PONG

// Compute FSM  
typedef enum {COMP_IDLE, COMP_NV, COMP_ACCUM, COMP_RETURN, COMP_DONE} comp_state_t;
comp_state_t comp_state;
logic comp_source;  // 0=PING, 1=PONG

// Handshake signals
logic filling_ping, filling_pong;
logic ping_ready, pong_ready;
```

### Startup Trigger
- External control (from main FSM) asserts initial `filling_ping = 1`
- OR: Fill FSM self-starts on i_tile_en rising edge

### Buffer Selection
- Compute FSM: `comp_source = pong_ready ? 1 : 0` (prefer PONG if both ready)
- Fill FSM: `fill_target = ~comp_source` (fill opposite of what's being computed)

## Advantages Over Single FSM

1. **Simpler Logic**: Each FSM has clear responsibility
2. **Natural Overlap**: Producer-consumer pattern enables overlap automatically
3. **Easier Debugging**: Can trace fill and compute independently
4. **Scalable**: Easy to add third buffer (triple buffering) if needed
5. **No Race Conditions**: Handshake protocol ensures mutual exclusion

## Expected Performance

- **Non-overlapped**: 10 cycles per V × V iterations = 10V + overhead
- **Ping-pong**: 10 (first) + 6×(V-1) + overhead ≈ 6V + 4 + overhead
- **Improvement**: ~40% reduction for large V (e.g., V=128)

