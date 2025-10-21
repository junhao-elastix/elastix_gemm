# BRAM Read/Write Conflict Analysis

## BRAM Configuration
- **Dual-port**: Port A (write from GDDR6), Port B (read by CE)
- **True dual-port**: Both can operate simultaneously
- **Depth**: 2048 entries

## Timing During Second FETCH Burst 33

**Dispatcher (Port A Write)**:
- Trying to write addresses: 1040-1055
- State: ST_FETCH_WAIT, waiting for AXI rvalid

**Compute Engine (Port B Read)**:
From debug: CE reading address 789, 555, etc.
- CE state = 1 or 2 (ST_LOAD_LEFT_EXP or ST_LOAD_RIGHT_EXP)
- CE is READING from BRAM while dispatcher is WRITING

**Potential Issue**:
If CE is reading addresses NEAR 1040, there could be:
1. BRAM arbitration delay
2. Read-during-write hazard
3. Timing violation in dual-port BRAM

But CE was reading ~555, not 1040, so different regions...
