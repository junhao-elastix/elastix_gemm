# Command FIFO Investigation Summary

**Date**: Mon Oct 13, 2025 - 17:20 PDT  
**Critical Finding**: Engine processes SOME commands then stops!

## Key Evidence

### 1. FIFO Count Behavior
- After reset: `cmd_fifo_count = 64` (FULL)
- After adding 1 more command (4 words): `cmd_fifo_count = 48`
- **Net change**: -16 entries = 4 commands processed!

### 2. Engine State
- `mc_state = 0x0` (IDLE)
- `engine_busy = 0`
- `fifo_empty = 0` (48 commands still pending)

### 3. Conclusion
**The engine DOES start processing commands but stops after ~4 commands!**

## Hypothesis
The engine may be:
1. **Hitting an error** and returning to IDLE
2. **Waiting for a condition** that never occurs
3. **Missing a completion signal** from dispatcher/compute engine

## Next Steps
1. Check `o_last_opcode` to see what command was last processed
2. Check dispatcher/compute engine done signals
3. Look for stuck WAIT commands
4. Check if there's a command that causes the engine to halt

