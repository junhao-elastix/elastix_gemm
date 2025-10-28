# Compute Engine Archive - October 9, 2025

## Archive Summary

This directory contains archived versions of compute_engine modules that were created during development but are no longer used in the active build.

**Active File**: `../compute_engine.sv` (50,373 bytes) - Integer-only GFP implementation with V-loop support

## Archived Files

### compute_engine_BACKUP.sv (2,627 bytes)
- **Purpose**: Simple working stub for CSR bridge testing
- **Features**: Minimal FSM with IDLE/ACTIVE/DONE states
- **Status**: Early development stub, replaced by full implementation
- **Date**: October 8, 2025

### compute_engine_sim_only.sv (37,531 bytes)  
- **Purpose**: Simulation-only version with real arithmetic for validation
- **Features**: 
  - V-loop support with real number accumulation
  - Parallel group-based dot product (4 groups x 32 elements)
  - Hardware-compatible GFP arithmetic using real numbers
  - FP16 output with overflow clamping
- **Status**: Simulation reference, replaced by integer-only hardware version
- **Date**: October 6, 2025

### compute_engine_fix.sv (2,983 bytes)
- **Purpose**: Documentation of timing fix for result write issue
- **Problem**: Results never written because v_idx reset on same clock edge as result write check
- **Solution**: Use result_ready_reg flag to fix timing issue
- **Status**: Fix documentation, solution implemented in main compute_engine.sv
- **Date**: October 9, 2025

### compute_engine_readback.sv (9,700 bytes)
- **Purpose**: BRAM readback test mode for dispatcher validation
- **Features**:
  - Reads sequential BRAM addresses from dispatcher_bram
  - Outputs 256-bit BRAM data as FP24 stream
  - Allows host to verify dispatcher BRAM contents via result DMA
- **Status**: Temporary test stub, functionality not needed in production
- **Date**: October 8, 2025

## Development History

1. **compute_engine_BACKUP.sv**: Initial stub for basic functionality testing
2. **compute_engine_sim_only.sv**: Full simulation implementation with real arithmetic
3. **compute_engine_readback.sv**: Test mode for BRAM readback validation  
4. **compute_engine_fix.sv**: Documentation of critical timing fix
5. **compute_engine.sv**: Final integer-only hardware implementation

## Key Differences

| Feature | BACKUP | sim_only | readback | fix | Active |
|---------|--------|----------|----------|-----|--------|
| Arithmetic | None | Real | None | N/A | Integer-only GFP |
| V-loop | No | Yes | No | N/A | Yes |
| BRAM Read | No | Yes | Yes | N/A | Yes |
| Result Write | No | Yes | Yes | N/A | Yes (fixed) |
| Hardware Ready | No | No | No | N/A | Yes |

## Archive Date
October 9, 2025 14:18:31 PDT

## Notes
- All archived files preserved for reference and potential future use
- Main compute_engine.sv contains all necessary functionality for production
- Integer-only implementation chosen for hardware compatibility and timing closure






