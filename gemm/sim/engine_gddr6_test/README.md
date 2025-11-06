# engine_gddr6_test - DEPRECATED

**Status**: ⚠️ **OBSOLETE** - This simulation directory has been deprecated.

**Date**: Thu Nov 6 2025

## Deprecation Notice

This directory is **no longer maintained** and has been replaced by `vector_system_test`.

### Why Deprecated?

1. **Obsolete Memory Model**: Uses `tb_memory_model.sv` (behavioral model) instead of the 100% compliant `tb_memory_model_realistic.sv`
2. **Legacy Interface**: Uses CSR register interface instead of modern FIFO interface
3. **Replaced**: Superseded by `vector_system_test` which has:
   - ✅ 100% compliant memory model (matches reference design)
   - ✅ Modern FIFO interface
   - ✅ All 10 tests passing
   - ✅ Cleaner, more maintainable architecture

### Current Standard

**Use Instead**: `/home/dev/Dev/elastix_gemm/gemm/sim/vector_system_test/`

```bash
cd /home/dev/Dev/elastix_gemm/gemm/sim/vector_system_test
make clean && make run
```

**Memory Model**: `/home/dev/Dev/elastix_gemm/gemm/src/tb/tb_memory_model_realistic.sv`

### Archived Files

Original files have been moved to `archive_nov06_deprecated/` for historical reference.

**Do not use this directory for new development or testing.**

