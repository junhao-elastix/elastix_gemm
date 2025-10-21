# RTL Archive

Unused or obsolete RTL modules moved here to keep the main src/rtl/ directory clean.

## Archived Files

### csr_cmd_bridge.sv
- **Date Archived**: Mon Oct 6 23:20:00 PDT 2025
- **Reason**: Replaced with direct CSR→FIFO connection pattern from engine_sim
- **Status**: Permanently stuck busy bug - architectural issue with CSR bridge FSM
- **Replacement**: Direct edge-triggered push logic in engine_wrapper.sv (lines 146-266)
- **Reference**: Proven pattern from engine_sim/src/tb/tb_vector_top_ms2.sv

### gddr6_to_bram_processor_external_nap.sv
- **Date Archived**: Mon Oct 6 22:55:00 PDT 2025
- **Reason**: Alternative G2B processor version not used in current build
- **Status**: Superseded by gddr6_to_bram_processor.sv and engine_wrapper.sv
- **Note**: G2B processor itself is now only used for channels 1-7; Channel 0 uses MS2.0 engine

### gddr6_to_bram_processor.sv
- **Date Archived**: Mon Oct 6 11:55:26 PM PDT 2025
- **Reason**: Legacy G2B processor replaced by MS2.0 GEMM engine on Channel 0
- **Status**: ARCHIVED - No longer used in GEMM-focused design
- **Note**: Contains +42 processing functionality that has been removed from project

### g2b_data_processor.sv
- **Date Archived**: Mon Oct 6 11:55:26 PM PDT 2025
- **Reason**: Data processing pipeline for legacy +42 functionality removed
- **Status**: ARCHIVED - No longer needed with GEMM engine focus
- **Note**: Configurable processing modes (passthrough, add, multiply, etc.) no longer used

### nap_initiator_readonly_wrapper.sv
- **Date Archived**: Tue Oct 7 12:14:00 AM PDT 2025
- **Reason**: Read-only NAP wrapper optimization never used in current design
- **Status**: ARCHIVED - Unused module with specialized read-only optimization
- **Note**: Designed for modules that only read from GDDR6, but current design uses standard wrapper

### nap_initiator_wrapper_fixed.sv
- **Date Archived**: Tue Oct 7 12:14:00 AM PDT 2025
- **Reason**: Interface direction fix wrapper never adopted in current design
- **Status**: ARCHIVED - Unused alternative to standard NAP wrapper
- **Note**: Attempted fix for AXI interface modport confusion, but standard wrapper works fine

### bram_vector_processor.sv
- **Date Archived**: Tue Oct 7 12:14:00 AM PDT 2025
- **Reason**: BRAM vector processor functionality removed from GEMM-focused design
- **Status**: ARCHIVED - No longer used, replaced by MS2.0 GEMM engine
- **Note**: FSM-based vector addition processor (128 int16 values), not instantiated in current design

### axi_pkt_gen.sv
- **Date Archived**: Tue Oct 7 12:20:23 AM PDT 2025
- **Reason**: Packet generator for GDDR6 channels 1-7 validation, disabled for GEMM focus
- **Status**: ARCHIVED - Only used by commented-out packet generator channels
- **Note**: AXI4 packet generation with configurable burst patterns and data patterns

### axi_pkt_chk.sv  
- **Date Archived**: Tue Oct 7 12:20:23 AM PDT 2025
- **Reason**: Packet checker for GDDR6 channels 1-7 validation, disabled for GEMM focus
- **Status**: ARCHIVED - Only used by commented-out packet generator channels
- **Note**: AXI4 packet validation with error detection and performance monitoring

### axi_mem_pkt_gen_chk_channel.sv
- **Date Archived**: Tue Oct 7 12:20:23 AM PDT 2025
- **Reason**: Memory channel test infrastructure for GDDR6 channels 1-7, disabled for GEMM focus
- **Status**: ARCHIVED - Only used by commented-out packet generator channels
- **Note**: Complete memory test channel combining packet generation and checking

### axi_bw_monitor.sv
- **Date Archived**: Tue Oct 7 12:20:23 AM PDT 2025
- **Reason**: Bandwidth monitoring for packet generators, unused with channels 1-7 disabled
- **Status**: ARCHIVED - Only used by packet generator infrastructure
- **Note**: AXI4 bandwidth measurement and reporting for performance analysis

### axi_latency_monitor.sv
- **Date Archived**: Tue Oct 7 12:20:23 AM PDT 2025
- **Reason**: Latency monitoring for packet generators, unused with channels 1-7 disabled
- **Status**: ARCHIVED - Only used by packet generator infrastructure
- **Note**: AXI4 latency measurement with min/max/average tracking

### axi_performance_monitor.sv
- **Date Archived**: Tue Oct 7 12:20:23 AM PDT 2025
- **Reason**: Performance monitoring for packet generators, unused with channels 1-7 disabled
- **Status**: ARCHIVED - Only used by packet generator infrastructure
- **Note**: Combined performance monitoring wrapper for bandwidth and latency

### random_seq_engine.sv
- **Date Archived**: Tue Oct 7 12:20:23 AM PDT 2025
- **Reason**: Random sequence generation for packet generators, unused with channels 1-7 disabled
- **Status**: ARCHIVED - Only used by packet generator infrastructure
- **Note**: Pseudo-random sequence generator for test pattern creation

### compute_engine.sv
- **Date Archived**: Fri Oct 10 12:55:44 PDT 2025
- **Reason**: Monolithic compute engine replaced by modular MS2.0 design with dual BRAM interface
- **Status**: ARCHIVED - Replaced by compute_engine_modular.sv for ~42% performance improvement
- **Note**: Original single BRAM interface design (~998 lines), superseded by hierarchical modular design with gfp8_bcv_controller
- **Replacement**: compute_engine_modular.sv (240 lines, dual BRAM reads, cleaner architecture)

### compute_engine_monolithic.sv.backup
- **Date Archived**: Fri Oct 10 12:55:44 PDT 2025
- **Reason**: Development backup file for monolithic compute engine
- **Status**: ARCHIVED - Historical backup of development iterations
- **Note**: Backup copy created during refactoring to modular design

### compute_engine_with_bypass.sv.backup
- **Date Archived**: Fri Oct 10 12:55:44 PDT 2025
- **Reason**: Development backup with bypass mode experimentation
- **Status**: ARCHIVED - Historical backup of development iterations
- **Note**: Experimental bypass mode for CE, not adopted in final design

### compute_engine.sv.backup
- **Date Archived**: Fri Oct 10 12:55:44 PDT 2025
- **Reason**: Development backup file
- **Status**: ARCHIVED - Historical backup of development iterations
- **Note**: Additional backup copy created during development

### dispatcher_bram_single_port.sv.backup
- **Date Archived**: Fri Oct 10 12:55:44 PDT 2025
- **Reason**: Single-port dispatcher BRAM superseded by dual-read architecture
- **Status**: ARCHIVED - Replaced by dispatcher_bram_dual_read.sv
- **Note**: Original single-port design, replaced for MS2.0 parallel left/right matrix reads

### dispatcher_control.sv.ms2_dual
- **Date Archived**: Fri Oct 10 12:55:44 PDT 2025
- **Reason**: Alternative dispatcher control version, MS2.0 features integrated into main file
- **Status**: ARCHIVED - MS2.0 dual BRAM support integrated into dispatcher_control.sv
- **Note**: Development iteration during MS2.0 migration, features now in main file

### vector_top_ms2.sv
- **Date Archived**: Fri Oct 10 12:55:44 PDT 2025
- **Reason**: MS2.0 reference integration example, not used in GEMM project
- **Status**: ARCHIVED - Reference module from compute_engine_w8a8 project
- **Note**: Example top-level integration for standalone MS2.0 engine, GEMM uses engine_wrapper.sv instead
