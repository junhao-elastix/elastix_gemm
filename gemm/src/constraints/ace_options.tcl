set_project_option autoselect_top_module 0
set_project_option bitstream_encryption_aes_key_file ./../mem_init_files/aes_key.txt
set_project_option bitstream_output_flash 1
set_project_option bitstream_page0_dummy_cycle_4byte 0A
set_project_option bitstream_page0_num_devices 4
set_project_option bitstream_page0_vendor 1
set_project_option flow_mode normal
set_project_option hdl_defines ACX_USE_SNAPSHOT=1
set_impl_option pnr_optimize_corners 1
set_impl_option report_unconstrained_timing_paths 1
set_impl_option syn_default_frequency 500
set_project_option top_module elastix_gemm_top

# # -------------------------------------------------------------------------
# # BUILD TIME OPTIMIZATIONS - Aggressive P&R settings for faster builds
# # -------------------------------------------------------------------------

# # Reduce P&R effort for faster builds (compromise: speed vs. optimal results) 
# set_impl_option pnr_effort_level medium

# # Enable aggressive placement strategy for faster convergence
# set_impl_option pnr_placement_effort medium

# # Reduce routing iterations to speed up P&R
# set_impl_option pnr_routing_iterations 3

# # Set timing closure limits to prevent excessive optimization
# set_impl_option pnr_timing_driven_placement 1
# set_impl_option pnr_timing_optimization_iterations 2

# # Enable parallel processing for faster builds
# set_impl_option pnr_parallel_jobs 4

# # Reduce post-route optimization for faster bitstream generation
# set_impl_option pnr_post_route_opt_effort medium

# # Skip non-critical optimization passes
# set_impl_option pnr_run_detailed_timing_analysis 0
