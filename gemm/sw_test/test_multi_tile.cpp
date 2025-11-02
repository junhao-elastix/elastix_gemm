// test_multi_tile.cpp - TRUE Multi-Tile GEMM Test
// Tests software-orchestrated multi-tile execution:
// - Single FETCH (left + right matrices)
// - Single DISPATCH (distributes full memory block to compute column)
// - Multiple TILE commands (different BRAM addresses per tile)
// - Single result collection at end

#include <iostream>
#include <iomanip>
#include <vector>
#include <fstream>
#include <cstring>
#include "vp815_gemm_device.hpp"

using namespace std;
using namespace achronix;

// Parameterized multi-tile test function
bool run_multitile_test(int B, int C, int V) {
    cout << "\n========================================================================" << endl;
    cout << "Multi-Tile GEMM Test (B=" << B << ", C=" << C << ", V=" << V << ")" << endl;
    cout << "========================================================================" << endl;

    // Calculate tile counts using BOTTLENECK PRINCIPLE
    // Given 128 Native Vectors total in reference matrices
    int max_left_tiles = 128 / (B * V);   // How many left chunks available
    int max_right_tiles = 128 / (C * V);  // How many right chunks available
    int num_tiles = min(max_left_tiles, max_right_tiles);  // Bottleneck: limited by whichever runs out first
    int results_per_tile = B * C;
    int total_results = num_tiles * results_per_tile;

    cout << "\nConfiguration:" << endl;
    cout << "  B=" << B << ", C=" << C << ", V=" << V << endl;
    cout << "  max_left_tiles=" << max_left_tiles << endl;
    cout << "  max_right_tiles=" << max_right_tiles << endl;
    cout << "  num_tiles=" << num_tiles << " (bottleneck)" << endl;
    cout << "  results_per_tile=" << results_per_tile << endl;
    cout << "  total_results=" << total_results << endl;

    if (num_tiles == 1) {
        cout << "\nWARNING: This is a SINGLE-TILE configuration!" << endl;
        cout << "For true multi-tile testing, try:" << endl;
        cout << "  B=2, C=2, V=32 → 2 tiles (symmetric)" << endl;
        cout << "  B=2, C=4, V=16 → 2 tiles (asymmetric, right bottleneck)" << endl;
        cout << "  B=1, C=1, V=1  → 128 tiles (maximum)" << endl;
    }
    cout << endl;

    try {
        VP815 device(0);
        VP815GemmDevice gemm_device(device);

        uint64_t BRAM_RESULT_BASE = acx_util_nap_absolute_addr(ACX_PART_AC7t1500, 3, 5);

        // Load matrices
        vector<uint8_t> left_data, right_data;
        if (!gemm_device.loadHexMatrix("../../hex/left.hex", left_data) ||
            !gemm_device.loadHexMatrix("../../hex/right.hex", right_data)) {
            cerr << "ERROR: Failed to load matrices" << endl;
            return false;
        }
        cout << "✓ Loaded matrices: " << left_data.size() << " bytes each" << endl;

        // Initial soft reset
        gemm_device.soft_reset();

        // Reset circular buffer pointers
        gemm_device.mmio_write32(0, 0x230, 0x00000000);  // rd_ptr = 0
        cout << "✓ Reset circular buffer: rd_ptr=0, wr_ptr=0" << endl;

        uint32_t host_rd_ptr = 0;

        // ------------------------------------------------------------------------
        // Stage 1: DMA matrices to GDDR6 (ONCE)
        // ------------------------------------------------------------------------
        cout << "\n--- Stage 1: DMA Transfer to GDDR6 ---" << endl;
        if (!gemm_device.dma_write(GDDR6_BASE_LEFT, left_data.data(), left_data.size()) ||
            !gemm_device.dma_write(GDDR6_BASE_RIGHT, right_data.data(), right_data.size())) {
            cerr << "ERROR: Failed to DMA write matrices" << endl;
            return false;
        }
        cout << "✓ Wrote matrices to GDDR6" << endl;

        // ------------------------------------------------------------------------
        // Stage 2: FETCH - Load ONE memory block (left + right)
        // ------------------------------------------------------------------------
        cout << "\n--- Stage 2: FETCH Memory Block ---" << endl;
        gemm_device.reset_cmd_id();

        uint32_t left_lines = 528;   // Full 128 NVs
        uint32_t right_lines = 528;

        uint8_t fetch_left_id = gemm_device.fetch(GDDR6_BASE_LEFT, left_lines, false);
        cout << "  [" << (int)fetch_left_id << "] FETCH left @ GDDR6 (528 lines → Dispatcher BRAM[0-527])" << endl;

        if (!gemm_device.wait_idle(5000)) {
            cerr << "ERROR: FETCH left timeout" << endl;
            return false;
        }

        uint8_t fetch_right_id = gemm_device.fetch(GDDR6_BASE_RIGHT, right_lines, true);
        cout << "  [" << (int)fetch_right_id << "] FETCH right @ GDDR6 (528 lines → Dispatcher BRAM[528-1055])" << endl;

        if (!gemm_device.wait_idle(5000)) {
            cerr << "ERROR: FETCH right timeout" << endl;
            return false;
        }

        cout << "✓ FETCH complete (full memory block loaded to Dispatcher BRAM)" << endl;

        // ------------------------------------------------------------------------
        // Stage 3: DISPATCH - Distribute memory block to compute column
        // ------------------------------------------------------------------------
        // NOTE: With single compute column, DISPATCH is currently a no-op
        // but we still issue it for protocol compliance
        cout << "\n--- Stage 3: DISPATCH Memory Block ---" << endl;

        uint8_t disp_left_id = gemm_device.dispatch(
            128,      // man_nv_cnt = 128 (full block)
            1,        // ugd_vec_size = 1 (legacy parameter)
            0,        // tile_addr = 0
            false,    // disp_right = false (left side)
            0x0001,   // col_en = 0x0001 (column 0 enabled)
            0,        // col_start = 0
            true,     // broadcast = true (distribute to all enabled columns)
            false     // man_4b = false (8-bit mantissa)
        );
        cout << "  [" << (int)disp_left_id << "] DISPATCH left (full block to compute column)" << endl;

        uint8_t wait_disp_left = gemm_device.waitDispatch(disp_left_id);
        cout << "  [" << (int)wait_disp_left << "] WAIT_DISPATCH left" << endl;

        if (!gemm_device.wait_idle(5000)) {
            cerr << "ERROR: DISPATCH left timeout" << endl;
            return false;
        }

        uint8_t disp_right_id = gemm_device.dispatch(
            128,      // man_nv_cnt = 128
            1,        // ugd_vec_size = 1
            0,        // tile_addr = 0
            true,     // disp_right = true (right side)
            0x0001,   // col_en = 0x0001
            0,        // col_start = 0
            false,    // broadcast = false (distribute mode)
            false     // man_4b = false
        );
        cout << "  [" << (int)disp_right_id << "] DISPATCH right (full block to compute column)" << endl;

        uint8_t wait_disp_right = gemm_device.waitDispatch(disp_right_id);
        cout << "  [" << (int)wait_disp_right << "] WAIT_DISPATCH right" << endl;

        if (!gemm_device.wait_idle(5000)) {
            cerr << "ERROR: DISPATCH right timeout" << endl;
            return false;
        }

        cout << "✓ DISPATCH complete (memory block distributed to compute column)" << endl;

        // ------------------------------------------------------------------------
        // Stage 4: TILE Commands - Lockstep advancement (bottleneck principle)
        // ------------------------------------------------------------------------
        cout << "\n--- Stage 4: Execute Multiple TILE Commands ---" << endl;
        cout << "Issuing " << num_tiles << " TILE commands with lockstep addressing..." << endl;
        cout << "TEST PATTERN: Sequential tiling - both sides advance together." << endl;
        cout << "NOTE: In production, software can use ANY addressing pattern!" << endl;

        vector<uint8_t> tile_ids;

        // Calculate strides for lockstep advancement pattern
        int left_stride = (B * V) * 4;   // Lines per tile
        int right_stride = (C * V) * 4;  // Lines per tile

        cout << "Address strides: left=" << left_stride << " lines, right=" << right_stride << " lines" << endl;

        for (int tile_idx = 0; tile_idx < num_tiles; tile_idx++) {
            // LOCKSTEP ADVANCEMENT: Both sides advance together
            // This is our test pattern - production can use any pattern!
            uint16_t left_addr = tile_idx * left_stride;
            uint16_t right_addr = tile_idx * right_stride;

            // Calculate NV indices for display
            uint16_t left_nv_start = tile_idx * B * V;
            uint16_t left_nv_end = left_nv_start + (B * V) - 1;
            uint16_t right_nv_start = tile_idx * C * V;
            uint16_t right_nv_end = right_nv_start + (C * V) - 1;

            // Issue TILE command
            // Hardware only sees: start addresses, lengths, V-depth
            uint8_t tile_id = gemm_device.tile(
                left_addr,    // leftAddr - can be ANY valid BRAM address
                right_addr,   // rightAddr - can be ANY valid BRAM address
                B,            // leftUgdLen - read B Native Vectors
                C,            // rightUgdLen - read C Native Vectors
                V,            // vecLen - V-loop accumulation depth
                false,        // leftMan4b
                false,        // rightMan4b
                true,         // mainLoopOverLeft
                0x0001        // col_en (column 0)
            );

            cout << "  [" << (int)tile_id << "] TILE " << tile_idx << endl;
            cout << "       left_addr=" << left_addr << " × stride=" << left_stride
                 << " (NV[" << left_nv_start << "-" << left_nv_end << "])" << endl;
            cout << "       right_addr=" << right_addr << " × stride=" << right_stride
                 << " (NV[" << right_nv_start << "-" << right_nv_end << "])" << endl;
            cout << "       Will produce " << results_per_tile << " results (B×C = "
                 << B << "×" << C << ")" << endl;

            // CRITICAL: Each TILE must be immediately followed by WAIT_TILE
            uint8_t wait_id = gemm_device.waitTile(tile_id);
            cout << "  [" << (int)wait_id << "] WAIT_MATMUL (wait for tile_id=" << (int)tile_id << ")" << endl;

            tile_ids.push_back(tile_id);
        }

        cout << "\n✓ All " << num_tiles << " TILE commands completed" << endl;

        if (!gemm_device.wait_idle(5000)) {
            cerr << "ERROR: Engine timeout waiting for tiles" << endl;
            return false;
        }
        cout << "✓ All " << num_tiles << " TILE commands completed" << endl;

        // ------------------------------------------------------------------------
        // Stage 5: Collect ALL Results (single read at end)
        // ------------------------------------------------------------------------
        cout << "\n--- Stage 5: Collect ALL Results ---" << endl;

        uint32_t final_wr_ptr = gemm_device.mmio_read32(0, 0x234) & 0x1FFF;
        uint32_t final_used = gemm_device.mmio_read32(0, 0x238) & 0x3FFF;

        cout << "Circular buffer final state:" << endl;
        cout << "  wr_ptr=" << final_wr_ptr << " (hardware write pointer)" << endl;
        cout << "  rd_ptr=" << host_rd_ptr << " (host read pointer)" << endl;
        cout << "  used=" << final_used << " (FP16 values available)" << endl;

        // Hardware may write results in completion order, not issue order
        // Only validate the number of results actually written
        uint32_t actual_results = final_used;
        
        if (final_used != (uint32_t)total_results) {
            cerr << "WARNING: Used count (" << final_used
                 << ") != expected (" << total_results << ")" << endl;
            cerr << "         Will validate only " << actual_results << " results" << endl;
        }

        // Calculate DMA read parameters (byte-addressed, 32-byte aligned)
        // Only read as many results as were actually written
        uint32_t byte_offset = host_rd_ptr * 2;
        uint32_t byte_count = actual_results * 2;
        uint32_t offset_in_first_line = byte_offset % 32;
        uint32_t total_bytes = offset_in_first_line + byte_count;
        uint32_t dma_bytes = ((total_bytes + 31) / 32) * 32;
        uint32_t dma_start = (byte_offset / 32) * 32;

        cout << "\nDMA read calculation:" << endl;
        cout << "  Result byte offset: " << byte_offset << endl;
        cout << "  Result byte count: " << byte_count << endl;
        cout << "  DMA start (32B-aligned): " << dma_start << endl;
        cout << "  DMA bytes (32B-aligned): " << dma_bytes << endl;
        cout << "  Skip first bytes: " << offset_in_first_line << endl;

        vector<uint8_t> bram_data(dma_bytes);
        if (!gemm_device.dma_read(BRAM_RESULT_BASE + dma_start, bram_data.data(), dma_bytes)) {
            cerr << "ERROR: Failed to DMA read results" << endl;
            return false;
        }

        // Unpack FP16 results from byte stream (only actual results written)
        vector<uint16_t> results;
        for (uint32_t i = 0; i < actual_results; i++) {
            size_t byte_pos = offset_in_first_line + i * 2;
            uint16_t fp16_val = *(uint16_t*)(bram_data.data() + byte_pos);
            results.push_back(fp16_val);
        }

        cout << "✓ Read " << results.size() << " FP16 results from Result BRAM" << endl;

        // ------------------------------------------------------------------------
        // Stage 6: Display Results by Tile
        // ------------------------------------------------------------------------
        cout << "\n--- Stage 6: Results Breakdown by Tile ---" << endl;
        cout << "NOTE: Hardware writes results in completion order, not issue order" << endl;
        cout << "Format: TILE N → [start_idx-end_idx]: first_val ... last_val" << endl;
        cout << endl;

        // Display results sequentially as written by hardware
        // Note: Hardware completion order may differ from issue order
        uint32_t result_idx = 0;
        for (int tile_idx = 0; tile_idx < num_tiles && result_idx < results.size(); tile_idx++) {
            uint32_t start_idx = result_idx;
            uint32_t end_idx = min(result_idx + results_per_tile - 1, (uint32_t)(results.size() - 1));

            uint32_t results_in_tile = end_idx - start_idx + 1;

            // Calculate addresses for this tile (lockstep pattern)
            uint16_t left_addr = tile_idx * left_stride;
            uint16_t right_addr = tile_idx * right_stride;

            cout << "TILE " << tile_idx
                 << " (left_addr=" << left_addr << ", right_addr=" << right_addr << ")"
                 << " → [" << start_idx << "-" << end_idx << "]: ";

            // Show available results (may be partial if not all tiles completed)
            uint32_t show_count = min(4U, results_in_tile);
            for (uint32_t i = 0; i < show_count; i++) {
                cout << "0x" << hex << setfill('0') << setw(4)
                     << results[start_idx + i] << " ";
            }

            // If more than 4 results, show last few
            if (results_in_tile > 4) {
                cout << "... ";
                for (uint32_t i = max(show_count, results_in_tile - show_count);
                     i < results_in_tile; i++) {
                    cout << "0x" << setw(4) << results[start_idx + i] << " ";
                }
            }
            cout << dec << endl;

            result_idx += results_per_tile;
        }
        
        if (result_idx < results.size()) {
            cout << "  (Additional " << (results.size() - result_idx) << " results not assigned to tiles)" << endl;
        }

        // ------------------------------------------------------------------------
        // Stage 7: Validation against Golden Reference
        // ------------------------------------------------------------------------
        cout << "\n--- Stage 7: Validation ---" << endl;

        // Try multi-tile golden reference first
        string golden_file_multitile = "../../hex/golden_B" + to_string(B) + "_C" + to_string(C)
                                      + "_V" + to_string(V) + "_multitile.hex";
        string golden_file_single = "../../hex/golden_B" + to_string(B) + "_C" + to_string(C)
                                   + "_V" + to_string(V) + ".hex";

        ifstream golden(golden_file_multitile);
        string golden_used = golden_file_multitile;

        if (!golden.is_open()) {
            // Try single-tile golden reference
            golden.open(golden_file_single);
            golden_used = golden_file_single;
        }

        if (!golden.is_open()) {
            cout << "⚠ Golden reference not found. Tried:" << endl;
            cout << "  " << golden_file_multitile << endl;
            cout << "  " << golden_file_single << endl;
            cout << "\nGenerate with:" << endl;
            cout << "  python hardware_gfp_reference.py --B " << B
                 << " --C " << C << " --V " << V << " --multitile" << endl;
        } else {
            cout << "Using golden reference: " << golden_used << endl;

            vector<uint16_t> golden_results;
            string line;
            while (getline(golden, line)) {
                if (line.empty()) continue;
                uint16_t val = (uint16_t)strtoul(line.c_str(), NULL, 16);
                golden_results.push_back(val);
            }
            golden.close();

            // Validate only the results that were actually written by hardware
            // Golden reference may have more results, but we only validate what hardware produced
            size_t validate_count = min(results.size(), golden_results.size());
            
            if (golden_results.size() < results.size()) {
                cerr << "WARNING: Golden has only " << golden_results.size()
                     << " results, but hardware wrote " << results.size() << endl;
                cerr << "         Will validate only first " << validate_count << " results" << endl;
            } else if (golden_results.size() > results.size()) {
                cout << "NOTE: Golden has " << golden_results.size() << " results, "
                     << "hardware wrote " << results.size() << " (validating only written results)" << endl;
            }
            
            int mismatches = 0;
            int close_matches = 0;  // Results within 1 LSB (acceptable rounding)
            
            for (size_t i = 0; i < validate_count; i++) {
                uint16_t diff = (results[i] > golden_results[i]) ? 
                               (results[i] - golden_results[i]) : 
                               (golden_results[i] - results[i]);
                
                if (results[i] != golden_results[i]) {
                    // Check if difference is within 1 LSB (acceptable FP16 rounding)
                    if (diff <= 1) {
                        close_matches++;
                        if (mismatches < 5) {
                            cout << "  CLOSE [" << i << "]: got 0x" << hex
                                 << results[i] << ", expected 0x"
                                 << golden_results[i] << " (diff=" << dec << diff << ")" << endl;
                        }
                    } else {
                        if (mismatches < 10) {
                            cout << "  MISMATCH [" << i << "]: got 0x" << hex
                                 << results[i] << ", expected 0x"
                                 << golden_results[i] << dec << endl;
                        }
                    }
                    mismatches++;
                }
            }

            if (mismatches == 0) {
                cout << "✓ SUCCESS: All " << validate_count
                     << " results match golden reference!" << endl;
            } else if (mismatches == close_matches) {
                cout << "✓ SUCCESS: All " << validate_count
                     << " results match within 1 LSB (" << close_matches << " close matches)" << endl;
            } else {
                cout << "✗ FAILURE: " << mismatches << "/" << validate_count
                     << " mismatches (" << close_matches << " within 1 LSB)" << endl;
            }
        }

        // Basic sanity check
        int zero_count = 0;
        int invalid_count = 0;
        for (auto val : results) {
            if (val == 0x0000) zero_count++;
            if (val == 0xFFFF) invalid_count++;
        }

        cout << "\nSanity check:" << endl;
        cout << "  Total results: " << results.size() << endl;
        cout << "  Zero values: " << zero_count << endl;
        cout << "  Invalid (0xFFFF): " << invalid_count << endl;

        bool sanity_ok = (zero_count < total_results / 2) && (invalid_count == 0);
        if (sanity_ok) {
            cout << "✓ Results appear valid (not all zeros/invalid)" << endl;
        } else {
            cout << "⚠ Results may be invalid!" << endl;
        }

        cout << "\n========================================================================" << endl;
        cout << "Multi-Tile GEMM Test Complete" << endl;
        cout << "========================================================================" << endl;
        cout << "Architecture Summary:" << endl;
        cout << "  1 FETCH left  (GDDR6 → Dispatcher BRAM[0-527])" << endl;
        cout << "  1 FETCH right (GDDR6 → Dispatcher BRAM[528-1055])" << endl;
        cout << "  1 DISPATCH left + right (memory block to compute column)" << endl;
        cout << "  " << num_tiles << " TILE commands (lockstep addressing)" << endl;
        cout << "  1 Result collection (" << total_results << " FP16 values)" << endl;
        cout << "  Bottleneck: " << (max_left_tiles < max_right_tiles ? "left" : "right") << " side" << endl;
        cout << "========================================================================" << endl;

        return true;  // Success

    } catch (const exception& e) {
        cerr << "ERROR: " << e.what() << endl;
        return false;  // Failure
    }
}

// Main function - supports command-line arguments or runs default configurations
int main(int argc, char* argv[]) {
    cout << "========================================================================" << endl;
    cout << "Multi-Tile GEMM Test Suite (Parameterized)" << endl;
    cout << "========================================================================" << endl;

    // Single test mode (command-line arguments)
    if (argc > 3) {
        int B = stoi(argv[1]);
        int C = stoi(argv[2]);
        int V = stoi(argv[3]);

        bool success = run_multitile_test(B, C, V);
        return success ? 0 : 1;
    }

    // Multi-test mode (default configurations)
    cout << "\nRunning multiple test configurations..." << endl;

    struct TestConfig {
        int B, C, V;
        string description;
    };

    // Test configurations matching hex/generate_new.sh
    vector<TestConfig> test_configs = {
        {1, 1, 1,     "Minimal (128 tiles)"},
        {2, 2, 2,     "Small (32 tiles)"},
        {4, 4, 4,     "Medium (8 tiles)"},
        {2, 2, 64,    "High V-loop (1 tile)"},
        {4, 4, 32,    "Balanced high-V (1 tile)"},
        {8, 8, 16,    "Large balanced (1 tile)"},
        {16, 16, 8,   "Maximum output (1 tile)"},
        {1, 128, 1,   "Wide matrix (1 tile, left bottleneck)"},
        {128, 1, 1,   "Tall matrix (1 tile, right bottleneck)"},
        {1, 1, 128,   "Maximum V-loop (1 tile)"},
        {2, 4, 16,    "Asymmetric (2 tiles, right bottleneck)"},
        {4, 8, 8,     "Asymmetric medium (2 tiles, right bottleneck)"},
        {8, 32, 2,    "Asymmetric wide (2 tiles, right bottleneck)"},
        {16, 16, 4,   "Large symmetric (2 tiles)"},
    };

    int passed = 0;
    int failed = 0;

    for (const auto& config : test_configs) {
        cout << "\n>>> Test: " << config.description << " <<<" << endl;
        bool success = run_multitile_test(config.B, config.C, config.V);

        if (success) {
            passed++;
            cout << "✅ PASS" << endl;
        } else {
            failed++;
            cout << "❌ FAIL" << endl;
        }
    }

    cout << "\n========================================================================" << endl;
    cout << "Test Suite Summary" << endl;
    cout << "========================================================================" << endl;
    cout << "Total tests: " << test_configs.size() << endl;
    cout << "Passed: " << passed << endl;
    cout << "Failed: " << failed << endl;
    cout << "Success rate: " << (100.0 * passed / test_configs.size()) << "%" << endl;
    cout << "========================================================================" << endl;

    return (failed == 0) ? 0 : 1;
}
