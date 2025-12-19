// test_linear.cpp - Linear Layer Test
//
// Tests a large linear layer operation with:
// - 16 right matrix fetch+dispatch operations (C4V32 each, spread across columns)
// - 1 left matrix fetch+dispatch (B4V32, broadcast)
// - Single TILE command: B4 C64 V32
// - Output: 4 x 64 = 256 FP16 results
//
// Uses individual hex files:
// - left_0.hex: Left matrix (activations)
// - right_0.hex through right_15.hex: 16 different right matrices (weights)
// - golden_B4_C4_V32_0.hex through golden_B4_C4_V32_15.hex: Expected results

#include <iostream>
#include <iomanip>
#include <fstream>
#include <sstream>
#include <cstring>
#include <cstdlib>
#include <chrono>
#include <cmath>
#include <vector>
#include <unistd.h>
#include "vp815_gemm_device.hpp"

using namespace std;
using namespace achronix;

// Configuration
static const int B = 4;      // Output rows (batch size)
static const int C = 64;     // Output columns
static const int V = 32;     // Inner dimension multiplier

// Derived constants
static const int LEFT_NVS = B * V;       // 4 * 32 = 128 NVs for left matrix
static const int RIGHT_NVS_PER_DISPATCH = 4 * V;  // C4V32 = 128 NVs per dispatch
static const int NUM_RIGHT_DISPATCHES = 16;  // 16 dispatches for C=64
static const int TOTAL_RESULTS = B * C;  // 4 * 64 = 256 results
static const int RESULTS_PER_DISPATCH = B * 4;  // 4 batches * 4 cols = 16 results per golden file

// GDDR6 layout: each right matrix gets its own region
// Right matrix size: 528 lines * 32 bytes = 16896 bytes = 0x4200
static const uint64_t RIGHT_MATRIX_SIZE = 528 * 32;

// ============================================================================
// Helper: FP16 to Float Conversion
// ============================================================================

float fp16ToFloat(uint16_t fp16_val) {
    uint16_t sign = (fp16_val >> 15) & 1;
    uint16_t exp = (fp16_val >> 10) & 0x1F;
    uint16_t frac = fp16_val & 0x3FF;

    if (exp == 0) {
        if (frac == 0) {
            return sign ? -0.0f : 0.0f;
        }
        // Subnormal
        return (sign ? -1.0f : 1.0f) * (frac / 1024.0f) * powf(2.0f, -14.0f);
    } else if (exp == 31) {
        return (frac == 0) ? (sign ? -INFINITY : INFINITY) : NAN;
    } else {
        // Normal
        return (sign ? -1.0f : 1.0f) * (1.0f + frac / 1024.0f) * powf(2.0f, (int)exp - 15);
    }
}

static inline int ceil_div16(int x) {
    return (x + 15) / 16;
}

// ============================================================================
// Main Test
// ============================================================================

int main(int argc, char* argv[]) {
    cout << "========================================================================" << endl;
    cout << "Linear Layer Test: B" << B << " C" << C << " V" << V << endl;
    cout << "========================================================================" << endl;
    cout << "Configuration:" << endl;
    cout << "  Left matrix:  B*V = " << B << " x " << V << " = " << LEFT_NVS << " NVs (broadcast)" << endl;
    cout << "  Right matrix: C*V = " << C << " x " << V << " = " << (C * V) << " NVs (" << NUM_RIGHT_DISPATCHES << " dispatches)" << endl;
    cout << "  Output:       B*C = " << B << " x " << C << " = " << TOTAL_RESULTS << " FP16 results" << endl;
    cout << endl;

    // Parse command line
    bool verbose = false;
    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "-v") == 0) verbose = true;
        if (strcmp(argv[i], "-h") == 0 || strcmp(argv[i], "--help") == 0) {
            cout << "Usage: test_linear [-v]" << endl;
            cout << "  -v    Verbose output" << endl;
            return 0;
        }
    }

    try {
        // Initialize device
        VP815 device(0);
        VP815GemmDevice gemm_device(device);

        uint32_t bitstream_id = gemm_device.mmio_read32(0, 0x214);
        cout << "Bitstream ID: 0x" << hex << bitstream_id << dec
             << " (Build: " << ((bitstream_id >> 24) & 0xFF) << "/"
             << ((bitstream_id >> 16) & 0xFF) << " "
             << ((bitstream_id >> 8) & 0xFF) << ":"
             << (bitstream_id & 0xFF) << ")" << endl;

        // Get BRAM result base address
        uint64_t BRAM_RESULT_BASE = acx_util_nap_absolute_addr(ACX_PART_AC7t1500, 3, 5);

        // ====================================================================
        // Load matrices from hex files
        // ====================================================================
        cout << "\nLoading matrices..." << endl;
        
        // Load left matrix (left_0.hex)
        vector<uint8_t> left_data;
        if (!gemm_device.loadHexMatrix("../../hex/left_0.hex", left_data)) {
            cerr << "ERROR: Failed to load left_0.hex" << endl;
            return 1;
        }
        cout << "  Left matrix (left_0.hex): " << left_data.size() << " bytes" << endl;
        
        // Load all 16 right matrices (right_0.hex through right_15.hex)
        vector<vector<uint8_t>> right_data(NUM_RIGHT_DISPATCHES);
        for (int i = 0; i < NUM_RIGHT_DISPATCHES; i++) {
            string filename = "../../hex/right_" + to_string(i) + ".hex";
            if (!gemm_device.loadHexMatrix(filename, right_data[i])) {
                cerr << "ERROR: Failed to load " << filename << endl;
                return 1;
            }
            if (verbose) {
                cout << "  Right matrix " << i << " (" << filename << "): " << right_data[i].size() << " bytes" << endl;
            }
        }
        cout << "  Loaded " << NUM_RIGHT_DISPATCHES << " right matrices" << endl;

        // ====================================================================
        // DMA matrices to GDDR6
        // ====================================================================
        cout << "\nDMA transfer to GDDR6..." << endl;
        
        // Left matrix to GDDR6_BASE_LEFT
        if (!gemm_device.dma_write(GDDR6_BASE_LEFT, left_data.data(), left_data.size())) {
            cerr << "ERROR: Failed to DMA write left matrix" << endl;
            return 1;
        }
        cout << "  Left matrix at:  0x" << hex << GDDR6_BASE_LEFT << dec << endl;
        
        // Each right matrix to its own GDDR6 region
        for (int i = 0; i < NUM_RIGHT_DISPATCHES; i++) {
            uint64_t right_addr = GDDR6_BASE_RIGHT + i * RIGHT_MATRIX_SIZE;
            if (!gemm_device.dma_write(right_addr, right_data[i].data(), right_data[i].size())) {
                cerr << "ERROR: Failed to DMA write right matrix " << i << endl;
                return 1;
            }
            if (verbose) {
                cout << "  Right matrix " << i << " at: 0x" << hex << right_addr << dec << endl;
            }
        }
        cout << "  Right matrices at: 0x" << hex << GDDR6_BASE_RIGHT << " - 0x" 
             << (GDDR6_BASE_RIGHT + NUM_RIGHT_DISPATCHES * RIGHT_MATRIX_SIZE) << dec << endl;

        // Soft reset and initialize
        gemm_device.soft_reset();
        gemm_device.reset_cmd_id();
        gemm_device.mmio_write32(0, 0x230, 0x00000000);  // Reset rd_ptr

        auto total_start = chrono::high_resolution_clock::now();

        // ====================================================================
        // Step 1: Fetch and Dispatch RIGHT matrices (16 dispatches, C4V32 each)
        // ====================================================================
        cout << "\n--- Step 1: RIGHT Matrix (16 x C4V32 dispatches) ---" << endl;

        // Right matrix parameters
        const uint32_t right_fetch_lines = 528;  // Lines per fetch
        const uint32_t right_nv_cnt = 4 * V;     // C4V32 = 4 * 32 = 128 NVs per dispatch
        const uint32_t col_en = 0xFFFF;          // All 16 tiles enabled

        // Tile address pattern must match TILE read formula: group * V * 8
        // For V=32: 0, 256, 512, 768
        // Col start pattern: 0, 4, 8, 12 within each group
        
        for (int dispatch_idx = 0; dispatch_idx < NUM_RIGHT_DISPATCHES; dispatch_idx++) {
            // Each dispatch uses its own right matrix from GDDR6
            uint64_t right_gddr6_addr = GDDR6_BASE_RIGHT + dispatch_idx * RIGHT_MATRIX_SIZE;
            
            // Calculate tile_addr and col_start
            int tile_group = dispatch_idx / 4;       // 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3
            int col_within_group = dispatch_idx % 4; // 0, 1, 2, 3, 0, 1, 2, 3, ...
            // CRITICAL: tile_addr = group * V * 8 to match TILE read address calculation
            uint16_t tile_addr = tile_group * V * 8; // 0, 256, 512, 768 for V=32
            uint8_t col_start = col_within_group * 4; // 0, 4, 8, 12

            if (verbose) {
                cout << "  Dispatch " << dispatch_idx << ": GDDR6=0x" << hex << right_gddr6_addr
                     << ", tile_addr=" << dec << tile_addr
                     << ", col_start=" << (int)col_start << endl;
            }

            // FETCH right matrix from its dedicated GDDR6 region
            gemm_device.fetch(right_gddr6_addr, right_fetch_lines, true);  // fetch_right=true

            // DISPATCH right matrix chunk
            uint8_t disp_id = gemm_device.dispatch(
                right_nv_cnt,    // man_nv_cnt = 128 NVs
                V,               // ugd_vec_size = 32
                tile_addr,       // tile_addr (0, 256, 512, 768)
                true,            // disp_right = true (RIGHT matrix)
                col_en,          // col_en = 0xFFFF (all 16 tiles)
                col_start,       // col_start (0, 4, 8, 12)
                false,           // broadcast = false (distribute mode)
                false            // man_4b = false
            );

            // Wait for dispatch to complete
            gemm_device.waitDispatch(disp_id);
        }

        cout << "  Completed " << NUM_RIGHT_DISPATCHES << " right matrix dispatches" << endl;

        // ====================================================================
        // Step 2: Fetch and Dispatch LEFT matrix (1 dispatch, B4V32, broadcast)
        // ====================================================================
        cout << "\n--- Step 2: LEFT Matrix (1 x B4V32 dispatch, broadcast) ---" << endl;

        const uint32_t left_fetch_lines = 528;  // Lines for left matrix
        const uint32_t left_nv_cnt = B * V;     // B4V32 = 4 * 32 = 128 NVs

        if (verbose) {
            cout << "  Fetch from GDDR6=0x" << hex << GDDR6_BASE_LEFT << dec
                 << ", lines=" << left_fetch_lines << endl;
        }

        // FETCH left matrix
        gemm_device.fetch(GDDR6_BASE_LEFT, left_fetch_lines, false);  // fetch_right=false

        // DISPATCH left matrix (broadcast to all columns)
        uint8_t left_disp_id = gemm_device.dispatch(
            left_nv_cnt,     // man_nv_cnt = 128 NVs
            V,               // ugd_vec_size = 32
            0,               // tile_addr = 0
            false,           // disp_right = false (LEFT matrix)
            col_en,          // col_en = 0xFFFF (all 16 tiles)
            0,               // col_start = 0
            true,            // broadcast = true (broadcast mode for LEFT)
            false            // man_4b = false
        );

        // Wait for dispatch to complete
        gemm_device.waitDispatch(left_disp_id);

        cout << "  Completed left matrix dispatch (broadcast)" << endl;

        // ====================================================================
        // Step 3: TILE Command (B4 C64 V32)
        // ====================================================================
        cout << "\n--- Step 3: TILE Command (B" << B << " C" << C << " V" << V << ") ---" << endl;

        if (verbose) {
            cout << "  Left Addr: 0, Right Addr: 0" << endl;
            cout << "  Left Ugd Len: " << B << ", Right Ugd Len: " << C << ", Vec Len: " << V << endl;
            cout << "  Col En: 0x" << hex << col_en << dec << endl;
        }

        // Issue TILE command
        uint8_t tile_id = gemm_device.tile(
            0,               // left_addr = 0
            0,               // right_addr = 0
            B,               // left_ugd_len (B)
            C,               // right_ugd_len (C)
            V,               // vec_len (V)
            false,           // left_man_4b
            false,           // right_man_4b
            false,           // main_loop_over_left = false
            col_en           // col_en = 0xFFFF
        );

        // Wait for TILE to complete
        gemm_device.waitTile(tile_id);

        cout << "  TILE command completed" << endl;

        // ====================================================================
        // Step 4: READOUT (256 results)
        // ====================================================================
        cout << "\n--- Step 4: READOUT (" << TOTAL_RESULTS << " results) ---" << endl;

        // Calculate padded result count
        int padded_C = ceil_div16(C) * 16;  // C=64 -> padded_C=64 (already aligned)
        int padded_results = B * padded_C;   // 4 * 64 = 256

        if (verbose) {
            cout << "  Start Col: 0, Read Length: " << padded_results << endl;
        }

        // Issue READOUT command
        gemm_device.readout(0, static_cast<uint32_t>(padded_results));

        // Wait for completion
        if (!gemm_device.wait_idle(5000)) {
            cerr << "ERROR: READOUT timeout" << endl;
            return 1;
        }

        auto total_end = chrono::high_resolution_clock::now();
        double total_ms = chrono::duration<double, milli>(total_end - total_start).count();

        cout << "  READOUT completed" << endl;

        // ====================================================================
        // Step 5: Read Results from Circular Buffer
        // ====================================================================
        cout << "\n--- Step 5: Read Results ---" << endl;

        // Read circular buffer state
        uint32_t wr_ptr = gemm_device.mmio_read32(0, 0x234) & 0x1FFF;
        uint32_t used_entries = gemm_device.mmio_read32(0, 0x238) & 0x3FFF;
        uint32_t rd_ptr = 0;  // We reset it to 0 at start

        cout << "  Circular buffer: wr_ptr=" << wr_ptr
             << ", rd_ptr=" << rd_ptr
             << ", used=" << used_entries << endl;

        if (used_entries < (uint32_t)padded_results) {
            cerr << "WARNING: Not enough results (expected " << padded_results
                 << ", got " << used_entries << ")" << endl;
        }

        // Calculate DMA read parameters (32-byte aligned)
        uint32_t byte_offset = rd_ptr * 2;
        uint32_t byte_count = padded_results * 2;
        uint32_t offset_in_first_line = byte_offset % 32;
        uint32_t total_bytes = offset_in_first_line + byte_count;
        uint32_t dma_bytes = ((total_bytes + 31) / 32) * 32;
        uint32_t dma_start = (byte_offset / 32) * 32;

        vector<uint8_t> bram_data(dma_bytes);
        if (!gemm_device.dma_read(BRAM_RESULT_BASE + dma_start, bram_data.data(), dma_bytes)) {
            cerr << "ERROR: Failed to DMA read results" << endl;
            return 1;
        }

        // Extract raw FP16 results (hardware order)
        vector<uint16_t> hw_results_raw(padded_results);
        for (int i = 0; i < padded_results; i++) {
            size_t byte_pos = offset_in_first_line + i * 2;
            hw_results_raw[i] = *(uint16_t*)(bram_data.data() + byte_pos);
        }

        // Reorder from batch-major hardware order to batch-major golden order
        // Hardware order: batch0[group0, group1, ...], batch1[group0, group1, ...], ...
        vector<uint16_t> result_fp16(TOTAL_RESULTS);
        const int num_col_groups = (C + 15) / 16;
        
        for (int golden_idx = 0; golden_idx < TOTAL_RESULTS; golden_idx++) {
            int batch_idx = golden_idx / C;
            int col_idx = golden_idx % C;
            int group_idx = col_idx / 16;
            int col_within_group = col_idx % 16;
            // Batch-major order (B outer, C inner) - matches new RTL scheduling
            int pulse_idx = batch_idx * num_col_groups + group_idx;
            int hw_idx = pulse_idx * 16 + col_within_group;
            result_fp16[golden_idx] = hw_results_raw[hw_idx];
        }

        cout << "  Read and reordered " << TOTAL_RESULTS << " FP16 results" << endl;

        // Display first few results
        cout << "\n  First 16 results (batch 0, cols 0-15):" << endl;
        for (int i = 0; i < min(16, TOTAL_RESULTS); i++) {
            float val = fp16ToFloat(result_fp16[i]);
            cout << "    [" << setw(3) << i << "] 0x" << hex << setfill('0') << setw(4)
                 << result_fp16[i] << dec << setfill(' ') << " = " << fixed << setprecision(6) << val << endl;
        }

        // ====================================================================
        // Step 6: Validation using individual golden files
        // ====================================================================
        cout << "\n--- Step 6: Validation ---" << endl;

        // Load golden references from 16 individual files
        // golden_B4_C4_V32_X.hex contains 16 results (4 batches * 4 cols)
        // File order matches dispatch order: dispatch 0 -> cols 0-3, dispatch 1 -> cols 4-7, etc.
        vector<uint16_t> golden_results(TOTAL_RESULTS);
        bool all_golden_loaded = true;
        
        for (int dispatch_idx = 0; dispatch_idx < NUM_RIGHT_DISPATCHES; dispatch_idx++) {
            string golden_file = "../../hex/golden_B4_C4_V32_" + to_string(dispatch_idx) + ".hex";
            ifstream golden(golden_file);
            if (!golden.is_open()) {
                cerr << "  ERROR: Could not open " << golden_file << endl;
                all_golden_loaded = false;
                break;
            }
            
            // Read 16 values from this golden file (4 batches * 4 cols)
            vector<uint16_t> file_values;
            string line;
            while (getline(golden, line)) {
                if (line.empty()) continue;
                uint16_t val = (uint16_t)strtoul(line.c_str(), NULL, 16);
                file_values.push_back(val);
            }
            golden.close();
            
            if (file_values.size() != RESULTS_PER_DISPATCH) {
                cerr << "  WARNING: " << golden_file << " has " << file_values.size() 
                     << " values, expected " << RESULTS_PER_DISPATCH << endl;
            }
            
            // Map file values to full result array
            // Dispatch idx -> column range: dispatch 0 = cols 0-3, dispatch 1 = cols 4-7, etc.
            int col_base = dispatch_idx * 4;  // Starting column for this dispatch
            for (int batch = 0; batch < B; batch++) {
                for (int col_in_dispatch = 0; col_in_dispatch < 4; col_in_dispatch++) {
                    int file_idx = batch * 4 + col_in_dispatch;
                    int golden_idx = batch * C + col_base + col_in_dispatch;
                    if (file_idx < (int)file_values.size() && golden_idx < TOTAL_RESULTS) {
                        golden_results[golden_idx] = file_values[file_idx];
                    }
                }
            }
            
            if (verbose) {
                cout << "  Loaded " << golden_file << ": " << file_values.size() << " values -> cols " 
                     << col_base << "-" << (col_base + 3) << endl;
            }
        }
        
        cout << "  Loaded all 16 golden reference files" << endl;

        if (all_golden_loaded) {
            // Compare
            int matches = 0, close_matches = 0, mismatches = 0;
            for (int i = 0; i < TOTAL_RESULTS; i++) {
                uint16_t diff = (result_fp16[i] > golden_results[i])
                              ? (result_fp16[i] - golden_results[i])
                              : (golden_results[i] - result_fp16[i]);

                if (result_fp16[i] == golden_results[i]) {
                    matches++;
                } else if (diff <= 4) {
                    close_matches++;
                } else {
                    mismatches++;
                    if (verbose && mismatches <= 20) {
                        int batch = i / C;
                        int col = i % C;
                        cout << "    MISMATCH[" << i << "] (B" << batch << ",C" << col << "): got 0x" 
                             << hex << setw(4) << setfill('0') << result_fp16[i] 
                             << ", expected 0x" << setw(4) << golden_results[i]
                             << dec << setfill(' ') << " (diff=" << diff << " LSB)" << endl;
                    }
                }
            }

            double match_rate = 100.0 * (matches + close_matches) / TOTAL_RESULTS;
            cout << "  Validation: " << (matches + close_matches) << "/" << TOTAL_RESULTS
                 << " within tolerance (" << matches << " exact, " << close_matches << " within 4 LSB)"
                 << " = " << fixed << setprecision(1) << match_rate << "%" << endl;

            if (mismatches > 0) {
                cout << "  Mismatches: " << mismatches << endl;
            }
        } else {
            // Basic sanity check if golden files not available
            int nan_count = 0, inf_count = 0, zero_count = 0;
            for (auto val : result_fp16) {
                if (val == 0x7C00 || val == 0xFC00) inf_count++;
                else if ((val & 0x7C00) == 0x7C00) nan_count++;
                else if (val == 0x0000 || val == 0x8000) zero_count++;
            }
            cout << "  Sanity: " << TOTAL_RESULTS << " results, "
                 << zero_count << " zeros, " << inf_count << " inf, " << nan_count << " NaN" << endl;
        }

        // ====================================================================
        // Summary
        // ====================================================================
        cout << "\n========================================================================" << endl;
        cout << "Linear Layer Test Complete" << endl;
        cout << "========================================================================" << endl;
        cout << "Configuration: B=" << B << ", C=" << C << ", V=" << V << endl;
        cout << "Total results: " << TOTAL_RESULTS << endl;
        cout << "Execution time: " << fixed << setprecision(3) << total_ms << " ms" << endl;
        
        // Performance calculation
        double total_ops = (double)B * C * V * 128 * 2;  // multiply-adds
        double gops = total_ops / (total_ms * 1e6);
        cout << "Throughput: " << fixed << setprecision(2) << gops << " GOPS" << endl;
        cout << "========================================================================" << endl;

        return 0;

    } catch (const exception& e) {
        cerr << "EXCEPTION: " << e.what() << endl;
        return 1;
    }
}
