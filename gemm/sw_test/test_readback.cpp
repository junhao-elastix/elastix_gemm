// test_readback.cpp - Batched Readback Test with Circular Buffer Management
// Mimics elastiapi.hpp production behavior for aggressive readback testing
//
// Key Features:
// - Loads all 14 golden references into single golden_array
// - Executes all configs sequentially with no buffer resets
// - Batched readback with READBACK_THRESHOLD = 256
// - Polling mechanism to wait for hardware to catch up
// - Comprehensive validation at the end

#include <iostream>
#include <iomanip>
#include <vector>
#include <fstream>
#include <sstream>
#include <cstring>
#include <cmath>     // for fabs(), powf()
#include <ctime>     // for timestamp
#include <chrono>    // for high_resolution_clock
#include <unistd.h>  // for usleep(), getopt()
#include <getopt.h>  // for getopt_long()
#include "vp815_gemm_device.hpp"

using namespace std;
using namespace achronix;


// ============================================================================
// Global State
// ============================================================================

const int READBACK_THRESHOLD = 4096;  // Trigger readback threshold
int stress_factor = 1;                 // Stress factor number of times to run the test (default 1)
bool verbose = false;                  // Verbose mode (-v): print everything
bool timing_only = false;              // Timing mode (-t): print timing info and summaries only
int pendingOutputElements = 0;       // Results waiting to be read
vector<uint16_t> result_array;       // Accumulated results from all tiles
VP815GemmDevice* g_gemm_device = nullptr;  // Global device pointer

// ============================================================================
// Timing Statistics
// ============================================================================

struct ConfigTiming {
    double fetch_left_ms;
    double fetch_right_ms;
    double dispatch_left_ms;
    double dispatch_right_ms;
    double tile_total_ms;
    double wait_idle_ms;
    int num_tiles;
    int B, C, V;  // Store config parameters for multiplication calculation
};

vector<ConfigTiming> all_timings;  // Store timing for each config iteration

// ============================================================================
// Test Configuration Structure
// ============================================================================

struct TestConfig {
    int B, C, V;
    string description;
};

// All 14 test configurations (matches generate_new.sh)
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

// ============================================================================
// Helper: Load Golden Hex File
// ============================================================================

bool loadGoldenHex(const string& filename, vector<uint16_t>& data) {
    ifstream file(filename);
    if (!file.is_open()) {
        return false;
    }

    string line;
    while (getline(file, line)) {
        // Skip empty lines and comments
        if (line.empty() || line[0] == '#') continue;

        // Parse hex value
        uint16_t value;
        if (sscanf(line.c_str(), "%hx", &value) == 1) {
            data.push_back(value);
        }
    }

    return true;
}

// ============================================================================
// Helper: Read Pending Output (mimics elastiapi.hpp)
// ============================================================================

void readPendingOutput() {
    if (pendingOutputElements == 0) {
        return;
    }

    if (verbose) {
        cout << "\n--- Readback: Waiting for " << pendingOutputElements << " results ---" << endl;
    }

    // Step 1: POLL until hardware catches up
    uint32_t used_entries = g_gemm_device->mmio_read32(0, 0x238) & 0x3FFF;
    int timeout = 0;
    const int MAX_POLLS = 100000;  // 10 second timeout (100k × 100µs)

    while (used_entries < (uint32_t)pendingOutputElements) {
        // Adaptive sleep: 100µs when far, 10µs when close
        // if (used_entries < (uint32_t)pendingOutputElements / 2) {
        //     usleep(100);  // Far from ready
        // } else {
        //     usleep(10);   // Almost ready
        // }

        used_entries = g_gemm_device->mmio_read32(0, 0x238) & 0x3FFF;

        if (++timeout > MAX_POLLS) {
            cerr << "ERROR: TIMEOUT waiting for results!" << endl;
            cerr << "  Expected: " << pendingOutputElements << endl;
            cerr << "  Got: " << used_entries << endl;
            cerr << "  After: " << timeout << " polls" << endl;
            return;
        }
    }

    if (verbose) {
        cout << "  Hardware ready: used_entries=" << used_entries
             << " (waited " << timeout << " polls)" << endl;
    }

    // Step 2: Read exactly pendingOutputElements from circular buffer
    uint32_t rd_ptr = g_gemm_device->mmio_read32(0, 0x230) & 0x1FFF;
    uint32_t read_count = pendingOutputElements;

    if (verbose) {
        cout << "  Reading from circular buffer: rd_ptr=" << rd_ptr
             << ", count=" << read_count << endl;
    }

    // Calculate DMA read parameters (32-byte aligned)
    uint32_t byte_offset = rd_ptr * 2;  // FP16 = 2 bytes
    uint32_t byte_count = read_count * 2;
    uint32_t offset_in_first_line = byte_offset % 32;
    uint32_t total_bytes = offset_in_first_line + byte_count;
    uint32_t dma_bytes = ((total_bytes + 31) / 32) * 32;
    uint32_t dma_start = (byte_offset / 32) * 32;

    // DMA read from BRAM
    uint64_t BRAM_RESULT_BASE = acx_util_nap_absolute_addr(ACX_PART_AC7t1500, 3, 5);
    vector<uint8_t> dma_buffer(dma_bytes);

    if (!g_gemm_device->dma_read(BRAM_RESULT_BASE + dma_start,
                                  reinterpret_cast<void*>(dma_buffer.data()),
                                  dma_bytes)) {
        cerr << "ERROR: DMA read failed!" << endl;
        return;
    }

    // Extract FP16 results from DMA buffer
    uint32_t skip_bytes = offset_in_first_line;
    for (uint32_t i = 0; i < read_count; i++) {
        uint32_t byte_idx = skip_bytes + (i * 2);
        uint16_t fp16_value = (uint16_t)dma_buffer[byte_idx] |
                              ((uint16_t)dma_buffer[byte_idx + 1] << 8);
        result_array.push_back(fp16_value);
    }

    if (verbose) {
        cout << "  Appended " << read_count << " results to result_array" << endl;
        cout << "  result_array.size() = " << result_array.size() << endl;
    }

    // Step 4: Update rd_ptr (host manages circular buffer advancement)
    uint32_t new_rd_ptr = (rd_ptr + read_count) % 8192;
    g_gemm_device->mmio_write32(0, 0x230, new_rd_ptr);

    if (verbose) {
        cout << "  Updated rd_ptr: " << rd_ptr << " → " << new_rd_ptr << endl;
    }

    // Step 5: Reset pending count
    pendingOutputElements = 0;
}

// ============================================================================
// Helper: Request Output (accumulate and trigger threshold)
// ============================================================================

void requestOutput(int numResults) {
    pendingOutputElements += numResults;
    if (verbose) {
        cout << "  requestOutput(" << numResults << ") → pending="
             << pendingOutputElements << endl;
    }

    if (pendingOutputElements >= READBACK_THRESHOLD) {
        if (verbose) {
            cout << "  Threshold reached (" << READBACK_THRESHOLD
                 << "), triggering readback" << endl;
        }
        readPendingOutput();
    }
}

// ============================================================================
// Usage / Help
// ============================================================================

void print_usage(const char* progname) {
    cout << "Usage: " << progname << " [OPTIONS]" << endl;
    cout << "\nOptions:" << endl;
    cout << "  -v           Verbose mode (print everything)" << endl;
    cout << "  -t           Timing mode (print timing info and summaries only)" << endl;
    cout << "  -s <number>  Stress factor (number of test iterations, default: 1)" << endl;
    cout << "  -h           Display this help message" << endl;
    cout << "\nDefault mode (no -v or -t): Print summaries only" << endl;
    cout << endl;
}

// ============================================================================
// Main Test Function
// ============================================================================

int main(int argc, char* argv[]) {
    // Parse command-line arguments
    int opt;
    while ((opt = getopt(argc, argv, "vts:h")) != -1) {
        switch (opt) {
            case 'v':
                verbose = true;
                break;
            case 't':
                timing_only = true;
                break;
            case 's':
                stress_factor = atoi(optarg);
                if (stress_factor < 1) {
                    cerr << "ERROR: Stress factor must be >= 1" << endl;
                    return 1;
                }
                break;
            case 'h':
                print_usage(argv[0]);
                return 0;
            default:
                print_usage(argv[0]);
                return 1;
        }
    }
    if (verbose || timing_only) {
        cout << "========================================================================" << endl;
        cout << "Batched Readback Test - Circular Buffer Management" << endl;
        cout << "========================================================================" << endl;
        cout << "Readback threshold: " << READBACK_THRESHOLD << " FP16 results" << endl;
        cout << "Test configurations: " << test_configs.size() << endl;
        cout << "Stress factor: " << stress_factor << endl;
        cout << endl;
    }

    try {
        VP815 device(0);
        VP815GemmDevice gemm_device(device);
        g_gemm_device = &gemm_device;  // Set global pointer

        // ====================================================================
        // Step 1: Load All Golden References
        // ====================================================================
        if (verbose) {
            cout << "========================================================================" << endl;
            cout << "Step 1: Loading All Golden References" << endl;
            cout << "========================================================================" << endl;
        }

        vector<uint16_t> golden_array;
        int total_expected_results = 0;

        for (const auto& config : test_configs) {
            string golden_file = "../../hex/golden_B" + to_string(config.B) +
                                 "_C" + to_string(config.C) +
                                 "_V" + to_string(config.V) + "_multitile.hex";

            vector<uint16_t> config_golden;
            if (!loadGoldenHex(golden_file, config_golden)) {
                cerr << "ERROR: Failed to load " << golden_file << endl;
                return 1;
            }

            // Calculate expected results for this config
            int max_left_tiles = 128 / (config.B * config.V);
            int max_right_tiles = 128 / (config.C * config.V);
            int num_tiles = min(max_left_tiles, max_right_tiles);
            int config_results = num_tiles * config.B * config.C;

            if (config_golden.size() != (size_t)config_results) {
                if (verbose) {
                    cerr << "WARNING: Golden file size mismatch for " << config.description << endl;
                    cerr << "  Expected: " << config_results << ", Got: " << config_golden.size() << endl;
                }
            }

            if (verbose) {
                cout << "  Loaded " << config.description << ": "
                     << config_golden.size() << " results" << endl;
            }

            // Append to golden_array
            golden_array.insert(golden_array.end(),
                                    config_golden.begin(), config_golden.end());
            total_expected_results += config_results;
        }

        // Repeat the golden_array contents for 'stress_factor' times
        vector<uint16_t> big_golden_array = golden_array;
        for (int i = 1; i < stress_factor; ++i) {
            big_golden_array.insert(big_golden_array.end(),
                                    golden_array.begin(),
                                    golden_array.end());
        }
        total_expected_results *= stress_factor;

        if (verbose) {
            cout << "\n✓ Total golden results loaded: " << big_golden_array.size() << endl;
            cout << "✓ Expected total results: " << total_expected_results << endl;
        }

        // ====================================================================
        // Step 2: Create Result Array (2× capacity)
        // ====================================================================
        if (verbose) {
            cout << "\n========================================================================" << endl;
            cout << "Step 2: Allocating Result Array" << endl;
            cout << "========================================================================" << endl;
        }

        size_t result_capacity = big_golden_array.size() * 2;
        result_array.reserve(result_capacity);

        if (verbose) {
            cout << "  Golden array size: " << big_golden_array.size() << endl;
            cout << "  Result array capacity: " << result_capacity << " (2×)" << endl;
        }

        // ====================================================================
        // Step 3: Load Matrices ONCE
        // ====================================================================
        if (verbose) {
            cout << "\n========================================================================" << endl;
            cout << "Step 3: Loading Reference Matrices" << endl;
            cout << "========================================================================" << endl;
        }

        vector<uint8_t> left_data, right_data;
        if (!gemm_device.loadHexMatrix("../../hex/left.hex", left_data) ||
            !gemm_device.loadHexMatrix("../../hex/right.hex", right_data)) {
            cerr << "ERROR: Failed to load matrices" << endl;
            return 1;
        }

        if (verbose) {
            cout << "✓ Loaded matrices: " << left_data.size() << " bytes each" << endl;
        }

        // DMA matrices to GDDR6 (each config gets fresh data)
        if (verbose) {
            cout << "\n  DMA Transfer to GDDR6..." << endl;
        }
        if (!gemm_device.dma_write(GDDR6_BASE_LEFT, left_data.data(), left_data.size()) ||
            !gemm_device.dma_write(GDDR6_BASE_RIGHT, right_data.data(), right_data.size())) {
            cerr << "ERROR: Failed to DMA write matrices" << endl;
            return 1;
        }

        // Initial soft reset
        gemm_device.soft_reset();
        // Reset command ID to 0
        gemm_device.reset_cmd_id();

        // Reset circular buffer pointers (ONLY ONCE at start)
        gemm_device.mmio_write32(0, 0x230, 0x00000000);  // rd_ptr = 0
        if (verbose) {
            cout << "✓ Reset circular buffer: rd_ptr=0, wr_ptr=0" << endl;
        }

        // ====================================================================
        // Step 4: Execute All 14 Configurations
        // ====================================================================
        if (verbose) {
            cout << "\n========================================================================" << endl;
            cout << "Step 4: Executing All Configurations (Batched Readback)" << endl;
            cout << "========================================================================" << endl;
        }

        for (int i = 0; i < stress_factor; i++) {
            for (const auto& config : test_configs) {
                if (verbose) {
                    cout << "\n>>> Configuration: " << config.description << " <<<" << endl;
                }

                // Initialize timing for this config
                ConfigTiming timing;
                timing.num_tiles = 0;
                timing.fetch_left_ms = 0;
                timing.fetch_right_ms = 0;
                timing.dispatch_left_ms = 0;
                timing.dispatch_right_ms = 0;
                timing.tile_total_ms = 0;
                timing.wait_idle_ms = 0;
                timing.B = config.B;
                timing.C = config.C;
                timing.V = config.V;

                // Calculate tile counts
                int max_left_tiles = 128 / (config.B * config.V);
                int max_right_tiles = 128 / (config.C * config.V);
                int num_tiles = min(max_left_tiles, max_right_tiles);
                int results_per_tile = config.B * config.C;
                timing.num_tiles = num_tiles;

                if (verbose) {
                    cout << "  B=" << config.B << ", C=" << config.C << ", V=" << config.V << endl;
                    cout << "  num_tiles=" << num_tiles << ", results_per_tile=" << results_per_tile << endl;
                }

                // FETCH memory block
                if (verbose) {
                    cout << "  FETCH Memory Block..." << endl;
                }

                uint32_t left_lines = 528;
                uint32_t right_lines = 528;

                auto fetch_left_start = chrono::high_resolution_clock::now();
                (void)gemm_device.fetch(GDDR6_BASE_LEFT, left_lines, false);
                if (!gemm_device.wait_idle(5000)) {
                    cerr << "ERROR: FETCH left timeout" << endl;
                    return 1;
                }
                auto fetch_left_end = chrono::high_resolution_clock::now();
                timing.fetch_left_ms = chrono::duration<double, milli>(fetch_left_end - fetch_left_start).count();

                auto fetch_right_start = chrono::high_resolution_clock::now();
                (void)gemm_device.fetch(GDDR6_BASE_RIGHT, right_lines, true);  // fetch_right=true for RIGHT matrix
                if (!gemm_device.wait_idle(5000)) {
                    cerr << "ERROR: FETCH right timeout" << endl;
                    return 1;
                }
                auto fetch_right_end = chrono::high_resolution_clock::now();
                timing.fetch_right_ms = chrono::duration<double, milli>(fetch_right_end - fetch_right_start).count();

                // DISPATCH memory block
                if (verbose) {
                    cout << "  DISPATCH Memory Block..." << endl;
                }

                // DISPATCH left (uses BROADCAST mode)
                auto dispatch_left_start = chrono::high_resolution_clock::now();
                uint8_t disp_left_id = gemm_device.dispatch(
                    config.B * config.V,  // man_nv_cnt = B × V Native Vectors
                    config.V,             // ugd_vec_size = V (NVs per UGD vector)
                    0,                    // tile_addr = 0
                    false,                // disp_right = false (LEFT matrix)
                    0x0001,               // col_en = enable tile 0
                    0,                    // col_start = 0
                    true,                 // broadcast = true (LEFT uses broadcast)
                    false                 // man_4b = false
                );
                (void)gemm_device.waitDispatch(disp_left_id);
                auto dispatch_left_end = chrono::high_resolution_clock::now();
                timing.dispatch_left_ms = chrono::duration<double, milli>(dispatch_left_end - dispatch_left_start).count();

                // DISPATCH right (uses DISTRIBUTE mode)
                auto dispatch_right_start = chrono::high_resolution_clock::now();
                uint8_t disp_right_id = gemm_device.dispatch(
                    config.C * config.V,  // man_nv_cnt = C × V Native Vectors
                    config.V,             // ugd_vec_size = V (NVs per UGD vector)
                    0,                    // tile_addr = 0
                    true,                 // disp_right = true (RIGHT matrix)
                    0x0001,               // col_en = enable tile 0
                    0,                    // col_start = 0
                    false,                // broadcast = false (RIGHT uses distribute)
                    false                 // man_4b = false
                );
                (void)gemm_device.waitDispatch(disp_right_id);
                auto dispatch_right_end = chrono::high_resolution_clock::now();
                timing.dispatch_right_ms = chrono::duration<double, milli>(dispatch_right_end - dispatch_right_start).count();

                // Execute TILE commands with batched readback
                if (verbose) {
                    cout << "  Executing " << num_tiles << " TILE commands..." << endl;
                }

                int left_stride = (config.B * config.V) * 4;
                int right_stride = (config.C * config.V) * 4;

                for (int tile_idx = 0; tile_idx < num_tiles; tile_idx++) {
                    uint16_t left_addr = tile_idx * left_stride;
                    uint16_t right_addr = tile_idx * right_stride;

                    // TILE command
                    auto tile_loop_start = chrono::high_resolution_clock::now();
                    uint8_t tile_id = gemm_device.tile(left_addr, right_addr,
                                                        config.B, config.C, config.V,
                                                        false, false, true, 0x0001);

                    // WAIT_TILE
                    (void)gemm_device.waitTile(tile_id);
                    auto tile_loop_end = chrono::high_resolution_clock::now();
                    timing.tile_total_ms += chrono::duration<double, milli>(tile_loop_end - tile_loop_start).count();

                    // Wait for this tile to complete
                    auto wait_idle_start = chrono::high_resolution_clock::now();
                    if (!gemm_device.wait_idle(5000)) {
                        cerr << "ERROR: TILE " << tile_idx << " timeout" << endl;
                        return 1;
                    }
                    auto wait_idle_end = chrono::high_resolution_clock::now();
                    timing.wait_idle_ms += chrono::duration<double, milli>(wait_idle_end - wait_idle_start).count();

                    // Request output (triggers readback if threshold reached)
                    requestOutput(results_per_tile);
                }
                // Report timing for this config
                if (verbose || timing_only) {
                    cout << "  Completed " << num_tiles << " tiles for this config" << endl;
                    cout << "  Timing:" << endl;
                    cout << "    FETCH left:       " << fixed << setprecision(3) << timing.fetch_left_ms << " ms" << endl;
                    cout << "    FETCH right:      " << fixed << setprecision(3) << timing.fetch_right_ms << " ms" << endl;
                    cout << "    DISPATCH left:    " << fixed << setprecision(3) << timing.dispatch_left_ms << " ms" << endl;
                    cout << "    DISPATCH right:   " << fixed << setprecision(3) << timing.dispatch_right_ms << " ms" << endl;
                    cout << "    TILE loop total:  " << fixed << setprecision(3) << timing.tile_total_ms << " ms" << endl;
                    cout << "    wait_idle total:  " << fixed << setprecision(3) << timing.wait_idle_ms << " ms" << endl;
                    cout << "    Per tile avg:     " << fixed << setprecision(3) << (timing.tile_total_ms / num_tiles) << " ms" << endl;
                }

                // Save timing
                all_timings.push_back(timing);
            }
            if (verbose) {
                cout << "  Completed stress factor iteration " << (i+1) << " of " << stress_factor << endl;
            }
        }

        // ====================================================================
        // Step 5: Final Flush (read any remaining results)
        // ====================================================================
        if (verbose) {
            cout << "\n========================================================================" << endl;
            cout << "Step 5: Final Flush" << endl;
            cout << "========================================================================" << endl;
        }

        if (pendingOutputElements > 0) {
            if (verbose) {
                cout << "Flushing remaining " << pendingOutputElements << " results..." << endl;
            }
            readPendingOutput();
        } else {
            if (verbose) {
                cout << "No pending results to flush." << endl;
            }
        }

        if (verbose) {
            cout << "\n✓ Final result_array.size() = " << result_array.size() << endl;
            cout << "✓ Expected big_golden_array.size() = " << big_golden_array.size() << endl;
        }

        // Check for over-production: are there extra results in buffer?
        uint32_t final_used_entries = gemm_device.mmio_read32(0, 0x238) & 0x3FFF;
        if (final_used_entries > 0) {
            cerr << "\nERROR: Hardware over-produced results!" << endl;
            cerr << "  Buffer still has " << final_used_entries << " unread results" << endl;
            cerr << "  This indicates hardware produced more than expected" << endl;
        }

        // ====================================================================
        // Step 5.5: Save Raw Results to Hex Log File
        // ====================================================================
        if (verbose) {
            cout << "\n========================================================================" << endl;
            cout << "Step 5.5: Saving Raw Results" << endl;
            cout << "========================================================================" << endl;
        }

        // Generate timestamped filename
        time_t now = time(0);
        tm* ltm = localtime(&now);
        stringstream log_filename;
        log_filename << "test_readback_results_"
                     << setfill('0') << setw(4) << (1900 + ltm->tm_year)
                     << setw(2) << (1 + ltm->tm_mon)
                     << setw(2) << ltm->tm_mday << "_"
                     << setw(2) << ltm->tm_hour
                     << setw(2) << ltm->tm_min
                     << ".hex";

        string log_file = log_filename.str();
        ofstream log_out(log_file);
        if (!log_out.is_open()) {
            cerr << "WARNING: Failed to open log file: " << log_file << endl;
        } else {
            // Write header comment
            log_out << "# test_readback.cpp raw results" << endl;
            log_out << "# Date: " << asctime(ltm);
            log_out << "# Total results: " << result_array.size() << endl;
            log_out << "# Configurations: 14" << endl;
            log_out << "#" << endl;

            // Write all results in hex format (one per line)
            for (size_t i = 0; i < result_array.size(); i++) {
                log_out << hex << setfill('0') << setw(4) << result_array[i] << dec << endl;
            }

            log_out.close();
            if (verbose) {
                cout << "✓ Saved " << result_array.size() << " raw results to: " << log_file << endl;
            }
        }

        // ====================================================================
        // Step 6: Validation
        // ====================================================================
        if (verbose) {
            cout << "\n========================================================================" << endl;
            cout << "Step 6: Validation" << endl;
            cout << "========================================================================" << endl;
        }

        if (result_array.size() != big_golden_array.size()) {
            cerr << "ERROR: Result count mismatch!" << endl;
            cerr << "  Got: " << result_array.size() << endl;
            cerr << "  Expected: " << big_golden_array.size() << endl;
        }

        int mismatches = 0;
        size_t compare_count = total_expected_results;
        double sum_squared_error = 0.0;
        double max_abs_error = 0.0;

        // Convert to float and compare with tolerance (like test_gemm.cpp)
        for (size_t i = 0; i < compare_count; i++) {
            float result_val = fp16ToFloat(result_array[i]);
            float golden_val = fp16ToFloat(big_golden_array[i]);

            float diff = fabs(result_val - golden_val);

            // Track error statistics
            sum_squared_error += (double)(diff * diff);
            if (diff > max_abs_error) {
                max_abs_error = diff;
            }

            // Use absolute error for very small values to avoid division by near-zero
            bool match;
            if (fabs(golden_val) < 1e-4f) {
                match = (diff < 1e-4f);  // Absolute error threshold for near-zero values
            } else {
                float rel_err = diff / fabs(golden_val);
                match = (rel_err <= 0.4f);  // 40% relative tolerance like test_gemm.cpp
            }

            if (!match) {
                if (mismatches < 20) {  // Limit output to first 20 mismatches
                    cerr << "MISMATCH[" << i << "]: got 0x" << hex << setw(4) << setfill('0')
                         << result_array[i] << " (" << dec << result_val << ") expected 0x"
                         << hex << setw(4) << setfill('0') << big_golden_array[i]
                         << dec << " (" << golden_val << "), diff=" << diff << endl;
                }
                mismatches++;
            }
        }

        // Calculate RMSE
        double rmse = sqrt(sum_squared_error / compare_count);

        cout << "\n========================================================================" << endl;
        cout << "Validation Summary" << endl;
        cout << "========================================================================" << endl;
        cout << "Total results validated: " << compare_count << endl;
        cout << "Mismatches: " << mismatches << endl;
        cout << "Match rate: " << (100.0 * (compare_count - mismatches) / compare_count) << "%" << endl;
        cout << "\nError Statistics:" << endl;
        cout << "  RMSE (Root Mean Square Error): " << scientific << setprecision(6) << rmse << dec << endl;
        cout << "  Max absolute error: " << scientific << setprecision(6) << max_abs_error << dec << endl;

        // ====================================================================
        // Timing Summary
        // ====================================================================

        // Calculate totals first (needed for performance summary)
        long long total_multiplications = 0;
        double total_time_ms = 0;

        if (!all_timings.empty()) {
            for (const auto& t : all_timings) {
                // Calculate multiplications for this config iteration
                // Total multiplications = num_tiles × B × C × V × 128
                long long muls = (long long)t.num_tiles * t.B * t.C * t.V * 128;
                total_multiplications += muls;

                // Total time includes FETCH + DISPATCH + TILE
                total_time_ms += (t.fetch_left_ms + t.fetch_right_ms +
                                  t.dispatch_left_ms + t.dispatch_right_ms +
                                  t.tile_total_ms);
            }
        }

        if (verbose || timing_only) {
            cout << "\n========================================================================" << endl;
            cout << "Timing Summary (averaged across " << all_timings.size() << " iterations)" << endl;
            cout << "========================================================================" << endl;

            if (!all_timings.empty()) {
                // Calculate averages
                double avg_fetch_left = 0, avg_fetch_right = 0;
                double avg_dispatch_left = 0, avg_dispatch_right = 0;
                double avg_tile_total = 0, avg_wait_idle = 0;
                int total_tiles = 0;

                for (const auto& t : all_timings) {
                    avg_fetch_left += t.fetch_left_ms;
                    avg_fetch_right += t.fetch_right_ms;
                    avg_dispatch_left += t.dispatch_left_ms;
                    avg_dispatch_right += t.dispatch_right_ms;
                    avg_tile_total += t.tile_total_ms;
                    avg_wait_idle += t.wait_idle_ms;
                    total_tiles += t.num_tiles;
                }

                int n = all_timings.size();
                avg_fetch_left /= n;
                avg_fetch_right /= n;
                avg_dispatch_left /= n;
                avg_dispatch_right /= n;
                avg_tile_total /= n;
                avg_wait_idle /= n;
                double avg_per_tile = avg_tile_total / (total_tiles / (double)n);

                cout << "\nAverage Command Timings:" << endl;
                cout << "  FETCH left:           " << fixed << setprecision(3) << avg_fetch_left << " ms" << endl;
                cout << "  FETCH right:          " << fixed << setprecision(3) << avg_fetch_right << " ms" << endl;
                cout << "  DISPATCH left:        " << fixed << setprecision(3) << avg_dispatch_left << " ms" << endl;
                cout << "  DISPATCH right:       " << fixed << setprecision(3) << avg_dispatch_right << " ms" << endl;
                cout << "  TILE loop total:      " << fixed << setprecision(3) << avg_tile_total << " ms" << endl;
                cout << "  wait_idle total:      " << fixed << setprecision(3) << avg_wait_idle << " ms" << endl;
                cout << "  Per tile (avg):       " << fixed << setprecision(3) << avg_per_tile << " ms" << endl;
                cout << "\nTotal tiles executed:   " << total_tiles << endl;
                cout << "Average tiles/config:   " << fixed << setprecision(1) << (total_tiles / (double)n) << endl;
            }
        }

        // ====================================================================
        // Performance Summary (always printed)
        // ====================================================================
        cout << "\n========================================================================" << endl;
        cout << "Performance Summary" << endl;
        cout << "========================================================================" << endl;

        // Convert to seconds for throughput calculation
        double total_time_sec = total_time_ms / 1000.0;

        cout << "\nTotal multiplications:  " << total_multiplications << endl;
        cout << "Total time:             " << fixed << setprecision(3) << total_time_sec << " seconds" << endl;
        cout << "\nThroughput:" << endl;
        cout << "  " << scientific << setprecision(3) << (total_multiplications / total_time_sec) << " multiplications/second" << endl;
        cout << "  " << fixed << setprecision(2) << (total_multiplications / total_time_sec / 1e9) << " GMUL/s (billions of multiplications/second)" << endl;
        cout << "  " << fixed << setprecision(2) << (total_multiplications / total_time_sec / 1e12) << " TMUL/s (trillions of multiplications/second)" << endl;

        if (mismatches == 0 && result_array.size() == big_golden_array.size()) {
            cout << "\n✅ ALL RESULTS MATCH! TEST PASSED!" << endl;
            return 0;
        } else {
            cout << "\n❌ TEST FAILED!" << endl;
            return 1;
        }

    } catch (const exception& e) {
        cerr << "EXCEPTION: " << e.what() << endl;
        return 1;
    }
}
