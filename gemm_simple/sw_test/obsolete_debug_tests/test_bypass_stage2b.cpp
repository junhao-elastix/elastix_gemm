// ============================================================================
// Stage 2b Bypass Test - BRAM Data Forwarding
//
// Tests bypass mode 2: Read first line from dispatcher BRAM and forward
// Expected: First line of left.hex (06 06 06 07 06 06...) should appear
//           as GFP nibbles converted to FP16 values
//
// Flow:
//   1. Set bypass_mode = 2
//   2. FETCH left matrix from GDDR6 → Dispatcher BRAM
//   3. MATMUL command (triggers ST_BYPASS_FORWARD state)
//   4. Read result BRAM - should contain first line data
//
// Author: Claude Code
// Date: Wed Oct 9 2025
// ============================================================================

#include <iostream>
#include <iomanip>
#include <fstream>
#include <sstream>
#include <cstring>
#include <cstdlib>
#include <chrono>
#include <thread>
#include <vector>
#include "vp815.hpp"

using namespace std;
using namespace achronix;

// Register offsets
#define ENGINE_CMD_WORD0        0x28
#define ENGINE_CMD_WORD1        0x2C
#define ENGINE_CMD_WORD2        0x30
#define ENGINE_CMD_WORD3        0x34
#define ENGINE_CMD_SUBMIT       0x38
#define ENGINE_STATUS           0x3C
#define ENGINE_BYPASS           0x24
#define ENGINE_RESULT_COUNT     0x40

// Opcodes
#define OPCODE_FETCH            0xF0
#define OPCODE_MATMUL           0xF2

// Memory addresses
#define GDDR6_BASE_LEFT         0x0
#define BRAM_RESULT_BASE        0x4460008000ULL

// Wait for engine idle
bool waitEngineIdle(VP815& device, uint32_t timeout_ms = 5000) {
    auto start = chrono::steady_clock::now();

    while (true) {
        uint32_t status = device.mmioRead32(0, ENGINE_STATUS);
        if ((status & 0x1) == 0) return true;  // Busy bit clear

        auto elapsed = chrono::duration_cast<chrono::milliseconds>(
            chrono::steady_clock::now() - start).count();
        if (elapsed > timeout_ms) {
            cerr << "ERROR: Engine timeout after " << timeout_ms << "ms" << endl;
            cerr << "ENGINE_STATUS: 0x" << hex << status << dec << endl;
            return false;
        }

        this_thread::sleep_for(chrono::milliseconds(10));
    }
}

// Issue command
void issueCommand(VP815& device, uint32_t word0, uint32_t word1,
                  uint32_t word2, uint32_t word3) {
    device.mmioWrite32(0, ENGINE_CMD_WORD0, word0);
    device.mmioWrite32(0, ENGINE_CMD_WORD1, word1);
    device.mmioWrite32(0, ENGINE_CMD_WORD2, word2);
    device.mmioWrite32(0, ENGINE_CMD_WORD3, word3);
    device.mmioWrite32(0, ENGINE_CMD_SUBMIT, 0x1);
}

// Load hex file
bool loadHexMatrix(const string& filename, vector<uint8_t>& data) {
    ifstream file(filename);
    if (!file.is_open()) {
        cerr << "ERROR: Cannot open " << filename << endl;
        return false;
    }

    data.clear();
    data.reserve(528 * 32);

    string line;
    int line_num = 0;

    while (getline(file, line)) {
        if (line.empty()) continue;

        istringstream iss(line);
        string hex_val;
        int byte_count = 0;

        while (iss >> hex_val) {
            if (byte_count >= 32) break;
            data.push_back((uint8_t)strtoul(hex_val.c_str(), NULL, 16));
            byte_count++;
        }

        if (byte_count != 32) {
            cerr << "ERROR: Line " << line_num << " has " << byte_count << " bytes" << endl;
            return false;
        }
        line_num++;
    }

    if (line_num != 528) {
        cerr << "ERROR: Expected 528 lines, got " << line_num << endl;
        return false;
    }

    return true;
}

int main() {
    cout << "\n=== Stage 2b Bypass Test - BRAM Data Forwarding ===" << endl;

    // Initialize device
    unique_ptr<VP815> device;
    try {
        device = make_unique<VP815>(0);
        cout << "✅ Device initialized\n" << endl;
    } catch (const exception& e) {
        cerr << "❌ Failed to initialize: " << e.what() << endl;
        return -1;
    }

    // Load left matrix
    cout << "[1] Loading left.hex..." << endl;
    vector<uint8_t> left_data;
    if (!loadHexMatrix("../../hex/left.hex", left_data)) {
        return -1;
    }
    cout << "  ✓ Loaded 528 lines (16896 bytes)\n" << endl;

    // Show first line content
    cout << "[2] First line of left.hex (first 32 bytes):" << endl;
    cout << "  ";
    for (int i = 0; i < 32; i++) {
        cout << hex << setw(2) << setfill('0') << (int)left_data[i] << " ";
        if ((i+1) % 16 == 0) cout << "\n  ";
    }
    cout << dec << endl;

    // DMA write to GDDR6
    cout << "[3] DMA writing left matrix to GDDR6..." << endl;
    device->dmaWrite(GDDR6_BASE_LEFT, left_data.size(), (char*)left_data.data());
    cout << "  ✓ Written to GDDR6 @ 0x0\n" << endl;

    // Set bypass mode 2
    cout << "[4] Setting bypass mode = 2 (BRAM data forwarding)..." << endl;
    device->mmioWrite32(0, ENGINE_BYPASS, 0x2);
    uint32_t bypass_val = device->mmioRead32(0, ENGINE_BYPASS);
    cout << "  Bypass mode: " << (bypass_val & 0x3) << "\n" << endl;

    // FETCH command: Load left matrix from GDDR6 → Dispatcher BRAM
    cout << "[5] FETCH: GDDR6 → Dispatcher BRAM (528 lines)..." << endl;
    uint32_t fetch_word0 = (OPCODE_FETCH << 0) | (0 << 8) | (12 << 16);
    uint32_t fetch_word1 = GDDR6_BASE_LEFT;  // start_addr (in 128B chunks)
    uint32_t fetch_word2 = (528 << 0) | (0 << 21);  // len=528 lines
    uint32_t fetch_word3 = 0;

    issueCommand(*device, fetch_word0, fetch_word1, fetch_word2, fetch_word3);

    if (!waitEngineIdle(*device)) {
        cerr << "❌ FETCH command timeout" << endl;
        return -1;
    }
    cout << "  ✓ FETCH complete\n" << endl;

    // MATMUL command: Triggers ST_BYPASS_FORWARD state
    // Params: B=4, C=4, V=32, left_addr=0 (first line)
    cout << "[6] MATMUL: Trigger bypass forward (B=4, C=4, V=32)..." << endl;

    uint32_t B = 4, C = 4, V = 32;
    uint32_t left_addr = 0;    // First line of dispatcher BRAM
    uint32_t right_addr = 528; // Doesn't matter for bypass

    // Build MATMUL command (cmd_tile_s structure)
    uint32_t matmul_word0, matmul_word1, matmul_word2, matmul_word3;

    // Word0: opcode, id, len
    matmul_word0 = (OPCODE_MATMUL << 0) | (9 << 8) | (12 << 16);

    // Word1: left_addr[10:0] at [31:21], right_addr[10:0] at [20:10], others
    matmul_word1 = ((left_addr & 0x7FF) << 21) | ((right_addr & 0x7FF) << 10) | 0;

    // Word2: vec_len=0, dim_b, dim_c, flags
    matmul_word2 = (0 << 21) | (B << 13) | (C << 5) | 0;

    // Word3: left_ugd_len=32, dim_v=32
    matmul_word3 = (0x20 << 0) | (V << 8) | 0;

    issueCommand(*device, matmul_word0, matmul_word1, matmul_word2, matmul_word3);

    if (!waitEngineIdle(*device)) {
        cerr << "❌ MATMUL command timeout" << endl;
        return -1;
    }
    cout << "  ✓ MATMUL complete\n" << endl;

    // Read result count
    uint32_t result_count = device->mmioRead32(0, ENGINE_RESULT_COUNT);
    cout << "[7] Result count: " << dec << result_count << " FP16 values\n" << endl;

    // Read result BRAM (first 64 bytes = 32 FP16 values)
    cout << "[8] Reading result BRAM..." << endl;
    vector<uint8_t> result_data(64);
    device->dmaRead(BRAM_RESULT_BASE, 64, (char*)result_data.data());

    cout << "\nFirst 16 FP16 results (should match first line GFP data):" << endl;
    cout << "Index | FP16 Hex | Nibble | Expected (from left.hex byte)" << endl;
    cout << "------|----------|--------|------------------------------" << endl;

    for (int i = 0; i < 16; i++) {
        uint16_t fp16_val = result_data[i*2] | (result_data[i*2+1] << 8);

        // Extract nibble from first line
        int byte_idx = i / 2;
        int nibble_idx = i % 2;
        uint8_t byte_val = left_data[byte_idx];
        uint8_t nibble = (nibble_idx == 0) ? (byte_val & 0x0F) : ((byte_val >> 4) & 0x0F);

        cout << setw(5) << dec << i << " | 0x" << hex << setw(4) << setfill('0') << fp16_val;
        cout << " | 0x" << hex << (int)nibble;
        cout << " | Byte[" << dec << byte_idx << "]=" << hex << setw(2) << (int)byte_val;
        cout << " → nibble[" << dec << nibble_idx << "]=0x" << hex << (int)nibble << dec << endl;
    }

    cout << "\n=== Analysis ===" << endl;
    cout << "First line of left.hex should contain GFP nibbles." << endl;
    cout << "Each FP16 result = 0x3800 + nibble_value" << endl;
    cout << "If working correctly, FP16 values should correlate with hex file nibbles.\n" << endl;

    return 0;
}
