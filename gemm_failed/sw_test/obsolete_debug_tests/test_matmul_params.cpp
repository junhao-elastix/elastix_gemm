#include <iostream>
#include <iomanip>
#include <cstdint>
#include <vector>
#include <memory>
#include <unistd.h>
#include "vp815.hpp"

using namespace std;

const uint32_t ENGINE_REG_BASE = 10;  // MS2.0 Engine registers start at offset 10

// Register offsets within engine block
const uint32_t ENGINE_CMD_FIFO_W0 = ENGINE_REG_BASE + 0;
const uint32_t ENGINE_CMD_FIFO_W1 = ENGINE_REG_BASE + 1;
const uint32_t ENGINE_CMD_FIFO_W2 = ENGINE_REG_BASE + 2;
const uint32_t ENGINE_CMD_FIFO_W3 = ENGINE_REG_BASE + 3;
const uint32_t ENGINE_CMD_CTRL = ENGINE_REG_BASE + 4;
const uint32_t ENGINE_STATUS = ENGINE_REG_BASE + 5;
const uint32_t ENGINE_RESULT_COUNT = ENGINE_REG_BASE + 6;

// Opcodes
const uint32_t OPCODE_MATMUL = 0xF2;

int main(int argc, char* argv[]) {
    cout << "\n=== MS2.0 MATMUL Parameter Debug Test ===" << endl;
    cout << "Testing correct parameter encoding for cmd_tile_s structure" << endl;

    // Open device
    std::unique_ptr<achronix::VP815> device;
    try {
        device = std::make_unique<achronix::VP815>(0);
        std::cout << "✅ Device initialized successfully" << std::endl;
    } catch (const std::exception& e) {
        std::cerr << "❌ Failed to initialize device: " << e.what() << std::endl;
        return 1;
    }

    // Check engine idle
    uint32_t status;
    device->mmioRead32(0, ENGINE_STATUS * 4, status);
    if ((status & 0x7) != 0) {
        cerr << "ERROR: Engine not idle, status=0x" << hex << status << dec << endl;
        return 1;
    }

    cout << "\n=== cmd_tile_s Structure (87-bit packed struct) ===" << endl;
    cout << "Bits [86:79]: dim_b (8 bits) - Batch/rows" << endl;
    cout << "Bits [78:71]: dim_c (8 bits) - Columns" << endl;
    cout << "Bits [70:63]: dim_v (8 bits) - Vector count" << endl;
    cout << "Bits [62:55]: flags (8 bits)" << endl;
    cout << "Bits [54:44]: vec_len (11 bits)" << endl;
    cout << "Bits [43:33]: right_ugd_len (11 bits)" << endl;
    cout << "Bits [32:22]: left_ugd_len (11 bits)" << endl;
    cout << "Bits [21:11]: right_addr (11 bits)" << endl;
    cout << "Bits [10:0]:  left_addr (11 bits)" << endl;

    // Test parameters: B=4, C=4, V=32
    uint32_t dim_b = 4;
    uint32_t dim_c = 4;
    uint32_t dim_v = 32;
    uint32_t left_addr = 0;
    uint32_t right_addr = 528;
    uint32_t left_ugd_len = 4;   // Usually same as dim_b
    uint32_t right_ugd_len = 4;  // Usually same as dim_c
    uint32_t vec_len = 32;       // Usually same as dim_v
    uint32_t flags = 0x00;       // 8-bit mantissas, loop over left

    cout << "\n=== Test Parameters ===" << endl;
    cout << "dim_b = " << dim_b << " (output rows)" << endl;
    cout << "dim_c = " << dim_c << " (output cols)" << endl;
    cout << "dim_v = " << dim_v << " (vector count for reduction)" << endl;
    cout << "left_addr = " << left_addr << endl;
    cout << "right_addr = " << right_addr << endl;
    cout << "left_ugd_len = " << left_ugd_len << endl;
    cout << "right_ugd_len = " << right_ugd_len << endl;
    cout << "vec_len = " << vec_len << endl;

    cout << "\n=== Building 87-bit cmd_tile_s ===" << endl;

    // Build 87-bit structure (will span 3 32-bit words)
    // Word1 (bits 31:0): left_addr[10:0] | right_addr[21:11]
    // Word2 (bits 63:32): right_addr[21] | left_ugd[32:22] | right_ugd[43:33] | vec_len[54:44] | flags[62:55]
    // Word3 (bits 86:64): flags[62] | dim_v[70:63] | dim_c[78:71] | dim_b[86:79]

    uint32_t cmd_word1 = (left_addr & 0x7FF) | ((right_addr & 0x7FF) << 11) | ((left_ugd_len & 0x7FF) << 22);
    uint32_t cmd_word2 = ((left_ugd_len >> 10) & 0x1) | ((right_ugd_len & 0x7FF) << 1) |
                         ((vec_len & 0x7FF) << 12) | ((flags & 0xFF) << 23);
    uint32_t cmd_word3 = ((flags >> 1) & 0x7F) | ((dim_v & 0xFF) << 7) |
                         ((dim_c & 0xFF) << 15) | ((dim_b & 0x7F) << 23);

    cout << "Word1 = 0x" << hex << setw(8) << setfill('0') << cmd_word1 << dec << endl;
    cout << "Word2 = 0x" << hex << setw(8) << setfill('0') << cmd_word2 << dec << endl;
    cout << "Word3 = 0x" << hex << setw(8) << setfill('0') << cmd_word3 << dec << " (only bits [22:0] used)" << endl;

    cout << "\n=== Issuing MATMUL Command ===" << endl;

    // Command header: opcode | id | len | args_bytes
    uint32_t cmd_word0 = (OPCODE_MATMUL << 24) | (0x00 << 16) | (12 << 8) | 11; // 11 bytes of args

    // Write command to FIFO
    device->mmioWrite32(0, ENGINE_CMD_FIFO_W0 * 4, cmd_word0);
    device->mmioWrite32(0, ENGINE_CMD_FIFO_W1 * 4, cmd_word1);
    device->mmioWrite32(0, ENGINE_CMD_FIFO_W2 * 4, cmd_word2);
    device->mmioWrite32(0, ENGINE_CMD_FIFO_W3 * 4, cmd_word3);

    // Trigger command execution
    device->mmioWrite32(0, ENGINE_CMD_CTRL * 4, 0x01);  // Push command

    cout << "Command sent, waiting for completion..." << endl;

    // Wait for idle
    int timeout = 1000000;
    while (timeout-- > 0) {
        device->mmioRead32(0, ENGINE_STATUS * 4, status);
        if ((status & 0x7) == 0) break;
        usleep(1);
    }

    if (timeout <= 0) {
        cerr << "ERROR: Command timeout!" << endl;
        return 1;
    }

    // Check result count
    uint32_t result_count;
    device->mmioRead32(0, ENGINE_RESULT_COUNT * 4, result_count);
    cout << "\n=== Results ===" << endl;
    cout << "Status: 0x" << hex << status << dec << " (MC=" << (status & 0x3)
         << ", DC=" << ((status >> 2) & 0x3) << ", CE=" << ((status >> 4) & 0x3) << ")" << endl;
    cout << "Result count: " << result_count << " (expected: " << (dim_b * dim_c) << ")" << endl;

    if (result_count == 0) {
        cout << "\n❌ FAILURE: No results written!" << endl;
        cout << "This confirms the parameter encoding issue." << endl;
    } else if (result_count == dim_b * dim_c) {
        cout << "\n✅ SUCCESS: Correct number of results written!" << endl;
        cout << "The parameter encoding is correct." << endl;
    } else {
        cout << "\n⚠️ PARTIAL: Got " << result_count << " results, expected " << (dim_b * dim_c) << endl;
    }

    return (result_count == dim_b * dim_c) ? 0 : 1;
}