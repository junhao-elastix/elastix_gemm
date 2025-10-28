#include <iostream>
#include <iomanip>
#include <cstdint>
#include <vector>
#include <memory>
#include <unistd.h>
#include "vp815.hpp"

using namespace std;

int main() {
    cout << "\n=== V_IDX Debug Test ===" << endl;
    cout << "Testing if dim_v is being passed correctly to compute engine" << endl;

    // Open device
    std::unique_ptr<achronix::VP815> device;
    try {
        device = std::make_unique<achronix::VP815>(0);
        std::cout << "✅ Device initialized" << std::endl;
    } catch (const std::exception& e) {
        std::cerr << "❌ Failed to initialize device: " << e.what() << std::endl;
        return 1;
    }

    // Read current state
    uint32_t status, result_count;
    device->mmioRead32(0, 15 * 4, status);
    device->mmioRead32(0, 16 * 4, result_count);

    cout << "\n=== Current State ===" << endl;
    cout << "Status register: 0x" << hex << status << dec << endl;
    cout << "  Master Control FSM: " << (status & 0x3) << endl;
    cout << "  Dispatcher FSM: " << ((status >> 2) & 0x3) << endl;
    cout << "  Compute Engine FSM: " << ((status >> 4) & 0x3) << endl;
    cout << "Result count: " << result_count << endl;

    // Issue a single MATMUL with known parameters
    cout << "\n=== Issuing Simple MATMUL ===" << endl;

    // First, need to have data in dispatcher BRAM
    // For this test, we'll skip the FETCH and just do MATMUL with whatever's in BRAM

    uint32_t dim_b = 1;  // Simplest case: 1x1 matrix
    uint32_t dim_c = 1;
    uint32_t dim_v = 1;  // Single vector - simplest case

    cout << "Test parameters: B=" << dim_b << ", C=" << dim_c << ", V=" << dim_v << endl;

    // Build the cmd_tile_s structure correctly
    // The structure in packed order (MSB to LSB):
    // [86:79] dim_b
    // [78:71] dim_c
    // [70:63] dim_v
    // [62:55] flags
    // [54:44] vec_len
    // [43:33] right_ugd_len
    // [32:22] left_ugd_len
    // [21:11] right_addr
    // [10:0]  left_addr

    uint32_t left_addr = 0;
    uint32_t right_addr = 0;
    uint32_t left_ugd_len = 1;
    uint32_t right_ugd_len = 1;
    uint32_t vec_len = 1;
    uint32_t flags = 0x00;

    // Pack into 87 bits across 3 words
    uint32_t cmd_word1 = (left_addr & 0x7FF) |
                         ((right_addr & 0x7FF) << 11) |
                         ((left_ugd_len & 0x7FF) << 22);

    uint32_t cmd_word2 = ((left_ugd_len >> 10) & 0x1) |
                         ((right_ugd_len & 0x7FF) << 1) |
                         ((vec_len & 0x7FF) << 12) |
                         ((flags & 0xFF) << 23);

    uint32_t cmd_word3 = ((flags >> 1) & 0x7F) |
                         ((dim_v & 0xFF) << 7) |
                         ((dim_c & 0xFF) << 15) |
                         ((dim_b & 0x7F) << 23);

    cout << "Command words:" << endl;
    cout << "  Word1: 0x" << hex << setw(8) << setfill('0') << cmd_word1 << dec << endl;
    cout << "  Word2: 0x" << hex << setw(8) << setfill('0') << cmd_word2 << dec << endl;
    cout << "  Word3: 0x" << hex << setw(8) << setfill('0') << cmd_word3 << dec << endl;

    // Issue command
    uint32_t cmd_word0 = (0xF2 << 24) | (0x00 << 16) | (12 << 8) | 11;

    device->mmioWrite32(0, 10 * 4, cmd_word0);
    device->mmioWrite32(0, 11 * 4, cmd_word1);
    device->mmioWrite32(0, 12 * 4, cmd_word2);
    device->mmioWrite32(0, 13 * 4, cmd_word3);
    device->mmioWrite32(0, 14 * 4, 0x01);  // Trigger

    cout << "Command issued, waiting..." << endl;

    // Wait for completion
    int timeout = 100000;
    while (timeout-- > 0) {
        device->mmioRead32(0, 15 * 4, status);
        if ((status & 0x7) == 0) break;
        usleep(10);
    }

    if (timeout <= 0) {
        cerr << "ERROR: Command timeout!" << endl;
        return 1;
    }

    // Read final state
    device->mmioRead32(0, 16 * 4, result_count);

    cout << "\n=== Final State ===" << endl;
    cout << "Status: 0x" << hex << status << dec << endl;
    cout << "Result count: " << result_count << " (expected: " << (dim_b * dim_c) << ")" << endl;

    if (result_count == 0) {
        cout << "\n❌ FAIL: No results written even for 1x1 matrix with V=1!" << endl;
        cout << "This suggests v_idx never reaches dim_v_reg-1, or" << endl;
        cout << "the result write logic has a timing/state issue." << endl;
    } else {
        cout << "\n✅ SUCCESS: Result written for simple case!" << endl;
    }

    return 0;
}