// Correct B=C=V=2 test using proper cmd_tile_s structure bit-packing
#include "vp815.hpp"
#include "Achronix_device.h"
#include <iostream>
#include <vector>
#include <cmath>
#include <iomanip>
#include <unistd.h>

using namespace std;
using namespace achronix;

#define OPCODE_FETCH            0xF0
#define OPCODE_DISPATCH         0xF1
#define OPCODE_MATMUL           0xF2
#define OPCODE_WAIT_DISPATCH    0xF3
#define OPCODE_WAIT_MATMUL      0xF4

#define ENGINE_CMD_WORD0        0x3C
#define ENGINE_CMD_WORD1        0x40
#define ENGINE_CMD_WORD2        0x44
#define ENGINE_CMD_WORD3        0x48
#define ENGINE_CMD_SUBMIT       0x4C
#define ENGINE_STATUS           0x50
#define ENGINE_RESULT_COUNT     0x54

#define RESULT_REG_0            0x21C
#define RESULT_REG_1            0x220
#define RESULT_REG_2            0x224
#define RESULT_REG_3            0x228

#define GDDR6_BASE_LEFT         0x0
#define GDDR6_BASE_RIGHT        0x1000

#define TEST_B  2
#define TEST_C  2
#define TEST_V  2

void issueCommand(VP815& device, uint32_t w0, uint32_t w1, uint32_t w2, uint32_t w3) {
    device.mmioWrite32(0, ENGINE_CMD_WORD0, w0);
    device.mmioWrite32(0, ENGINE_CMD_WORD1, w1);
    device.mmioWrite32(0, ENGINE_CMD_WORD2, w2);
    device.mmioWrite32(0, ENGINE_CMD_WORD3, w3);
    device.mmioWrite32(0, ENGINE_CMD_SUBMIT, 1);
    usleep(10000);
}

bool waitEngineIdle(VP815& device, int max_ms = 5000) {
    for (int i = 0; i < max_ms; i++) {
        uint32_t status = device.mmioRead32(0, ENGINE_STATUS);
        if ((status & 0x1) == 0) return true;
        usleep(1000);
    }
    return false;
}

float fp16_to_float(uint16_t fp16) {
    uint32_t sign = (fp16 >> 15) & 0x1;
    uint32_t exp = (fp16 >> 10) & 0x1F;
    uint32_t mant = fp16 & 0x3FF;
    
    if (exp == 0) {
        if (mant == 0) return sign ? -0.0f : 0.0f;
        float f = mant / 1024.0f;
        f = ldexpf(f, -14);
        return sign ? -f : f;
    }
    if (exp == 31) {
        return (mant == 0) ? (sign ? -INFINITY : INFINITY) : NAN;
    }
    
    float f = 1.0f + mant / 1024.0f;
    f = ldexpf(f, exp - 15);
    return sign ? -f : f;
}

int main() {
    cout << "=== B=C=V=2 Test with CORRECT cmd_tile_s Encoding ===" << endl;
    
    try {
        VP815 device(0);
        if (!device.isReady()) {
            cerr << "ERROR: Device not ready" << endl;
            return 1;
        }
        
        // Reset engine
        cout << "\n[1] Resetting..." << endl;
        device.mmioWrite32(0, 0x0, 0x10);
        usleep(100000);
        device.mmioWrite32(0, 0x0, 0x0);
        usleep(100000);
        
        // Prepare test data (GFP8 0x3C = ~1.0)
        cout << "\n[2] Preparing data (512 bytes = 4 Native Vectors each)..." << endl;
        vector<uint8_t> left_data(512, 0x3C);
        vector<uint8_t> right_data(512, 0x3C);
        
        // Write to GDDR6
        cout << "\n[3] Writing to GDDR6..." << endl;
        if (!device.dmaWrite(ACX_GDDR6_SPACE + GDDR6_BASE_LEFT, left_data.size(), (char*)left_data.data())) {
            cerr << "ERROR: Left write failed" << endl;
            return 1;
        }
        if (!device.dmaWrite(ACX_GDDR6_SPACE + GDDR6_BASE_RIGHT, right_data.size(), (char*)right_data.data())) {
            cerr << "ERROR: Right write failed" << endl;
            return 1;
        }
        cout << "  [PASS]" << endl;
        
        // FETCH left (16 lines)
        cout << "\n[4] FETCH left..." << endl;
        uint32_t w0 = (0x00 << 24) | (12 << 16) | (0 << 8) | OPCODE_FETCH;
        uint32_t w1 = GDDR6_BASE_LEFT / 32;
        uint32_t w2 = (16 << 16);
        issueCommand(device, w0, w1, w2, 0);
        if (!waitEngineIdle(device)) {
            cerr << "ERROR: Timeout" << endl;
            return 1;
        }
        cout << "  [PASS]" << endl;
        
        // FETCH right (16 lines)
        cout << "\n[5] FETCH right..." << endl;
        w0 = (0x00 << 24) | (12 << 16) | (1 << 8) | OPCODE_FETCH;
        w1 = GDDR6_BASE_RIGHT / 32;
        w2 = (16 << 16);
        issueCommand(device, w0, w1, w2, 0);
        if (!waitEngineIdle(device)) {
            cerr << "ERROR: Timeout" << endl;
            return 1;
        }
        cout << "  [PASS]" << endl;
        
        // DISPATCH left
        cout << "\n[6] DISPATCH left..." << endl;
        w0 = (0x00 << 24) | (8 << 16) | (3 << 8) | OPCODE_DISPATCH;
        w1 = (0 << 22) | (128 << 11) | 0;  // man_4b=0, len=128, tile_addr=0
        issueCommand(device, w0, w1, 0, 0);
        if (!waitEngineIdle(device)) {
            cerr << "ERROR: Timeout" << endl;
            return 1;
        }
        cout << "  [PASS]" << endl;
        
        // WAIT_DISPATCH left
        cout << "\n[7] WAIT_DISPATCH left..." << endl;
        w0 = (0x00 << 24) | (3 << 16) | (0 << 8) | OPCODE_WAIT_DISPATCH;
        issueCommand(device, w0, 0, 0, 0);
        if (!waitEngineIdle(device)) {
            cerr << "ERROR: Timeout" << endl;
            return 1;
        }
        cout << "  [PASS]" << endl;
        
        // DISPATCH right
        cout << "\n[8] DISPATCH right..." << endl;
        w0 = (0x00 << 24) | (8 << 16) | (5 << 8) | OPCODE_DISPATCH;
        w1 = (0 << 22) | (128 << 11) | (GDDR6_BASE_RIGHT / 32);
        issueCommand(device, w0, w1, 0, 0);
        if (!waitEngineIdle(device)) {
            cerr << "ERROR: Timeout" << endl;
            return 1;
        }
        cout << "  [PASS]" << endl;
        
        // WAIT_DISPATCH right
        cout << "\n[9] WAIT_DISPATCH right..." << endl;
        w0 = (0x00 << 24) | (5 << 16) | (0 << 8) | OPCODE_WAIT_DISPATCH;
        issueCommand(device, w0, 0, 0, 0);
        if (!waitEngineIdle(device)) {
            cerr << "ERROR: Timeout" << endl;
            return 1;
        }
        cout << "  [PASS]" << endl;
        
        // MATMUL with CORRECT cmd_tile_s bit packing
        cout << "\n[10] MATMUL (B=2, C=2, V=2) with CORRECT encoding..." << endl;
        
        // Parameters matching simulation:
        uint32_t left_addr = 0;
        uint32_t right_addr = 0;  // Dispatcher already handled address translation
        uint32_t left_ugd_len = 1;   // From simulation
        uint32_t right_ugd_len = 1;  // From simulation
        uint32_t vec_len = TEST_V;   // From simulation: vec_len = dim_v
        uint32_t flags = 0;
        uint32_t dim_v = TEST_V;
        uint32_t dim_c = TEST_C;
        uint32_t dim_b = TEST_B;
        
        // Correct bit packing per cmd_tile_s structure:
        // [10:0]:   left_addr       (11 bits)
        // [21:11]:  right_addr      (11 bits)
        // [32:22]:  left_ugd_len    (11 bits)  <-- THIS WAS THE BUG!
        // [43:33]:  right_ugd_len   (11 bits)
        // [54:44]:  vec_len         (11 bits)
        // [62:55]:  flags           (8 bits)
        // [70:63]:  dim_v           (8 bits)
        // [78:71]:  dim_c           (8 bits)
        // [86:79]:  dim_b           (8 bits)
        
        uint32_t payload_bits_31_0 = (left_addr & 0x7FF) |          // [10:0]
                                      ((right_addr & 0x7FF) << 11) |  // [21:11]
                                      ((left_ugd_len & 0x7FF) << 22); // [32:22] - 10 bits fit in word1
        
        uint32_t payload_bits_63_32 = ((left_ugd_len >> 10) & 0x1) |  // [32] - 11th bit of left_ugd_len
                                       ((right_ugd_len & 0x7FF) << 1) | // [43:33]
                                       ((vec_len & 0x7FF) << 12) |       // [54:44]
                                       ((flags & 0xFF) << 23) |          // [62:55]
                                       ((dim_v & 0xFF) << 31);           // [70:63] - only LSB fits in word2
        
        uint32_t payload_bits_86_64 = ((dim_v >> 1) & 0x7F) |          // [70:64] - upper 7 bits of dim_v
                                       ((dim_c & 0xFF) << 7) |           // [78:71]
                                       ((dim_b & 0xFF) << 15);           // [86:79]
        
        w0 = (0x00 << 24) | (12 << 16) | (9 << 8) | OPCODE_MATMUL;
        w1 = payload_bits_31_0;
        w2 = payload_bits_63_32;
        uint32_t w3 = payload_bits_86_64;
        
        cout << "  Encoded command:" << endl;
        cout << "    word0: 0x" << hex << setw(8) << setfill('0') << w0 << dec << endl;
        cout << "    word1: 0x" << hex << setw(8) << setfill('0') << w1 << dec << endl;
        cout << "    word2: 0x" << hex << setw(8) << setfill('0') << w2 << dec << endl;
        cout << "    word3: 0x" << hex << setw(8) << setfill('0') << w3 << dec << endl;
        
        issueCommand(device, w0, w1, w2, w3);
        if (!waitEngineIdle(device)) {
            cerr << "ERROR: Timeout" << endl;
            return 1;
        }
        cout << "  [PASS]" << endl;
        
        // WAIT_MATMUL
        cout << "\n[11] WAIT_MATMUL..." << endl;
        w0 = (0x00 << 24) | (4 << 16) | (0 << 8) | OPCODE_WAIT_MATMUL;
        issueCommand(device, w0, 0, 0, 0);
        if (!waitEngineIdle(device)) {
            cerr << "ERROR: Timeout" << endl;
            return 1;
        }
        cout << "  [PASS]" << endl;
        
        // Read results
        cout << "\n[12] Reading results..." << endl;
        uint32_t result_count = device.mmioRead32(0, ENGINE_RESULT_COUNT);
        uint32_t bcv_dims = device.mmioRead32(0, 0x24);
        
        cout << "  ENGINE_RESULT_COUNT: " << (result_count & 0xFFFF) << " FP16 values" << endl;
        cout << "  BCV_DIMS: 0x" << hex << bcv_dims << dec;
        cout << " (B=" << ((bcv_dims >> 24) & 0xFF);
        cout << ", C=" << ((bcv_dims >> 16) & 0xFF);
        cout << ", V=" << ((bcv_dims >> 8) & 0xFF) << ")" << endl;
        
        uint32_t r[4];
        r[0] = device.mmioRead32(0, RESULT_REG_0);
        r[1] = device.mmioRead32(0, RESULT_REG_1);
        r[2] = device.mmioRead32(0, RESULT_REG_2);
        r[3] = device.mmioRead32(0, RESULT_REG_3);
        
        cout << "\n  Results:" << endl;
        for (int i = 0; i < 4; i++) {
            uint16_t fp16 = r[i] & 0xFFFF;
            float val = fp16_to_float(fp16);
            cout << "    result[" << i << "]: 0x" << hex << setw(4) << setfill('0') << fp16;
            cout << " → " << fixed << setprecision(6) << val << dec << endl;
        }
        
        if ((result_count & 0xFFFF) == 4) {
            cout << "\n[SUCCESS] Got expected 4 results!" << endl;
            return 0;
        } else {
            cout << "\n[PARTIAL] Got " << (result_count & 0xFFFF) << " results instead of 4" << endl;
            return 1;
        }
        
    } catch (const exception& e) {
        cerr << "ERROR: " << e.what() << endl;
        return 1;
    }
}
