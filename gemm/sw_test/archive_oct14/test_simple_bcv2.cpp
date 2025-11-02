// Simple B=C=V=2 test using correct MS2.0 command format
#include "vp815.hpp"
#include "Achronix_device.h"
#include <iostream>
#include <vector>
#include <cmath>
#include <iomanip>
#include <unistd.h>

using namespace std;
using namespace achronix;

// MS2.0 Command Opcodes (from test_ms2_gemm_full.cpp)
#define OPCODE_FETCH            0xF0
#define OPCODE_DISPATCH         0xF1
#define OPCODE_MATMUL           0xF2
#define OPCODE_WAIT_DISPATCH    0xF3
#define OPCODE_WAIT_MATMUL      0xF4

// Engine registers (CORRECTED - from RTL register map)
#define ENGINE_CMD_WORD0        0x3C
#define ENGINE_CMD_WORD1        0x40
#define ENGINE_CMD_WORD2        0x44
#define ENGINE_CMD_WORD3        0x48
#define ENGINE_CMD_SUBMIT       0x4C
#define ENGINE_STATUS           0x50  // FIXED: was 0x30
#define ENGINE_RESULT_COUNT     0x54  // FIXED: was 0x34
#define ENGINE_DEBUG            0x58  // last_opcode[11:4], mc_state[3:0], cmd_fifo_count[19:12]

// Result registers
#define RESULT_REG_0            0x21C
#define RESULT_REG_1            0x220
#define RESULT_REG_2            0x224
#define RESULT_REG_3            0x228

// GDDR6 addresses
#define GDDR6_BASE_LEFT         0x0
#define GDDR6_BASE_RIGHT        0x1000  // 4KB offset

// Parameters: B=2, C=2, V=2
#define TEST_B  2
#define TEST_C  2
#define TEST_V  2

void issueCommand(VP815& device, uint32_t w0, uint32_t w1, uint32_t w2, uint32_t w3) {
    device.mmioWrite32(0, ENGINE_CMD_WORD0, w0);
    device.mmioWrite32(0, ENGINE_CMD_WORD1, w1);
    device.mmioWrite32(0, ENGINE_CMD_WORD2, w2);
    device.mmioWrite32(0, ENGINE_CMD_WORD3, w3);
    device.mmioWrite32(0, ENGINE_CMD_SUBMIT, 1);
    
    // Read ENGINE_STATUS immediately to catch state transitions
    uint32_t status_immediate = device.mmioRead32(0, ENGINE_STATUS);
    uint8_t mc_state_imm = (status_immediate >> 12) & 0xF;
    uint8_t dc_state_imm = (status_immediate >> 8) & 0xF;
    uint8_t ce_state_imm = (status_immediate >> 4) & 0xF;
    bool busy_imm = status_immediate & 0x1;
    
    usleep(10000);  // 10ms for command processing
    
    // Read again after settling
    uint32_t engine_debug = device.mmioRead32(0, ENGINE_DEBUG);
    uint32_t status_final = device.mmioRead32(0, ENGINE_STATUS);
    uint8_t last_opcode = (engine_debug >> 4) & 0xF;
    uint8_t mc_state_final = engine_debug & 0xF;
    
    cout << "    [DEBUG] immediate: busy=" << busy_imm 
         << " mc=" << hex << (int)mc_state_imm 
         << " dc=" << (int)dc_state_imm 
         << " ce=" << (int)ce_state_imm << dec << endl;
    cout << "    [DEBUG] final: last_op=0x" << hex << (int)last_opcode 
         << " mc=0x" << (int)mc_state_final << dec << endl;
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
    cout << "=== Simple B=C=V=2 Test ===" << endl;
    cout << "Using correct MS2.0 command format" << endl;
    
    try {
        VP815 device(0);
        if (!device.isReady()) {
            cerr << "ERROR: Device not ready" << endl;
            return 1;
        }
        
        // Reset engine
        cout << "\n[1] Resetting engine..." << endl;
        uint32_t status_before = device.mmioRead32(0, ENGINE_STATUS);
        cout << "  Status before reset: 0x" << hex << setw(8) << setfill('0') << status_before << dec;
        cout << " (busy=" << (status_before & 0x1) << ")" << endl;
        
        device.mmioWrite32(0, 0x0, 0x10);
        usleep(100000);  // 100ms
        device.mmioWrite32(0, 0x0, 0x0);
        usleep(100000);  // 100ms
        
        uint32_t status_after = device.mmioRead32(0, ENGINE_STATUS);
        cout << "  Status after reset: 0x" << hex << setw(8) << setfill('0') << status_after << dec;
        cout << " (busy=" << (status_after & 0x1) << ")" << endl;
        
        if (status_after & 0x1) {
            cerr << "WARNING: Engine still busy after reset!" << endl;
        }
        
        // Prepare simple test data: all 1.0 in GFP8 format (0x3C)
        // For B=2, C=2, V=2:
        //   Left: B×V = 2×2 = 4 Native Vectors = 4×128 GFP8 = 512 bytes → 16 lines × 32 bytes
        //   Right: V×C = 2×2 = 4 Native Vectors = 4×128 GFP8 = 512 bytes → 16 lines × 32 bytes
        cout << "\n[2] Preparing test data..." << endl;
        vector<uint8_t> left_data(512, 0x3C);   // 4 NVs × 128 elements = 512 bytes
        vector<uint8_t> right_data(512, 0x3C);  // 4 NVs × 128 elements = 512 bytes
        
        cout << "  Left: " << left_data.size() << " bytes = " << (left_data.size()/128) << " Native Vectors" << endl;
        cout << "  Right: " << right_data.size() << " bytes = " << (right_data.size()/128) << " Native Vectors" << endl;
        
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
        cout << "  [PASS] Data written" << endl;
        
        // FETCH left (16 lines = 512 bytes from address 0)
        cout << "\n[4] FETCH left..." << endl;
        uint32_t left_lines = (left_data.size() + 31) / 32;
        uint32_t w0 = (0x00 << 24) | (12 << 16) | (0 << 8) | OPCODE_FETCH;
        uint32_t w1 = GDDR6_BASE_LEFT / 32;
        uint32_t w2 = (left_lines << 16);  // 16 lines
        issueCommand(device, w0, w1, w2, 0);
        if (!waitEngineIdle(device)) {
            cerr << "ERROR: FETCH left timeout" << endl;
            return 1;
        }
        cout << "  [PASS] Fetched " << left_lines << " lines" << endl;
        
        // FETCH right (16 lines = 512 bytes from address 0x1000)
        cout << "\n[5] FETCH right..." << endl;
        uint32_t right_lines = (right_data.size() + 31) / 32;
        w0 = (0x00 << 24) | (12 << 16) | (1 << 8) | OPCODE_FETCH;
        w1 = GDDR6_BASE_RIGHT / 32;
        w2 = (right_lines << 16);  // 16 lines
        issueCommand(device, w0, w1, w2, 0);
        if (!waitEngineIdle(device)) {
            cerr << "ERROR: FETCH right timeout" << endl;
            return 1;
        }
        cout << "  [PASS] Fetched " << right_lines << " lines" << endl;
        
        // DISPATCH left (id=3, tile_addr=0, len=128 NVs)
        cout << "\n[6] DISPATCH left..." << endl;
        uint32_t man_4b_8b_n = 0;  // 8-bit mantissa mode
        w0 = (0x00 << 24) | (8 << 16) | (3 << 8) | OPCODE_DISPATCH;
        w1 = (man_4b_8b_n << 22) | (128 << 11) | 0;  // len=128, tile_addr=0
        issueCommand(device, w0, w1, 0, 0);
        if (!waitEngineIdle(device)) {
            cerr << "ERROR: DISPATCH left timeout" << endl;
            return 1;
        }
        cout << "  [PASS]" << endl;
        
        // WAIT_DISPATCH left (id=3)
        cout << "\n[7] WAIT_DISPATCH left..." << endl;
        w0 = (0x00 << 24) | (3 << 16) | (0 << 8) | OPCODE_WAIT_DISPATCH;
        issueCommand(device, w0, 0, 0, 0);
        if (!waitEngineIdle(device)) {
            cerr << "ERROR: WAIT_DISPATCH left timeout" << endl;
            return 1;
        }
        cout << "  [PASS]" << endl;
        
        // DISPATCH right (id=5, tile_addr=0x1000/32, len=128 NVs)
        cout << "\n[8] DISPATCH right..." << endl;
        w0 = (0x00 << 24) | (8 << 16) | (5 << 8) | OPCODE_DISPATCH;
        w1 = (man_4b_8b_n << 22) | (128 << 11) | (GDDR6_BASE_RIGHT / 32);  // len=128, tile_addr
        issueCommand(device, w0, w1, 0, 0);
        if (!waitEngineIdle(device)) {
            cerr << "ERROR: DISPATCH right timeout" << endl;
            return 1;
        }
        cout << "  [PASS]" << endl;
        
        // WAIT_DISPATCH right (id=5)
        cout << "\n[9] WAIT_DISPATCH right..." << endl;
        w0 = (0x00 << 24) | (5 << 16) | (0 << 8) | OPCODE_WAIT_DISPATCH;
        issueCommand(device, w0, 0, 0, 0);
        if (!waitEngineIdle(device)) {
            cerr << "ERROR: WAIT_DISPATCH right timeout" << endl;
            return 1;
        }
        cout << "  [PASS]" << endl;
        
        // MATMUL (TILE) with B=2, C=2, V=2
        // CORRECTED: Use simulation parameters (left_ugd_len=1, right_ugd_len=1, vec_len=dim_v)
        cout << "\n[10] MATMUL (B=2, C=2, V=2)..." << endl;
        uint32_t left_addr = 0;
        uint32_t right_addr = GDDR6_BASE_RIGHT / 32;  // In 32-byte units
        uint32_t left_ugd = 1;      // CORRECTED: Should be 1, not 128!
        uint32_t right_ugd = 1;     // CORRECTED: Should be 1, not 128!
        uint32_t flags = 0;
        uint32_t dim_v = TEST_V;
        uint32_t dim_c = TEST_C;
        uint32_t dim_b = TEST_B;
        uint32_t vec_len = dim_v;   // CORRECTED: Should be dim_v, not 128!
        
        // Pack into words following cmd_tile_s format:
        w1 = ((left_ugd & 0x3FF) << 22) | ((right_addr & 0x7FF) << 11) | (left_addr & 0x7FF);
        w2 = ((dim_v & 0x1) << 31) | ((flags & 0xFF) << 23) | ((vec_len & 0x7FF) << 12) | 
             ((right_ugd & 0x7FF) << 1) | ((left_ugd >> 10) & 0x1);
        uint32_t w3 = ((dim_b & 0xFF) << 15) | ((dim_c & 0xFF) << 7) | ((dim_v >> 1) & 0x7F);
        w0 = (0x00 << 24) | (12 << 16) | (9 << 8) | OPCODE_MATMUL;
        
        issueCommand(device, w0, w1, w2, w3);
        if (!waitEngineIdle(device)) {
            cerr << "ERROR: MATMUL timeout" << endl;
            return 1;
        }
        cout << "  [PASS]" << endl;
        
        // WAIT_MATMUL
        cout << "\n[11] WAIT_MATMUL..." << endl;
        w0 = (0x00 << 24) | (4 << 16) | (0 << 8) | OPCODE_WAIT_MATMUL;
        issueCommand(device, w0, 0, 0, 0);
        if (!waitEngineIdle(device)) {
            cerr << "ERROR: WAIT_MATMUL timeout" << endl;
            return 1;
        }
        cout << "  [PASS]" << endl;
        
        // Read results and debug registers
        cout << "\n[12] Reading results..." << endl;
        uint32_t result_count = device.mmioRead32(0, ENGINE_RESULT_COUNT);
        uint32_t engine_status = device.mmioRead32(0, ENGINE_STATUS);
        uint32_t bcv_debug = device.mmioRead32(0, 0x20);  // BCV_DEBUG
        uint32_t bcv_dims = device.mmioRead32(0, 0x24);   // BCV_DIMS
        uint32_t mc_dims = device.mmioRead32(0, 0x28);    // MC_DIMS
        
        cout << "  ENGINE_RESULT_COUNT: " << (result_count & 0xFFFF) << " FP16 values" << endl;
        cout << "  ENGINE_STATUS: 0x" << hex << setw(8) << setfill('0') << engine_status << dec << endl;
        cout << "  BCV_DEBUG: 0x" << hex << bcv_debug << dec << endl;
        cout << "  BCV_DIMS: 0x" << hex << bcv_dims << dec;
        cout << " (B=" << ((bcv_dims >> 24) & 0xFF);
        cout << ", C=" << ((bcv_dims >> 16) & 0xFF);
        cout << ", V=" << ((bcv_dims >> 8) & 0xFF) << ")" << endl;
        cout << "  MC_DIMS: 0x" << hex << mc_dims << dec;
        cout << " (dim_b=" << ((mc_dims >> 16) & 0xFF);
        cout << ", dim_c=" << ((mc_dims >> 8) & 0xFF);
        cout << ", dim_v=" << (mc_dims & 0xFF) << ")" << endl;
        
        uint32_t r[4];
        r[0] = device.mmioRead32(0, RESULT_REG_0);
        r[1] = device.mmioRead32(0, RESULT_REG_1);
        r[2] = device.mmioRead32(0, RESULT_REG_2);
        r[3] = device.mmioRead32(0, RESULT_REG_3);
        
        cout << "\n  Results (hex):" << endl;
        for (int i = 0; i < 4; i++) {
            uint16_t fp16 = r[i] & 0xFFFF;
            float val = fp16_to_float(fp16);
            cout << "    result[" << i << "]: 0x" << hex << setw(4) << setfill('0') << fp16 << dec;
            cout << " → " << fixed << setprecision(6) << val << endl;
        }
        
        bool has_results = (result_count & 0xFFFF) > 0;
        if (has_results) {
            cout << "\n[SUCCESS] Compute engine produced results!" << endl;
        } else {
            cout << "\n[FAIL] No results produced" << endl;
            return 1;
        }
        
        return 0;
        
    } catch (const exception& e) {
        cerr << "ERROR: " << e.what() << endl;
        return 1;
    }
}
