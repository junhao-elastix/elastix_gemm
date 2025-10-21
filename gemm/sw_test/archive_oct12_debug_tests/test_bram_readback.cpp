// test_bram_readback.cpp - Verify BRAM contents after DISP commands
// Purpose: Check if input matrices are correctly loaded into dispatcher BRAM
// This helps isolate whether the problem is input data or compute engine

#include <iostream>
#include <iomanip>
#include <fstream>
#include <vector>
#include <cstdint>
#include <unistd.h>
#include <cmath>
#include "../../../eus/shell/devices/acx/vp815/api/vp815.hpp"

using namespace std;
using namespace achronix;

// Register offsets (133-register configuration - Oct 10, 2025)
#define ENGINE_CMD_WORD0        0x3C    // Command word 0 (opcode)
#define ENGINE_CMD_WORD1        0x40    // Command word 1
#define ENGINE_CMD_WORD2        0x44    // Command word 2
#define ENGINE_CMD_WORD3        0x48    // Command word 3
#define ENGINE_CMD_SUBMIT       0x4C    // Submit trigger
#define ENGINE_STATUS           0x50    // {CE[3:0], DC[3:0], MC[3:0], busy}
#define ENGINE_RESULT_COUNT     0x54    // FP16 result count
#define ENGINE_DEBUG            0x58    // Debug register

// Command opcodes
#define CMD_FETCH               0xF0
#define CMD_DISP                0xF1
#define CMD_TILE                0xF2
#define CMD_WAIT_DISP           0xF3
#define CMD_WAIT_TILE           0xF4

// Result BRAM base address (from elastix_gemm_top.sv)
#define RESULT_BRAM_BASE        0x4460008000ULL

// Helper: Submit command
void submit_command(VP815& device, uint32_t w0, uint32_t w1, uint32_t w2, uint32_t w3) {
    device.mmioWrite32(0, ENGINE_CMD_WORD0, w0);
    device.mmioWrite32(0, ENGINE_CMD_WORD1, w1);
    device.mmioWrite32(0, ENGINE_CMD_WORD2, w2);
    device.mmioWrite32(0, ENGINE_CMD_WORD3, w3);
    device.mmioWrite32(0, ENGINE_CMD_SUBMIT, 1);  // Trigger
}

// Helper: Wait for command completion
bool wait_for_idle(VP815& device, int max_polls = 1000) {
    for (int i = 0; i < max_polls; i++) {
        uint32_t status = device.mmioRead32(0, ENGINE_STATUS);
        if ((status & 0x1) == 0) {  // Check busy bit
            return true;
        }
        usleep(1000);  // 1ms
    }
    return false;
}

// Helper: Load test data to GDDR6 (simple pattern for verification)
void load_test_pattern_to_gddr6(VP815& device) {
    cout << "\n[INFO] Loading test pattern to GDDR6..." << endl;
    
    // Channel 0 GDDR6 base address (from hardware mapping)
    uint64_t gddr6_base = 0x1A00000000ULL;
    
    // Create simple test patterns:
    // Left matrix (128x128 GFP8): Each Native Vector has increasing exponents
    // Right matrix (128x128 GFP8): Each Native Vector has constant exponents
    
    vector<uint8_t> left_matrix(128 * 128);   // 16,384 bytes
    vector<uint8_t> right_matrix(128 * 128);  // 16,384 bytes
    
    // Left matrix: exp[group] = group number (0-31), mantissas = sequential
    for (int nv = 0; nv < 128; nv++) {
        for (int byte = 0; byte < 128; byte++) {
            if (byte < 4) {
                // Exponent bytes: exp[0]=0, exp[1]=1, exp[2]=2, exp[3]=3
                left_matrix[nv * 128 + byte] = byte;
            } else {
                // Mantissa bytes: sequential pattern
                left_matrix[nv * 128 + byte] = (nv + byte) & 0xFF;
            }
        }
    }
    
    // Right matrix: exp[group] = 5 (constant), mantissas = 0x42
    for (int nv = 0; nv < 128; nv++) {
        for (int byte = 0; byte < 128; byte++) {
            if (byte < 4) {
                // Exponent bytes: all groups have exp=5
                right_matrix[nv * 128 + byte] = 5;
            } else {
                // Mantissa bytes: constant 0x42 pattern
                right_matrix[nv * 128 + byte] = 0x42;
            }
        }
    }
    
    // Write to GDDR6
    cout << "  Writing left matrix to GDDR6 @ 0x" << hex << gddr6_base << "..." << endl;
    device.dmaWrite(gddr6_base, left_matrix.size(), (char*)left_matrix.data());
    
    uint64_t right_base = gddr6_base + 16896;  // 528 lines * 32 bytes/line
    cout << "  Writing right matrix to GDDR6 @ 0x" << hex << right_base << "..." << endl;
    device.dmaWrite(right_base, right_matrix.size(), (char*)right_matrix.data());
    
    cout << "  Test pattern loaded successfully!" << dec << endl;
}

// Helper: Read BRAM via result BRAM interface
void read_bram_contents(VP815& device, const string& name, uint64_t start_addr, int num_lines) {
    cout << "\n[INFO] Reading " << name << " from BRAM..." << endl;
    cout << "  Base address: 0x" << hex << start_addr << dec << endl;
    cout << "  Lines to read: " << num_lines << " (256-bit each = 32 bytes)" << endl;
    
    vector<uint8_t> buffer(num_lines * 32);
    device.dmaRead(start_addr, buffer.size(), (char*)buffer.data());
    
    // Display first 8 lines (8 Native Vectors)
    cout << "\n  First 8 Native Vectors (256-bit lines):" << endl;
    for (int line = 0; line < min(8, num_lines); line++) {
        cout << "    NV[" << dec << setw(3) << line << "]: ";
        
        // Show first 16 bytes only (out of 32)
        for (int byte = 0; byte < 16; byte++) {
            cout << hex << setw(2) << setfill('0') 
                 << (int)buffer[line * 32 + byte] << " ";
        }
        cout << "..." << endl;
    }
    
    // Check for expected pattern in left matrix
    if (name == "Left Matrix") {
        bool pattern_ok = true;
        int errors = 0;
        
        // Check first NV exponents (should be 0,1,2,3)
        for (int i = 0; i < 4; i++) {
            if (buffer[i] != i) {
                if (errors < 10) {
                    cout << "    ERROR: exp[" << i << "] = 0x" << hex 
                         << (int)buffer[i] << ", expected 0x" << i << dec << endl;
                }
                pattern_ok = false;
                errors++;
            }
        }
        
        if (pattern_ok) {
            cout << "    [PASS] Left matrix exponents match expected pattern!" << endl;
        } else {
            cout << "    [FAIL] Left matrix has " << errors << " errors!" << endl;
        }
    }
    
    // Check for expected pattern in right matrix
    if (name == "Right Matrix") {
        bool pattern_ok = true;
        int errors = 0;
        
        // Check first NV exponents (should be all 5)
        for (int i = 0; i < 4; i++) {
            if (buffer[i] != 5) {
                if (errors < 10) {
                    cout << "    ERROR: exp[" << i << "] = 0x" << hex 
                         << (int)buffer[i] << ", expected 0x05" << dec << endl;
                }
                pattern_ok = false;
                errors++;
            }
        }
        
        // Check mantissa bytes (should be all 0x42)
        for (int i = 4; i < 32; i++) {
            if (buffer[i] != 0x42) {
                if (errors < 10) {
                    cout << "    ERROR: man[" << i << "] = 0x" << hex 
                         << (int)buffer[i] << ", expected 0x42" << dec << endl;
                }
                pattern_ok = false;
                errors++;
            }
        }
        
        if (pattern_ok) {
            cout << "    [PASS] Right matrix matches expected pattern!" << endl;
        } else {
            cout << "    [FAIL] Right matrix has " << errors << " errors!" << endl;
        }
    }
    
    cout << endl;
}

int main() {
    cout << "=== MS2.0 GEMM BRAM Readback Test ===" << endl;
    cout << "Purpose: Verify input data is correctly loaded into dispatcher BRAM\n" << endl;
    
    try {
        // Open device (device ID 0 = first Achronix device)
        VP815 device(0);  // Device index 0
        cout << "[OK] Device opened successfully" << endl;
        
        // Load test pattern to GDDR6
        load_test_pattern_to_gddr6(device);
        
        // Issue FETCH commands to load data into dispatcher BRAM
        cout << "\n[STEP 1] Issuing FETCH commands..." << endl;
        
        // FETCH left matrix (528 lines from GDDR6 address 0)
        uint32_t fetch1_w0 = (CMD_FETCH << 0) | (1 << 8) | (12 << 16);  // op=FETCH, id=1, len=12
        uint32_t fetch1_w1 = 0;           // GDDR6 address 0 (in 128B chunks)
        uint32_t fetch1_w2 = 528;         // 528 lines
        submit_command(device, fetch1_w0, fetch1_w1, fetch1_w2, 0);
        cout << "  FETCH[1]: addr=0, lines=528 (left matrix)" << endl;
        
        if (!wait_for_idle(device, 5000)) {
            cout << "[ERROR] FETCH[1] timeout!" << endl;
            return 1;
        }
        cout << "  FETCH[1] completed" << endl;
        
        // FETCH right matrix (528 lines from GDDR6 address 528)
        uint32_t fetch2_w0 = (CMD_FETCH << 0) | (2 << 8) | (12 << 16);  // op=FETCH, id=2, len=12
        uint32_t fetch2_w1 = 528;         // GDDR6 address 528 (in 128B chunks)
        uint32_t fetch2_w2 = 528;         // 528 lines
        submit_command(device, fetch2_w0, fetch2_w1, fetch2_w2, 0);
        cout << "  FETCH[2]: addr=528, lines=528 (right matrix)" << endl;
        
        if (!wait_for_idle(device, 5000)) {
            cout << "[ERROR] FETCH[2] timeout!" << endl;
            return 1;
        }
        cout << "  FETCH[2] completed" << endl;
        
        // Issue DISP commands
        cout << "\n[STEP 2] Issuing DISP commands..." << endl;
        
        // DISP left matrix (addr=0, len=128 NVs)
        uint32_t disp1_w0 = (CMD_DISP << 0) | (3 << 8) | (4 << 16);  // op=DISP, id=3, len=4
        uint32_t disp1_w1 = (0 << 21) | (128 << 10) | (0 << 0);  // addr=0, len=128, man_4b=0
        submit_command(device, disp1_w0, disp1_w1, 0, 0);
        cout << "  DISP[3]: tile_addr=0, len=128 (left matrix)" << endl;
        
        if (!wait_for_idle(device)) {
            cout << "[ERROR] DISP[3] timeout!" << endl;
            return 1;
        }
        
        // DISP right matrix (addr=528, len=128 NVs)
        uint32_t disp2_w0 = (CMD_DISP << 0) | (5 << 8) | (4 << 16);  // op=DISP, id=5, len=4
        uint32_t disp2_w1 = (528 << 21) | (128 << 10) | (0 << 0);  // addr=528, len=128, man_4b=0
        submit_command(device, disp2_w0, disp2_w1, 0, 0);
        cout << "  DISP[5]: tile_addr=528, len=128 (right matrix)" << endl;
        
        if (!wait_for_idle(device)) {
            cout << "[ERROR] DISP[5] timeout!" << endl;
            return 1;
        }
        
        cout << "\n[STEP 3] DISP commands completed, BRAM should be loaded" << endl;
        
        // Unfortunately, we cannot directly read dispatcher BRAM from PCIe
        // It's internal to the FPGA fabric, not mapped to BAR space
        // We need to use the compute engine to process data and check results
        
        cout << "\n[INFO] Dispatcher BRAM is internal to FPGA - cannot read directly via PCIe" << endl;
        cout << "[INFO] Solution: Add debug registers to expose BRAM contents" << endl;
        cout << "[INFO] OR: Run compute operation and verify results" << endl;
        
        // Alternative: Run a simple TILE operation with known inputs
        cout << "\n[STEP 4] Running simple TILE operation (B=1, C=1, V=1)..." << endl;
        
        // TILE: left_addr=0, right_addr=528, B=1, C=1, V=1
        uint32_t tile_w0 = (CMD_TILE << 0) | (4 << 8) | (10 << 16);  // op=TILE, id=4, len=10
        // Build TILE command: 87-bit structure packed into 3 words
        // [86:79]=dim_b, [78:71]=dim_c, [70:63]=dim_v, [62:52]=left_addr, [51:41]=right_addr, ...
        uint32_t tile_w1 = (0 << 21) | (528 << 10) | (128 << 0);  // left_addr=0, right_addr=528, left_ugd_len=128[9:0]
        uint32_t tile_w2 = (128 << 21) | (1 << 13) | (1 << 5) | (0 << 0);  // right_ugd_len=128, vec_len=128, dim_b=1, dim_c[7:6]=0
        uint32_t tile_w3 = (1 << 24) | (1 << 16) | (0 << 0);  // dim_c[5:0]=1, dim_v=1, flags=0
        
        submit_command(device, tile_w0, tile_w1, tile_w2, tile_w3);
        cout << "  TILE[4]: B=1, C=1, V=1, left_addr=0, right_addr=528" << endl;
        
        // Wait for completion (with timeout)
        cout << "  Waiting for TILE completion..." << endl;
        if (!wait_for_idle(device, 10000)) {
            cout << "[ERROR] TILE timeout!" << endl;
            return 1;
        }
        
        uint32_t result_count = device.mmioRead32(0, ENGINE_RESULT_COUNT);
        cout << "  TILE completed: result_count=" << result_count << endl;
        
        if (result_count != 1) {
            cout << "[WARNING] Expected 1 result (B=1×C=1), got " << result_count << endl;
        }
        
        // Read result from result BRAM
        cout << "\n[STEP 5] Reading result from result BRAM..." << endl;
        uint16_t result_fp16;
        device.dmaRead(RESULT_BRAM_BASE, sizeof(result_fp16), (char*)&result_fp16);
        
        cout << "  Result[0] (FP16): 0x" << hex << result_fp16 << dec << endl;
        
        // Decode FP16
        uint16_t sign = (result_fp16 >> 15) & 0x1;
        uint16_t exp = (result_fp16 >> 10) & 0x1F;
        uint16_t man = result_fp16 & 0x3FF;
        
        cout << "    Sign: " << sign << endl;
        cout << "    Exponent: " << exp << " (biased, bias=15)" << endl;
        cout << "    Mantissa: 0x" << hex << man << dec << endl;
        
        // Convert to float for display
        float value = 0.0f;
        if (exp == 0) {
            // Subnormal
            value = (sign ? -1.0f : 1.0f) * pow(2.0f, -14.0f) * (man / 1024.0f);
        } else if (exp == 31) {
            // Inf or NaN
            value = (man == 0) ? (sign ? -INFINITY : INFINITY) : NAN;
        } else {
            // Normal
            value = (sign ? -1.0f : 1.0f) * pow(2.0f, (int)exp - 15) * (1.0f + man / 1024.0f);
        }
        
        cout << "    Float value: " << value << endl;
        
        cout << "\n=== Test Complete ===" << endl;
        cout << "[INFO] To fully verify BRAM contents, add debug registers in RTL" << endl;
        cout << "[INFO] See Option 2 for result format verification" << endl;
        
        return 0;
        
    } catch (const exception& e) {
        cerr << "[ERROR] Exception: " << e.what() << endl;
        return 1;
    }
}

