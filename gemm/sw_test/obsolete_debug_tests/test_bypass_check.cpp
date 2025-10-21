#include <iostream>
#include <iomanip>
#include <memory>
#include "vp815.hpp"

using namespace std;
using namespace achronix;

#define REG_ENGINE_BYPASS   0x24
#define REG_ENGINE_STATUS   0x08
#define REG_RESULT_COUNT    0x0C
#define RESULT_BRAM_BASE    0x4460008000ULL

int main() {
    cout << "\n=== Bypass Stage Verification ===" << endl;

    unique_ptr<VP815> device = make_unique<VP815>(0);
    cout << "✅ Device initialized\n" << endl;

    // Configure bypass mode 2
    device->mmioWrite32(0, REG_ENGINE_BYPASS, 0x2);
    
    uint32_t bypass_mode;
    device->mmioRead32(0, REG_ENGINE_BYPASS, bypass_mode);
    cout << "Bypass mode: " << (bypass_mode & 0x3) << "\n" << endl;

    // Read first 32 values from result BRAM
    cout << "Reading first 32 FP16 values from Result BRAM:\n" << endl;
    
    vector<uint8_t> result_data(64);
    device->dmaRead(RESULT_BRAM_BASE, 64, (char*)result_data.data());

    cout << "Pattern Analysis:" << endl;
    for (int i = 0; i < 16; i++) {
        uint16_t even_val = result_data[i*4] | (result_data[i*4+1] << 8);
        uint16_t odd_val = result_data[i*4+2] | (result_data[i*4+3] << 8);
        
        cout << "[" << setw(2) << i*2 << "] 0x" << hex << setw(4) << setfill('0') << even_val;
        cout << "  [" << setw(2) << dec << i*2+1 << "] 0x" << hex << setw(4) << setfill('0') << odd_val << dec << endl;
    }

    cout << "\n=== Analysis ===" << endl;
    cout << "If Stage 2a (test pattern): Even values increment, odd values all same (0x6001)" << endl;
    cout << "If Stage 2b (BRAM forward): Should see actual GFP data from first BRAM line" << endl;
    cout << "\nFirst line of left.hex contains: 06 06 06 07 06 06..." << endl;
    cout << "Each byte = 2 nibbles, so we should see pattern based on 0x6 and 0x0 nibbles\n" << endl;

    return 0;
}
