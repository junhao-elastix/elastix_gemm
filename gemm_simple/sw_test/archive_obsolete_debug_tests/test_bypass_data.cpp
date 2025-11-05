#include <iostream>
#include <iomanip>
#include <vector>
#include <memory>
#include "vp815.hpp"

using namespace std;
using namespace achronix;

// Register offsets
#define REG_ENGINE_BYPASS   0x24
#define REG_RESULT_COUNT    0x0C

// BRAM addresses
#define RESULT_BRAM_BASE    0x4460008000ULL

int main() {
    cout << "\n=== Stage 2b Data Verification ===" << endl;

    // Initialize device
    unique_ptr<VP815> device;
    try {
        device = make_unique<VP815>(0);
        cout << "✅ Device initialized successfully\n" << endl;
    } catch (const exception& e) {
        cerr << "❌ Failed to initialize device: " << e.what() << endl;
        return -1;
    }

    // Read result count
    uint32_t result_count;
    device->mmioRead32(0, REG_RESULT_COUNT, result_count);
    cout << "Result count register: " << dec << result_count << " FP16 values\n" << endl;

    // Read first 64 FP16 values from result BRAM
    cout << "Reading first 64 FP16 values from Result BRAM:" << endl;
    cout << "Address: 0x" << hex << RESULT_BRAM_BASE << dec << "\n" << endl;

    vector<uint8_t> result_data(256);  // 128 bytes = 64 FP16 values
    try {
        device->dmaRead(RESULT_BRAM_BASE, 256, (char*)result_data.data());
    } catch (const exception& e) {
        cerr << "❌ DMA read failed: " << e.what() << endl;
        return -1;
    }

    // Display as FP16 values (16 values per row)
    cout << "Index | FP16 Hex | Decoded" << endl;
    cout << "------|----------|--------" << endl;
    
    for (int i = 0; i < 64; i++) {
        uint16_t fp16_val = result_data[i*2] | (result_data[i*2+1] << 8);
        
        // Decode FP16
        uint16_t sign = (fp16_val >> 15) & 0x1;
        uint16_t exp5 = (fp16_val >> 10) & 0x1F;
        uint16_t man10 = fp16_val & 0x3FF;
        
        cout << setw(5) << dec << i << " | ";
        cout << "0x" << hex << setw(4) << setfill('0') << fp16_val << " | ";
        cout << "s=" << dec << sign << " e=" << setw(2) << exp5 << " m=0x" << hex << setw(3) << man10;
        
        if (i % 16 == 15) cout << "\n";
        else cout << endl;
    }

    cout << "\n=== Expected Data from First Line ===" << endl;
    cout << "First line of left.hex: 06 06 06 07 06 06 06 06 ..." << endl;
    cout << "Each byte contains 2 nibbles (4-bit values)" << endl;
    cout << "Byte 0x06 = nibbles [0x6, 0x0]" << endl;
    cout << "We extract 4-bit values and convert to FP16 with simple mapping\n" << endl;

    return 0;
}
