#include <iostream>
#include <iomanip>
using namespace std;

int main() {
    uint32_t w3 = 0x00010101;
    
    cout << "word3 = 0x" << hex << w3 << dec << endl;
    cout << "Binary: ";
    for (int i = 31; i >= 0; i--) {
        cout << ((w3 >> i) & 1);
        if (i % 8 == 0) cout << " ";
    }
    cout << endl;
    
    // The packing is: ((dim_b & 0xFF) << 15) | ((dim_c & 0xFF) << 7) | ((dim_v >> 1) & 0x7F)
    // So to decode:
    // dim_b = (w3 >> 15) & 0xFF
    // dim_c = (w3 >> 7) & 0xFF
    // dim_v_upper = w3 & 0x7F
    
    uint8_t dim_b = (w3 >> 15) & 0xFF;
    uint8_t dim_c = (w3 >> 7) & 0xFF;
    uint8_t dim_v_upper = w3 & 0x7F;
    
    cout << "\nDecode attempt 1:" << endl;
    cout << "  dim_b (bits [22:15]) = (0x" << hex << w3 << " >> 15) & 0xFF = 0x" << (int)dim_b << dec << " = " << (int)dim_b << endl;
    cout << "  dim_c (bits [14:7]) = (0x" << hex << w3 << " >> 7) & 0xFF = 0x" << hex << (int)dim_c << dec << " = " << (int)dim_c << endl;
    cout << "  dim_v[7:1] (bits [6:0]) = 0x" << hex << w3 << " & 0x7F = 0x" << hex << (int)dim_v_upper << dec << " = " << (int)dim_v_upper << endl;
    
    // Reconstruct dim_v with LSB from word2
    uint8_t dim_v = (dim_v_upper << 1);  // Assuming dim_v[0] = 0 for now
    cout << "  dim_v (reconstructed, assuming LSB=0) = " << (int)dim_v << endl;
    
    return 0;
}
