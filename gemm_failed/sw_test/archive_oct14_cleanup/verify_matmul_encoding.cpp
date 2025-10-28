#include <iostream>
#include <iomanip>
using namespace std;

int main() {
    // Test encoding with B=2, C=2, V=2
    uint32_t left_addr = 0;
    uint32_t right_addr = 0x1000 / 32;  // 0x80
    uint32_t left_ugd = 128;
    uint32_t right_ugd = 128;
    uint32_t vec_len = 128;
    uint32_t flags = 0;
    uint32_t dim_v = 2;
    uint32_t dim_c = 2;
    uint32_t dim_b = 2;
    
    // Pack into words
    uint32_t w1 = ((left_ugd & 0x3FF) << 22) | ((right_addr & 0x7FF) << 11) | (left_addr & 0x7FF);
    uint32_t w2 = ((dim_v & 0x1) << 31) | ((flags & 0xFF) << 23) | ((vec_len & 0x7FF) << 12) | 
                  ((right_ugd & 0x7FF) << 1) | ((left_ugd >> 10) & 0x1);
    uint32_t w3 = ((dim_b & 0xFF) << 15) | ((dim_c & 0xFF) << 7) | ((dim_v >> 1) & 0x7F);
    uint32_t w0 = (0x00 << 24) | (12 << 16) | (9 << 8) | 0xF2;
    
    cout << "MATMUL Command Encoding (B=2, C=2, V=2):" << endl;
    cout << "  word0: 0x" << hex << setw(8) << setfill('0') << w0 << dec;
    cout << " (opcode=0x" << hex << (w0 & 0xFF) << ", id=" << dec << ((w0 >> 8) & 0xFF);
    cout << ", len=" << ((w0 >> 16) & 0xFF) << ")" << endl;
    cout << "  word1: 0x" << hex << setw(8) << setfill('0') << w1 << dec << endl;
    cout << "  word2: 0x" << hex << setw(8) << setfill('0') << w2 << dec << endl;
    cout << "  word3: 0x" << hex << setw(8) << setfill('0') << w3 << dec << endl;
    
    // Decode word3 to verify
    uint8_t decoded_b = (w3 >> 15) & 0xFF;
    uint8_t decoded_c = (w3 >> 7) & 0xFF;
    uint8_t decoded_v_upper = w3 & 0x7F;
    uint8_t decoded_v_lsb = (w2 >> 31) & 0x1;
    uint8_t decoded_v = (decoded_v_upper << 1) | decoded_v_lsb;
    
    cout << "\nDecoded dimensions:" << endl;
    cout << "  dim_b: " << (int)decoded_b << endl;
    cout << "  dim_c: " << (int)decoded_c << endl;
    cout << "  dim_v: " << (int)decoded_v << endl;
    
    return 0;
}
