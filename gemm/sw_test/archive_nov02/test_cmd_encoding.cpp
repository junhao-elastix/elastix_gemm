// Quick test to verify command encoding
#include <iostream>
#include <iomanip>
using namespace std;

int main() {
    // Test DISPATCH word 1 encoding
    // Testbench: {8'b0, man_nv_cnt[7:0], 8'b0, ugd_vec_size[7:0]}
    // Software: (man_nv_cnt << 16) | ugd_vec_size
    
    uint8_t man_nv_cnt = 4;
    uint8_t ugd_vec_size = 2;
    
    uint32_t w1_tb = (0 << 24) | (man_nv_cnt << 16) | (0 << 8) | ugd_vec_size;
    uint32_t w1_sw = (static_cast<uint32_t>(man_nv_cnt) << 16) | static_cast<uint32_t>(ugd_vec_size);
    
    cout << "DISPATCH Word 1 Test:" << endl;
    cout << "  man_nv_cnt=" << (unsigned)man_nv_cnt << ", ugd_vec_size=" << (unsigned)ugd_vec_size << endl;
    cout << "  Testbench encoding: 0x" << hex << setw(8) << setfill('0') << w1_tb << dec << endl;
    cout << "  Software encoding: 0x" << hex << setw(8) << setfill('0') << w1_sw << dec << endl;
    cout << "  Match: " << (w1_tb == w1_sw ? "YES" : "NO") << endl;
    
    // Test MATMUL word 3 encoding
    // Testbench: {col_en, 5'b0, left_4b, right_4b, main_loop_left}
    // Software: ((col_en & 0xFFFFFF) << 8) | (leftMan4b ? 4u : 0u) | (rightMan4b ? 2u : 0u) | (mainLoopOverLeft ? 1u : 0u)
    
    uint32_t col_en = 0x0001;
    bool left_4b = false;
    bool right_4b = false;
    bool main_loop_left = false;
    
    uint32_t w3_tb = (col_en << 8) | (0 << 3) | (left_4b ? 4 : 0) | (right_4b ? 2 : 0) | (main_loop_left ? 1 : 0);
    uint32_t w3_sw = ((col_en & 0xFFFFFF) << 8) | (left_4b ? 4u : 0u) | (right_4b ? 2u : 0u) | (main_loop_left ? 1u : 0u);
    
    cout << "\nMATMUL Word 3 Test:" << endl;
    cout << "  col_en=0x" << hex << col_en << dec << ", left_4b=" << left_4b << ", right_4b=" << right_4b << ", main_loop_left=" << main_loop_left << endl;
    cout << "  Testbench encoding: 0x" << hex << setw(8) << setfill('0') << w3_tb << dec << endl;
    cout << "  Software encoding: 0x" << hex << setw(8) << setfill('0') << w3_sw << dec << endl;
    cout << "  Match: " << (w3_tb == w3_sw ? "YES" : "NO") << endl;
    
    return 0;
}
