#include <iostream>
#include <iomanip>
using namespace std;

void analyze_fp16(uint16_t val) {
    uint16_t sign = (val >> 15) & 1;
    uint16_t exp = (val >> 10) & 0x1F;
    uint16_t frac = val & 0x3FF;
    
    cout << "  0x" << hex << setw(4) << setfill('0') << val << dec 
         << " = sign:" << sign << " exp:" << setw(2) << exp << " frac:0x" << hex << setw(3) << setfill('0') << frac << dec << endl;
}

int main() {
    cout << "B2_C2_V2 Results Analysis:" << endl;
    cout << "\nSimulation (correct):" << endl;
    analyze_fp16(0x0404);
    analyze_fp16(0x067e);
    analyze_fp16(0x842d);
    analyze_fp16(0x848d);
    
    cout << "\nHardware (wrong):" << endl;
    analyze_fp16(0x0735);
    analyze_fp16(0x0410);
    analyze_fp16(0x04c1);
    analyze_fp16(0x02d7);
    
    return 0;
}
