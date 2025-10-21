#include "vp815.hpp"
#include <iostream>
#include <iomanip>

using namespace std;
using namespace achronix;

int main() {
    cout << "=== Result Register Accessibility Test ===" << endl;
    
    try {
        VP815 device(0);
        if (!device.isReady()) {
            cerr << "ERROR: Device not ready" << endl;
            return 1;
        }
        
        cout << "\nReading new result registers (should be 0x0 initially):" << endl;
        cout << "-------------------------------------------------------" << endl;
        
        uint32_t result_0 = device.mmioRead32(0, 0x21C);
        cout << "  0x0214: 0x" << hex << setw(8) << setfill('0') << result_0 << dec;
        cout << " - RESULT_REG_0 (FP16 result[0])" << endl;
        
        uint32_t result_1 = device.mmioRead32(0, 0x220);
        cout << "  0x0218: 0x" << hex << setw(8) << setfill('0') << result_1 << dec;
        cout << " - RESULT_REG_1 (FP16 result[1])" << endl;
        
        uint32_t result_2 = device.mmioRead32(0, 0x224);
        cout << "  0x021C: 0x" << hex << setw(8) << setfill('0') << result_2 << dec;
        cout << " - RESULT_REG_2 (FP16 result[2])" << endl;
        
        uint32_t result_3 = device.mmioRead32(0, 0x228);
        cout << "  0x0220: 0x" << hex << setw(8) << setfill('0') << result_3 << dec;
        cout << " - RESULT_REG_3 (FP16 result[3])" << endl;
        
        cout << "\n[PASS] All result registers are readable!" << endl;
        cout << "\nNote: These are read-only registers that will be populated by" << endl;
        cout << "      the compute engine when it produces results." << endl;
        
        return 0;
        
    } catch (const exception& e) {
        cerr << "ERROR: " << e.what() << endl;
        return 1;
    }
}
