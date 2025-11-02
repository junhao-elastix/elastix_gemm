#include <iostream>
#include <iomanip>
#include "../../../eus/shell/devices/acx/vp815/api/vp815.hpp"

using namespace std;
using namespace achronix;

int main() {
    try {
        VP815 device(0);
        
        // Read dispatcher BRAM write count (0x60)
        uint32_t bram_wr_count = device.mmioRead32(0, 0x60);
        cout << "Dispatcher BRAM write count: " << (bram_wr_count & 0x3FF) << " lines" << endl;
        
        // Read result count
        uint32_t result_count = device.mmioRead32(0, 0x54);
        cout << "Result count: " << (result_count & 0xFFFF) << " FP16 values" << endl;
        
        return 0;
    } catch (const exception& e) {
        cerr << "ERROR: " << e.what() << endl;
        return 1;
    }
}
