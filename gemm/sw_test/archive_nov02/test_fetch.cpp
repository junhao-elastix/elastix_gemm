#include <iostream>
#include <iomanip>
#include <unistd.h>
#include "../../../eus/shell/devices/acx/vp815/api/vp815.hpp"
#include "Achronix_device.h"
#include "Achronix_util.h"

using namespace std;
using namespace achronix;

#define MS2_CMD_WORD0      0x3C
#define MS2_CMD_WORD1      0x40
#define MS2_CMD_WORD2      0x44
#define MS2_CMD_WORD3      0x48
#define MS2_CMD_SUBMIT     0x4C
#define MS2_STATUS         0x50
#define DC_BRAM_WR_COUNT   0x60
#define OPC_FETCH          0xF0

int main() {
    try {
        VP815 device(0);
        
        // Reset engine
        device.mmioWrite32(0, 0x0, 0x2);
        device.mmioWrite32(0, 0x0, 0x0);
        
        cout << "Testing FETCH operation..." << endl;
        cout << "BRAM write count before FETCH: " << (device.mmioRead32(0, DC_BRAM_WR_COUNT) & 0x3FF) << endl;
        
        // Issue FETCH LEFT command
        uint32_t w0 = (0x00 << 24) | (16 << 16) | (0 << 8) | OPC_FETCH;
        uint32_t w1 = 0 / 32;  // Address 0 in line units
        uint32_t w2 = 528;     // 528 lines
        uint32_t w3 = 0;       // fetch_right=0 (left)
        
        cout << "FETCH command: w0=0x" << hex << setw(8) << setfill('0') << w0
             << " w1=0x" << w1 << " w2=0x" << w2 << " w3=0x" << w3 << dec << endl;
        
        device.mmioWrite32(0, MS2_CMD_WORD0, w0);
        device.mmioWrite32(0, MS2_CMD_WORD1, w1);
        device.mmioWrite32(0, MS2_CMD_WORD2, w2);
        device.mmioWrite32(0, MS2_CMD_WORD3, w3);
        device.mmioWrite32(0, MS2_CMD_SUBMIT, 0x1);
        
        // Wait for completion
        for (int i = 0; i < 1000; i++) {
            uint32_t status = device.mmioRead32(0, MS2_STATUS);
            if ((status & 0x1) == 0) break;
            usleep(100);
        }
        
        uint32_t wr_count = device.mmioRead32(0, DC_BRAM_WR_COUNT) & 0x3FF;
        uint32_t status = device.mmioRead32(0, MS2_STATUS);
        cout << "BRAM write count after FETCH:  " << wr_count << endl;
        cout << "Expected: 528 lines" << endl;
        cout << "Final status: 0x" << hex << setw(8) << setfill('0') << status << dec << endl;
        cout << "  MC state: " << ((status >> 12) & 0xF) << endl;
        cout << "  DC state: " << ((status >> 8) & 0xF) << endl;
        cout << "  Busy: " << ((status & 0x1) ? "YES" : "NO") << endl;
        
        if (wr_count == 528) {
            cout << "✅ FETCH operation working!" << endl;
        } else {
            cout << "❌ FETCH operation FAILED!" << endl;
        }
        
        return 0;
    } catch (const exception& e) {
        cerr << "ERROR: " << e.what() << endl;
        return 1;
    }
}
