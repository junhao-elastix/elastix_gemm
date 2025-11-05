#include <iostream>
#include <iomanip>
#include <memory>
#include <unistd.h>
#include "vp815.hpp"

using namespace std;
using namespace achronix;

#define ENGINE_DEBUG     0x44
#define ENGINE_CMD_WORD0 0x28
#define ENGINE_CMD_SUBMIT 0x38
#define OPCODE_MATMUL    0xF2

int main() {
    cout << "\n=== Command Queue Debug ===" << endl;

    unique_ptr<VP815> device = make_unique<VP815>(0);
    
    // Read initial debug state
    uint32_t debug = device->mmioRead32(0, ENGINE_DEBUG);
    uint32_t fifo_count = debug & 0x1FFF;
    uint32_t fifo_empty = (debug >> 31) & 0x1;
    
    cout << "Before command:" << endl;
    cout << "  ENGINE_DEBUG: 0x" << hex << debug << dec << endl;
    cout << "  FIFO count: " << fifo_count << endl;
    cout << "  FIFO empty: " << fifo_empty << "\n" << endl;

    // Issue MATMUL command
    cout << "Issuing MATMUL command..." << endl;
    uint32_t cmd = (OPCODE_MATMUL << 0) | (1 << 8) | (12 << 16);
    device->mmioWrite32(0, ENGINE_CMD_WORD0, cmd);
    device->mmioWrite32(0, ENGINE_CMD_WORD0+4, 0);  
    device->mmioWrite32(0, ENGINE_CMD_WORD0+8, (4 << 13) | (4 << 5));  
    device->mmioWrite32(0, ENGINE_CMD_WORD0+12, (32 << 8)); 
    device->mmioWrite32(0, ENGINE_CMD_SUBMIT, 0x1);

    // Read debug state after command
    usleep(1000);
    debug = device->mmioRead32(0, ENGINE_DEBUG);
    fifo_count = debug & 0x1FFF;
    fifo_empty = (debug >> 31) & 0x1;
    uint32_t submitted = (debug >> 16) & 0xFF;
    
    cout << "\nAfter command:" << endl;
    cout << "  ENGINE_DEBUG: 0x" << hex << debug << dec << endl;
    cout << "  FIFO count: " << fifo_count << endl;
    cout << "  FIFO empty: " << fifo_empty << endl;
    cout << "  Submitted count: " << submitted << endl;

    return 0;
}
