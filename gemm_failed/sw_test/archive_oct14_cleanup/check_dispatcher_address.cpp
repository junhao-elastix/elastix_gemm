// Check what data is at the dispatcher's calculated GDDR6 address
#include <iostream>
#include <iomanip>
#include <vector>
#include <cstring>
#include "vp815.hpp"

using namespace std;

int main() {
    // Initialize device
    achronix::VP815 device(0);
    cout << "Device initialized successfully" << endl;

    // Dispatcher calculates address as:
    // {GDDR6_PAGE_ID[9], Pad[2], Line[26], Byte[5]} = 42 bits
    // With GDDR6_PAGE_ID = 9'd2 = 0b000000010
    // For first line (line=0, byte=0):
    // Address = {9'b000000010, 2'b00, 26'd0, 5'd0} = 0b00000001000 << 33 = 0x200000000
    
    uint64_t dispatcher_addr_line0 = 0x200000000ULL;  // Page 2, Line 0
    
    cout << "\nDispatcher would read from: 0x" << hex << dispatcher_addr_line0 << dec << endl;
    
    // Try DMA read from this address
    vector<uint8_t> data(32);
    if (!device.dmaRead(dispatcher_addr_line0, 32, (char*)data.data())) {
        cerr << "ERROR: Failed to DMA read from dispatcher address" << endl;
        return 1;
    }

    cout << "First 32 bytes at dispatcher address:" << endl << "  ";
    for (size_t i = 0; i < 32; i++) {
        cout << setfill('0') << setw(2) << hex << (int)data[i] << " ";
    }
    cout << dec << endl;

    // Compare with what we wrote to 0x0
    vector<uint8_t> expected(32);
    if (!device.dmaRead(0x0, 32, (char*)expected.data())) {
        cerr << "ERROR: Failed to DMA read from 0x0" << endl;
        return 1;
    }

    cout << "\nFirst 32 bytes at 0x0 (where we wrote data):" << endl << "  ";
    for (size_t i = 0; i < 32; i++) {
        cout << setfill('0') << setw(2) << hex << (int)expected[i] << " ";
    }
    cout << dec << endl;

    // Check if they match
    bool match = (memcmp(data.data(), expected.data(), 32) == 0);
    
    if (match) {
        cout << "\n✅ Data at 0x" << hex << dispatcher_addr_line0 << " MATCHES data at 0x0" << dec << endl;
        cout << "This means the dispatcher is reading the correct data!" << endl;
    } else {
        cout << "\n❌ Data at 0x" << hex << dispatcher_addr_line0 << " DOES NOT MATCH data at 0x0" << dec << endl;
        cout << "This means the dispatcher is reading from the WRONG address!" << endl;
        cout << "\nPossible issue: GDDR6_PAGE_ID mismatch between DMA and dispatcher" << endl;
    }

    return match ? 0 : 1;
}

