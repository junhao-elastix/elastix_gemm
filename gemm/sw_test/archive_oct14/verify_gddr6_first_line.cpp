// Quick test to verify GDDR6 first line matches hex file
#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <iomanip>
#include "vp815.hpp"

using namespace std;

// GDDR6 base addresses (from test_ms2_gemm_full.cpp)
const uint64_t GDDR6_BASE_LEFT  = 0x0;  // Left matrix base address

int main() {
    // Initialize device
    achronix::VP815 device(0);
    cout << "Device initialized successfully" << endl;

    // Read first 32 bytes from GDDR6
    vector<uint8_t> gddr6_data(32);
    if (!device.dmaRead(GDDR6_BASE_LEFT, 32, (char*)gddr6_data.data())) {
        cerr << "ERROR: Failed to DMA read from GDDR6" << endl;
        return 1;
    }

    cout << "First 32 bytes from GDDR6 @ 0x" << hex << GDDR6_BASE_LEFT << dec << ":" << endl << "  ";
    for (size_t i = 0; i < 32; i++) {
        cout << setfill('0') << setw(2) << hex << (int)gddr6_data[i] << " ";
    }
    cout << dec << endl;

    // Read expected from hex file
    ifstream hex_file("../../hex/left.hex");
    if (!hex_file.is_open()) {
        cerr << "ERROR: Cannot open ../../hex/left.hex" << endl;
        return 1;
    }

    string line;
    getline(hex_file, line);
    hex_file.close();

    cout << "\nFirst line from left.hex:" << endl << "  " << line << endl;

    // Parse hex file line
    istringstream iss(line);
    vector<uint8_t> expected_data;
    string byte_str;
    while (iss >> byte_str) {
        expected_data.push_back(stoi(byte_str, nullptr, 16));
    }

    // Compare
    bool match = true;
    for (size_t i = 0; i < 32 && i < expected_data.size(); i++) {
        if (gddr6_data[i] != expected_data[i]) {
            if (match) {
                cout << "\nMISMATCH FOUND:" << endl;
                match = false;
            }
            cout << "  Byte " << i << ": GDDR6=0x" << hex << setw(2) << setfill('0')
                 << (int)gddr6_data[i] << ", expected=0x" << (int)expected_data[i] << dec << endl;
        }
    }

    if (match) {
        cout << "\n✅ GDDR6 data MATCHES hex file!" << endl;
    } else {
        cout << "\n❌ GDDR6 data DOES NOT MATCH hex file!" << endl;
    }

    return match ? 0 : 1;
}

