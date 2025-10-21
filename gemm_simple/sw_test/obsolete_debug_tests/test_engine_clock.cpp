#include <iostream>
#include <iomanip>
#include <cstring>
#include <memory>
#include <chrono>
#include <thread>
#include "vp815.hpp"

int main() {
    std::cout << "=== Engine Clock Diagnostic ===" << std::endl;
    
    // Initialize device
    std::unique_ptr<achronix::VP815> device;
    try {
        device = std::make_unique<achronix::VP815>(0);
        std::cout << "✅ Device initialized successfully\n" << std::endl;
    } catch (const std::exception& e) {
        std::cerr << "❌ Failed to initialize device: " << e.what() << std::endl;
        return 1;
    }

    // MS2.0 GEMM Engine Registers (from elastix_gemm_top.sv)
    const uint32_t ENGINE_CMD_WORD0   = 10;  // 0x28
    const uint32_t ENGINE_CMD_WORD1   = 11;  // 0x2C
    const uint32_t ENGINE_CMD_WORD2   = 12;  // 0x30
    const uint32_t ENGINE_CMD_SUBMIT  = 13;  // 0x34
    const uint32_t ENGINE_STATUS      = 14;  // 0x38
    const uint32_t ENGINE_MC_STATE    = 15;  // 0x3C
    const uint32_t ENGINE_DEBUG       = 16;  // 0x40
    
    std::cout << "\nPurpose: Monitor engine state registers to verify clock is running\n" << std::endl;

    // Helper function to extract state fields from ENGINE_STATUS
    auto extract_states = [](uint32_t status_reg) {
        struct States {
            uint8_t mc_state;
            uint8_t dc_state;
            uint8_t ce_state;
        };
        States s;
        s.mc_state = (status_reg >> 8) & 0xF;   // Bits [11:8]
        s.dc_state = (status_reg >> 4) & 0xF;   // Bits [7:4]
        s.ce_state = (status_reg >> 0) & 0xF;   // Bits [3:0]
        return s;
    };

    // Read initial state
    uint32_t status0;
    try {
        device->mmioRead32(0, ENGINE_STATUS * 4, status0);
        auto states0 = extract_states(status0);

        std::cout << "Initial State:" << std::endl;
        std::cout << "  ENGINE_STATUS = 0x" << std::hex << status0 << std::endl;
        std::cout << "  MC State: " << std::dec << (int)states0.mc_state << std::endl;
        std::cout << "  DC State: " << std::dec << (int)states0.dc_state << std::endl;
        std::cout << "  CE State: " << std::dec << (int)states0.ce_state << std::endl;
        std::cout << std::endl;

        // Monitor state changes over 10 seconds
        std::cout << "Monitoring state transitions for 10 seconds..." << std::endl;
        std::cout << "(If clock is running, states should change when issuing commands)" << std::endl;
        std::cout << std::endl;

        bool state_changed = false;
        for (int i = 0; i < 10; i++) {
            std::this_thread::sleep_for(std::chrono::seconds(1));

            uint32_t status_now;
            device->mmioRead32(0, ENGINE_STATUS * 4, status_now);
            auto states_now = extract_states(status_now);

            if (status_now != status0) {
                state_changed = true;
                std::cout << "  [t=" << (i+1) << "s] ⚠️  State changed!" << std::endl;
                std::cout << "    ENGINE_STATUS = 0x" << std::hex << status_now << std::endl;
                std::cout << "    MC: " << std::dec << (int)states_now.mc_state
                         << ", DC: " << (int)states_now.dc_state
                         << ", CE: " << (int)states_now.ce_state << std::endl;
                status0 = status_now;
            } else {
                std::cout << "  [t=" << (i+1) << "s] No change (MC=" << std::dec << (int)states_now.mc_state
                         << ", DC=" << (int)states_now.dc_state
                         << ", CE=" << (int)states_now.ce_state << ")" << std::endl;
            }
        }

        std::cout << std::endl;

        if (!state_changed) {
            std::cout << "✅ States remained stable (no spontaneous transitions)" << std::endl;
        }

        // Now try issuing a simple command to see if state transitions occur
        std::cout << "\n=== Issuing FETCH Command to Test State Transition ===" << std::endl;

        // Simple FETCH command: opcode=0xF0, id=0, len=12 (3-word payload)
        uint32_t cmd_word0 = (0xF0 << 0) | (0 << 8) | (12 << 16);
        uint32_t cmd_word1 = 0x0;  // GDDR6 address (chunk 0)
        uint32_t cmd_word2 = 0x100;  // Fetch 256 lines (small test)

        std::cout << "Writing command:" << std::endl;
        std::cout << "  CMD_WORD0 = 0x" << std::hex << cmd_word0 << std::endl;
        std::cout << "  CMD_WORD1 = 0x" << std::hex << cmd_word1 << std::endl;
        std::cout << "  CMD_WORD2 = 0x" << std::hex << cmd_word2 << std::endl;

        device->mmioWrite32(0, ENGINE_CMD_WORD0 * 4, cmd_word0);
        device->mmioWrite32(0, ENGINE_CMD_WORD1 * 4, cmd_word1);
        device->mmioWrite32(0, ENGINE_CMD_WORD2 * 4, cmd_word2);

        // Submit command
        device->mmioWrite32(0, ENGINE_CMD_SUBMIT * 4, 0x1);

        // Monitor state for 5 seconds
        std::cout << "\nMonitoring state after command submit..." << std::endl;

        uint32_t prev_status = status0;
        bool transition_detected = false;

        for (int i = 0; i < 50; i++) {  // 50 × 100ms = 5 seconds
            std::this_thread::sleep_for(std::chrono::milliseconds(100));

            uint32_t status_now;
            device->mmioRead32(0, ENGINE_STATUS * 4, status_now);
            auto states_now = extract_states(status_now);

            if (status_now != prev_status) {
                transition_detected = true;
                std::cout << "  [t=" << (i*100) << "ms] State changed!" << std::endl;
                std::cout << "    ENGINE_STATUS = 0x" << std::hex << status_now << std::endl;
                std::cout << "    MC: " << std::dec << (int)states_now.mc_state
                         << ", DC: " << (int)states_now.dc_state
                         << ", CE: " << (int)states_now.ce_state << std::endl;
                prev_status = status_now;
            }
        }

        std::cout << std::endl;

        // Read final state
        uint32_t status_final;
        device->mmioRead32(0, ENGINE_STATUS * 4, status_final);
        auto states_final = extract_states(status_final);

        std::cout << "Final State:" << std::endl;
        std::cout << "  ENGINE_STATUS = 0x" << std::hex << status_final << std::endl;
        std::cout << "  MC State: " << std::dec << (int)states_final.mc_state << std::endl;
        std::cout << "  DC State: " << std::dec << (int)states_final.dc_state << std::endl;
        std::cout << "  CE State: " << std::dec << (int)states_final.ce_state << std::endl;
        std::cout << std::endl;

        // Analysis
        if (!transition_detected) {
            std::cout << "❌ CRITICAL: NO state transitions detected!" << std::endl;
            std::cout << "   This indicates one of the following:" << std::endl;
            std::cout << "   1. i_nap_clk is not running to engine_wrapper" << std::endl;
            std::cout << "   2. nap_rstn is stuck asserted (reset never releases)" << std::endl;
            std::cout << "   3. State register update path is broken" << std::endl;
            std::cout << std::endl;
            std::cout << "   DC stuck at state " << std::dec << (int)states_final.dc_state << " confirms clock issue" << std::endl;
        } else {
            std::cout << "✅ State transitions detected - clock is running!" << std::endl;
            std::cout << "   Issue is likely in command processing logic or handshaking" << std::endl;
        }

    } catch (const std::exception& e) {
        std::cerr << "❌ Error during clock diagnostic: " << e.what() << std::endl;
        return 1;
    }
    
    return 0;
}