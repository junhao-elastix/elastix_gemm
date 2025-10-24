#pragma once

#include <cstdint>
#include <vector>
#include <string>
#include <iostream>
#include <fstream>
#include <sstream>
#include <chrono>
#include "../../../eus/shell/devices/acx/vp815/api/vp815.hpp"
#include "Achronix_device.h"
#include "Achronix_util.h"

// ============================================================================
// VP815 MS2.0 GEMM Engine Device Wrapper (Simplified)
// ============================================================================

// ---------------------- Register Offsets (BAR0) ----------------------------
constexpr uint32_t MS2_CMD_WORD0      = 0x3C;
constexpr uint32_t MS2_CMD_WORD1      = 0x40;
constexpr uint32_t MS2_CMD_WORD2      = 0x44;
constexpr uint32_t MS2_CMD_WORD3      = 0x48;
constexpr uint32_t MS2_CMD_SUBMIT     = 0x4C;
constexpr uint32_t MS2_STATUS         = 0x50;
constexpr uint32_t MS2_RESULT_COUNT   = 0x54;

// --------------------------- Microcode Opcodes -----------------------------
constexpr uint8_t  OPC_FETCH          = 0xF0;
constexpr uint8_t  OPC_DISPATCH       = 0xF1;
constexpr uint8_t  OPC_MATMUL         = 0xF2;
constexpr uint8_t  OPC_WAIT_DISPATCH  = 0xF3;
constexpr uint8_t  OPC_WAIT_MATMUL    = 0xF4;

// -------------------------- Memory Layout ----------------------------------
constexpr uint64_t GDDR6_BASE_LEFT    = 0x0ULL;
constexpr uint64_t GDDR6_BASE_RIGHT   = 0x4200ULL;

// ============================================================================
// VP815GemmDevice - Simplified GEMM Engine Wrapper
// ============================================================================
class VP815GemmDevice {
public:
    explicit VP815GemmDevice(achronix::VP815& device) 
        : device_(device), current_id_(0) {}

    // ---------------------- Soft Reset --------------------------------------
    void soft_reset() {
        mmio_write32(0, 0x0, 0x2);  // Assert reset
        mmio_write32(0, 0x0, 0x0);  // Deassert
    }

    // ---------------------- Wait for Engine Idle ----------------------------
    bool wait_idle(uint32_t timeout_ms = 5000) {
        auto start = std::chrono::steady_clock::now();
        while (true) {
            uint32_t status = mmio_read32(0, MS2_STATUS);
            if ((status & 0x1) == 0) {
                return true;
            }
            auto elapsed = std::chrono::duration_cast<std::chrono::milliseconds>(
                std::chrono::steady_clock::now() - start).count();
            if (elapsed > (long long)timeout_ms) {
                std::cerr << "ERROR: Engine timeout after " << timeout_ms << "ms" << std::endl;
                std::cerr << "ENGINE_STATUS: 0x" << std::hex << status << std::dec << std::endl;
                return false;
            }
        }
    }

    // ---------------------- Command ID Management ---------------------------
    uint8_t next_cmd_id() {
        uint8_t id = current_id_;
        current_id_ = static_cast<uint8_t>((current_id_ + 1) & 0xFF);
        return id;
    }

    void reset_cmd_id() {
        current_id_ = 0;
    }

    // ---------------------- FETCH Command -----------------------------------
    uint8_t fetch(uint32_t startAddr, uint16_t length, bool fetch_right = false) {
        uint8_t id = next_cmd_id();
        uint32_t w0 = build_word0(OPC_FETCH, id, 12);
        uint32_t w1 = startAddr / 32;  // Address in 32-byte units
        uint32_t w2 = length | (fetch_right ? (1 << 16) : 0);
        uint32_t w3 = 0x00000000;
        issue_command(w0, w1, w2, w3);
        return id;
    }

    // ---------------------- DISPATCH Command --------------------------------
    uint8_t dispatch(uint16_t tileAddr, uint16_t length, bool man4b = false) {
        uint8_t id = next_cmd_id();
        uint32_t man_4b_8b_n = man4b ? 1 : 0;
        uint32_t w0 = build_word0(OPC_DISPATCH, id, 8);
        uint32_t w1 = (man_4b_8b_n << 22) | (length << 11) | tileAddr;
        issue_command(w0, w1, 0, 0);
        return id;
    }

    // ---------------------- WAIT_DISPATCH Command ---------------------------
    uint8_t waitDispatch(uint8_t waitId) {
        uint8_t id = next_cmd_id();
        uint32_t w0 = (0x00 << 24) | (static_cast<uint32_t>(waitId) << 16) | 
                      (static_cast<uint32_t>(id) << 8) | OPC_WAIT_DISPATCH;
        issue_command(w0, 0, 0, 0);
        return id;
    }

    // ---------------------- MATMUL (TILE) Command ---------------------------
    // AMD-compatible signature: leftUgdLen=B, rightUgdLen=C, vecLen=V
    // These are used both as dimensions AND ugd_len values in hardware encoding
    uint8_t tile(uint16_t leftAddr, uint16_t rightAddr, 
                 uint16_t leftUgdLen, uint16_t rightUgdLen, uint16_t vecLen,
                 bool leftMan4b = false, bool rightMan4b = false, 
                 bool mainLoopOverLeft = true) {
        uint8_t id = next_cmd_id();
        
        // Pack flags
        uint32_t flags_val = (leftMan4b ? 0x01 : 0x00) | 
                            (rightMan4b ? 0x02 : 0x00) | 
                            (mainLoopOverLeft ? 0x04 : 0x00);
        
        // Pack into words following cmd_tile_s bit layout (87-bit payload)
        // Word1: left_ugd[9:0], right_addr[10:0], left_addr[10:0]
        uint32_t w1 = ((leftUgdLen & 0x3FF) << 22) | 
                      ((rightAddr & 0x7FF) << 11) | 
                      (leftAddr & 0x7FF);
        
        // Word2: dim_v[0], flags[7:0], vec_len[10:0], right_ugd[10:0], left_ugd[10]
        uint32_t w2 = ((vecLen & 0x1) << 31) | 
                      ((flags_val & 0xFF) << 23) |
                      ((vecLen & 0x7FF) << 12) | 
                      ((rightUgdLen & 0x7FF) << 1) |
                      ((leftUgdLen >> 10) & 0x1);
        
        // Word3: dim_v[7:1], dim_c[7:0], dim_b[7:0]
        uint32_t w3 = ((leftUgdLen & 0xFF) << 15) | 
                      ((rightUgdLen & 0xFF) << 7) | 
                      ((vecLen >> 1) & 0x7F);
        
        uint32_t w0 = build_word0(OPC_MATMUL, id, 12);
        issue_command(w0, w1, w2, w3);
        return id;
    }

    // ---------------------- WAIT_MATMUL Command -----------------------------
    uint8_t waitTile(uint8_t waitId) {
        uint8_t id = next_cmd_id();
        uint32_t w0 = (0x00 << 24) | (static_cast<uint32_t>(waitId) << 16) | 
                      (static_cast<uint32_t>(id) << 8) | OPC_WAIT_MATMUL;
        issue_command(w0, 0, 0, 0);
        return id;
    }

    // ---------------------- DMA Wrappers ------------------------------------
    bool dma_write(uint64_t addr, const void* buf, size_t size) {
        return device_.dmaWrite(addr, size, const_cast<char*>(
            reinterpret_cast<const char*>(buf)));
    }

    bool dma_read(uint64_t addr, void* buf, size_t size) {
        return device_.dmaRead(addr, size, reinterpret_cast<char*>(buf));
    }

    // ---------------------- MMIO Wrappers -----------------------------------
    uint32_t mmio_read32(uint32_t bar, uint64_t offset) {
        return device_.mmioRead32(bar, offset);
    }

    void mmio_write32(uint32_t bar, uint64_t offset, uint32_t val) {
        device_.mmioWrite32(bar, offset, val);
    }

    // ---------------------- Load Hex Matrix ---------------------------------
    bool loadHexMatrix(const std::string& filename, std::vector<uint8_t>& data) {
        std::ifstream file(filename);
        if (!file.is_open()) {
            std::cerr << "ERROR: Cannot open hex file: " << filename << std::endl;
            return false;
        }

        data.clear();
        data.reserve(528 * 32);

        std::string line;
        int line_num = 0;

        while (std::getline(file, line)) {
            if (line.empty()) continue;

            std::istringstream iss(line);
            std::string hex_val;
            int byte_count = 0;

            while (iss >> hex_val) {
                if (byte_count >= 32) {
                    std::cerr << "ERROR: Line " << line_num << " has more than 32 bytes" << std::endl;
                    return false;
                }

                uint8_t val = (uint8_t)std::strtoul(hex_val.c_str(), NULL, 16);
                data.push_back(val);
                byte_count++;
            }

            if (byte_count != 32) {
                std::cerr << "ERROR: Line " << line_num << " has " << byte_count
                         << " bytes, expected 32" << std::endl;
                return false;
            }

            line_num++;
        }

        if (line_num != 528) {
            std::cerr << "ERROR: Expected 528 lines in hex file, got " << line_num << std::endl;
            return false;
        }

        return true;
    }

private:
    achronix::VP815& device_;
    uint8_t current_id_;

    // Build command word0
    uint32_t build_word0(uint8_t opcode, uint8_t id, uint8_t len_field) {
        return (0x00u << 24) | (uint32_t(len_field) << 16) | 
               (uint32_t(id) << 8) | uint32_t(opcode);
    }

    // Issue command to hardware
    void issue_command(uint32_t w0, uint32_t w1, uint32_t w2, uint32_t w3) {
        mmio_write32(0, MS2_CMD_WORD0, w0);
        mmio_write32(0, MS2_CMD_WORD1, w1);
        mmio_write32(0, MS2_CMD_WORD2, w2);
        mmio_write32(0, MS2_CMD_WORD3, w3);
        mmio_write32(0, MS2_CMD_SUBMIT, 0x1);
    }
};

