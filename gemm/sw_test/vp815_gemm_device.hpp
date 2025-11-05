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
// VP815 MS2.0 GEMM Engine Device Wrapper (4-Word Command Format)
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
// VP815GemmDevice - MS2.0 GEMM Engine Wrapper with 4-Word Command Format
// ============================================================================
class VP815GemmDevice {
public:
    explicit VP815GemmDevice(achronix::VP815& device)
        : device_(device), current_id_(0) {}

    // ---------------------- Soft Reset --------------------------------------
    void soft_reset() {
        mmio_write32(0, 0x0, 0x2);  // Assert reset
        mmio_write32(0, 0x0, 0x0);  // Deassert
        
        mmio_write32(0, 0x230, 0x0);  // rd_ptr = 0
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
    // 4-Word Format:
    // cmd[0] = {8'h00, 16'd16, cmd_id[7:0], OPC_FETCH}
    // cmd[1] = start_addr[31:0] (in 32-byte units, NOT bytes!)
    // cmd[2] = {reserved[15:0], len[15:0]}
    // cmd[3] = {reserved[30:0], fetch_right}
    // IMPORTANT: Hardware expects addresses in 32-byte line units (verified in gemm_simple)
    uint8_t fetch(uint32_t startAddr, uint16_t length, bool fetch_right = false) {
        uint8_t id = next_cmd_id();
        uint32_t w0 = build_word0(OPC_FETCH, id);
        uint32_t w1 = startAddr / 32;  // Convert byte address to 32-byte line units
        uint32_t w2 = static_cast<uint32_t>(length & 0xFFFF);
        uint32_t w3 = fetch_right ? 1u : 0u;
        issue_command(w0, w1, w2, w3);
        return id;
    }

    // ---------------------- DISPATCH Command --------------------------------
    // 4-Word Format:
    // cmd[0] = {8'h00, 16'd16, cmd_id[7:0], OPC_DISPATCH}
    // cmd[1] = {8'b0, man_nv_cnt[7:0], 8'b0, ugd_vec_size[7:0]}
    // cmd[2] = {16'b0, tile_addr[15:0]}
    // cmd[3] = {col_en[23:0], col_start[4:0], disp_right, broadcast, man_4b}
    uint8_t dispatch(uint8_t man_nv_cnt, uint8_t ugd_vec_size, uint16_t tile_addr,
                     bool disp_right, uint32_t col_en = 0x0001, uint8_t col_start = 0,
                     bool broadcast = false, bool man_4b = false) {
        uint8_t id = next_cmd_id();
        uint32_t w0 = build_word0(OPC_DISPATCH, id);
        // Word 1: {8'b0, man_nv_cnt[7:0], 8'b0, ugd_vec_size[7:0]}
        uint32_t w1 = (static_cast<uint32_t>(man_nv_cnt) << 16) |
                      static_cast<uint32_t>(ugd_vec_size);
        // Word 2: {16'b0, tile_addr[15:0]}
        uint32_t w2 = static_cast<uint32_t>(tile_addr & 0xFFFF);
        // Word 3: {col_en[23:0], col_start[4:0], disp_right, broadcast, man_4b}
        uint32_t w3 = ((col_en & 0xFFFFFF) << 8) |              // col_en[23:0] at bits [31:8]
                      ((col_start & 0x1F) << 3) |                // col_start[4:0] at bits [7:3]
                      (disp_right ? 4u : 0u) |                   // disp_right at bit 2
                      (broadcast ? 2u : 0u) |                    // broadcast at bit 1
                      (man_4b ? 1u : 0u);                        // man_4b at bit 0
        issue_command(w0, w1, w2, w3);
        return id;
    }

    // ---------------------- WAIT_DISPATCH Command ---------------------------
    // 4-Word Format:
    // cmd[0] = {8'h00, 16'd16, cmd_id[7:0], OPC_WAIT_DISPATCH}
    // cmd[1] = {24'd0, wait_id[7:0]}
    // cmd[2] = 32'h00000000
    // cmd[3] = 32'h00000000
    uint8_t waitDispatch(uint8_t waitId) {
        uint8_t id = next_cmd_id();
        uint32_t w0 = build_word0(OPC_WAIT_DISPATCH, id);
        uint32_t w1 = static_cast<uint32_t>(waitId);
        issue_command(w0, w1, 0, 0);
        return id;
    }

    // ---------------------- MATMUL (TILE) Command ---------------------------
    // 4-Word Format:
    // cmd[0] = {8'h00, 16'd16, cmd_id[7:0], OPC_MATMUL}
    // cmd[1] = {left_addr[15:0], right_addr[15:0]}
    // cmd[2] = {8'b0, left_ugd_len[7:0], right_ugd_len[7:0], vec_len[7:0]}
    // cmd[3] = {col_en[23:0], 5'b0, left_4b, right_4b, main_loop_left}
    uint8_t tile(uint16_t leftAddr, uint16_t rightAddr,
                 uint8_t leftUgdLen, uint8_t rightUgdLen, uint8_t vecLen,
                 bool leftMan4b = false, bool rightMan4b = false,
                 bool mainLoopOverLeft = true, uint32_t col_en = 0x0001) {
        uint8_t id = next_cmd_id();

        uint32_t w0 = build_word0(OPC_MATMUL, id);
        // Word 1: {left_addr[15:0], right_addr[15:0]}
        uint32_t w1 = (static_cast<uint32_t>(leftAddr) << 16) |
                      static_cast<uint32_t>(rightAddr);
        // Word 2: {8'b0, left_ugd_len[7:0], right_ugd_len[7:0], vec_len[7:0]}
        uint32_t w2 = (static_cast<uint32_t>(leftUgdLen) << 16) |
                      (static_cast<uint32_t>(rightUgdLen) << 8) |
                      static_cast<uint32_t>(vecLen);
        // Word 3: {col_en[23:0], 5'b0, left_4b, right_4b, main_loop_left}
        uint32_t w3 = ((col_en & 0xFFFFFF) << 8) |  // col_en[23:0] at bits [31:8]
                      (leftMan4b ? 4u : 0u) |        // left_4b at bit [2]
                      (rightMan4b ? 2u : 0u) |       // right_4b at bit [1]
                      (mainLoopOverLeft ? 1u : 0u);   // main_loop_left at bit [0]

        issue_command(w0, w1, w2, w3);
        return id;
    }

    // ---------------------- WAIT_MATMUL Command -----------------------------
    // 4-Word Format:
    // cmd[0] = {8'h00, 16'd16, cmd_id[7:0], OPC_WAIT_MATMUL}
    // cmd[1] = {24'd0, wait_id[7:0]}
    // cmd[2] = 32'h00000000
    // cmd[3] = 32'h00000000
    uint8_t waitTile(uint8_t waitId) {
        uint8_t id = next_cmd_id();
        uint32_t w0 = build_word0(OPC_WAIT_MATMUL, id);
        uint32_t w1 = static_cast<uint32_t>(waitId);
        issue_command(w0, w1, 0, 0);
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

    // Build command word0 (fixed 4-word format: all commands are 16 bytes)
    // cmd[0] = {8'h00, 16'd16, cmd_id[7:0], opcode[7:0]}
    uint32_t build_word0(uint8_t opcode, uint8_t id) {
        return (0x00u << 24) | (16u << 16) |
               (static_cast<uint32_t>(id) << 8) |
               static_cast<uint32_t>(opcode);
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

