#pragma once

#include <cstdint>
#include <vector>
#include <string>
#include <iostream>
#include <fstream>
#include <sstream>
#include <chrono>
#include <thread>
#include <unistd.h>  // For usleep()
#include "../../../eus/shell/devices/acx/vp815/api/vp815.hpp"
#include "Achronix_device.h"
#include "Achronix_util.h"

// ============================================================================
// VP815 Multi-Row 2D GEMM Engine Device Wrapper (4-Word Command Format)
//
// IMPORTANT: This API targets the 2D multi-row GEMM architecture with:
//   - 16 parallel rows (each with its own GDDR6 channel)
//   - 16 columns per row (compute engines)
//   - Row reduction via result_collector_2d
//
// Command formats verified against RTL:
//   - dispatcher_control_2d.sv (FETCH, DISPATCH)
//   - compute_engine_2d.sv (MATMUL)
//   - result_collector_2d.sv (READOUT)
//
// NOTE: The old test files (test_gemm.cpp, test_gemm_full.cpp) use the
// single-row MLP API and are NOT compatible with this 2D GEMM API.
// Use test_gemm_2d.cpp for 2D GEMM testing.
// ============================================================================

// ---------------------- Register Offsets (BAR0) ----------------------------
// New DMA-BRAM command interface (refactored Jan 2026)
constexpr uint32_t DMA_CMD_CNT        = 0x3C;   // Number of commands in BRAM
constexpr uint32_t DMA_CMD_VALID      = 0x40;   // Write 1 to trigger, auto-clears when done
constexpr uint32_t DMA_CMD_RD_ADDR    = 0x44;   // Debug: current BRAM read address (read-only)
constexpr uint32_t DMA_CMD_RESERVED   = 0x48;   // Reserved
constexpr uint32_t ENGINE_CMD_SUBMIT  = 0x4C;   // Legacy (deprecated)
constexpr uint32_t MS2_STATUS         = 0x50;
constexpr uint32_t MS2_RESULT_COUNT   = 0x54;

// --------------------------- Microcode Opcodes -----------------------------
constexpr uint8_t  OPC_FETCH          = 0xF0;
constexpr uint8_t  OPC_DISPATCH       = 0xF1;
constexpr uint8_t  OPC_MATMUL         = 0xF2;
constexpr uint8_t  OPC_WAIT_DISPATCH  = 0xF3;
constexpr uint8_t  OPC_WAIT_MATMUL    = 0xF4;
constexpr uint8_t  OPC_READOUT        = 0xF5;

// -------------------------- Memory Layout ----------------------------------
// For 2D multi-row GEMM, addresses are LINE addresses (not byte addresses).
// Each row has its own GDDR6 channel; Master Control broadcasts commands to all rows.
// Block 0 (left):  lines 0-527
// Block 1 (right): lines 528-1055
constexpr uint32_t GDDR6_LINE_ADDR_LEFT   = 0;           // Line address for left block
constexpr uint32_t GDDR6_LINE_ADDR_RIGHT  = 528;         // Line address for right block
constexpr uint16_t LINES_PER_BLOCK        = 528;         // 16 exp + 512 man lines

// DMA base addresses (for host-side DMA writes to GDDR6)
constexpr uint8_t  GDDR6_PAGE_ID_SW   = 1;               // Match RTL/testbench GDDR6_PAGE_ID
constexpr uint64_t GDDR6_FETCH_BASE_LEFT   = 0x0ULL;     // page-relative byte address
constexpr uint64_t GDDR6_FETCH_BASE_RIGHT  = 0x40000000ULL; // 1GB page-relative offset
constexpr uint64_t GDDR6_PAGE_BASE         = (static_cast<uint64_t>(GDDR6_PAGE_ID_SW & 0x1FFULL) << 33);
constexpr uint64_t GDDR6_DMA_BASE_LEFT     = GDDR6_PAGE_BASE + GDDR6_FETCH_BASE_LEFT;
constexpr uint64_t GDDR6_DMA_BASE_RIGHT    = GDDR6_PAGE_BASE + GDDR6_FETCH_BASE_RIGHT;

// 2D GEMM configuration
constexpr int NUM_ROWS = 16;                             // Number of parallel rows
constexpr int NUM_COLS = 4;                              // Number of columns per row (NUM_MLPS=2)

// ---------------------- GDDR6 Channel Configuration --------------------------
// 16 rows mapped to 16 GDDR6 controller IDs (from engine_top_2d.sv GDDR6_CTRL_ID)
// DMA address format: (GDDR6_CTRL_ID << 33) | byte_offset
// West controllers (0-3): Ch0=lower ID, Ch1=higher ID
// East controllers (4-7): Ch0=higher ID, Ch1=lower ID (reversed)
// NOTE: GDDR6 NAP placements are in ace_placements.pdc (col 1 West, col 10 East)
//       Software only needs CTRL_ID for DMA address formation, not NAP locations.
constexpr uint16_t GDDR6_CTRL_ID[NUM_ROWS] = {
    0x00C, 0x00D,   // Controller 0: Ch0, Ch1 (West)
    0x004, 0x005,   // Controller 1: Ch0, Ch1 (West)
    0x000, 0x001,   // Controller 2: Ch0, Ch1 (West)
    0x008, 0x009,   // Controller 3: Ch0, Ch1 (West)
    0x00F, 0x00E,   // Controller 4: Ch0, Ch1 (East, reversed)
    0x007, 0x006,   // Controller 5: Ch0, Ch1 (East, reversed)
    0x003, 0x002,   // Controller 6: Ch0, Ch1 (East, reversed)
    0x00B, 0x00A    // Controller 7: Ch0, Ch1 (East, reversed)
};

// Calculate DMA base address for a given row/channel
// Format: (GDDR6_CTRL_ID << 33) | byte_offset
inline uint64_t gddr6_dma_addr(int row, uint64_t byte_offset = 0) {
    return (static_cast<uint64_t>(GDDR6_CTRL_ID[row] & 0x1FF) << 33) | byte_offset;
}

// DMA-BRAM NAP placements (moved from column 3 to column 7 to avoid ADM congestion)
// See ace_placements.pdc for RTL placement constraints
constexpr int CMD_BRAM_NAP_COL = 7;                      // Command input BRAM column
constexpr int CMD_BRAM_NAP_ROW = 6;                      // Command input BRAM row (NAP[7][6])
constexpr int DATA_OUT_BRAM_NAP_COL = 7;                 // Data output BRAM column
constexpr int DATA_OUT_BRAM_NAP_ROW = 5;                 // Data output BRAM row (NAP[7][5])

// Command BRAM configuration (DMA-BRAM interface)
constexpr int CMD_BRAM_DEPTH = 512;                      // 512 x 256-bit lines
constexpr int CMD_BYTES_PER_LINE = 32;                   // 256 bits = 32 bytes
constexpr int CMD_WORDS_PER_CMD = 4;                     // 128-bit command = 4 x 32-bit words

// ============================================================================
// VP815GemmDevice - Multi-Row 2D GEMM Engine Wrapper
// Refactored Jan 2026: Uses DMA-BRAM command interface instead of CSR
// Commands are batched in host memory, DMA'd to BRAM, then triggered
// ============================================================================
class VP815GemmDevice {
public:
    explicit VP815GemmDevice(achronix::VP815& device)
        : device_(device), current_id_(0) {
        // Calculate command BRAM DMA address from NAP coordinates
        cmd_bram_addr_ = acx_util_nap_absolute_addr(ACX_PART_AC7t1500, 
                                                     CMD_BRAM_NAP_COL, CMD_BRAM_NAP_ROW);
        // Reserve space for max commands
        cmd_buffer_.reserve(CMD_BRAM_DEPTH * CMD_BYTES_PER_LINE);
    }

    // ---------------------- Soft Reset --------------------------------------
    void soft_reset() {
        mmio_write32(0, 0x0, 0x2);  // Assert reset (bit 1 of control register)
        // usleep(100);                 // Hold reset for 100us (>> 5 clock cycles at 400MHz)
        mmio_write32(0, 0x0, 0x0);  // Deassert reset
        // usleep(100);                 // Wait for state to settle
        // Note: wr_ptr auto-resets via engine_rstn (async reset)
        // Register 0x234 is READ-ONLY (hardware wr_ptr status)
        mmio_write32(0, 0x230, 0);  // Reset rd_ptr to 0
        // Reset cmd_id counter to match hardware reset state
        current_id_ = 0;
        // Clear command buffer on reset
        // begin_command_batch();
    }

    // ---------------------- Wait for Engine Idle ----------------------------
    bool wait_idle(uint32_t timeout_ms = 1000) {
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

    // =========================================================================
    // Command Batch Management (DMA-BRAM Interface)
    // =========================================================================
    // Start a new command batch (clears buffer)
    // NOTE: Does NOT reset cmd_id - let it increment naturally for RTL wrap-around handling
    void begin_command_batch() {
        cmd_buffer_.clear();
        cmd_count_ = 0;
        // Don't reset current_id_ here - RTL handles wrap-around with signed comparison
    }

    // Submit command batch to hardware via DMA-BRAM interface
    // Returns true on success, false on error
    bool submit_commands(bool verbose = false, bool verify = false) {
        if (cmd_count_ == 0) {
            if (verbose) std::cout << "  No commands to submit" << std::endl;
            return true;
        }

        if (verbose) {
            std::cout << "  Submitting " << cmd_count_ << " commands via DMA-BRAM" << std::endl;
            std::cout << "    CMD BRAM addr: 0x" << std::hex << cmd_bram_addr_ << std::dec << std::endl;
            std::cout << "    Buffer size: " << cmd_buffer_.size() << " bytes" << std::endl;
        }

        // Step 1: DMA command buffer to BRAM
        if (!dma_write(cmd_bram_addr_, cmd_buffer_.data(), cmd_buffer_.size())) {
            std::cerr << "ERROR: DMA write to command BRAM failed" << std::endl;
            return false;
        }

        // Step 1.5: Verify BRAM contents if requested
        if (verify) {
            std::vector<uint8_t> readback(cmd_buffer_.size());
            if (!dma_read(cmd_bram_addr_, readback.data(), readback.size())) {
                std::cerr << "ERROR: DMA read from command BRAM failed" << std::endl;
                return false;
            }

            bool mismatch = false;
            for (size_t i = 0; i < cmd_buffer_.size(); i++) {
                if (cmd_buffer_[i] != readback[i]) {
                    if (!mismatch) {
                        std::cerr << "ERROR: BRAM verification failed!" << std::endl;
                        mismatch = true;
                    }
                    std::cerr << "  Byte " << i << ": wrote 0x" << std::hex 
                              << static_cast<int>(cmd_buffer_[i]) 
                              << ", read 0x" << static_cast<int>(readback[i]) 
                              << std::dec << std::endl;
                }
            }

            if (mismatch) {
                return false;
            }

            if (verbose) {
                std::cout << "    BRAM verification passed (" << cmd_buffer_.size() << " bytes)" << std::endl;
                // Print command contents for debugging
                for (size_t cmd_idx = 0; cmd_idx < cmd_count_; cmd_idx++) {
                    size_t offset = cmd_idx * CMD_BYTES_PER_LINE;
                    uint32_t w3 = readback[offset + 0] | (readback[offset + 1] << 8) |
                                  (readback[offset + 2] << 16) | (readback[offset + 3] << 24);
                    uint32_t w2 = readback[offset + 4] | (readback[offset + 5] << 8) |
                                  (readback[offset + 6] << 16) | (readback[offset + 7] << 24);
                    uint32_t w1 = readback[offset + 8] | (readback[offset + 9] << 8) |
                                  (readback[offset + 10] << 16) | (readback[offset + 11] << 24);
                    uint32_t w0 = readback[offset + 12] | (readback[offset + 13] << 8) |
                                  (readback[offset + 14] << 16) | (readback[offset + 15] << 24);
                    uint8_t opcode = w0 & 0xFF;
                    uint8_t cmd_id = (w0 >> 8) & 0xFF;
                    std::cout << "    Cmd[" << cmd_idx << "]: opcode=0x" << std::hex 
                              << static_cast<int>(opcode) << " id=" << static_cast<int>(cmd_id)
                              << " w0=0x" << w0 << " w1=0x" << w1 
                              << " w2=0x" << w2 << " w3=0x" << w3 << std::dec << std::endl;
                }
            }
        }

        // Step 2: Write command count to DMA_CMD_CNT register
        mmio_write32(0, DMA_CMD_CNT, static_cast<uint32_t>(cmd_count_));

        // Step 3: Trigger command transfer by setting DMA_CMD_VALID
        mmio_write32(0, DMA_CMD_VALID, 0x1);

        // Step 4: Wait for DMA_CMD_VALID to auto-clear (bridge done)
        auto start = std::chrono::steady_clock::now();
        int poll_count = 0;
        while (true) {
            uint32_t valid = mmio_read32(0, DMA_CMD_VALID);
            if ((valid & 0x1) == 0) {
                break;  // Transfer complete
            }
            poll_count++;
            auto elapsed = std::chrono::duration_cast<std::chrono::milliseconds>(
                std::chrono::steady_clock::now() - start).count();
            if (elapsed > 1000) {  // 1 second timeout
                std::cerr << "ERROR: Command transfer timeout (DMA_CMD_VALID stuck)" << std::endl;
                std::cerr << "  DMA_CMD_VALID=0x" << std::hex << valid << std::dec << std::endl;
                std::cerr << "  DMA_CMD_RD_ADDR=0x" << std::hex 
                         << mmio_read32(0, DMA_CMD_RD_ADDR) << std::dec << std::endl;
                return false;
            }
            usleep(10);  // 10us between polls
        }

        if (verbose) {
            std::cout << "    Transfer complete after " << poll_count << " polls" << std::endl;
        }

        // Clear buffer for next batch
        begin_command_batch();
        return true;
    }

    // Get current command count in buffer
    size_t get_command_count() const { return cmd_count_; }

    // Get command BRAM address
    uint64_t get_cmd_bram_addr() const { return cmd_bram_addr_; }

    // =========================================================================
    // FETCH Command (0xF0) - Per dispatcher_control_2d.sv
    // =========================================================================
    // Purpose: Fetch memory block from GDDR6 to Dispatcher FIFO
    // 4-Word Format (verified against RTL lines 298-305):
    //   cmd[0] = {16'd16, cmd_id[7:0], OPC_FETCH}
    //   cmd[1] = {start_addr[31:0]}           -- LINE address (not byte!)
    //   cmd[2] = {ugd_len[15:0], len[15:0]}   -- ugd_len=V total, len=lines to fetch
    //   cmd[3] = {31'b0, fetch_right}
    //
    // RTL extracts (dispatcher_control_2d.sv):
    //   fetch_addr_internal <= word1[link_addr_width_gp-1:0]  // 26-bit line address
    //   fetch_len_internal  <= word2[15:0]                    // len (lines)
    //   (ugd_len in word2[31:16] passed to MC for V partitioning)
    //
    // IMPORTANT: start_addr is LINE address. For 2D multi-row GEMM:
    //   - Block 0 (left):  line 0
    //   - Block 1 (right): line 528
    uint8_t fetch(uint32_t start_addr_line, uint16_t ugd_len, uint16_t len, bool fetch_right) {
        uint8_t id = next_cmd_id();
        uint32_t w0 = build_word0(OPC_FETCH, id);
        uint32_t w1 = start_addr_line;  // LINE address (not byte!)
        uint32_t w2 = (static_cast<uint32_t>(ugd_len) << 16) | static_cast<uint32_t>(len);
        uint32_t w3 = fetch_right ? 1u : 0u;
        issue_command(w0, w1, w2, w3);
        return id;
    }

    // =========================================================================
    // DISPATCH Command (0xF1) - Per dispatcher_control_2d.sv
    // =========================================================================
    // Purpose: Route data from FIFO to row_bram (left) or mlp_bram (right)
    // 4-Word Format (verified against RTL lines 353-360):
    //   cmd[0] = {16'd16, cmd_id[7:0], OPC_DISPATCH}
    //   cmd[1] = {nv_cnt[15:0], ugd_len[15:0]}   -- nv_cnt=B or C, ugd_len=V total
    //   cmd[2] = {16'b0, tile_addr[15:0]}        -- destination address
    //   cmd[3] = {16'b0, col_start[7:0], 5'b0, disp_right, broadcast, man_4b}
    //
    // RTL extracts:
    //   disp_nv_cnt_reg    <= word1[31:16]   // nv_cnt
    //   disp_ugd_len_reg   <= word1[15:0]    // ugd_len (V)
    //   disp_tile_addr_reg <= word2[ADDR_WIDTH-1:0]
    //   disp_col_start_reg <= word3[11:8]   // Only 4 bits used (0-15)
    //   disp_right_reg     <= word3[2]
    //
    // For left (activations):  disp_right=0, broadcast=1
    // For right (weights):     disp_right=1, broadcast=0
    uint8_t dispatch(uint16_t nv_cnt, uint16_t ugd_len, uint16_t tile_addr,
                     uint8_t col_start, bool disp_right, bool man_4b = false) {
        uint8_t id = next_cmd_id();
        uint32_t w0 = build_word0(OPC_DISPATCH, id);
        // Word 1: {nv_cnt[15:0], ugd_len[15:0]}
        uint32_t w1 = (static_cast<uint32_t>(nv_cnt) << 16) |
                      static_cast<uint32_t>(ugd_len);
        // Word 2: {16'b0, tile_addr[15:0]}
        uint32_t w2 = static_cast<uint32_t>(tile_addr);
        // Word 3: {16'b0, col_start[7:0], 5'b0, disp_right, broadcast, man_4b}
        // Note: RTL extracts col_start from bits[11:8], so only col_start[3:0] is used
        // broadcast = ~disp_right (left=broadcast, right=distribute)
        bool broadcast = !disp_right;
        uint32_t w3 = (static_cast<uint32_t>(col_start & 0x0F) << 8) |  // col_start[3:0] -> bits[11:8]
                      (disp_right ? 4u : 0u) |      // disp_right at bit 2
                      (broadcast ? 2u : 0u) |       // broadcast at bit 1
                      (man_4b ? 1u : 0u);           // man_4b at bit 0
        issue_command(w0, w1, w2, w3);
        return id;
    }

    // =========================================================================
    // WAIT_DISPATCH Command (0xF3) - Per MULTI_ROW_REFERENCE.md
    // =========================================================================
    // Purpose: Synchronization barrier - wait for DISPATCH to complete
    // 4-Word Format:
    //   cmd[0] = {16'd16, cmd_id[7:0], OPC_WAIT_DISPATCH}
    //   cmd[1] = {24'd0, wait_id[7:0]}
    //   cmd[2] = 0
    //   cmd[3] = 0
    uint8_t waitDispatch(uint8_t waitId) {
        uint8_t id = next_cmd_id();
        uint32_t w0 = build_word0(OPC_WAIT_DISPATCH, id);
        uint32_t w1 = static_cast<uint32_t>(waitId);
        issue_command(w0, w1, 0, 0);
        return id;
    }

    // =========================================================================
    // MATMUL (TILE) Command (0xF2) - Per compute_engine_2d.sv
    // =========================================================================
    // Purpose: Execute parallel matrix multiplication
    // 4-Word Format (verified against RTL lines 313-317):
    //   cmd[0] = {16'd16, cmd_id[7:0], OPC_MATMUL}
    //   cmd[1] = {left_addr[15:0], right_addr[15:0]}
    //   cmd[2] = {B[15:0], C[15:0]}     -- B and C (16-bit each)
    //   cmd[3] = {V[15:0], flags[15:0]}
    //
    // RTL extracts (compute_engine_2d.sv):
    //   left_addr_reg  <= word1[31:16]
    //   right_addr_reg <= word1[15:0]
    //   B_reg          <= word2[23:16]  // Low byte of B[15:0]
    //   C_reg          <= word2[7:0]    // Low byte of C[15:0]
    //   V_reg          <= word3[23:16]  // Low byte of V[15:0]
    //
    // Note: B, C, V are stored as 16-bit but RTL only uses low byte (max 255)
    uint8_t matmul(uint16_t left_addr, uint16_t right_addr,
                   uint16_t B, uint16_t C, uint16_t V,
                   bool left_4b = false, bool right_4b = false,
                   bool main_loop_left = false) {
        uint8_t id = next_cmd_id();
        uint32_t w0 = build_word0(OPC_MATMUL, id);
        // Word 1: {left_addr[15:0], right_addr[15:0]}
        uint32_t w1 = (static_cast<uint32_t>(left_addr) << 16) |
                      static_cast<uint32_t>(right_addr);
        // Word 2: {B[15:0], C[15:0]}
        uint32_t w2 = (static_cast<uint32_t>(B) << 16) |
                      static_cast<uint32_t>(C);
        // Word 3: {V[15:0], flags[15:0]}
        uint32_t w3 = (static_cast<uint32_t>(V) << 16) |
                      (left_4b ? 4u : 0u) |
                      (right_4b ? 2u : 0u) |
                      (main_loop_left ? 1u : 0u);
        issue_command(w0, w1, w2, w3);
        return id;
    }

    // Alias for backward compatibility
    uint8_t tile(uint16_t left_addr, uint16_t right_addr,
                 uint16_t B, uint16_t C, uint16_t V,
                 bool left_4b = false, bool right_4b = false,
                 bool main_loop_left = false) {
        return matmul(left_addr, right_addr, B, C, V, left_4b, right_4b, main_loop_left);
    }

    // =========================================================================
    // WAIT_MATMUL Command (0xF4) - Per MULTI_ROW_REFERENCE.md
    // =========================================================================
    // Purpose: Synchronization barrier - wait for MATMUL to complete
    // 4-Word Format:
    //   cmd[0] = {16'd16, cmd_id[7:0], OPC_WAIT_MATMUL}
    //   cmd[1] = {24'd0, wait_id[7:0]}
    //   cmd[2] = 0
    //   cmd[3] = 0
    uint8_t waitMatmul(uint8_t waitId) {
        uint8_t id = next_cmd_id();
        uint32_t w0 = build_word0(OPC_WAIT_MATMUL, id);
        uint32_t w1 = static_cast<uint32_t>(waitId);
        issue_command(w0, w1, 0, 0);
        return id;
    }

    // Alias for backward compatibility
    uint8_t waitTile(uint8_t waitId) {
        return waitMatmul(waitId);
    }

    // =========================================================================
    // READOUT Command (0xF5) - Per result_collector_2d.sv
    // =========================================================================
    // Purpose: Read results from CE FIFOs to output BRAM (includes all-reduce)
    // 4-Word Format (verified against RTL lines 131-133):
    //   cmd[0] = {16'd16, cmd_id[7:0], OPC_READOUT}
    //   cmd[1] = {B[15:0], C[15:0]}   -- left_len=B, right_len=C
    //   cmd[2] = {16'b0, V[15:0]}     -- ugd_len (not used by RC, but included)
    //   cmd[3] = 0
    //
    // RTL extracts (result_collector_2d.sv):
    //   cmd_left_len  = word1[31:16]  // B (batch count)
    //   cmd_right_len = word1[15:0]   // C (column count)
    //   word2 is reserved in RC (V not used for result collection)
    uint8_t readout(uint16_t B, uint16_t C, uint16_t V) {
        uint8_t id = next_cmd_id();
        uint32_t w0 = build_word0(OPC_READOUT, id);
        // Word 1: {B[15:0], C[15:0]}
        uint32_t w1 = (static_cast<uint32_t>(B) << 16) |
                      static_cast<uint32_t>(C);
        // Word 2: {16'b0, V[15:0]} - included for consistency with testbench
        uint32_t w2 = static_cast<uint32_t>(V);
        issue_command(w0, w1, w2, 0);
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
    
    // DMA-BRAM command interface state
    std::vector<uint8_t> cmd_buffer_;     // Command buffer (host side)
    size_t cmd_count_ = 0;                // Number of commands in buffer
    uint64_t cmd_bram_addr_;              // DMA address of command BRAM

    // Build command word0 (fixed 4-word format: all commands are 16 bytes)
    // cmd[0] = {8'h00, 8'd16, cmd_id[7:0], opcode[7:0]}
    // Note: byte at [23:16] is command length in bytes (16 = 4 words)
    uint32_t build_word0(uint8_t opcode, uint8_t id) {
        return (0x00u << 24) | (16u << 16) |
               (static_cast<uint32_t>(id) << 8) |
               static_cast<uint32_t>(opcode);
    }

    // Append command to buffer (DMA-BRAM interface)
    // Each command is 128-bit (16 bytes), stored in lower 128 bits of 256-bit BRAM line
    // BRAM line format: {128'b0, w0[31:0], w1[31:0], w2[31:0], w3[31:0]}
    void issue_command(uint32_t w0, uint32_t w1, uint32_t w2, uint32_t w3) {
        // Allocate 32-byte BRAM line (256 bits)
        uint8_t line[CMD_BYTES_PER_LINE] = {0};
        
        // Pack 4 words into lower 128 bits (bytes 0-15)
        // Little-endian: w3 at bytes 0-3, w2 at 4-7, w1 at 8-11, w0 at 12-15
        // Match RTL: cmd_128 = {w0, w1, w2, w3} where w0 is MSB
        line[0]  = (w3 >>  0) & 0xFF;
        line[1]  = (w3 >>  8) & 0xFF;
        line[2]  = (w3 >> 16) & 0xFF;
        line[3]  = (w3 >> 24) & 0xFF;
        line[4]  = (w2 >>  0) & 0xFF;
        line[5]  = (w2 >>  8) & 0xFF;
        line[6]  = (w2 >> 16) & 0xFF;
        line[7]  = (w2 >> 24) & 0xFF;
        line[8]  = (w1 >>  0) & 0xFF;
        line[9]  = (w1 >>  8) & 0xFF;
        line[10] = (w1 >> 16) & 0xFF;
        line[11] = (w1 >> 24) & 0xFF;
        line[12] = (w0 >>  0) & 0xFF;
        line[13] = (w0 >>  8) & 0xFF;
        line[14] = (w0 >> 16) & 0xFF;
        line[15] = (w0 >> 24) & 0xFF;
        // Bytes 16-31 are zeros (upper 128 bits of BRAM line)
        
        // Append line to buffer
        cmd_buffer_.insert(cmd_buffer_.end(), line, line + CMD_BYTES_PER_LINE);
        cmd_count_++;
    }
};

