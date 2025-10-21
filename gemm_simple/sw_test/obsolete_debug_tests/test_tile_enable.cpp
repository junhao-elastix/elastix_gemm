#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <unistd.h>
#include <sys/mman.h>
#include <fcntl.h>
#include <errno.h>

// Register offsets
#define ENGINE_CMD_WORD0        40
#define ENGINE_CMD_WORD1        41
#define ENGINE_CMD_WORD2        42
#define ENGINE_CMD_WORD3        43
#define ENGINE_CMD_SUBMIT       44
#define ENGINE_STATUS          45
#define ENGINE_RESULT_COUNT    46
#define ENGINE_DEBUG           47

// Base address for PCIe BAR0
#define BAR0_BASE    0x4240000000ULL
#define REG_SIZE     0x20000

// NAP BAR2 for Result BRAM
#define BRAM_BASE    0x4460008000ULL
#define BRAM_SIZE    0x2000

// Command opcodes
#define CMD_TILE    0xF2

int main() {
    int fd;
    uint32_t *regs;
    volatile uint32_t *result_bram;
    uint32_t val;

    printf("=== Test TILE Enable Signal ===\n");

    // Open memory device
    fd = open("/dev/mem", O_RDWR | O_SYNC);
    if (fd < 0) {
        perror("Failed to open /dev/mem");
        return 1;
    }

    // Map registers
    regs = (uint32_t *)mmap(NULL, REG_SIZE, PROT_READ | PROT_WRITE, MAP_SHARED, fd, BAR0_BASE);
    if (regs == MAP_FAILED) {
        perror("Failed to mmap registers");
        close(fd);
        return 1;
    }

    // Map result BRAM
    result_bram = (uint32_t *)mmap(NULL, BRAM_SIZE, PROT_READ | PROT_WRITE, MAP_SHARED, fd, BRAM_BASE);
    if (result_bram == MAP_FAILED) {
        perror("Failed to mmap result BRAM");
        munmap(regs, REG_SIZE);
        close(fd);
        return 1;
    }

    printf("✅ Memory mapped successfully\n\n");

    // Clear result BRAM first
    for (int i = 0; i < 256; i++) {
        result_bram[i] = 0xDEADBEEF;
    }

    // Check initial status
    val = regs[ENGINE_STATUS];
    printf("Initial status: 0x%08x (MC=%d, DC=%d, CE=%d)\n",
           val, (val >> 8) & 0xF, (val >> 4) & 0xF, val & 0xF);

    val = regs[ENGINE_RESULT_COUNT];
    printf("Initial result count: %d\n", val);

    // Build minimal TILE command
    // B=1, C=1, V=1 (simplest possible case)
    uint32_t dim_b = 1;
    uint32_t dim_c = 1;
    uint32_t dim_v = 1;
    uint32_t left_addr = 0;
    uint32_t right_addr = 1;
    uint32_t vec_len = 1;
    uint32_t left_ugd_len = 1;
    uint32_t right_ugd_len = 1;
    uint32_t flags = 0;

    // Encode cmd_tile_s (87-bit structure)
    uint64_t payload_low = 0;
    uint32_t payload_high = 0;

    payload_low |= ((uint64_t)left_addr & 0x7FF);
    payload_low |= ((uint64_t)right_addr & 0x7FF) << 11;
    payload_low |= ((uint64_t)left_ugd_len & 0x7FF) << 22;
    payload_low |= ((uint64_t)right_ugd_len & 0x7FF) << 33;
    payload_low |= ((uint64_t)vec_len & 0x7FF) << 44;

    uint64_t payload_mid = ((uint64_t)vec_len & 0x7FF) >> 20;  // Upper bits of vec_len
    payload_mid |= ((uint64_t)flags & 0xFF) << 35;

    payload_high |= (dim_v & 0xFF);
    payload_high |= (dim_c & 0xFF) << 8;
    payload_high |= (dim_b & 0xFF) << 16;

    uint32_t cmd_word0 = (CMD_TILE << 0) | (1 << 8) | (12 << 16);
    uint32_t cmd_word1 = payload_low & 0xFFFFFFFF;
    uint32_t cmd_word2 = (payload_low >> 32) & 0xFFFFFFFF;
    uint32_t cmd_word3 = payload_high;

    printf("\n=== Sending TILE Command (1x1x1 matrix) ===\n");
    printf("Word0: 0x%08x (opcode=0xF2, id=1, len=12)\n", cmd_word0);
    printf("Word1: 0x%08x\n", cmd_word1);
    printf("Word2: 0x%08x\n", cmd_word2);
    printf("Word3: 0x%08x\n", cmd_word3);

    // Write command words
    regs[ENGINE_CMD_WORD0] = cmd_word0;
    regs[ENGINE_CMD_WORD1] = cmd_word1;
    regs[ENGINE_CMD_WORD2] = cmd_word2;
    regs[ENGINE_CMD_WORD3] = cmd_word3;

    // Submit command
    printf("\nSubmitting command...\n");
    regs[ENGINE_CMD_SUBMIT] = 1;

    // Poll for completion
    int timeout = 1000;
    while (timeout-- > 0) {
        val = regs[ENGINE_STATUS];
        int mc_state = (val >> 8) & 0xF;
        int dc_state = (val >> 4) & 0xF;
        int ce_state = val & 0xF;

        if (mc_state == 0 && dc_state == 0 && ce_state == 0) {
            printf("✅ All FSMs returned to IDLE\n");
            break;
        }

        if (timeout % 100 == 0) {
            printf("  Waiting... MC=%d, DC=%d, CE=%d\n", mc_state, dc_state, ce_state);
        }

        usleep(100);
    }

    if (timeout <= 0) {
        printf("❌ Timeout waiting for completion\n");
    }

    // Check result count
    val = regs[ENGINE_RESULT_COUNT];
    printf("\n=== Results ===\n");
    printf("Result count: %d (expected: 1)\n", val);

    // Read debug register
    val = regs[ENGINE_DEBUG];
    printf("Debug register: 0x%08x\n", val);

    // Check first result BRAM location
    printf("\nFirst result BRAM word: 0x%08x (should NOT be 0xDEADBEEF)\n", result_bram[0]);

    // Cleanup
    munmap(result_bram, BRAM_SIZE);
    munmap(regs, REG_SIZE);
    close(fd);

    return (val == 1) ? 0 : 1;
}