#include <stdio.h>
#include <stdint.h>
#include <fcntl.h>
#include <sys/mman.h>
#include <unistd.h>

#define BAR0_SIZE 0x10000
#define ENGINE_CMD_WORD0  0x28
#define ENGINE_CMD_WORD1  0x2C
#define ENGINE_CMD_WORD2  0x30
#define ENGINE_CMD_WORD3  0x34
#define ENGINE_CMD_SUBMIT 0x38
#define ENGINE_STATUS     0x3C
#define ENGINE_RESULT_COUNT 0x40
#define ENGINE_DEBUG      0x44

int main() {
    int fd = open("/dev/mem", O_RDWR | O_SYNC);
    if (fd < 0) {
        perror("Failed to open /dev/mem");
        return 1;
    }

    // Map BAR0 registers
    uint64_t bar0_phys = 0x04240000000ULL;
    volatile uint32_t* regs = (uint32_t*)mmap(NULL, BAR0_SIZE, 
                                              PROT_READ | PROT_WRITE,
                                              MAP_SHARED, fd, bar0_phys);
    if (regs == MAP_FAILED) {
        perror("Failed to map BAR0");
        close(fd);
        return 1;
    }

    printf("=== Engine Register Check ===\n");
    
    // First check standard registers to ensure device is accessible
    printf("\nStandard registers:\n");
    printf("  Control (0x00): 0x%08x\n", regs[0x00/4]);
    printf("  Scratch (0x1FC): 0x%08x\n", regs[0x1FC/4]);
    
    printf("\nEngine registers:\n");
    printf("  CMD_WORD0 (0x%02x): 0x%08x\n", ENGINE_CMD_WORD0, regs[ENGINE_CMD_WORD0/4]);
    printf("  CMD_WORD1 (0x%02x): 0x%08x\n", ENGINE_CMD_WORD1, regs[ENGINE_CMD_WORD1/4]);
    printf("  CMD_WORD2 (0x%02x): 0x%08x\n", ENGINE_CMD_WORD2, regs[ENGINE_CMD_WORD2/4]);
    printf("  CMD_WORD3 (0x%02x): 0x%08x\n", ENGINE_CMD_WORD3, regs[ENGINE_CMD_WORD3/4]);
    printf("  CMD_SUBMIT (0x%02x): 0x%08x\n", ENGINE_CMD_SUBMIT, regs[ENGINE_CMD_SUBMIT/4]);
    printf("  STATUS (0x%02x): 0x%08x\n", ENGINE_STATUS, regs[ENGINE_STATUS/4]);
    printf("  RESULT_COUNT (0x%02x): 0x%08x\n", ENGINE_RESULT_COUNT, regs[ENGINE_RESULT_COUNT/4]);
    printf("  DEBUG (0x%02x): 0x%08x\n", ENGINE_DEBUG, regs[ENGINE_DEBUG/4]);
    
    // Try writing to engine command registers
    printf("\nTrying to write to CMD_WORD0...\n");
    regs[ENGINE_CMD_WORD0/4] = 0x12345678;
    usleep(1000);
    uint32_t readback = regs[ENGINE_CMD_WORD0/4];
    if (readback == 0x12345678) {
        printf("  ✅ Write successful: 0x%08x\n", readback);
    } else {
        printf("  ❌ Write failed: got 0x%08x\n", readback);
    }
    
    munmap((void*)regs, BAR0_SIZE);
    close(fd);
    return 0;
}
