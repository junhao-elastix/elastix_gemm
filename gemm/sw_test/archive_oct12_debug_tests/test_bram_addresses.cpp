// Simple BRAM address test
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <fcntl.h>
#include <sys/mman.h>
#include <unistd.h>

int main() {
    // Open BAR2 for BRAM access
    int fd = open("/sys/bus/pci/devices/0000:01:00.0/resource2", O_RDWR | O_SYNC);
    if (fd < 0) {
        perror("Failed to open BAR2");
        return 1;
    }

    // Map entire BAR2 (assuming 256MB)
    size_t bar_size = 256ULL * 1024 * 1024;
    void* bar2 = mmap(NULL, bar_size, PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
    if (bar2 == MAP_FAILED) {
        perror("Failed to mmap BAR2");
        close(fd);
        return 1;
    }

    printf("=== BRAM Address Scan ===\n\n");

    // Test addresses (offset within BAR2)
    uint64_t test_offsets[] = {
        0x0060008000ULL,  // OLD: NAP[8][7] - convert to BAR offset
        0x0038008000ULL,  // Guess: NAP[3][5]
        0x0035008000ULL,  // Guess: NAP[3][5]
        0x0030008000ULL,  // Guess: NAP[3][5]
        0x0070008000ULL,  // ATU: NAP[7][7]
    };

    for (int i = 0; i < 5; i++) {
        // Write test pattern
        uint32_t pattern = 0x12340000 + i;
        uint64_t offset = test_offsets[i];
        
        if (offset < bar_size) {
            volatile uint32_t* addr = (volatile uint32_t*)((char*)bar2 + offset);
            *addr = pattern;
            uint32_t readback = *addr;

            printf("Offset 0x%012lx: ", offset);
            if (readback == pattern) {
                printf("✅ BRAM FOUND!\n");
            } else if (readback == 0xFFFFFFFF) {
                printf("❌ No device\n");
            } else {
                printf("⚠️  Unexpected 0x%08x\n", readback);
            }
        }
    }

    munmap(bar2, bar_size);
    close(fd);
    return 0;
}
