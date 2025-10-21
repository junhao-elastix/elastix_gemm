// Quick debug: Check if result_bram_writer is actually firing
#include <stdio.h>
#include <stdint.h>
#include <unistd.h>
#include "../../acxsdk/include/Achronix_device.h"
#include "../../acxsdk/include/Achronix_util.h"

int main() {
    ACX_DEV_PCIe_device* device = NULL;
    
    if (acx_device_init(&device, ACX_DEV_ACHRONIX, 0) != ACX_SDK_STATUS_OK) {
        printf("Failed to initialize device\n");
        return 1;
    }

    // Check result count register (should increment if writer is active)
    uint32_t addr = 0x28 + 0x4240000000ULL;  // ENGINE_RESULT_COUNT
    uint32_t count_before, count_after;
    
    // Read initial count
    acx_device_read32(device, addr, &count_before);
    printf("Initial result count: %u\n", count_before);
    
    // Issue a simple MATMUL (will fail but writer should try)
    uint32_t cmd_addr_base = 0x3c + 0x4240000000ULL;
    
    // Reset engine first
    acx_device_write32(device, 0x4240000000ULL, 0x2);
    usleep(1000);
    acx_device_write32(device, 0x4240000000ULL, 0x0);
    
    // Issue MATMUL with small params
    acx_device_write32(device, cmd_addr_base, 0x100f2);  // MATMUL, id=1, len=0
    acx_device_write32(device, cmd_addr_base + 4, 0x0);
    acx_device_write32(device, cmd_addr_base + 8, 0x80080);  // B=1,C=1,V=8
    acx_device_write32(device, cmd_addr_base + 12, 0x0);
    
    // Trigger command
    uint32_t submit_addr = 0x4c + 0x4240000000ULL;
    acx_device_write32(device, submit_addr, 0x1);
    
    // Wait a bit
    usleep(100000);  // 100ms
    
    // Read count after
    acx_device_read32(device, addr, &count_after);
    printf("After MATMUL count: %u\n", count_after);
    
    if (count_after > count_before) {
        printf("✅ Result writer IS firing! (count increased by %u)\n", count_after - count_before);
    } else {
        printf("❌ Result writer NOT firing (count unchanged)\n");
    }
    
    acx_device_close(device);
    return 0;
}
