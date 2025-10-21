// Quick utility to calculate correct BRAM address after NAP relocation
// NAP moved from [8][7] to [3][5] - need to verify address change

#include <stdio.h>
#include <stdint.h>
#include "../../../acxsdk/include/Achronix_device.h"
#include "../../../acxsdk/include/Achronix_util.h"

int main() {
    // Old placement: NAP[8][7]
    uint64_t old_base = acx_util_nap_absolute_addr(ACX_PART_AC7t1500, 8, 7);
    uint64_t old_addr = old_base + 0x8000;

    // New placement: NAP[3][5]
    uint64_t new_base = acx_util_nap_absolute_addr(ACX_PART_AC7t1500, 3, 5);
    uint64_t new_addr = new_base + 0x8000;

    printf("=== NAP Address Calculation ===\n");
    printf("Old NAP[8][7] base:   0x%016llx\n", old_base);
    printf("Old address + 0x8000: 0x%016llx\n", old_addr);
    printf("\n");
    printf("New NAP[3][5] base:   0x%016llx\n", new_base);
    printf("New address + 0x8000: 0x%016llx\n", new_addr);
    printf("\n");

    if (old_addr != new_addr) {
        printf("❌ ADDRESSES DIFFER - Test using wrong address!\n");
        printf("   Test hardcodes: 0x4460008000\n");
        printf("   Should use:     0x%016llx\n", new_addr);
    } else {
        printf("✅ Addresses are the same\n");
    }

    return 0;
}
