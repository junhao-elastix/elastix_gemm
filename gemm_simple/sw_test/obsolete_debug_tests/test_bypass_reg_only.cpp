#include <iostream>
#include <iomanip>
#include <cstdint>
#include <cstdio>

int main() {
    // Read bypass register directly via /dev/mem (if we have access)
    // For now, just show we expect register at offset 0x24
    printf("Expected bypass register:\n");
    printf("  Address: BAR0 + 0x24 (offset 9 * 4 bytes)\n");
    printf("  Bits[1:0]: bypass_mode (0=normal, 1=skip, 2=forward)\n\n");
    
    printf("To test manually:\n");
    printf("  Use scan_registers to see all register values\n");
    printf("  Check offset 0x24 for bypass mode value\n");
    
    return 0;
}
