#include <stdio.h>
#include <stdint.h>
#include <unistd.h>
#include "vp815.h"

int main() {
    vp815_t* dev = vp815_init(0);
    if (!dev) {
        printf("Failed to init device\n");
        return 1;
    }
    
    printf("=== Engine Status Decoder ===\n\n");
    
    // Read engine status multiple times to see if it changes
    for (int i = 0; i < 5; i++) {
        uint32_t status = vp815_bar0_read32(dev, 0x38);
        uint32_t mc_state_next = (status >> 16) & 0xF;
        uint32_t mc_state = (status >> 12) & 0xF;
        uint32_t dc_state = (status >> 8) & 0xF;
        uint32_t ce_state = (status >> 4) & 0xF;
        uint32_t gc_state = status & 0xF;
        
        printf("[%d] ENGINE_STATUS: 0x%x\n", i, status);
        printf("    MC_state_next=%x, MC_state=%x, DC_state=%x, CE_state=%x, GC_state=%x\n",
               mc_state_next, mc_state, dc_state, ce_state, gc_state);
        
        // Decode states
        const char* dc_states[] = {"IDLE", "FETCH_INIT", "FETCH_READ", "FETCH_WAIT", "FETCH_DONE", "DISP_ACK"};
        const char* ce_states[] = {"IDLE", "LOAD_LEFT_EXP", "LOAD_LEFT", "LOAD_RIGHT_EXP", "LOAD_RIGHT", 
                                   "COMPUTE_WAIT", "COMPUTE", "STORE", "DONE"};
        
        if (dc_state < 6) printf("    DC: %s\n", dc_states[dc_state]);
        if (ce_state < 9) printf("    CE: %s\n", ce_states[ce_state]);
        
        sleep(1);
    }
    
    printf("\n=== CE Control Signals (from master_control) ===\n");
    // The CE signals are outputs from master_control, check if they're asserted
    uint32_t debug = vp815_bar0_read32(dev, 0x24);
    printf("ENGINE_DEBUG: 0x%x\n", debug);
    
    vp815_cleanup(dev);
    return 0;
}
