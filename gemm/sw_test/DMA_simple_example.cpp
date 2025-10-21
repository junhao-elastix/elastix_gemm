// SDK/examples/DMA_simple_example/DMA_simple_example.cpp
// @copyright Copyright (c) 2022-@showdate "%Y " Achronix Semiconductor Corp. Portions Copyright  (c) 2021, 2022 Synopsys, Inc. Used with permission. All rights reserved. Synopsys & DesignWare are registered trademarks of Synopsys, Inc.

#include <stdio.h>
#include <string.h>
#include "Achronix_device.h"
#include "Achronix_DMA.h"

int main(int argc, char *argv[])
{
    int device_id = 0;
    const char *device_bdf = nullptr;
    if (argc > 1) {
        uint32_t dom, bus, dev, fun;
        int num_filled = sscanf(argv[1], "%x:%x:%x.%x", &dom, &bus, &dev, &fun);
        if (num_filled == 4) {
            device_bdf = argv[1];
        } else {
            num_filled = sscanf(argv[1], "%d", &device_id);
            if (num_filled != 1) {
                printf("ERROR! Illegal device identifier '%s'. The '%s' command must be followed by a valid device index (e.g. '1') or a valid BDF number (e.g. 0000:01:00.0). Default is index=0.\n", argv[1], argv[0]);
                return 1;
            }
        }
    }
    // open and initialize the PCIe device for use
    ACX_DEV_PCIe_device *device = nullptr;
    if (device_bdf != nullptr)
        device = acx_dev_init_pcie_device_bdf(device_bdf);
    else
        device = acx_dev_init_pcie_device_idx(device_id);
    if (device == nullptr || device->status != ACX_SDK_STATUS_OK) {
        if (device_bdf != nullptr)
            printf("ERROR: Failed to open device '%s'. Exiting.\n", device_bdf);
        else
            printf("ERROR: Failed to open device '%d'. Exiting.\n", device_id);
        return 1; 
    }
    
    // set up the device's DMA engine
    ACX_DMA_engine_context engine;
    acx_dma_build_engine_cntx(&engine, device, 0);
    acx_dma_init_engine_cntx(&engine);

    if (engine.status != ACX_SDK_STATUS_OK)
    {
        printf("ERROR: failed to setup dma engine\n");
        return 1;
    }

    printf("finished engine config\n");

    // data that will be needed for the transfers
    const size_t size = 4;
    uint32_t buff[4] = {
        0x001,
        0x002,
        0x003,
        0x004
    };
    const size_t size_in_bytes = sizeof(uint32_t) * size;
    const uint64_t dev_address = ACX_GDDR6_SPACE;

    // start the host to device trasnfer using the high level DMA functions
    ACX_DMA_transaction* h2d_transaction = NULL;
    ACX_SDK_STATUS status = acx_dma_start_xfer_h2d((void*)buff, size_in_bytes, dev_address, /*chan*/ 0, &engine, &h2d_transaction);

    //make sure that the returned transaction object is valid
    if (status != ACX_SDK_STATUS_OK)
    {
        printf("ERROR: failed to alloc h2d_transaction\n");
        return 1;
    }

    printf("started h2d transfer\n");

    // wait for the DMA transfer to finish
    ACX_DMA_TRANSFER_STATUS xfer_status = acx_dma_wait(h2d_transaction, 5);
    
    // make sure the transfer finished
    if (xfer_status != ACX_DMA_XFER_COMPLETE)
    {
        acx_dma_halt_tactn(h2d_transaction); // if the trasnfer did not finish halt it and exit
        printf("ERROR: failed to finish h2d dma transfer\n");
        return 1;
    }

    printf("h2d transfer complete\n");

    // cleanup the transaction object
    acx_dma_cleanup_tactn(h2d_transaction); 

    // start the device to host transfer
    ACX_DMA_transaction *d2h_transaction = NULL;
    status = acx_dma_start_xfer_d2h(size_in_bytes, dev_address, /*chan*/ 0, &engine, &d2h_transaction);

    //make sure that the returned transaction object is valid
    if (status != ACX_SDK_STATUS_OK)
    {
        printf("ERROR: failed to alloc d2h_transaction\n");
        return 1;
    }

    printf("started d2h transfer\n");

    // wait for the DMA transfer to finish
    xfer_status = acx_dma_wait(d2h_transaction, 5);
    
    // make sure the transfer finished
    if (xfer_status != ACX_DMA_XFER_COMPLETE)
    {   
        acx_dma_halt_tactn(d2h_transaction); // if the trasnfer did not finish halt it and exit
        printf("ERROR: failed to finish d2h dma transfer\n");
        return 1;
    }

    printf("d2h transfer complete. Comparing sent and received data...\n");

    int success = memcmp(buff, d2h_transaction->dma_buffer->data, size_in_bytes);
    
    //make sure to cleanup resources before exit
    acx_dma_cleanup_tactn(d2h_transaction);
    acx_dev_cleanup_pcie_device(device);

    if (success == 0)
        printf("SUCCESS: sent and received data matched\n");
    else
        printf("ERROR: sent and received data did not match\n");
    return success;
}
