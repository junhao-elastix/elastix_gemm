// SDK/examples/DMA_example/DMA_example.cpp
// @copyright Copyright (c) 2022-@showdate "%Y " Achronix Semiconductor Corp. Portions Copyright  (c) 2021, 2022 Synopsys, Inc. Used with permission. All rights reserved. Synopsys & DesignWare are registered trademarks of Synopsys, Inc.

#include "Achronix_device.h"
#include "Achronix_util.h"
#include "Achronix_IP/Achronix_DBI_interface.h"
#include <iostream>
#include <vector>
#include <tuple>
#include <math.h>

#define DDR4_SIZE (1UL << 32)  // 4GB in Vectorpath S7tVG6
#define GDDR6_SIZE (1UL << 34) // 16GB in Vectorpath S7tVG6
#define NAP_SIZE (1UL << 14)   // in the demo design we know this is a 16K BRAM responder
#define DESCRIPTOR_SIZE 24     // each DMA descriptor (data or link) is 24 bytes
#define BRAM_DESCRIPTOR_MAX_NUM (NAP_SIZE/DESCRIPTOR_SIZE/2 - 2) // 682/2 - 2 = 340 (divide by 2 for duplex, sub two for link at the end)
#define BUFFER_DEFAULT_SIZE 0x400UL
#define BUFFER_MAX_SIZE 0x400000UL // DMA engine does not support transfers > one VM Page.  Will require linked-list support (unimplemented)

enum OptDmaDir {
    DIR_H2D,
    DIR_D2H,
    DIR_H2D2H_SIM,
    DIR_H2D2H_DUP
};

enum OptFill {
    FILL_RANDOM,
    FILL_DEADBEEF
};

enum PCIE_ENDPOINT_TYPE {
    ENDPOINT_UNDEFINED,
    ENDPOINT_GDDR6,
    ENDPOINT_DDR4,
    ENDPOINT_BRAM,
};

const char* pcie_endpoint_type_to_string(PCIE_ENDPOINT_TYPE endpoint_type)
{
    switch (endpoint_type)
    {
    case ENDPOINT_UNDEFINED: return "ENDPOINT_UNDEFINED";
    case ENDPOINT_GDDR6: return "ENDPOINT_GDDR6";
    case ENDPOINT_DDR4: return "ENDPOINT_DDR4";
    case ENDPOINT_BRAM: return "ENDPOINT_BRAM";
    default: return "unknown endpoint type";
    }
}

struct DMAOptions {
    int device_id;
    const char *device_bdf;
    int channel;
    int num_iters;
    uint64_t num_descriptors;
    uint64_t buffer_size_in_bytes;
    int verbosity;
    OptDmaDir direction;
    OptFill fill;
    PCIE_ENDPOINT_TYPE endpoint;
    PCIE_ENDPOINT_TYPE descriptor_endpoint;
    bool sanity();
    void dump();
};

bool DMAOptions::sanity() {
    // See Speedster7t NoC Address Mapping document for maximum address ranges
    // (No way to know if those address ranges are physically populated on the card)
    uint64_t max_ip_size = 0UL;
    if (endpoint ==ENDPOINT_GDDR6) {
        max_ip_size = 1UL << 30;
    } else if (endpoint ==ENDPOINT_DDR4) {
        max_ip_size = 1UL << 39;
    } else if (endpoint ==ENDPOINT_BRAM) {
        //max_ip_size = 1UL << 34;
        max_ip_size = 1UL << 14;  // in the demo design we know this is a 16K BRAM responder
    }

    uint64_t scaler = 1;
    if(direction == DIR_H2D2H_DUP) // duplex uses double the memory size for buffers and descriptors
        scaler = 2;

    uint64_t max_buffer_size = BUFFER_MAX_SIZE;
    max_buffer_size = std::min(max_buffer_size, max_ip_size);

    if (buffer_size_in_bytes == 0) {
        std::cerr << "ERROR: Value of --buffer_size "
                  << buffer_size_in_bytes
                  << " must be greater than zero"
                  << std::endl;
        return false;
    }

    if (buffer_size_in_bytes > max_buffer_size) {
        std::cerr << "ERROR: Value of --buffer_size "
                  << buffer_size_in_bytes
                  << " is out of range. For --endpoint "
                  << pcie_endpoint_type_to_string(endpoint)
                  << " the buffer size must be <= "
                  << max_buffer_size
                  << std::endl;
        return false;
    }

    uint64_t total_size_bytes = buffer_size_in_bytes * num_descriptors * scaler;
    if (total_size_bytes > max_ip_size) {
        std::cerr << "ERROR: Value of (--buffer_size * --list) "
                  << total_size_bytes
                  << " is out of range. For --endpoint "
                  << pcie_endpoint_type_to_string(endpoint)
                  << " in " << (direction == DIR_H2D2H_DUP ? "duplex" : "simplex") << " mode,"
                  << " the total number of bytes must be <= "
                  << max_ip_size
                  << std::endl;
        return false;
    }

    if (descriptor_endpoint ==ENDPOINT_BRAM && (num_descriptors + 1) * DESCRIPTOR_SIZE * scaler > NAP_SIZE) {
        std::cerr << "Error: Value of --list "
                  << num_descriptors
                  << " must be " << NAP_SIZE/DESCRIPTOR_SIZE/scaler - (scaler == 1 ? 0 : 2) << " or smaller wheb using --memory BRAM"
                  << std::endl;
        return false;
    }

    // Make sure that descriptors don't overflow the endpoint size. Not an issue for the BRAM 
    // endpoint because descriptors use a second dedicated BRAM.
    if (descriptor_endpoint == endpoint && endpoint != ENDPOINT_BRAM)
    {
        total_size_bytes += (DESCRIPTOR_SIZE * (num_descriptors + 1) * scaler);
        if (total_size_bytes > max_ip_size)
        {
            std::cerr << "Error: Combination of --list "
                  << num_descriptors
                  << " and --buffer_size "
                  << buffer_size_in_bytes
                  << " results in "
                  << total_size_bytes
                  << " bytes needed, which exceeds endpoint max size of "
                  << max_ip_size
                  << " bytes for endpoint "
                  << pcie_endpoint_type_to_string(endpoint)
                  << std::endl;
            return false;
        }
    }
    return true;
}

void DMAOptions::dump() {
    std::cout << "Options:" << std::endl;
    std::cout << "    device_id = " << device_id << std::endl;
    std::cout << "    device_bdf = " << device_bdf << std::endl;
    std::cout << "    channel = " << channel << std::endl;
    std::cout << "    num_iters = " << std::hex << num_iters << std::endl;
    std::cout << "    num_descriptors = " << std::hex << num_descriptors << std::endl;
    std::cout << "    buffer_size = " << buffer_size_in_bytes << " bytes" << std::endl;
    std::cout << "    verbosity = " << verbosity << std::endl;
    std::cout << "    direction = ";
    if (direction == DIR_H2D)
        std::cout << "H2D" << std::endl;
    else if (direction == DIR_D2H)
        std::cout << "D2H" << std::endl;
    else if (direction == DIR_H2D2H_DUP)
        std::cout << "H2D2H_DUP" << std::endl;
    else if (direction == DIR_H2D2H_SIM)
        std::cout << "H2D2H_SIM" << std::endl;
    std::cout << "    fill = ";
    if (fill == FILL_RANDOM)
        std::cout <<"random" << std::endl;
    else if (fill == FILL_DEADBEEF)
        std::cout << "deadbeef" << std::endl;
    std::cout << "endpoint = ";
    if (endpoint ==ENDPOINT_DDR4)
        std::cout << "DDR4" << std::endl;
    else if (endpoint ==ENDPOINT_GDDR6)
        std::cout << "GDDR6" << std::endl;
    else if (endpoint ==ENDPOINT_BRAM)
        std::cout << "BRAM" << std::endl;
    std::cout << "descriptor_endpoint = ";
    if (descriptor_endpoint ==ENDPOINT_DDR4)
        std::cout << "DDR4" << std::endl;
    else if (descriptor_endpoint ==ENDPOINT_GDDR6)
        std::cout << "GDDR6" << std::endl;
    else if (descriptor_endpoint ==ENDPOINT_BRAM)
        std::cout << "BRAM" << std::endl;
}

static void print_usage() {
    std::cout << "This application provides a demonstration of Achronix VectorPath(tm) DMA capabilities. To function correctly, the host machine" << std::endl;
    std::cout << "must have a VectorPath card mounted in a PCIe slot, and the card must be loaded with a compatible overlay bitstream. The " << std::endl;
    std::cout << "bitstream must have configured the PCIe, DDR4 and GDDR6 IPs, it must contain a BRAM responder macro at NAP col=7 row=8, and " << std::endl;
    std::cout << "it must have a DBI block configured. For more information about DBI block configuration" << std::endl;
    std::cout << "please see the Achronix SDK README file." << std::endl;
    std::cout << std::endl;
    std::cout << "Usage: dma_example <options>" << std::endl;
    std::cout << "<options> :" << std::endl;
    std::cout << "    [-b|--buffer_size] <int64> : The size of the host buffer in bytes (default = 0x" << std::hex << BUFFER_DEFAULT_SIZE << ", max = 0x" << std::hex << BUFFER_MAX_SIZE << " = 4MB)" << std::endl;
    std::cout << "    [-c|--channel] <int> : The DMA channel number (0-3)" << std::endl;
    std::cout << "    [-d|--direction] <string> : Transfer direction (Host to Device, or Device to Host, round trip simplex, or round trip duplex): one of \"H2D\", \"D2H\", \"H2D2H_SIM\", \"H2D2H_DUP\" (default = H2D2H_SIM)" << std::endl;
    std::cout << "    [-e|--endpoint] <string> : Endpoint type : one of \"DDR4\", \"GDDR6\", \"BRAM\" (default = GDDR6)" << std::endl;
    std::cout << "    [-f|--fill] <string> : Fill type of H2D buffer : one of \"random\", \"deadbeef\" (default = random)" << std::endl;
    std::cout << "    [-h|--help] : Prints this usage information" << std::endl;
    std::cout << "    [-i|--device_id] <int> : Specify the device to open by index (default = 0)" << std::endl;
    std::cout << "    [-l|--list] <int> : If nonzero use linked-list-mode with this number of DMA descriptors (default = 0, max = " << BRAM_DESCRIPTOR_MAX_NUM << " for \"-m BRAM\", 0x400 for \"-e DDR4\" in simplex mode (0x200 for duplex))" << std::endl;
    std::cout << "    [-m|--memory] <string> : Which local memory to hold descriptors in linked-list-mode: one of \"DDR4\", \"GDDR6\", \"BRAM\" (default = BRAM)" << std::endl;
    std::cout << "    [-n|--num_iters] <int> : Number of DMA iterations to run (default = 1)" << std::endl;
    std::cout << "    [-s|--slot <<domain>:<bus>:<device>.<func>>  Specify the device to open by slot (BDF) name (e.g. '0000:0b:00.0')" << std::endl;
    std::cout << "    [-v|--verbosity] <int> : Verbosity level during H2D2H buffer compare (0=none (default), 1=buffer mismatch)" << std::endl;
}

static int parse_int_arg( std::string &arg_name, std::string &arg_val )
{
    int lval = 0;
    try {
        lval = stoi(arg_val);
    }
    catch (const std::out_of_range &e) {
        std::cerr << "ERROR: Out-of-range value specified for " << arg_name << ": " << arg_val << std::endl;
        print_usage();
        exit(EXIT_FAILURE);
    }
    catch (...) {
        std::cerr << "ERROR: Illegal value specified for " << arg_name << ": " << arg_val << std::endl;
        print_usage();
        exit(EXIT_FAILURE);
    }
    return lval;
}

static uint64_t parse_uint64_arg( std::string &arg_name, std::string &arg_val )
{
    size_t size;
    int base = 0;  // allow hex formatting
    long long int lval = 0LL;
    try {
        lval = stoll(arg_val, &size, base);
    }
    catch (const std::out_of_range &e) {
        std::cerr << "ERROR: Out-of-range value specified for " << arg_name << ": " << arg_val << std::endl;
        print_usage();
        exit(EXIT_FAILURE);
    }
    catch (...) {
        std::cerr << "ERROR: Illegal value specified for " << arg_name << ": " << arg_val << std::endl;
        print_usage();
        exit(EXIT_FAILURE);
    }
    return lval;
}

static const char *parse_slot_name  ( std::string &arg_name, std::string &arg_val )
{
    uint32_t dom, bus, dev, fun;
    int num_filled = sscanf(arg_val.c_str(), "%x:%x:%x.%x", &dom, &bus, &dev, &fun);
    if (num_filled != 4) {
        std::cerr << "ERROR! Illegal slot name '" << arg_val << "'. The " << arg_name << " command must be followed by a valid slot name (e.g. 0000:01:00.0)" << std::endl;
        print_usage();
        exit(EXIT_FAILURE);
    }
    return arg_val.c_str();
}

static void get_options( int argc, char *argv[], DMAOptions &options)
{
    // Set defaults
    options.device_id = -1;
    options.device_bdf = nullptr;
    options.channel = 0;
    options.num_iters = 1;
    options.num_descriptors = 0x0;
    options.buffer_size_in_bytes = BUFFER_DEFAULT_SIZE;
    options.verbosity = 0;
    options.direction = DIR_H2D2H_SIM;
    options.fill = FILL_RANDOM;
    options.endpoint =ENDPOINT_GDDR6;
    options.descriptor_endpoint =ENDPOINT_BRAM;
    
    int argn = 1;
    while (argn < argc) {
        std::string arg_name = argv[argn++];
        if (arg_name == "-h" || arg_name == "--help")
        {
            print_usage();
            exit(EXIT_SUCCESS);
        }
        else if (arg_name == "-v" || arg_name == "--verbosity")
        {
            if (argn == argc) {
                std::cerr << "ERROR: The " << arg_name << " option requires an argument" << std::endl;
                print_usage();
                exit(EXIT_FAILURE);
            }
            std::string arg_val = argv[argn++];
            options.verbosity = parse_int_arg(arg_name, arg_val);
        }
        else if (arg_name == "-b" || arg_name == "--buffer_size")
        {
            if (argn == argc) {
                std::cerr << "ERROR: The " << arg_name << " option requires an argument" << std::endl;
                print_usage();
                exit(EXIT_FAILURE);
            }
            std::string arg_val = argv[argn++];
            options.buffer_size_in_bytes = parse_uint64_arg(arg_name, arg_val);
            if (options.buffer_size_in_bytes > BUFFER_MAX_SIZE) {
                std::cerr << "ERROR: The value of --buffer_size" << arg_name << " is too large.  A maximum of 4MB is supported." << std::endl;
                print_usage();
                exit(EXIT_FAILURE);
            }
        }
        else if (arg_name == "-c" || arg_name == "--channel")
        {
            if (argn == argc) {
                std::cerr << "ERROR: The " << arg_name << " option requires an argument" << std::endl;
                print_usage();
                exit(EXIT_FAILURE);
            }
            std::string arg_val = argv[argn++];
            options.channel = parse_int_arg(arg_name, arg_val);
            if (options.channel < 0 || options.channel > 3) {
                std::cerr << "ERROR: The value of --channel" << arg_name << " must be between 0 and 3" << std::endl;
                print_usage();
                exit(EXIT_FAILURE);
            }
        }
        else if (arg_name == "-i" || arg_name == "--device_id")
        {
            if (argn == argc) {
                std::cerr << "ERROR: The " << arg_name << " option requires an argument" << std::endl;
                print_usage();
                exit(EXIT_FAILURE);
            }
            std::string arg_val = argv[argn++];
            options.device_id = parse_int_arg(arg_name, arg_val);
        }
        else if (arg_name == "-s" || arg_name == "--slot")
        {
            if (argn == argc)
            {
                std::cerr << "ERROR: The " << arg_name << " option requires an argument" << std::endl;
                print_usage();
                exit(EXIT_FAILURE);
            }
            std::string arg_val = argv[argn++];
            options.device_bdf = parse_slot_name(arg_name, arg_val);
        }
        else if (arg_name == "-l" || arg_name == "--list")
        {
            if (argn == argc) {
                std::cerr << "ERROR: The " << arg_name << " option requires an argument" << std::endl;
                print_usage();
                exit(EXIT_FAILURE);
            }
            std::string arg_val = argv[argn++];
            options.num_descriptors = parse_uint64_arg(arg_name, arg_val);
        }
        else if (arg_name == "-n" || arg_name == "--num_iters")
        {
            if (argn == argc) {
                std::cerr << "ERROR: The " << arg_name << " option requires an argument" << std::endl;
                print_usage();
                exit(EXIT_FAILURE);
            }
            std::string arg_val = argv[argn++];
            options.num_iters = parse_int_arg(arg_name, arg_val);
        }
        else if (arg_name == "-d" || arg_name == "--direction")
        {
            if (argn == argc) {
                std::cerr << "ERROR: The " << arg_name << " option requires an argument" << std::endl;
                print_usage();
                exit(EXIT_FAILURE);
            }
            std::string arg_val = argv[argn++];
            if (arg_val == "h2d" || arg_val == "H2D")
                options.direction = DIR_H2D;
            else if (arg_val == "d2h" || arg_val == "D2H")
                options.direction = DIR_D2H;
            else if (arg_val == "h2d2h_dup" || arg_val == "H2D2H_DUP")
                options.direction = DIR_H2D2H_DUP;
            else if (arg_val == "h2d2h_sim" || arg_val == "H2D2H_SIM")
                options.direction = DIR_H2D2H_SIM;
            else {
                std::cerr << "ERROR: Illegal value specified for " << arg_name << ": " << arg_val << std::endl;
                print_usage();
                exit(EXIT_FAILURE);
            }
        }
        else if (arg_name == "-e" || arg_name == "--endpoint")
        {
            if (argn == argc) {
                std::cerr << "ERROR: The " << arg_name << " option requires an argument" << std::endl;
                print_usage();
                exit(EXIT_FAILURE);
            }
            std::string arg_val = argv[argn++];
            if (arg_val == "ddr4" || arg_val == "DDR4")
                options.endpoint =ENDPOINT_DDR4;
            else if (arg_val == "gddr6" || arg_val == "GDDR6")
                options.endpoint =ENDPOINT_GDDR6;
            else if (arg_val == "bram" || arg_val == "BRAM" || arg_val == "nap" || arg_val == "NAP")
                options.endpoint =ENDPOINT_BRAM;
            else {
                std::cerr << "ERROR: Illegal value specified for " << arg_name << ": " << arg_val << std::endl;
                print_usage();
                exit(EXIT_FAILURE);
            }
        }
        else if (arg_name == "-m" || arg_name == "--memory")
        {
            if (argn == argc) {
                std::cerr << "ERROR: The " << arg_name << " option requires an argument" << std::endl;
                print_usage();
                exit(EXIT_FAILURE);
            }
            std::string arg_val = argv[argn++];
            if (arg_val == "ddr4" || arg_val == "DDR4")
                options.descriptor_endpoint =ENDPOINT_DDR4;
            else if (arg_val == "gddr6" || arg_val == "GDDR6")
                options.descriptor_endpoint =ENDPOINT_GDDR6;
            else if (arg_val == "bram" || arg_val == "BRAM" || arg_val == "nap" || arg_val == "NAP")
                options.descriptor_endpoint =ENDPOINT_BRAM;
            else {
                std::cerr << "ERROR: Illegal value specified for " << arg_name << ": " << arg_val << std::endl;
                print_usage();
                exit(EXIT_FAILURE);
            }
        }
        else if (arg_name == "-f" || arg_name == "--fill")
        {
            if (argn == argc) {
                std::cerr << "ERROR: The " << arg_name << " option requires an argument" << std::endl;
                print_usage();
                exit(EXIT_FAILURE);
            }
            std::string arg_val = argv[argn++];
            if (arg_val == "random" || arg_val == "RANDOM")
                options.fill = FILL_RANDOM;
            else if (arg_val == "deadbeef" || arg_val == "DEADBEEF")
                options.fill = FILL_DEADBEEF;
            else {
                std::cerr << "ERROR: Illegal value specified for " << arg_name << ": " << arg_val << std::endl;
                print_usage();
                exit(EXIT_FAILURE);
            }
        }
        else
        {
            std::cerr << "WARNING: Unknown option " << arg_name << " will be ignored" << std::endl;
        }
    }

    // error check the device specifier
    if (options.device_id < 0 && options.device_bdf == nullptr)
        options.device_id = 0;
    else if (options.device_id >= 0 && options.device_bdf) {
        std::cerr << "ERROR: Can't specify both -i:--device_id and -s|--slot option" << std::endl;
            print_usage();
            exit(EXIT_FAILURE);
    }
}

// Logs a transaction's bandwidth result to console
static void log_result(
    ACX_DMA_transaction *tactn, 
    timespec *time_elapsed,
    ACX_DMA_TRANSFER_STATUS status,
    bool duplex
)
{
    double time_elapsed_seconds = acx_util_to_sec(time_elapsed);
    uint64_t total_bytes = tactn->mode == ACX_DMA_TACTN_BUFFER ? tactn->byte_count : (tactn->list_node->num_descriptors - 1) * tactn->list_node->dma_buffers[0]->size_in_bytes;
    double bandwidth = ((double)total_bytes / pow(2.0,20.0)) / time_elapsed_seconds;
    uint64_t from = tactn->mode == ACX_DMA_TACTN_BUFFER ? (uint64_t)(tactn->dma_buffer->dma_addr) : (uint64_t)(tactn->list_node->dma_buffers[0]->dma_addr);
    uint64_t to = tactn->device_address;
    std::string duplex_str = duplex ? "duplex " : "";
    if (tactn->direction == ACX_DMA_DEVICE_TO_HOST) std::swap(to, from);
    printf("%s%s transfer of %lu (0x%lx) bytes in %f milliseconds from 0x%lx to 0x%lx (%.3f MB/Sec): %s\n",
        duplex_str.c_str(),
        acx_dma_direction_to_string(tactn->direction),
        total_bytes,
        total_bytes,
        time_elapsed_seconds * 1000.0,
        from,
        to,
        bandwidth,
        acx_dma_xfer_status_to_string(status)
    );   
}

// uploads a transaction's descriptors to a device
static ACX_SDK_STATUS upload_descriptors(ACX_DMA_transaction *tactn)
{
    ACX_SDK_STATUS status = acx_dma_start_xfer_descs_w_tactn(tactn);
    if (status != ACX_SDK_STATUS_OK) return ACX_SDK_STATUS_ERROR;

    if (acx_dma_wait(tactn, /*timeout ms*/ 2000) != ACX_DMA_XFER_COMPLETE)
    {
        acx_dma_halt_tactn(tactn);
        std::cerr << "ERROR: failed to finish descriptor upload" << std::endl;
        return ACX_SDK_STATUS_ERROR;
    }

    // set the transfer state to perform a list transfer next
    acx_dma_set_list_xfer_state(tactn, ACX_DMA_LIST_STATE_XFER_LIST);

    return ACX_SDK_STATUS_OK;
}

/*
    run_dma_duplex:
    Configures and runs 2 DMA transactions in duplex. Will upload descriptors (if needed) if the transaction is in list mode

    Returns a pair consisting of a boolean status flag and an elapsed time timespec: <bool dma_complete, timespec dma_time_elapsed>
    dma_complete: true if one or both DMA operations completed without errors or timeouts
    dma_time_elapsed: The amount of time that the DMA transfer took to run. Time is zero if transfer failed to run.
 */
static std::pair<bool, timespec> run_dma_duplex(
    ACX_DMA_transaction *tactn_h2d,
    ACX_DMA_transaction *tactn_d2h,
    bool log = true
)
{
    timespec time_start, time_end, time_elapsed = {0,0};
    if (log)
    {
        printf("Starting duplex DMA on channel #%d...\n", tactn_h2d->channel);
    }

    // upload descriptors if needed
    if (tactn_h2d->mode != ACX_DMA_TACTN_BUFFER)
    {
        if (upload_descriptors(tactn_h2d) != ACX_SDK_STATUS_OK)
            return {false, time_elapsed};
        if (upload_descriptors(tactn_d2h) != ACX_SDK_STATUS_OK)
            return {false, time_elapsed};
    }

    // Confirgure the DMA read/write engine with parameters of the current transaction
    acx_dma_config_xfer(tactn_h2d);
    acx_dma_config_xfer(tactn_d2h);
    
    // Start the DMA transfer
    acx_util_clock_gettime(&time_start);
    acx_dma_start_xfer(tactn_h2d);
    acx_dma_start_xfer(tactn_d2h);

    // Wait for the transfer to finish or timeout. The wait is blocking, but both transfers will run at the same time.
    ACX_DMA_TRANSFER_STATUS status_h2d = acx_dma_wait(tactn_h2d, /*timeout ms*/ 2000);
    ACX_DMA_TRANSFER_STATUS status_d2h = acx_dma_wait(tactn_d2h, /*timeout ms*/ 2000);
    bool dma_complete = (status_h2d == ACX_DMA_XFER_COMPLETE && status_d2h == ACX_DMA_XFER_COMPLETE);

    // On a timeout make sure to halt the current transaction
    if (status_h2d != ACX_DMA_XFER_COMPLETE)
        acx_dma_halt_tactn(tactn_h2d);
    if (status_d2h != ACX_DMA_XFER_COMPLETE)
        acx_dma_halt_tactn(tactn_d2h);

    // Calculate final bandwidth.  Note that accuracy will be limitd by the 
    // polling interval in ac::dma_wait() which is currently 10 milliseconds.
    acx_util_clock_gettime(&time_end);
    acx_util_sub_timespec(&time_end, &time_start, &time_elapsed);

    if (log)
    {
        log_result(tactn_h2d, &time_elapsed, status_h2d, true);
        log_result(tactn_d2h, &time_elapsed, status_d2h, true);
    }

    return std::make_pair(dma_complete, time_elapsed);
}

/*
    run_dma_simplex:
    Configures and runs a dma transaction. Will upload descriptors (if needed) if the transaction is in list mode
    
    Returns a pair consisting of a boolean status flag and an elapsed time timespec: <bool dma_complete, timespec dma_time_elapsed>
    dma_complete: true if one or both DMA operations completed without errors or timeouts
    dma_time_elapsed: The amount of time that the DMA transfer took to run. Time is zero if transfer failed to run.
 */
static std::pair<bool, timespec> run_dma_simplex(ACX_DMA_transaction *tactn, bool log = true)
{
     timespec time_start, time_end, time_elapsed = {0,0};
    if (log)
    {
        const char *str1 = "Host";
        const char *str2 = "Device";
        if (tactn->direction == ACX_DMA_DEVICE_TO_HOST) std::swap(str1, str2);
        printf("Starting DMA from %s to %s on channel #%d...\n", str1, str2, tactn->channel);
    }

    // upload descriptors if needed
    if (tactn->mode != ACX_DMA_TACTN_BUFFER)
    {
        if (upload_descriptors(tactn) != ACX_SDK_STATUS_OK)
            return {false, time_elapsed};
    }

    // Confirgure the DMA read/write engine with parameters of the current transaction
    acx_dma_config_xfer(tactn);
    
    acx_util_clock_gettime(&time_start);

    // Start the DMA transfer
    acx_dma_start_xfer(tactn);
    // Wait for the transfer to finish or timeout
    ACX_DMA_TRANSFER_STATUS status = acx_dma_wait(tactn, /*timeout ms*/ 2000);
    bool dma_complete = (status == ACX_DMA_XFER_COMPLETE);

    // On a timeout make sure to halt the current transaction
    if (status != ACX_DMA_XFER_COMPLETE)
        acx_dma_halt_tactn(tactn);

    // Calculate final bandwidth.  Note that accuracy will be limitd by the 
    // polling interval in ac::dma_wait() which is currently 10 milliseconds.
    acx_util_clock_gettime(&time_end);
    acx_util_sub_timespec(&time_end, &time_start, &time_elapsed);

    if (log)
        log_result(tactn, &time_elapsed, status, false);

    return std::make_pair(dma_complete, time_elapsed);
}

/**
 * This function is based on the Vectorpath S7tVG6 card design which has 16GB
 * of GDDR6 memory. Each channel of each controller is populated with 1GB of memory.
 * Each controller has a max of 33 bits of address space, so with 1GB each that is 30 bits
 * of address space per controller. This means there is a hole in the address space in the top
 * 3 most significant bits of each controller's address space. This function will adjust incoming 
 * addresses to avoid the holes in those controllers and make the memory seem contiguous
 * 
 * This function will need to be rewritten if the GDDR6 hardware configuration changes.
*/
uint64_t gddr6_address_translation(uint64_t address)
{
    const static uint64_t GDDR6_ADDRESS_MASK = 0x3FFFFFFFUL; // 1GB address splace needs a 30 bit mask
    // first get the lower 30 bits of the address for a channel
    uint64_t channel_address = address & GDDR6_ADDRESS_MASK;
    // mask off the lower bits, leaving the upper 3 bits where the hole in the address space is
    // shift the upper bits out of the hole into the controller select bits
    uint64_t controller_select = (address & ~GDDR6_ADDRESS_MASK) << 3;
    // or together the channel address and the channel select bits
    uint64_t new_address = controller_select | channel_address;
    return new_address;
}

// builds a single buffer transaction object, returns null and prints to stderr if allocation failed
ACX_DMA_transaction* build_buffer_tactn(
    ACX_DMA_engine_context *engine_ctx,
    DMAOptions *options,
    uint64_t dev_addr,
    ACX_DMA_DIRECTION direction
)
{
    // allocate an empty transaction
    ACX_DMA_transaction *tactn = acx_dma_alloc_tactn(engine_ctx);

    if (tactn == NULL)
    {
        std::cerr << "ERROR: failed to allocate transaction object" << std::endl;
        return NULL;
    }

    // allocate a DMA buffer to hold the sent or received data
    ACX_DMA_buffer *dma_buf = acx_dma_alloc_buf(engine_ctx->device, options->buffer_size_in_bytes);

    if (dma_buf == NULL)
    {
        std::cerr << "ERROR: failed to allocate DMA buffer of size" << options->buffer_size_in_bytes << std::endl;
        return NULL;
    }

    // Build the transaction object for a single buffer transfer. No need to check status since args have already been checked for null.
    acx_dma_build_buf_tactn(tactn, dma_buf, options->channel, direction, 
        dev_addr, /*offset*/ 0, options->buffer_size_in_bytes
    );

    return tactn;
}

// builds a list transaction object, returns null and prints to stderr if allocation failed
// note: the transaction will have options->num_descriptors + 1 descriptors for the terminating link at the end
ACX_DMA_transaction* build_list_tactn(
    ACX_DMA_engine_context *engine_ctx, 
    DMAOptions *options,
    std::vector<ACX_DMA_buffer*> &dma_buffs,
    uint64_t descriptor_addr,
    uint64_t data_addr, 
    ACX_DMA_DIRECTION direction
)
{
    // allocate an empty transaction
    ACX_DMA_transaction *tactn = acx_dma_alloc_tactn(engine_ctx);

    if (tactn == NULL)
    {
        std::cerr << "ERROR: failed to allocate transaction object" << std::endl;
        return NULL;
    }

    // allocate the list node object
    ACX_DMA_list_node *list = acx_dma_alloc_list_node(engine_ctx->device, options->num_descriptors + 1, descriptor_addr, direction);
    
    if (list == NULL)
    {
        std::cerr << "ERROR: failed to allocate list object" << std::endl;
        return NULL;
    }

    // allocate the DMA buffers and associate each one with the list object
    for (size_t i = 0; i < options->num_descriptors; i++)
    {
        // offset each buffer so that they don't overlap
        uint64_t dev_addr = data_addr + i * options->buffer_size_in_bytes;

        if (options->endpoint == ENDPOINT_GDDR6)
            dev_addr = gddr6_address_translation(dev_addr);

        acx_dma_set_list_node_data_desc(list, i, dma_buffs[i], dev_addr, /*offset*/ 0, dma_buffs[i]->size_in_bytes);
    }

    // Terminate the list with a link. The end_transaction flag is set in order to terminate the DMA.  It will 
    // terminate before the link is consumed, so the link destination is a don't-care.
    acx_dma_set_list_node_link_desc(list, options->num_descriptors, /*next index*/ 0, /*end tactn*/ true);

    // Build the transaction object for list transfer. No need to check status since args have already been checked for null.
    acx_dma_build_list_tactn(tactn, list, options->channel, ACX_DMA_LIST_STATE_XFER_DESC);

    return tactn;
}

// fill a transaction's DMA buffer with 0xDEADBEEF values to facilitate visual bit-error debuggin
void fill_deadbeef(ACX_DMA_transaction *tactn)
{
    if (!tactn) return;
    if (tactn->mode == ACX_DMA_TACTN_BUFFER)
        acx_dma_fill_buf_deadbeef(tactn->dma_buffer);
    else
        for (size_t i = 0; i < tactn->list_node->num_descriptors - 1; i++)
            acx_dma_fill_buf_deadbeef(tactn->list_node->dma_buffers[i]);
}

// fill a transaction's DMA buffer with pseudo-random values to facilitate bit-error test coverage
void fill_random(ACX_DMA_transaction *tactn)
{
    if (!tactn) return;
    if (tactn->mode == ACX_DMA_TACTN_BUFFER)
        acx_dma_fill_buf_random(tactn->dma_buffer);
    else
        for (size_t i = 0; i < tactn->list_node->num_descriptors - 1; i++)
            acx_dma_fill_buf_random(tactn->list_node->dma_buffers[i]);
}

// zero-fill a transaction's DMA buffer, usually before it's used to receive new data
void fill_zero(ACX_DMA_transaction *tactn)
{
    if (!tactn) return;
    if (tactn->mode == ACX_DMA_TACTN_BUFFER)
        acx_dma_memset_buf(tactn->dma_buffer, 0x0);
    else
        for (size_t i = 0; i < tactn->list_node->num_descriptors - 1; i++)
            acx_dma_memset_buf(tactn->list_node->dma_buffers[i], 0x0);
}

// Main function
int main ( int argc, char *argv[] )
{
    timespec total_start, total_end, total_elapsed;
    acx_util_clock_gettime(&total_start);

    DMAOptions options;
    get_options(argc, argv, options);
    if (!options.sanity())
        return 1;

    // initiaize the PCIe device and get it's handle
    ACX_DEV_PCIe_device *device = nullptr;
    if (options.device_id >= 0)
        device = acx_dev_init_pcie_device_idx(options.device_id);
    else if (options.device_bdf)
        device = acx_dev_init_pcie_device_bdf(options.device_bdf);

    if (device == NULL || device->status != ACX_SDK_STATUS_OK)
    {
        if (options.device_id >= 0)
            std::cerr << "ERROR: Failed to open device " << options.device_id << ". Exiting." << std::endl;
        else if (options.device_bdf)
            std::cerr << "ERROR: Failed to open device " << options.device_bdf << ". Exiting." << std::endl;
        return 1;
    }

    // double check link health
    if (acx_util_pci_link_is_up(device) != ACX_SDK_STATUS_OK) 
    {
        std::cerr << "1ERROR: PCIe link appears to be down. Exiting." << std::endl;
        return 1;
    }

    // configure the selected part
    device->part_name = ACX_PART_AC7t1500; // USER : Change this to match the target part

    // Configure the BRAM responder locations.  There are two in the acx_sdk_vp_demo design.
    // One is reserved to demonstrate DMA to and from a NAP.  The other is reserved to store the DMA descriptor
    // lists. Note that each BRAM responder has 16KB of memory attached to the NAP, which is a maximum of 681 
    // data descriptors. If you need more descriptors then you must use the "-m DDR4" option to place the 
    // descriptors at the base of DDR4 space instead.  The AXI BRAM responder NAP locations are set in the 
    // project's pdc file.  The row and column numbers below must be changed if the NAP locations are changed.

    // BRAM responder location for DMA endpoint
    int axi_bram_resp_dma_col = 8;
    int axi_bram_resp_dma_row = 7;

    // BRAM responder location for descriptor list storage
    int axi_bram_resp_dl_col = 9;
    int axi_bram_resp_dl_row = 7;

    // calculate the DMA target addresses in the device
    uint64_t BRAM_RESP_DMA_SPACE = acx_util_nap_absolute_addr(device->part_name, axi_bram_resp_dma_col, axi_bram_resp_dma_row);
    uint64_t BRAM_RESP_DL_SPACE = acx_util_nap_absolute_addr(device->part_name, axi_bram_resp_dl_col, axi_bram_resp_dl_row);

    uint64_t device_phys_data_addr = 0x0;
    if (options.endpoint == ENDPOINT_DDR4)
        device_phys_data_addr = ACX_DDR4_SPACE;
    else if (options.endpoint == ENDPOINT_GDDR6)
        device_phys_data_addr = ACX_GDDR6_SPACE;
    else if (options.endpoint == ENDPOINT_BRAM) 
    {
        device_phys_data_addr = BRAM_RESP_DMA_SPACE;
        if (device_phys_data_addr == 0ul)
            return 1;
    } 
    else 
    {
        std::cerr << "ERROR: endpoint type is unimplemented" << std::endl;
        return 1;
    }

    //build a DMA engine using the opened device, and then configure the DMA engine for use
    ACX_DMA_engine_context engine_ctx;
    acx_dma_build_engine_cntx(&engine_ctx, device, 0);
    acx_dma_init_engine_cntx(&engine_ctx);

    ACX_DMA_transaction *tactn_h2d = NULL;       // transaction for host-to-device transfers
    ACX_DMA_transaction *tactn_d2h = NULL;       // transaction for device-to-host transfers
    
    /*
        tactn_h2d_init is only used for duplex transfers. The duplex transfer will happen in 
        two steps:
        1.  First it will a simplex transfer will be run to populate the device with data using 
            tactn_h2d_init. tactn_h2d_init will hold pointers to the same buffers as the tactn_h2d 
            transaction, but it's destination will be offset to write to the same location that
            tactn_d2h will read from. This is needed because reading and writing from the same 
            location in duplex is unsafe operation
        2.  The duplex transfer will be run using tactn_h2d and tactn_d2h. tactn_d2h will read the data
            that has already been written by tactn_h2d_init in step 1.
        Both tactn_h2d and tactn_h2d_init point to the same DMA buffers, this both reduces used memory
        overhead and allows for the comparison code to not need a special case for duplex transfer.

        start = endpoint start address
        size  = transaction size in bytes

        | first transfer (simplex) | second transfer (duplex) | - location
        |                          | tactn_h2d                | - [start, start + size]
        | tactn_h2d_init           | tactn_d2h                | - [start + size, start + 2 * size]
    */ 
   ACX_DMA_transaction *tactn_h2d_init = NULL;
    
    // Build the DMA transaction objects. Setup depends on the direction mode delected on the command line, and whether
    // this is a simple DMA transfer or a list-mode transfer.
    if (options.num_descriptors == 0) // Single buffer mode
    {
        if (options.direction != DIR_D2H) // don't alloc a h2d buffer for d2h mode
        {
            tactn_h2d = build_buffer_tactn(&engine_ctx, &options, device_phys_data_addr, ACX_DMA_HOST_TO_DEVICE);
            if (tactn_h2d == NULL) return 1;
        }
        // if in duplex mode offset the addresses so that the reads and writes don't collide
        if (options.direction == DIR_H2D2H_DUP) device_phys_data_addr += options.buffer_size_in_bytes;
        if (options.direction != DIR_H2D) // don't alloc a d2h buffer for h2d mode
        {
            tactn_d2h = build_buffer_tactn(&engine_ctx, &options, device_phys_data_addr, ACX_DMA_DEVICE_TO_HOST);
            if (tactn_d2h == NULL) return 1;
        }
        if (options.direction == DIR_H2D2H_DUP)
        {
            // if duplex mode then make another transaction object that points past the data intially written
            tactn_h2d_init = acx_dma_alloc_tactn(&engine_ctx);
            if (!tactn_h2d_init)
            {
                std::cerr << "ERROR: failed to allocate transaction object" << std::endl;
                return 1;
            }
            // point to the buffer held by tactn_h2d rather than building a whole new buffer
            acx_dma_build_buf_tactn(tactn_h2d_init, tactn_h2d->dma_buffer, options.channel, 
                ACX_DMA_HOST_TO_DEVICE, device_phys_data_addr, 0, options.buffer_size_in_bytes
            );
        }
    }
    else
    {
        // If descriptors are stored in the same memory as the DMA endpoint, leave extra room at the base of the memory to hold the descriptors.
        // Ignore the BRAM endpoint since it has a dedicated separate area for descriptors.
        if (options.descriptor_endpoint == options.endpoint && options.descriptor_endpoint != ENDPOINT_BRAM) 
            device_phys_data_addr += (options.num_descriptors + 1) * DESCRIPTOR_SIZE * (options.direction == DIR_H2D2H_DUP ? 2 : 1);

        uint64_t device_phys_desc_addr = 0x0;
        
        if (options.descriptor_endpoint == ENDPOINT_DDR4)
            device_phys_desc_addr = ACX_DDR4_SPACE;
        else if (options.descriptor_endpoint == ENDPOINT_GDDR6)
            device_phys_desc_addr = ACX_GDDR6_SPACE;
        else if (options.descriptor_endpoint == ENDPOINT_BRAM) 
        {
            device_phys_desc_addr = BRAM_RESP_DL_SPACE;
            if (device_phys_desc_addr == 0ul)
                return 1;
        } 
        else 
        {
            std::cerr << "ERROR: descriptor endpoint type is unimplemented" << std::endl;
            return 1;
        }

        std::vector<ACX_DMA_buffer*> h2d_buffs;
        std::vector<ACX_DMA_buffer*> d2h_buffs;

        // build the DMA buffers, one for each descriptor, that will be used to store the sent and received data
        for (size_t i = 0; i < options.num_descriptors; i++)
        {
            h2d_buffs.push_back(acx_dma_alloc_buf(device, options.buffer_size_in_bytes));
            d2h_buffs.push_back(acx_dma_alloc_buf(device, options.buffer_size_in_bytes));
            if (h2d_buffs.back() == NULL || d2h_buffs.back() == NULL)
            {
                std::cerr << "ERROR: failed to allocate DMA buffer of size" << options.buffer_size_in_bytes << std::endl;
                return 1;
            }
        }

        if (options.direction != DIR_D2H)
        {
            tactn_h2d = build_list_tactn(&engine_ctx, &options, h2d_buffs, device_phys_desc_addr, device_phys_data_addr, ACX_DMA_HOST_TO_DEVICE);
            if (tactn_h2d == NULL) return 1;
        }
        // if in duplex mode offset the data and descriptor addresses so that the reads and writes don't collide
        if (options.direction == DIR_H2D2H_DUP)
        {
            device_phys_data_addr += options.buffer_size_in_bytes * options.num_descriptors;
            device_phys_desc_addr += (options.num_descriptors + 1) * DESCRIPTOR_SIZE;
        }
        if (options.direction != DIR_H2D)
        {
            tactn_d2h = build_list_tactn(&engine_ctx, &options, d2h_buffs, device_phys_desc_addr, device_phys_data_addr, ACX_DMA_DEVICE_TO_HOST);
            if (tactn_d2h == NULL) return 1;
        }
        if (options.direction == DIR_H2D2H_DUP)
        {
            // for duplex mode, use the same buffers for the initial and final transaction, so no data needs to be copied
            tactn_h2d_init = build_list_tactn(&engine_ctx, &options, h2d_buffs, device_phys_desc_addr, device_phys_data_addr, ACX_DMA_HOST_TO_DEVICE);
            if (tactn_h2d_init == NULL) return 1;
        }
    }

    if (options.fill == FILL_DEADBEEF)
        fill_deadbeef(tactn_h2d); 

    int num_passed = 0, num_dma_incomplete = 0, num_compare_failures = 0;
    timespec dma_time_total = {0,0};
    for (int iter = 1; iter <= options.num_iters; ++iter) 
    {
        // double check link health again before each iteration
        if (acx_util_pci_link_is_up(device) != ACX_SDK_STATUS_OK) 
        {
            std::cerr << "ERROR: PCIe link appears to be down. Exiting." << std::endl;
            break;
        }

        // If random is set then refill for every iter to improve test coverage.
        // Alternatively, if deadbeef mode, keep it the same to make bit-errors easy to spot by eye.
        if (options.fill == FILL_RANDOM)
            fill_random(tactn_h2d);

        // zero out the d2h buffer each time to make sure we aren't comparing stale data
        fill_zero(tactn_d2h);

        if (options.num_iters > 1)
            printf("---- Begin iteration #%d ----\n", iter);
        bool dma_complete, compare_success = true;
        timespec dma_time_elapsed;

        if (options.direction == DIR_H2D2H_SIM) 
        {
            // roundtrip simplex done via 2 simplex runs
            bool complete_temp;
            timespec time_1, time_2;
            std::tie(complete_temp, time_1) = run_dma_simplex (tactn_h2d, true);
            std::tie(dma_complete, time_2) = run_dma_simplex (tactn_d2h, true);
            dma_complete = complete_temp && dma_complete;
            acx_util_add_timespec(&time_1, &time_2, &dma_time_elapsed);
        }
        else if (options.direction == DIR_H2D2H_DUP) 
        {
            // first do a simplex transfer to populate data on the device, enabling the duplex to do bit-error checking
            timespec time_ignored;
            std::tie(dma_complete, time_ignored) = run_dma_simplex(tactn_h2d_init, false);
            // now do a duplex transfer to test simultaneous transfers in both directions
            if (dma_complete)
                std::tie(dma_complete, dma_time_elapsed) = run_dma_duplex(tactn_h2d, tactn_d2h, true);
        }
        else
        {
            // simple single-direction transfer (with no bit-error checking)
            ACX_DMA_transaction *tactn = options.direction == DIR_H2D ? tactn_h2d : tactn_d2h;
            std::tie(dma_complete, dma_time_elapsed) = run_dma_simplex(tactn, true);
        }

        // Compare sent/received data. Don't compare for non round trip modes.
        if (options.direction != DIR_H2D && options.direction != DIR_D2H)
        {
            size_t i = 0;
            if (options.num_descriptors == 0)
                compare_success = acx_dma_compare_buf(tactn_h2d->dma_buffer, tactn_d2h->dma_buffer) == 0;
            else
                for (; i < options.num_descriptors; i++)
                {
                    compare_success &= acx_dma_compare_buf(tactn_h2d->list_node->dma_buffers[i], tactn_d2h->list_node->dma_buffers[i]) == 0;
                    if (!compare_success) break;
                }

            if (options.verbosity == 1)
            {
                if (!compare_success)
                {
                    printf("Buffer compare failed\n");
                    ACX_DMA_buffer *buf = options.num_descriptors == 0 ? tactn_h2d->dma_buffer : tactn_h2d->list_node->dma_buffers[i];
                    printf("Host to device buffer\n");
                    acx_dma_print_buf(buf);
                    buf = options.num_descriptors == 0 ? tactn_d2h->dma_buffer : tactn_d2h->list_node->dma_buffers[i];
                    printf("Device to host buffer\n");
                    acx_dma_print_buf(buf);
                }
            }

            printf("Buffer compare: %s\n", compare_success ? "PASSED" : "FAILED");
        }

        acx_util_add_timespec(&dma_time_elapsed, &dma_time_total, &dma_time_total);
        if (dma_complete && compare_success)
            num_passed++;
        if (!dma_complete)
            num_dma_incomplete++;
        if (!compare_success)
            num_compare_failures++;
        if (options.num_iters > 1)
            printf("---- End iteration #%d ----\n\n", iter);
    }

    double dma_time_seconds = acx_util_to_sec(&dma_time_total);
    if (options.num_iters > 1)
    {
        printf("Final results: %d of %d iterations passed (%d dma timeouts, %d buffer compare failures)\n",
            num_passed, options.num_iters, num_dma_incomplete, num_compare_failures
        );
        printf("Average time per iteration: %f sec\n\n", dma_time_seconds/(double)num_passed);
    }

    acx_util_clock_gettime(&total_end);
    acx_util_sub_timespec(&total_end, &total_start, &total_elapsed);
    double total_elapsed_seconds = acx_util_to_sec(&total_elapsed);
    printf("Total wallclock time: %f sec (%f sec/iteration)\n\n", total_elapsed_seconds, total_elapsed_seconds/(double)options.num_iters);

    // Cleanup memory and release resources back to the system
    acx_dma_cleanup_tactn(tactn_h2d);
    acx_dma_cleanup_tactn(tactn_d2h);
    if (options.direction == DIR_H2D2H_DUP)
    {
        // The tactn_h2d_init and tactn_h2d both point to the same DMA buffers. 
        // Need to clean up the transaction object, but not its buffers, since they are already freed by the call
        // to cleanup tactn_h2d.
        if(options.num_descriptors > 0) acx_dma_cleanup_list_node_no_payload(tactn_h2d_init->list_node);
        acx_dma_cleanup_tactn_no_payload(tactn_h2d_init);
    }
    acx_dev_cleanup_pcie_device(device);
    return 0;
}
