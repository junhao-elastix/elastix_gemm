#ifndef DEVICE_H
#define DEVICE_H

#include <iostream>
#include <string>
#include <functional>

using namespace std;

#define DEVICE_STATUS_OKAY 0
#define DEVICE_STATUS_ERROR -1

class BDF {
public:
    // PCI Bus, Device, Function
    // BDF format: 0000:bb:dd.f
    unsigned int bus;
    unsigned int dev;
    unsigned int fun;

    BDF() = default;
    BDF(unsigned int b, unsigned int d, unsigned int f) : bus(b), dev(d), fun(f) {}
    BDF(unsigned int bdf) {
        bus = (bdf >> 12) & 0xFF;
        dev = (bdf >> 4) & 0x1F;
        fun = bdf & 0x07;
    }
    BDF(const string &bdf_str) {
        sscanf(bdf_str.c_str(), "0000:%02x:%02x.%1x", &bus, &dev, &fun);
    }
    unsigned int to_int() const {
        return (bus << 12) | (dev << 4) | fun;
    }
    string to_str() const {
        char buf[16];
        snprintf(buf, sizeof(buf), "0000:%02x:%02x.%1x", bus, dev, fun);
        return string(buf);
    }

    string to_str_short() const {
        char buf[16];
        snprintf(buf, sizeof(buf), "%02x%02x%1x", bus, dev, fun);
        return string(buf);
    }

    friend ostream& operator<<(ostream &os, const BDF &bdf) {
        os << bdf.to_str();
        return os;
    }
};

class Device {
public:
    BDF bdf;
    bool ready = false;

    Device(const BDF &bdf) : bdf(bdf) {}
    ~Device() = default;

    virtual void print_info() = 0;

    virtual bool program(const char* bitstream) = 0;

    virtual bool mmioWrite(uint64_t addr, size_t size, char* buf) = 0;
    virtual bool mmioRead(uint64_t addr, size_t size, char* buf) = 0;

    virtual bool dmaWrite(uint64_t addr, size_t size, char* buf) = 0;
    virtual bool dmaRead(uint64_t addr, size_t size, char* buf) = 0;

    // ==================== INTERRUPT INTERFACE ====================
    
    // Interrupt callback function type
    typedef std::function<void(uint32_t vector_id)> InterruptHandler;
    
    // Capability discovery
    virtual bool hasInterrupts() const = 0;
    virtual uint32_t getInterruptVectorCount() const = 0;
    
    // Callback-based interrupt handling (non-blocking, immediate response)
    virtual bool registerInterruptHandler(uint32_t vector_id, InterruptHandler handler) = 0;
    virtual bool unregisterInterruptHandler(uint32_t vector_id) = 0;
    virtual bool startInterruptHandling() = 0;
    virtual void stopInterruptHandling() = 0;
    
    // Basic blocking interface (for compatibility and simple use cases)
    virtual bool waitForInterrupt(uint32_t vector_id, uint32_t timeout_ms = 5000) = 0;
    virtual void cancelInterruptWait(uint32_t vector_id) = 0;
    
    // Testing/debugging support
    virtual bool triggerInterrupt(uint32_t vector_id) = 0;
    
    // Advanced interrupt control
    virtual bool enableInterrupts() = 0;
    virtual bool disableInterrupts() = 0;

    // ==================== USAGE EXAMPLES ====================
    //
    // Callback-based interrupt handling (non-blocking, immediate response):
    //
    //   Device* device = new VP815(0);
    //   if (device->hasInterrupts()) {
    //       // Register callback for immediate response
    //       device->registerInterruptHandler(0, [](uint32_t vector_id) {
    //           std::cout << "Interrupt " << vector_id << " received!" << std::endl;
    //           process_immediate_response();  // Custom handling
    //       });
    //       
    //       device->startInterruptHandling();  // Start background thread
    //       
    //       // Main thread can continue other work...
    //       do_other_work();
    //       
    //       device->stopInterruptHandling();   // Clean shutdown
    //   }
    //
    // Blocking interface (for simple use cases):
    //
    //   if (device->waitForInterrupt(0, 1000)) {  // Vector 0, 1s timeout
    //       std::cout << "Interrupt received!" << std::endl;
    //   }
    //
    // =========================================================
};

#endif // DEVICE_H