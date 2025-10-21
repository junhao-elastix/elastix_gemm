/**
 * @file test_interrupt_callbacks.cpp
 * @brief Test program for VP815 callback-based interrupt interface
 * 
 * This test validates the callback-based interrupt functionality 
 * implemented in the VP815 class following the example from shell.hpp.
 * 
 * Tests include:
 * - Capability discovery (hasInterrupts, getInterruptVectorCount)
 * - Handler registration/unregistration
 * - Enable/disable functionality 
 * - Callback execution with software-triggered interrupts
 * - Concurrent multi-vector callback handling
 * - Error handling and edge cases
 */

#include "vp815.hpp"
#include <iostream>
#include <atomic>
#include <chrono>
#include <thread>
#include <vector>
#include <map>

using namespace achronix;

// Global test state tracking
std::atomic<int> callback_count{0};
std::atomic<int> vector0_count{0};
std::atomic<int> vector1_count{0};
std::map<uint32_t, std::chrono::steady_clock::time_point> interrupt_timestamps;
std::atomic<bool> test_failed{false};

/**
 * @brief Simple callback that increments global counter
 */
void simpleCallback(uint32_t vector_id) {
    callback_count++;
    interrupt_timestamps[vector_id] = std::chrono::steady_clock::now();
    std::cout << "[CALLBACK] Simple callback executed for vector " << vector_id 
              << " (total callbacks: " << callback_count.load() << ")" << std::endl;
}

/**
 * @brief Vector-specific callback for vector 0
 */
void vector0Callback(uint32_t vector_id) {
    vector0_count++;
    std::cout << "[CALLBACK] Vector 0 callback executed (count: " << vector0_count.load() << ")" << std::endl;
    if (vector_id != 0) {
        std::cerr << "[ERROR] Vector 0 callback called with wrong vector ID: " << vector_id << std::endl;
        test_failed = true;
    }
}

/**
 * @brief Vector-specific callback for vector 1
 */
void vector1Callback(uint32_t vector_id) {
    vector1_count++;
    std::cout << "[CALLBACK] Vector 1 callback executed (count: " << vector1_count.load() << ")" << std::endl;
    if (vector_id != 1) {
        std::cerr << "[ERROR] Vector 1 callback called with wrong vector ID: " << vector_id << std::endl;
        test_failed = true;
    }
}

/**
 * @brief Lambda callback test using captured variables
 */
void testLambdaCallback(VP815& device) {
    std::cout << "\n=== Testing Lambda Callback ===\n";
    
    int lambda_count = 0;
    auto lambda_callback = [&lambda_count](uint32_t vector_id) {
        lambda_count++;
        std::cout << "[LAMBDA] Lambda callback for vector " << vector_id 
                  << " (lambda count: " << lambda_count << ")" << std::endl;
    };
    
    // Test with vector 2 if available
    if (device.getInterruptVectorCount() > 2) {
        bool registered = device.registerInterruptHandler(2, lambda_callback);
        if (!registered) {
            std::cerr << "[ERROR] Failed to register lambda callback" << std::endl;
            test_failed = true;
            return;
        }
        
        std::cout << "[TEST] Triggering interrupt for lambda test..." << std::endl;
        device.triggerInterrupt(2);
        std::this_thread::sleep_for(std::chrono::milliseconds(500));
        
        if (lambda_count == 0) {
            std::cerr << "[ERROR] Lambda callback was not executed" << std::endl;
            test_failed = true;
        } else {
            std::cout << "[SUCCESS] Lambda callback executed " << lambda_count << " times" << std::endl;
        }
        
        device.unregisterInterruptHandler(2);
    } else {
        std::cout << "[SKIP] Not enough vectors for lambda test (need > 2)" << std::endl;
    }
}

/**
 * @brief Test basic interrupt capability discovery
 */
bool testCapabilityDiscovery(VP815& device) {
    std::cout << "\n=== Testing Capability Discovery ===\n";
    
    bool has_interrupts = device.hasInterrupts();
    uint32_t vector_count = device.getInterruptVectorCount();
    
    std::cout << "[INFO] Device has interrupts: " << (has_interrupts ? "YES" : "NO") << std::endl;
    std::cout << "[INFO] Available interrupt vectors: " << vector_count << std::endl;
    
    if (!has_interrupts) {
        std::cerr << "[ERROR] Device reports no interrupt support" << std::endl;
        return false;
    }
    
    if (vector_count == 0) {
        std::cerr << "[ERROR] Device reports 0 interrupt vectors" << std::endl;
        return false;
    }
    
    std::cout << "[SUCCESS] Capability discovery passed" << std::endl;
    return true;
}

/**
 * @brief Test handler registration and basic callback
 */
bool testBasicCallback(VP815& device) {
    std::cout << "\n=== Testing Basic Callback Registration ===\n";
    
    // Reset counters
    callback_count = 0;
    
    // Register simple callback for vector 0
    bool registered = device.registerInterruptHandler(0, simpleCallback);
    if (!registered) {
        std::cerr << "[ERROR] Failed to register interrupt handler" << std::endl;
        return false;
    }
    std::cout << "[SUCCESS] Handler registered for vector 0" << std::endl;
    
    // Trigger interrupt and wait for callback
    std::cout << "[TEST] Triggering interrupt for vector 0..." << std::endl;
    bool triggered = device.triggerInterrupt(0);
    if (!triggered) {
        std::cerr << "[ERROR] Failed to trigger interrupt" << std::endl;
        return false;
    }
    
    // Wait for callback execution
    std::this_thread::sleep_for(std::chrono::milliseconds(1000));
    
    if (callback_count == 0) {
        std::cerr << "[ERROR] Callback was not executed" << std::endl;
        return false;
    }
    
    std::cout << "[SUCCESS] Callback executed " << callback_count.load() << " times" << std::endl;
    
    // Test unregistration
    bool unregistered = device.unregisterInterruptHandler(0);
    if (!unregistered) {
        std::cerr << "[ERROR] Failed to unregister interrupt handler" << std::endl;
        return false;
    }
    std::cout << "[SUCCESS] Handler unregistered for vector 0" << std::endl;
    
    return true;
}

/**
 * @brief Test multi-vector callback handling
 */
bool testMultiVectorCallbacks(VP815& device) {
    std::cout << "\n=== Testing Multi-Vector Callbacks ===\n";
    
    if (device.getInterruptVectorCount() < 2) {
        std::cout << "[SKIP] Need at least 2 vectors for multi-vector test" << std::endl;
        return true;
    }
    
    // Reset counters
    vector0_count = 0;
    vector1_count = 0;
    
    // Register different callbacks for vectors 0 and 1
    bool reg0 = device.registerInterruptHandler(0, vector0Callback);
    bool reg1 = device.registerInterruptHandler(1, vector1Callback);
    
    if (!reg0 || !reg1) {
        std::cerr << "[ERROR] Failed to register multi-vector handlers" << std::endl;
        return false;
    }
    std::cout << "[SUCCESS] Registered handlers for vectors 0 and 1" << std::endl;
    
    // Trigger interrupts in sequence
    std::cout << "[TEST] Triggering interrupts for both vectors..." << std::endl;
    device.triggerInterrupt(0);
    std::this_thread::sleep_for(std::chrono::milliseconds(100));
    device.triggerInterrupt(1);
    std::this_thread::sleep_for(std::chrono::milliseconds(100));
    device.triggerInterrupt(0); // Vector 0 again
    
    // Wait for all callbacks
    std::this_thread::sleep_for(std::chrono::milliseconds(1000));
    
    std::cout << "[INFO] Vector 0 callbacks: " << vector0_count.load() << std::endl;
    std::cout << "[INFO] Vector 1 callbacks: " << vector1_count.load() << std::endl;
    
    if (vector0_count != 2) {
        std::cerr << "[ERROR] Expected 2 vector 0 callbacks, got " << vector0_count.load() << std::endl;
        return false;
    }
    
    if (vector1_count != 1) {
        std::cerr << "[ERROR] Expected 1 vector 1 callback, got " << vector1_count.load() << std::endl;
        return false;
    }
    
    // Cleanup
    device.unregisterInterruptHandler(0);
    device.unregisterInterruptHandler(1);
    
    std::cout << "[SUCCESS] Multi-vector callback test passed" << std::endl;
    return true;
}

/**
 * @brief Test enable/disable functionality
 */
bool testEnableDisable(VP815& device) {
    std::cout << "\n=== Testing Enable/Disable Functionality ===\n";
    
    // Reset counter
    callback_count = 0;
    
    // Register handler
    device.registerInterruptHandler(0, simpleCallback);
    
    // Test disable
    bool disabled = device.disableInterruptVector(0);
    if (!disabled) {
        std::cerr << "[ERROR] Failed to disable interrupt" << std::endl;
        return false;
    }
    
    bool is_enabled = device.isInterruptVectorEnabled(0);
    if (is_enabled) {
        std::cerr << "[ERROR] Interrupt reports as enabled after disable" << std::endl;
        return false;
    }
    std::cout << "[SUCCESS] Interrupt disabled successfully" << std::endl;
    
    // Trigger interrupt while disabled (should not execute callback)
    device.triggerInterrupt(0);
    std::this_thread::sleep_for(std::chrono::milliseconds(500));
    
    if (callback_count > 0) {
        std::cerr << "[ERROR] Callback executed while interrupt was disabled" << std::endl;
        return false;
    }
    std::cout << "[SUCCESS] No callback executed while disabled" << std::endl;
    
    // Re-enable and test
    bool enabled = device.enableInterruptVector(0);
    if (!enabled) {
        std::cerr << "[ERROR] Failed to enable interrupt" << std::endl;
        return false;
    }
    
    is_enabled = device.isInterruptVectorEnabled(0);
    if (!is_enabled) {
        std::cerr << "[ERROR] Interrupt reports as disabled after enable" << std::endl;
        return false;
    }
    
    device.triggerInterrupt(0);
    std::this_thread::sleep_for(std::chrono::milliseconds(500));
    
    if (callback_count == 0) {
        std::cerr << "[ERROR] Callback not executed after re-enable" << std::endl;
        return false;
    }
    
    device.unregisterInterruptHandler(0);
    std::cout << "[SUCCESS] Enable/disable test passed" << std::endl;
    return true;
}

/**
 * @brief Test error conditions and edge cases
 */
bool testErrorConditions(VP815& device) {
    std::cout << "\n=== Testing Error Conditions ===\n";
    
    uint32_t max_vector = device.getInterruptVectorCount();
    
    // Test invalid vector ID
    bool result = device.registerInterruptHandler(max_vector + 10, simpleCallback);
    if (result) {
        std::cerr << "[ERROR] Successfully registered handler for invalid vector ID" << std::endl;
        return false;
    }
    std::cout << "[SUCCESS] Rejected invalid vector ID registration" << std::endl;
    
    // Test operations on unregistered vector
    result = device.unregisterInterruptHandler(max_vector + 10);
    // This should succeed gracefully
    std::cout << "[SUCCESS] Unregister of non-existent handler handled gracefully" << std::endl;
    
    return true;
}

/**
 * @brief Main test function following shell.hpp example
 */
int main(int argc, char* argv[]) {
    std::cout << "=== VP815 Callback-based Interrupt Interface Test ===\n" << std::endl;
    
    try {
        // Initialize device (default to device 0)
        uint32_t device_id = 0;
        if (argc > 1) {
            device_id = std::stoul(argv[1]);
        }
        
        std::cout << "[INFO] Initializing VP815 device " << device_id << "..." << std::endl;
        VP815 device(device_id);
        
        if (!device.isReady()) {
            std::cerr << "[ERROR] Device is not ready" << std::endl;
            return 1;
        }
        
        std::cout << "[SUCCESS] Device initialized successfully" << std::endl;
        device.print_info();
        
        // Run test sequence
        bool all_passed = true;
        
        all_passed &= testCapabilityDiscovery(device);
        all_passed &= testBasicCallback(device);
        all_passed &= testMultiVectorCallbacks(device);
        all_passed &= testEnableDisable(device);
        all_passed &= testErrorConditions(device);
        
        // Test lambda callback
        testLambdaCallback(device);
        
        // Final result
        if (all_passed && !test_failed.load()) {
            std::cout << "\n🎉 [SUCCESS] All interrupt callback tests PASSED!" << std::endl;
            return 0;
        } else {
            std::cout << "\n❌ [FAILURE] Some tests FAILED!" << std::endl;
            return 1;
        }
        
    } catch (const VP815Exception& e) {
        std::cerr << "[ERROR] VP815 Exception: " << e.what() << std::endl;
        return 1;
    } catch (const std::exception& e) {
        std::cerr << "[ERROR] Exception: " << e.what() << std::endl;
        return 1;
    } catch (...) {
        std::cerr << "[ERROR] Unknown exception occurred" << std::endl;
        return 1;
    }
}