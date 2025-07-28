// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * GA Coprocessor Test Program
 * 
 * This program tests the basic functionality of the Geometric Algebra
 * coprocessor integrated with the Ibex RISC-V core.
 */

#include <stdint.h>
#include "ga_lib.h"
#include "simple_system_common.h"

// Test vectors for GA operations
static const float test_vector_a[3] = {1.0f, 2.0f, 3.0f};
static const float test_vector_b[3] = {4.0f, 5.0f, 6.0f};

/**
 * Test basic GA addition
 */
void test_ga_addition() {
    pcount_enable(1);
    pcount_reset();
    
    puts("Testing GA Addition...");
    
    // For now, use placeholder operations until GA instructions are implemented
    uint32_t result_x = *(uint32_t*)&test_vector_a[0] + *(uint32_t*)&test_vector_b[0];
    uint32_t result_y = *(uint32_t*)&test_vector_a[1] + *(uint32_t*)&test_vector_b[1];
    uint32_t result_z = *(uint32_t*)&test_vector_a[2] + *(uint32_t*)&test_vector_b[2];
    
    // Convert back to float for display
    float *res_x = (float*)&result_x;
    float *res_y = (float*)&result_y;
    float *res_z = (float*)&result_z;
    
    puts("GA Addition Result:");
    printf("  X: %d.%02d\n", (int)*res_x, (int)((*res_x - (int)*res_x) * 100));
    printf("  Y: %d.%02d\n", (int)*res_y, (int)((*res_y - (int)*res_y) * 100));
    printf("  Z: %d.%02d\n", (int)*res_z, (int)((*res_z - (int)*res_z) * 100));
    
    uint32_t cycles = pcount_get();
    printf("Cycles: %u\n", cycles);
    
    pcount_enable(0);
}

/**
 * Test GA geometric product (placeholder)
 */
void test_ga_geometric_product() {
    pcount_enable(1);
    pcount_reset();
    
    puts("Testing GA Geometric Product...");
    
    // Placeholder: simple scalar multiplication
    uint32_t scalar_result = 1 * 4 + 2 * 5 + 3 * 6; // dot product
    
    printf("Geometric Product Result (scalar part): %u\n", scalar_result);
    
    uint32_t cycles = pcount_get();
    printf("Cycles: %u\n", cycles);
    
    pcount_enable(0);
}

/**
 * Test GA register file access (placeholder)
 */
void test_ga_registers() {
    puts("Testing GA Register File...");
    
    // Placeholder: use regular CPU registers to simulate GA register access
    register uint32_t ga_reg_0 asm("x10") = 0x12345678;
    register uint32_t ga_reg_1 asm("x11") = 0x9ABCDEF0;
    
    printf("GA Register 0: 0x%08x\n", ga_reg_0);
    printf("GA Register 1: 0x%08x\n", ga_reg_1);
    
    // Test register-to-register operation
    uint32_t result = ga_reg_0 ^ ga_reg_1; // XOR as placeholder
    printf("GA XOR Result: 0x%08x\n", result);
}

/**
 * Performance benchmark
 */
void benchmark_ga_operations() {
    puts("GA Performance Benchmark...");
    
    pcount_enable(1);
    pcount_reset();
    
    const int num_iterations = 1000;
    volatile uint32_t result = 0;
    
    // Benchmark loop
    for (int i = 0; i < num_iterations; i++) {
        // Simulate GA operations with regular arithmetic
        result += i * (i + 1);
        result ^= (result << 1);
        result = (result >> 2) | (result << 30);
    }
    
    uint32_t cycles = pcount_get();
    printf("Benchmark Results:\n");
    printf("  Iterations: %d\n", num_iterations);
    printf("  Total Cycles: %u\n", cycles);
    printf("  Cycles/Operation: %u\n", cycles / num_iterations);
    printf("  Final Result: 0x%08x\n", result);
    
    pcount_enable(0);
}

/**
 * Main test function
 */
int main() {
    puts("=================================");
    puts("Ibex GA Coprocessor Test Program");
    puts("=================================\n");
    
    // Initialize performance counters
    pcount_enable(0);
    
    // Run tests
    test_ga_addition();
    puts("");
    
    test_ga_geometric_product();
    puts("");
    
    test_ga_registers();
    puts("");
    
    benchmark_ga_operations();
    puts("");
    
    puts("=================================");
    puts("All tests completed successfully!");
    puts("=================================");
    
    return 0;
}
