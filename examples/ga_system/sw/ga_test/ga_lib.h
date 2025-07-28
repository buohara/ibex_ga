// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef GA_LIB_H_
#define GA_LIB_H_

#include <stdint.h>

/**
 * GA Library - Software interface for Geometric Algebra Coprocessor
 * 
 * This library provides C functions and macros for interfacing with
 * the GA coprocessor from RISC-V software.
 */

#ifdef __cplusplus
extern "C" {
#endif

//////////////////////////
// GA Data Structures   //
//////////////////////////

/**
 * GA Multivector structure (3D Euclidean)
 * Represents a complete multivector with all grades
 */
typedef struct {
    float scalar;      // Grade 0: scalar part
    float e1, e2, e3;  // Grade 1: vector part (e1, e2, e3)
    float e12, e13, e23; // Grade 2: bivector part (e1^e2, e1^e3, e2^e3)
    float e123;        // Grade 3: trivector part (e1^e2^e3)
} ga_multivector_t;

/**
 * GA Vector structure (simplified)
 */
typedef struct {
    float x, y, z;
} ga_vector_t;

/**
 * GA Rotor structure (for rotations)
 */
typedef struct {
    float scalar;      // Scalar part
    float e12, e13, e23; // Bivector part
} ga_rotor_t;

//////////////////////////
// GA Coprocessor Macros //
//////////////////////////

// Custom instruction encodings (CUSTOM-0 opcode: 7'h0B)
// These will be replaced with actual custom instructions when implemented

/**
 * GA Addition: rd = rs1 + rs2 (componentwise)
 */
#define GA_ADD(rd, rs1, rs2) \
    asm volatile ("add %0, %1, %2" : "=r"(rd) : "r"(rs1), "r"(rs2))

/**
 * GA Subtraction: rd = rs1 - rs2 (componentwise)  
 */
#define GA_SUB(rd, rs1, rs2) \
    asm volatile ("sub %0, %1, %2" : "=r"(rd) : "r"(rs1), "r"(rs2))

/**
 * GA Geometric Product: rd = rs1 * rs2
 */
#define GA_MUL(rd, rs1, rs2) \
    asm volatile ("mul %0, %1, %2" : "=r"(rd) : "r"(rs1), "r"(rs2))

/**
 * GA Outer (Wedge) Product: rd = rs1 ^ rs2
 */
#define GA_WEDGE(rd, rs1, rs2) \
    asm volatile ("xor %0, %1, %2" : "=r"(rd) : "r"(rs1), "r"(rs2))

/**
 * GA Inner (Dot) Product: rd = rs1 · rs2
 */
#define GA_DOT(rd, rs1, rs2) \
    asm volatile ("and %0, %1, %2" : "=r"(rd) : "r"(rs1), "r"(rs2))

/**
 * GA Dual operation
 */
#define GA_DUAL(rd, rs1) \
    asm volatile ("not %0, %1" : "=r"(rd) : "r"(rs1))

/**
 * GA Reverse operation
 */
#define GA_REVERSE(rd, rs1) \
    asm volatile ("neg %0, %1" : "=r"(rd) : "r"(rs1))

/**
 * Load from GA register file
 */
#define GA_LOAD_REG(rd, ga_reg) \
    asm volatile ("mv %0, %1" : "=r"(rd) : "r"(ga_reg))

/**
 * Store to GA register file
 */
#define GA_STORE_REG(ga_reg, rs1) \
    asm volatile ("mv %0, %1" : "=r"(ga_reg) : "r"(rs1))

//////////////////////////
// GA Library Functions //
//////////////////////////

/**
 * Initialize GA library
 */
void ga_init(void);

/**
 * Create a multivector from components
 */
ga_multivector_t ga_create_mv(float scalar, float e1, float e2, float e3,
                              float e12, float e13, float e23, float e123);

/**
 * Create a vector (grade 1 multivector)
 */
ga_multivector_t ga_create_vector(float x, float y, float z);

/**
 * Create a scalar (grade 0 multivector)
 */
ga_multivector_t ga_create_scalar(float value);

/**
 * Add two multivectors
 */
ga_multivector_t ga_add(ga_multivector_t a, ga_multivector_t b);

/**
 * Subtract two multivectors
 */
ga_multivector_t ga_sub(ga_multivector_t a, ga_multivector_t b);

/**
 * Geometric product of two multivectors
 */
ga_multivector_t ga_geometric_product(ga_multivector_t a, ga_multivector_t b);

/**
 * Outer (wedge) product of two multivectors
 */
ga_multivector_t ga_wedge_product(ga_multivector_t a, ga_multivector_t b);

/**
 * Inner (dot) product of two multivectors
 */
ga_multivector_t ga_inner_product(ga_multivector_t a, ga_multivector_t b);

/**
 * Dual of a multivector
 */
ga_multivector_t ga_dual(ga_multivector_t a);

/**
 * Reverse of a multivector
 */
ga_multivector_t ga_reverse(ga_multivector_t a);

/**
 * Magnitude (norm) of a multivector
 */
float ga_magnitude(ga_multivector_t a);

/**
 * Normalize a multivector
 */
ga_multivector_t ga_normalize(ga_multivector_t a);

/**
 * Create a rotor from angle and bivector axis
 */
ga_rotor_t ga_create_rotor(float angle, ga_multivector_t bivector_axis);

/**
 * Apply rotor to vector (rotation)
 */
ga_multivector_t ga_rotate_vector(ga_multivector_t vector, ga_rotor_t rotor);

/**
 * Reflect vector across plane defined by normal
 */
ga_multivector_t ga_reflect_vector(ga_multivector_t vector, ga_multivector_t normal);

/**
 * Print multivector for debugging
 */
void ga_print_mv(const char* name, ga_multivector_t mv);

/**
 * Convert float to uint32_t for GA operations
 */
static inline uint32_t ga_float_to_uint32(float f) {
    return *(uint32_t*)&f;
}

/**
 * Convert uint32_t to float from GA operations
 */
static inline float ga_uint32_to_float(uint32_t u) {
    return *(float*)&u;
}

//////////////////////////
// GA Constants         //
//////////////////////////

// Unit vectors
extern const ga_multivector_t GA_E1;  // e1 basis vector
extern const ga_multivector_t GA_E2;  // e2 basis vector  
extern const ga_multivector_t GA_E3;  // e3 basis vector

// Unit bivectors
extern const ga_multivector_t GA_E12; // e1^e2 basis bivector
extern const ga_multivector_t GA_E13; // e1^e3 basis bivector
extern const ga_multivector_t GA_E23; // e2^e3 basis bivector

// Pseudoscalar
extern const ga_multivector_t GA_I;   // e1^e2^e3 pseudoscalar

// Identity elements
extern const ga_multivector_t GA_ZERO;   // Zero multivector
extern const ga_multivector_t GA_ONE;    // Unit scalar

#ifdef __cplusplus
}
#endif

#endif  // GA_LIB_H_
