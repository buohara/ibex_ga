// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "ga_lib.h"
#include <math.h>
#include <stdio.h>

//////////////////////////
// GA Constants         //
//////////////////////////

const ga_multivector_t GA_E1 = {0.0f, 1.0f, 0.0f, 0.0f, 0.0f, 0.0f, 0.0f, 0.0f};
const ga_multivector_t GA_E2 = {0.0f, 0.0f, 1.0f, 0.0f, 0.0f, 0.0f, 0.0f, 0.0f};
const ga_multivector_t GA_E3 = {0.0f, 0.0f, 0.0f, 1.0f, 0.0f, 0.0f, 0.0f, 0.0f};

const ga_multivector_t GA_E12 = {0.0f, 0.0f, 0.0f, 0.0f, 1.0f, 0.0f, 0.0f, 0.0f};
const ga_multivector_t GA_E13 = {0.0f, 0.0f, 0.0f, 0.0f, 0.0f, 1.0f, 0.0f, 0.0f};
const ga_multivector_t GA_E23 = {0.0f, 0.0f, 0.0f, 0.0f, 0.0f, 0.0f, 1.0f, 0.0f};

const ga_multivector_t GA_I = {0.0f, 0.0f, 0.0f, 0.0f, 0.0f, 0.0f, 0.0f, 1.0f};

const ga_multivector_t GA_ZERO = {0.0f, 0.0f, 0.0f, 0.0f, 0.0f, 0.0f, 0.0f, 0.0f};
const ga_multivector_t GA_ONE = {1.0f, 0.0f, 0.0f, 0.0f, 0.0f, 0.0f, 0.0f, 0.0f};

//////////////////////////
// GA Library Functions //
//////////////////////////

void ga_init(void) {
    // Initialize GA coprocessor if needed
    // For now, this is a placeholder
    printf("GA Library initialized\n");
}

ga_multivector_t ga_create_mv(float scalar, float e1, float e2, float e3,
                              float e12, float e13, float e23, float e123) {
    ga_multivector_t result = {scalar, e1, e2, e3, e12, e13, e23, e123};
    return result;
}

ga_multivector_t ga_create_vector(float x, float y, float z) {
    return ga_create_mv(0.0f, x, y, z, 0.0f, 0.0f, 0.0f, 0.0f);
}

ga_multivector_t ga_create_scalar(float value) {
    return ga_create_mv(value, 0.0f, 0.0f, 0.0f, 0.0f, 0.0f, 0.0f, 0.0f);
}

ga_multivector_t ga_add(ga_multivector_t a, ga_multivector_t b) {
    // TODO: Use GA coprocessor when available
    ga_multivector_t result;
    result.scalar = a.scalar + b.scalar;
    result.e1 = a.e1 + b.e1;
    result.e2 = a.e2 + b.e2;
    result.e3 = a.e3 + b.e3;
    result.e12 = a.e12 + b.e12;
    result.e13 = a.e13 + b.e13;
    result.e23 = a.e23 + b.e23;
    result.e123 = a.e123 + b.e123;
    return result;
}

ga_multivector_t ga_sub(ga_multivector_t a, ga_multivector_t b) {
    // TODO: Use GA coprocessor when available
    ga_multivector_t result;
    result.scalar = a.scalar - b.scalar;
    result.e1 = a.e1 - b.e1;
    result.e2 = a.e2 - b.e2;
    result.e3 = a.e3 - b.e3;
    result.e12 = a.e12 - b.e12;
    result.e13 = a.e13 - b.e13;
    result.e23 = a.e23 - b.e23;
    result.e123 = a.e123 - b.e123;
    return result;
}

ga_multivector_t ga_geometric_product(ga_multivector_t a, ga_multivector_t b) {
    // TODO: Use GA coprocessor when available
    // For now, implement geometric product in software
    ga_multivector_t result;
    
    // Scalar part
    result.scalar = a.scalar * b.scalar + a.e1 * b.e1 + a.e2 * b.e2 + a.e3 * b.e3
                   - a.e12 * b.e12 - a.e13 * b.e13 - a.e23 * b.e23 - a.e123 * b.e123;
    
    // Vector parts (grade 1)
    result.e1 = a.scalar * b.e1 + a.e1 * b.scalar - a.e2 * b.e12 - a.e3 * b.e13
               + a.e12 * b.e2 + a.e13 * b.e3 - a.e23 * b.e123 - a.e123 * b.e23;
               
    result.e2 = a.scalar * b.e2 + a.e1 * b.e12 + a.e2 * b.scalar - a.e3 * b.e23
               - a.e12 * b.e1 + a.e13 * b.e123 + a.e23 * b.e3 - a.e123 * b.e13;
               
    result.e3 = a.scalar * b.e3 + a.e1 * b.e13 + a.e2 * b.e23 + a.e3 * b.scalar
               - a.e12 * b.e123 - a.e13 * b.e1 - a.e23 * b.e2 - a.e123 * b.e12;
    
    // Bivector parts (grade 2)
    result.e12 = a.scalar * b.e12 + a.e1 * b.e2 - a.e2 * b.e1 + a.e3 * b.e123
                + a.e12 * b.scalar - a.e13 * b.e23 + a.e23 * b.e13 + a.e123 * b.e3;
                
    result.e13 = a.scalar * b.e13 + a.e1 * b.e3 - a.e2 * b.e123 - a.e3 * b.e1
                + a.e12 * b.e23 + a.e13 * b.scalar - a.e23 * b.e12 + a.e123 * b.e2;
                
    result.e23 = a.scalar * b.e23 + a.e1 * b.e123 + a.e2 * b.e3 - a.e3 * b.e2
                - a.e12 * b.e13 + a.e13 * b.e12 + a.e23 * b.scalar + a.e123 * b.e1;
    
    // Trivector part (grade 3)
    result.e123 = a.scalar * b.e123 + a.e1 * b.e23 - a.e2 * b.e13 + a.e3 * b.e12
                 + a.e12 * b.e3 - a.e13 * b.e2 + a.e23 * b.e1 + a.e123 * b.scalar;
    
    return result;
}

ga_multivector_t ga_wedge_product(ga_multivector_t a, ga_multivector_t b) {
    // TODO: Use GA coprocessor when available
    // Outer product only keeps terms that increase grade
    ga_multivector_t result = GA_ZERO;
    
    // Grade 0 ^ Grade 1 = Grade 1
    result.e1 = a.scalar * b.e1;
    result.e2 = a.scalar * b.e2;
    result.e3 = a.scalar * b.e3;
    
    // Grade 1 ^ Grade 0 = Grade 1
    result.e1 += a.e1 * b.scalar;
    result.e2 += a.e2 * b.scalar;
    result.e3 += a.e3 * b.scalar;
    
    // Grade 1 ^ Grade 1 = Grade 2
    result.e12 = a.e1 * b.e2 - a.e2 * b.e1;
    result.e13 = a.e1 * b.e3 - a.e3 * b.e1;
    result.e23 = a.e2 * b.e3 - a.e3 * b.e2;
    
    // Grade 0 ^ Grade 2 = Grade 2
    result.e12 += a.scalar * b.e12;
    result.e13 += a.scalar * b.e13;
    result.e23 += a.scalar * b.e23;
    
    // Grade 2 ^ Grade 0 = Grade 2
    result.e12 += a.e12 * b.scalar;
    result.e13 += a.e13 * b.scalar;
    result.e23 += a.e23 * b.scalar;
    
    // Grade 1 ^ Grade 2 = Grade 3
    result.e123 = a.e1 * b.e23 - a.e2 * b.e13 + a.e3 * b.e12;
    
    // Grade 2 ^ Grade 1 = Grade 3
    result.e123 += a.e12 * b.e3 - a.e13 * b.e2 + a.e23 * b.e1;
    
    // Grade 0 ^ Grade 3 = Grade 3
    result.e123 += a.scalar * b.e123;
    
    // Grade 3 ^ Grade 0 = Grade 3
    result.e123 += a.e123 * b.scalar;
    
    return result;
}

ga_multivector_t ga_inner_product(ga_multivector_t a, ga_multivector_t b) {
    // TODO: Use GA coprocessor when available
    // Inner product only keeps terms that decrease or maintain grade
    ga_multivector_t result = GA_ZERO;
    
    // Grade 1 · Grade 1 = Grade 0
    result.scalar = a.e1 * b.e1 + a.e2 * b.e2 + a.e3 * b.e3;
    
    // Grade 2 · Grade 2 = Grade 0
    result.scalar += -(a.e12 * b.e12 + a.e13 * b.e13 + a.e23 * b.e23);
    
    // Grade 3 · Grade 3 = Grade 0
    result.scalar += -a.e123 * b.e123;
    
    // Additional inner product terms would go here
    // This is a simplified implementation
    
    return result;
}

ga_multivector_t ga_dual(ga_multivector_t a) {
    // TODO: Use GA coprocessor when available
    // Dual is multiplication by pseudoscalar I = e123
    ga_multivector_t result;
    
    result.scalar = a.e123;     // scalar * I = e123
    result.e1 = a.e23;          // e1 * I = e23
    result.e2 = -a.e13;         // e2 * I = -e13  
    result.e3 = a.e12;          // e3 * I = e12
    result.e12 = -a.e3;         // e12 * I = -e3
    result.e13 = a.e2;          // e13 * I = e2
    result.e23 = -a.e1;         // e23 * I = -e1
    result.e123 = -a.scalar;    // e123 * I = -1
    
    return result;
}

ga_multivector_t ga_reverse(ga_multivector_t a) {
    // TODO: Use GA coprocessor when available
    // Reverse changes sign of grade 2 and 3 terms
    ga_multivector_t result;
    
    result.scalar = a.scalar;   // Grade 0: no change
    result.e1 = a.e1;           // Grade 1: no change
    result.e2 = a.e2;
    result.e3 = a.e3;
    result.e12 = -a.e12;        // Grade 2: sign change
    result.e13 = -a.e13;
    result.e23 = -a.e23;
    result.e123 = -a.e123;      // Grade 3: sign change
    
    return result;
}

float ga_magnitude(ga_multivector_t a) {
    // |a| = sqrt(a * reverse(a))
    ga_multivector_t rev = ga_reverse(a);
    ga_multivector_t product = ga_geometric_product(a, rev);
    return sqrtf(product.scalar);
}

ga_multivector_t ga_normalize(ga_multivector_t a) {
    float mag = ga_magnitude(a);
    if (mag > 1e-6f) {  // Avoid division by zero
        ga_multivector_t result;
        result.scalar = a.scalar / mag;
        result.e1 = a.e1 / mag;
        result.e2 = a.e2 / mag;
        result.e3 = a.e3 / mag;
        result.e12 = a.e12 / mag;
        result.e13 = a.e13 / mag;
        result.e23 = a.e23 / mag;
        result.e123 = a.e123 / mag;
        return result;
    }
    return GA_ZERO;
}

ga_rotor_t ga_create_rotor(float angle, ga_multivector_t bivector_axis) {
    // R = cos(θ/2) - sin(θ/2) * B_normalized
    float half_angle = angle / 2.0f;
    float cos_half = cosf(half_angle);
    float sin_half = sinf(half_angle);
    
    // Normalize the bivector axis
    float b_mag = sqrtf(bivector_axis.e12 * bivector_axis.e12 + 
                       bivector_axis.e13 * bivector_axis.e13 + 
                       bivector_axis.e23 * bivector_axis.e23);
    
    ga_rotor_t rotor;
    rotor.scalar = cos_half;
    if (b_mag > 1e-6f) {
        rotor.e12 = -sin_half * bivector_axis.e12 / b_mag;
        rotor.e13 = -sin_half * bivector_axis.e13 / b_mag;
        rotor.e23 = -sin_half * bivector_axis.e23 / b_mag;
    } else {
        rotor.e12 = rotor.e13 = rotor.e23 = 0.0f;
    }
    
    return rotor;
}

ga_multivector_t ga_rotate_vector(ga_multivector_t vector, ga_rotor_t rotor) {
    // Convert rotor to multivector
    ga_multivector_t R = ga_create_mv(rotor.scalar, 0.0f, 0.0f, 0.0f,
                                     rotor.e12, rotor.e13, rotor.e23, 0.0f);
    ga_multivector_t R_rev = ga_reverse(R);
    
    // Rotated vector = R * vector * R_reverse
    ga_multivector_t temp = ga_geometric_product(R, vector);
    return ga_geometric_product(temp, R_rev);
}

ga_multivector_t ga_reflect_vector(ga_multivector_t vector, ga_multivector_t normal) {
    // Reflected vector = -n * vector * n (where n is unit normal)
    ga_multivector_t unit_normal = ga_normalize(normal);
    ga_multivector_t temp = ga_geometric_product(unit_normal, vector);
    ga_multivector_t result = ga_geometric_product(temp, unit_normal);
    
    // Negate the result
    result.scalar = -result.scalar;
    result.e1 = -result.e1;
    result.e2 = -result.e2;
    result.e3 = -result.e3;
    result.e12 = -result.e12;
    result.e13 = -result.e13;
    result.e23 = -result.e23;
    result.e123 = -result.e123;
    
    return result;
}

void ga_print_mv(const char* name, ga_multivector_t mv) {
    printf("%s = %.3f", name, mv.scalar);
    if (mv.e1 != 0.0f) printf(" + %.3fe1", mv.e1);
    if (mv.e2 != 0.0f) printf(" + %.3fe2", mv.e2);
    if (mv.e3 != 0.0f) printf(" + %.3fe3", mv.e3);
    if (mv.e12 != 0.0f) printf(" + %.3fe12", mv.e12);
    if (mv.e13 != 0.0f) printf(" + %.3fe13", mv.e13);
    if (mv.e23 != 0.0f) printf(" + %.3fe23", mv.e23);
    if (mv.e123 != 0.0f) printf(" + %.3fe123", mv.e123);
    printf("\n");
}
