// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Test vector generator for GA coprocessor using Versor as golden reference
 * Generates randomized test cases and corner cases for all GA operations
 */

#include <iostream>
#include <fstream>
#include <random>
#include <vector>
#include <string>
#include <iomanip>
#include <cmath>

#ifndef USE_SIMPLIFIED_GA
// Versor CGA headers - assuming build system sets correct include paths
#include "versor/include/vsr/vsr.h"
using namespace vsr;
using namespace vsr::cga;
#endif

#ifdef USE_SIMPLIFIED_GA
    // Fallback implementation without Versor
    #include <limits>
    
    struct Multivector {
        float scalar = 0.0f;
        float e1 = 0.0f, e2 = 0.0f, e3 = 0.0f;
        float e12 = 0.0f, e13 = 0.0f, e23 = 0.0f;
        float e123 = 0.0f;
        
        uint32_t to_uint32() const {
            union { float f; uint32_t u; } converter;
            converter.f = scalar;
            return converter.u;
        }
    };
    
    #define VERSOR_AVAILABLE false
    
#else
    // Include Versor library for golden reference - using Conformal GA
    #include <vsr/vsr.h>
    #include <vsr/space/vsr_cga3D_types.h>
    #include <vsr/space/vsr_cga3D_op.h>
    
    // Use Versor's 3D Conformal GA types
    using namespace vsr;
    using namespace vsr::cga;
    
    // Extended multivector for Conformal GA operations
    // We'll extract key components from Versor's CGA multivector
    struct Multivector {
        // Grade 0 (scalar)
        float scalar = 0.0f;
        
        // Grade 1 (vectors) - euclidean part + infinity + origin  
        float e1 = 0.0f, e2 = 0.0f, e3 = 0.0f;
        float ni = 0.0f;  // null infinity
        float no = 0.0f;  // null origin
        
        // Grade 2 (bivectors) - key ones for rotations and translations
        float e12 = 0.0f, e13 = 0.0f, e23 = 0.0f;  // Euclidean bivectors
        float e1n = 0.0f, e2n = 0.0f, e3n = 0.0f;  // Translation generators
        
        // Grade 3 (trivectors) - pseudoscalar and others
        float e123 = 0.0f;
        float e12n = 0.0f, e13n = 0.0f, e23n = 0.0f;
        
        // Additional CGA components (simplified representation)
        float e1no = 0.0f, e2no = 0.0f, e3no = 0.0f;
        float e123n = 0.0f, e123o = 0.0f;
        float e123no = 0.0f;  // Full 5D pseudoscalar
        
        // Constructor from Versor CGA multivector
        Multivector() = default;
        
        // Extract components from Versor's general multivector
        template<class T>
        Multivector(const T& mv) {
            // Extract available components (Versor uses [] operator to access components)
            if (mv.size() > 0) scalar = mv[0];     // scalar
            if (mv.size() > 1) e1 = mv[1];         // e1
            if (mv.size() > 2) e2 = mv[2];         // e2  
            if (mv.size() > 3) e3 = mv[3];         // e3
            if (mv.size() > 4) no = mv[4];         // no (origin)
            if (mv.size() > 5) ni = mv[5];         // ni (infinity)
            if (mv.size() > 6) e12 = mv[6];        // e12
            if (mv.size() > 7) e13 = mv[7];        // e13
            if (mv.size() > 8) e23 = mv[8];        // e23
            // Continue for more components as needed...
        }
        
        uint32_t to_uint32() const {
            union { float f; uint32_t u; } converter;
            converter.f = scalar;  // For now, just return scalar part
            return converter.u;
        }
    };
    
    #define VERSOR_AVAILABLE true
    
#endif

// GA operation types matching hardware
enum GAFunction {
    GA_FUNCT_ADD       = 0,   // Geometric addition
    GA_FUNCT_SUB       = 1,   // Geometric subtraction  
    GA_FUNCT_MUL       = 2,   // Geometric product
    GA_FUNCT_WEDGE     = 3,   // Outer (wedge) product
    GA_FUNCT_DOT       = 4,   // Inner (dot) product
    GA_FUNCT_DUAL      = 5,   // Dual operation
    GA_FUNCT_REV       = 6,   // Reverse operation
    GA_FUNCT_NORM      = 7,   // Norm calculation
    GA_FUNCT_LOAD      = 8,   // Load from GA register
    GA_FUNCT_STORE     = 9,   // Store to GA register
    GA_FUNCT_ROTATE    = 10,  // Rotor application
    GA_FUNCT_REFLECT   = 11   // Reflection operation
};
class GATestVectorGenerator {
private:
    std::mt19937 rng;
    std::uniform_real_distribution<float> uniform_dist;
    std::normal_distribution<float> normal_dist;
    
public:
    GATestVectorGenerator() : 
        rng(std::random_device{}()),
        uniform_dist(-100.0f, 100.0f),
        normal_dist(0.0f, 10.0f) {}
    
    // Generate random multivector using Versor CGA or fallback
    Multivector random_multivector() {
#ifdef USE_SIMPLIFIED_GA
        Multivector mv;
        mv.scalar = uniform_dist(rng);
        mv.e1 = uniform_dist(rng);
        mv.e2 = uniform_dist(rng);
        mv.e3 = uniform_dist(rng);
        mv.e12 = uniform_dist(rng);
        mv.e13 = uniform_dist(rng);
        mv.e23 = uniform_dist(rng);
        mv.e123 = uniform_dist(rng);
        return mv;
#else
        // Create random 3D CGA multivector using Versor
        // Generate a general multivector with random coefficients
        auto scalar_part = Scalar(uniform_dist(rng));
        auto vector_part = Vec(uniform_dist(rng), uniform_dist(rng), uniform_dist(rng));
        auto bivector_part = Biv(uniform_dist(rng), uniform_dist(rng), uniform_dist(rng));
        auto trivector_part = Tri(uniform_dist(rng));
        
        // Create points for CGA-specific elements
        auto random_point = Round::null(uniform_dist(rng), uniform_dist(rng), uniform_dist(rng));
        
        // Combine into a general multivector (this creates a mixed-grade element)
        auto cga_mv = scalar_part + vector_part + bivector_part + trivector_part + random_point * 0.1f;
        
        return Multivector(cga_mv);
#endif
    }
    
    // Generate corner case multivectors
    std::vector<Multivector> corner_cases() {
        std::vector<Multivector> cases;
        
#ifdef USE_SIMPLIFIED_GA
        // Simplified corner cases
        cases.push_back(Multivector{});  // Zero
        cases.push_back(Multivector{1.0f, 0, 0, 0, 0, 0, 0, 0});  // Unit scalar
        cases.push_back(Multivector{0, 1.0f, 0, 0, 0, 0, 0, 0});  // e1
        cases.push_back(Multivector{0, 0, 1.0f, 0, 0, 0, 0, 0});  // e2
        cases.push_back(Multivector{0, 0, 0, 1.0f, 0, 0, 0, 0});  // e3
        cases.push_back(Multivector{std::numeric_limits<float>::infinity(), 0, 0, 0, 0, 0, 0, 0});
        cases.push_back(Multivector{std::numeric_limits<float>::quiet_NaN(), 0, 0, 0, 0, 0, 0, 0});
        return cases;
#else
        // CGA corner cases using Versor - important geometric elements
        
        // Zero multivector
        cases.push_back(Multivector(Scalar(0.0f)));
        
        // Pure scalar
        cases.push_back(Multivector(Scalar(1.0f)));
        cases.push_back(Multivector(Scalar(-1.0f)));
        
        // Unit euclidean vectors  
        cases.push_back(Multivector(Vec::x));
        cases.push_back(Multivector(Vec::y));
        cases.push_back(Multivector(Vec::z));
        cases.push_back(Multivector(-Vec::x));
        cases.push_back(Multivector(-Vec::y));
        cases.push_back(Multivector(-Vec::z));
        
        // CGA null vectors (infinity and origin)
        cases.push_back(Multivector(Inf(1.0f)));    // Infinity
        cases.push_back(Multivector(Ori(1.0f)));    // Origin
        
        // Unit bivectors (rotation generators)
        cases.push_back(Multivector(Biv::xy));
        cases.push_back(Multivector(Biv::xz));
        cases.push_back(Multivector(Biv::yz));
        cases.push_back(Multivector(-Biv::xy));
        cases.push_back(Multivector(-Biv::xz));
        cases.push_back(Multivector(-Biv::yz));
        
        // Points at specific locations (key CGA geometric elements)
        cases.push_back(Multivector(Round::null(0,0,0)));      // Point at origin
        cases.push_back(Multivector(Round::null(1,0,0)));      // Point at (1,0,0)
        cases.push_back(Multivector(Round::null(0,1,0)));      // Point at (0,1,0)
        cases.push_back(Multivector(Round::null(0,0,1)));      // Point at (0,0,1)
        cases.push_back(Multivector(Round::null(1,1,1)));      // Point at (1,1,1)
        
        // Simple circles and spheres
        auto pa = Round::null(1,0,0);
        auto pb = Round::null(-1,0,0);  
        auto pc = Round::null(0,1,0);
        auto pd = Round::null(0,-1,0);
        cases.push_back(Multivector(pa ^ pb ^ pc));            // Circle through 3 points
        cases.push_back(Multivector(pa ^ pb ^ pc ^ pd));       // Sphere through 4 points
        
        // Unit rotors (important for robotics)
        cases.push_back(Multivector(Gen::rot(Biv::xy * 0.0f)));     // Identity rotor
        cases.push_back(Multivector(Gen::rot(Biv::xy * 0.25f)));    // 45° rotation in xy
        cases.push_back(Multivector(Gen::rot(Biv::xz * 0.25f)));    // 45° rotation in xz
        
        // Unit translators (key for 6-DOF robotics)
        cases.push_back(Multivector(Gen::trs(1,0,0)));         // Translation in x
        cases.push_back(Multivector(Gen::trs(0,1,0)));         // Translation in y  
        cases.push_back(Multivector(Gen::trs(0,0,1)));         // Translation in z
        
        // Motors (combined rotation + translation - the essence of 6-DOF)
        auto dual_line_x = DualLine(0,0,0,1,0,0);  // Dual line along x-axis
        auto dual_line_y = DualLine(0,0,0,0,1,0);  // Dual line along y-axis
        cases.push_back(Multivector(Gen::mot(dual_line_x * 0.1f)));  // Small twist about x
        cases.push_back(Multivector(Gen::mot(dual_line_y * 0.1f)));  // Small twist about y
        
        // Pseudoscalar
        cases.push_back(Multivector(Pss(1.0f)));
        
        // Special floating point values
        cases.push_back(Multivector(Scalar(std::numeric_limits<float>::infinity())));
        cases.push_back(Multivector(Scalar(std::numeric_limits<float>::quiet_NaN())));
        cases.push_back(Multivector(Scalar(1e-38f)));   // Very small
        cases.push_back(Multivector(Scalar(1e38f)));    // Very large
        
#endif
        return cases;
    }
    
    // Convert CGA multivector to 32-bit float representation
    uint32_t multivector_to_uint32(const Multivector& mv) {
#ifdef USE_SIMPLIFIED_GA
        return mv.to_uint32();
#else
        // For CGA, we'll return the scalar part as the primary output
        // In a full implementation, we'd pack multiple components
        union { float f; uint32_t u; } converter;
        converter.f = mv.scalar;
        return converter.u;
#endif
    }
    
    // Create CGA multivector from 32-bit representation
    Multivector uint32_to_multivector(uint32_t val) {
        union { float f; uint32_t u; } converter;
        converter.u = val;
        Multivector mv;
        mv.scalar = converter.f;
        return mv;
    }
    
    // Compute golden reference using Versor CGA or simplified implementation
    Multivector compute_golden(GAFunction op, const Multivector& a, const Multivector& b) {
#ifdef USE_SIMPLIFIED_GA
        // Simplified implementation without Versor
        Multivector result;
        switch (op) {
            case GA_FUNCT_ADD:
                result.scalar = a.scalar + b.scalar;
                result.e1 = a.e1 + b.e1;
                result.e2 = a.e2 + b.e2;
                result.e3 = a.e3 + b.e3;
                break;
            case GA_FUNCT_SUB:
                result.scalar = a.scalar - b.scalar;
                result.e1 = a.e1 - b.e1;
                result.e2 = a.e2 - b.e2;
                result.e3 = a.e3 - b.e3;
                break;
            case GA_FUNCT_MUL:
                result.scalar = a.scalar * b.scalar;  // Simplified
                break;
            default:
                result = a;
                break;
        }
        return result;
#else
        // Full Versor CGA implementation
        // Convert our simplified multivectors back to Versor types for computation
        // This is a simplified approach - in practice we'd maintain Versor types throughout
        
        // Create Versor multivectors from our components
        auto va = Scalar(a.scalar) + Vec(a.e1, a.e2, a.e3) + Biv(a.e12, a.e13, a.e23);
        auto vb = Scalar(b.scalar) + Vec(b.e1, b.e2, b.e3) + Biv(b.e12, b.e13, b.e23);
        
        switch (op) {
            case GA_FUNCT_ADD:
                return Multivector(va + vb);       // Versor addition
                
            case GA_FUNCT_SUB:
                return Multivector(va - vb);       // Versor subtraction
                
            case GA_FUNCT_MUL:
                return Multivector(va * vb);       // Versor geometric product
                
            case GA_FUNCT_WEDGE:
                return Multivector(va ^ vb);       // Versor wedge product
                
            case GA_FUNCT_DOT:
                return Multivector(va <= vb);      // Versor inner product
                
            case GA_FUNCT_REV:
                return Multivector(~va);           // Versor reverse
                
            case GA_FUNCT_DUAL:
                return Multivector(va.dual());     // Versor dual
                
            case GA_FUNCT_NORM:
                return Multivector(Scalar(va.norm()));  // Versor norm
                
            case GA_FUNCT_ROTATE: {
                // Apply rotor (assuming 'b' is a rotor and 'a' is the element to rotate)
                auto rotor = Gen::rot(Biv(b.e12, b.e13, b.e23));
                return Multivector(va.sp(rotor));  // Sandwich product
            }
                
            case GA_FUNCT_REFLECT: {
                // Reflect in a plane/sphere (assuming 'b' defines the reflection element)
                return Multivector(va.re(vb));     // Reflection
            }
                
            default:
                return Multivector(va);            // Default case
        }
#endif
    }
    
    // Generate test vectors and write to files
    void generate_test_suite(int num_random_tests = 1000) {
        std::ofstream input_file("vectors/ga_test_inputs.mem");
        std::ofstream output_file("vectors/ga_test_outputs.mem");
        std::ofstream control_file("vectors/ga_test_control.mem");
        
        if (!input_file || !output_file || !control_file) {
            std::cerr << "Error: Could not create test vector files" << std::endl;
            return;
        }
        
        int test_count = 0;
        
        // Generate corner case tests
        auto corners = corner_cases();
        for (int op = GA_FUNCT_ADD; op <= GA_FUNCT_REFLECT; ++op) {
            for (size_t i = 0; i < corners.size(); ++i) {
                for (size_t j = 0; j < corners.size(); ++j) {
                    Multivector a = corners[i];
                    Multivector b = corners[j];
                    Multivector expected = compute_golden(static_cast<GAFunction>(op), a, b);
                    
                    // Write test vector using CGA conversion
                    input_file << std::hex << std::setfill('0') << std::setw(8) 
                              << multivector_to_uint32(a) << " " << multivector_to_uint32(b) << std::endl;
                    output_file << std::hex << std::setfill('0') << std::setw(8) 
                               << multivector_to_uint32(expected) << std::endl;
                    control_file << op << std::endl;
                    
                    test_count++;
                }
            }
        }
        
        // Generate random tests
        for (int i = 0; i < num_random_tests; ++i) {
            int op = rng() % 12;  // Random operation
            Multivector a = random_multivector();
            Multivector b = random_multivector();
            Multivector expected = compute_golden(static_cast<GAFunction>(op), a, b);
            
            input_file << std::hex << std::setfill('0') << std::setw(8) 
                      << multivector_to_uint32(a) << " " << multivector_to_uint32(b) << std::endl;
            output_file << std::hex << std::setfill('0') << std::setw(8) 
                       << multivector_to_uint32(expected) << std::endl;
            control_file << op << std::endl;
            
            test_count++;
        }
        
        std::cout << "Generated " << test_count << " test vectors" << std::endl;
        
        input_file.close();
        output_file.close();
        control_file.close();
    }
};

int main() {
    std::cout << "GA Coprocessor Test Vector Generator" << std::endl;
    std::cout << "====================================" << std::endl;
    
#if VERSOR_AVAILABLE
    std::cout << "Using Versor library for golden reference calculations" << std::endl;
#else
    std::cout << "Using simplified GA implementation (Versor not available)" << std::endl;
#endif
    
    GATestVectorGenerator generator;
    generator.generate_test_suite(1000);
    
    std::cout << "Test vector generation complete!" << std::endl;
    std::cout << "Files generated:" << std::endl;
    std::cout << "  - vectors/ga_test_inputs.mem" << std::endl;
    std::cout << "  - vectors/ga_test_outputs.mem" << std::endl;
    std::cout << "  - vectors/ga_test_control.mem" << std::endl;
    
    return 0;
}
