#include <iostream>
#include <random>
#include <vector>
#include <string>
#include <iomanip>
#include <cmath>
#include <cstdio>
#include <limits>
#include <algorithm>
#include <array>

using namespace std;

enum GAFunction 
{
    GA_FUNCT_ADD       = 0,
    GA_FUNCT_SUB       = 1,
    GA_FUNCT_MUL       = 2,
    GA_FUNCT_WEDGE     = 3,
    GA_FUNCT_DOT       = 4,
    GA_FUNCT_DUAL      = 5,
    GA_FUNCT_REV       = 6,
    GA_FUNCT_NORM      = 7
};

class FixedPointQ511 
{
public:

    static int16_t floatToQ511(float f) 
    {
        const float kMaxFloat = 15.9995f;
        const float kMinFloat = -16.0f;
        const int kFracBits = 11;
        
        f = max(kMinFloat, min(kMaxFloat, f));
        return static_cast<int16_t>(f * (1 << kFracBits));
    }
    
    static float q511ToFloat(int16_t q) 
    {
        const int kFracBits = 11;
        return static_cast<float>(q) / (1 << kFracBits);
    }
};

class CgaMultivector 
{
public:

    static const int kNumComponents = 32;
    array<float, kNumComponents> components_;
    
    CgaMultivector() 
    {
        reset();
    }
    
    void reset() 
    {
        fill(components_.begin(), components_.end(), 0.0f);
    }
    
    float& operator[](int index) 
    {
        return components_[index];
    }
    
    const float& operator[](int index) const 
    {
        return components_[index];
    }
    
    float& scalar() { return components_[0]; }
    float& e1() { return components_[1]; }
    float& e2() { return components_[2]; }
    float& e3() { return components_[3]; }
    float& eo() { return components_[4]; }
    float& ei() { return components_[5]; }
    float& e12() { return components_[6]; }
    float& e13() { return components_[7]; }
    float& e23() { return components_[8]; }
    float& e1o() { return components_[9]; }
    float& e2o() { return components_[10]; }
    float& e3o() { return components_[11]; }
    float& e1i() { return components_[12]; }
    float& e2i() { return components_[13]; }
    float& e3i() { return components_[14]; }
    float& eoi() { return components_[15]; }
    float& e123() { return components_[16]; }
    float& e12o() { return components_[17]; }
    float& e13o() { return components_[18]; }
    float& e23o() { return components_[19]; }
    float& e12i() { return components_[20]; }
    float& e13i() { return components_[21]; }
    float& e23i() { return components_[22]; }
    float& e1oi() { return components_[23]; }
    float& e2oi() { return components_[24]; }
    float& e3oi() { return components_[25]; }
    float& e123o() { return components_[26]; }
    float& e123i() { return components_[27]; }
    float& e12oi() { return components_[28]; }
    float& e13oi() { return components_[29]; }
    float& e23oi() { return components_[30]; }
    float& e123oi() { return components_[31]; }
    
    const float& scalar() const { return components_[0]; }
    const float& e1() const { return components_[1]; }
    const float& e2() const { return components_[2]; }
    const float& e3() const { return components_[3]; }
    const float& eo() const { return components_[4]; }
    const float& ei() const { return components_[5]; }
    
    CgaMultivector operator+(CgaMultivector& other)
    {
        CgaMultivector result;

        for (int i = 0; i < kNumComponents; ++i) 
        {
            result[i] = components_[i] + other[i];
        }

        return result;
    }
    
    CgaMultivector operator-(CgaMultivector& other)
    {
        CgaMultivector result;

        for (int i = 0; i < kNumComponents; ++i) 
        {
            result[i] = components_[i] - other[i];
        }

        return result;
    }
    
    CgaMultivector geometricProduct(CgaMultivector& b)
    {
        CgaMultivector result;
        CgaMultivector& a = *this;
        
        result.scalar() = a.scalar() * b.scalar() + 
                         a.e1() * b.e1() + a.e2() * b.e2() + a.e3() * b.e3() +
                         a.eo() * b.eo() - a.ei() * b.ei() -
                         a.e12() * b.e12() - a.e13() * b.e13() - a.e23() * b.e23() +
                         a.e1o() * b.e1o() + a.e2o() * b.e2o() + a.e3o() * b.e3o() -
                         a.e1i() * b.e1i() - a.e2i() * b.e2i() - a.e3i() * b.e3i() -
                         a.eoi() * b.eoi() - a.e123() * b.e123();
        
        result.e1() = a.scalar() * b.e1() + a.e1() * b.scalar() -
                     a.e2() * b.e12() + a.e3() * b.e13() +
                     a.e12() * b.e2() - a.e13() * b.e3();
        
        result.e2() = a.scalar() * b.e2() + a.e1() * b.e12() +
                     a.e2() * b.scalar() - a.e3() * b.e23() -
                     a.e12() * b.e1() + a.e23() * b.e3();
        
        result.e3() = a.scalar() * b.e3() - a.e1() * b.e13() +
                     a.e2() * b.e23() + a.e3() * b.scalar() +
                     a.e13() * b.e1() - a.e23() * b.e2();
        
        result.eo() = a.scalar() * b.eo() + a.eo() * b.scalar() +
                     a.e1() * b.e1o() + a.e2() * b.e2o() + a.e3() * b.e3o();
        
        result.ei() = a.scalar() * b.ei() + a.ei() * b.scalar() +
                     a.e1() * b.e1i() + a.e2() * b.e2i() + a.e3() * b.e3i();
        
        result.e12() = a.scalar() * b.e12() + a.e1() * b.e2() -
                      a.e2() * b.e1() + a.e12() * b.scalar();
        
        result.e13() = a.scalar() * b.e13() + a.e1() * b.e3() -
                      a.e3() * b.e1() + a.e13() * b.scalar();
        
        result.e23() = a.scalar() * b.e23() + a.e2() * b.e3() -
                      a.e3() * b.e2() + a.e23() * b.scalar();
        
        result.e1o() = a.scalar() * b.e1o() + a.e1() * b.eo() +
                      a.eo() * b.e1() + a.e1o() * b.scalar();
        
        result.e2o() = a.scalar() * b.e2o() + a.e2() * b.eo() +
                      a.eo() * b.e2() + a.e2o() * b.scalar();
        
        result.e3o() = a.scalar() * b.e3o() + a.e3() * b.eo() +
                      a.eo() * b.e3() + a.e3o() * b.scalar();
        
        result.e1i() = a.scalar() * b.e1i() + a.e1() * b.ei() -
                      a.ei() * b.e1() + a.e1i() * b.scalar();
        
        result.e2i() = a.scalar() * b.e2i() + a.e2() * b.ei() -
                      a.ei() * b.e2() + a.e2i() * b.scalar();
        
        result.e3i() = a.scalar() * b.e3i() + a.e3() * b.ei() -
                      a.ei() * b.e3() + a.e3i() * b.scalar();
        
        result.eoi() = a.scalar() * b.eoi() + a.eo() * b.ei() -
                      a.ei() * b.eo() + a.eoi() * b.scalar();
        
        result.e123() = a.scalar() * b.e123() + a.e1() * b.e23() +
                       a.e2() * b.e13() + a.e3() * b.e12() +
                       a.e12() * b.e3() + a.e13() * b.e2() +
                       a.e23() * b.e1() + a.e123() * b.scalar();
        
        result.e12o() = a.scalar() * b.e12o() + a.e12o() * b.scalar();
        result.e13o() = a.scalar() * b.e13o() + a.e13o() * b.scalar();
        result.e23o() = a.scalar() * b.e23o() + a.e23o() * b.scalar();
        result.e12i() = a.scalar() * b.e12i() + a.e12i() * b.scalar();
        result.e13i() = a.scalar() * b.e13i() + a.e13i() * b.scalar();
        result.e23i() = a.scalar() * b.e23i() + a.e23i() * b.scalar();
        result.e1oi() = a.scalar() * b.e1oi() + a.e1oi() * b.scalar();
        result.e2oi() = a.scalar() * b.e2oi() + a.e2oi() * b.scalar();
        result.e3oi() = a.scalar() * b.e3oi() + a.e3oi() * b.scalar();
        
        result.e123o() = a.scalar() * b.e123o() + a.e123o() * b.scalar();
        result.e123i() = a.scalar() * b.e123i() + a.e123i() * b.scalar();
        result.e12oi() = a.scalar() * b.e12oi() + a.e12oi() * b.scalar();
        result.e13oi() = a.scalar() * b.e13oi() + a.e13oi() * b.scalar();
        result.e23oi() = a.scalar() * b.e23oi() + a.e23oi() * b.scalar();
        result.e123oi() = a.scalar() * b.e123oi() + a.e123oi() * b.scalar();
        
        return result;
    }
    
    CgaMultivector wedgeProduct(CgaMultivector& b)
    {
        CgaMultivector result;
        CgaMultivector& a = *this;
        
        result.scalar() = a.scalar() * b.scalar();
        
        result.e1() = a.scalar() * b.e1() + a.e1() * b.scalar();
        result.e2() = a.scalar() * b.e2() + a.e2() * b.scalar();
        result.e3() = a.scalar() * b.e3() + a.e3() * b.scalar();
        result.eo() = a.scalar() * b.eo() + a.eo() * b.scalar();
        result.ei() = a.scalar() * b.ei() + a.ei() * b.scalar();
        
        result.e12() = a.scalar() * b.e12() + a.e1() * b.e2() - 
                      a.e2() * b.e1() + a.e12() * b.scalar();
        result.e13() = a.scalar() * b.e13() + a.e1() * b.e3() - 
                      a.e3() * b.e1() + a.e13() * b.scalar();
        result.e23() = a.scalar() * b.e23() + a.e2() * b.e3() - 
                      a.e3() * b.e2() + a.e23() * b.scalar();
        
        result.e123() = a.scalar() * b.e123() + a.e1() * b.e23() + 
                       a.e2() * b.e13() + a.e3() * b.e12() + 
                       a.e12() * b.e3() + a.e13() * b.e2() + 
                       a.e23() * b.e1() + a.e123() * b.scalar();
        
        return result;
    }
    
    CgaMultivector reverse()
    {
        CgaMultivector result = *this;
        
        result.e12() = -result.e12();
        result.e13() = -result.e13();
        result.e23() = -result.e23();
        result.e1o() = -result.e1o();
        result.e2o() = -result.e2o();
        result.e3o() = -result.e3o();
        result.e1i() = -result.e1i();
        result.e2i() = -result.e2i();
        result.e3i() = -result.e3i();
        result.eoi() = -result.eoi();
        
        result.e123() = -result.e123();
        result.e12o() = -result.e12o();
        result.e13o() = -result.e13o();
        result.e23o() = -result.e23o();
        result.e12i() = -result.e12i();
        result.e13i() = -result.e13i();
        result.e23i() = -result.e23i();
        result.e1oi() = -result.e1oi();
        result.e2oi() = -result.e2oi();
        result.e3oi() = -result.e3oi();

        
        return result;
    }
    
    CgaMultivector dual()
    {
        CgaMultivector result;
        
        result.e123oi() = scalar();
        result.e23oi() = e1();
        result.e13oi() = -e2();
        result.e12oi() = e3();
        result.e3oi() = -eo();
        result.e2oi() = ei();
        
        result.e1oi() = -e12();
        result.eoi() = e13();
        result.e3i() = -e23();
        result.e2i() = e1o();
        result.e1i() = -e2o();
        result.ei() = e3o();
        result.e3o() = e1i();
        result.e2o() = -e2i();
        result.e1o() = e3i();
        result.eo() = -eoi();
        
        result.e23() = -e1oi();
        result.e13() = e2oi();
        result.e12() = -e3oi();
        result.e3() = e12oi();
        result.e2() = -e13oi();
        result.e1() = e23oi();
        result.scalar() = e123oi();
        
        return result;
    }
    
    float norm() const 
    {
        float sum = 0.0f;
        
        for (int i = 0; i < kNumComponents; ++i) 
        {
            sum += components_[i] * components_[i];
        }

        return sqrt(sum);
    }
    
    CgaMultivector dotProduct(CgaMultivector& b)
    {

        CgaMultivector result;
        const CgaMultivector& a = *this;
        
        result.scalar() = a.e1() * b.e1() + a.e2() * b.e2() + a.e3() * b.e3() +
                         a.eo() * b.eo() - a.ei() * b.ei();
        
        return result;
    }
};

class CgaTestVectorGenerator 
{
private:

    mt19937 rng_;
    uniform_real_distribution<float> uniform_dist_;
    normal_distribution<float> normal_dist_;
    
public:

    CgaTestVectorGenerator() : 
        rng_(random_device{}()),
        uniform_dist_(-2.0f, 2.0f),
        normal_dist_(0.0f, 1.0f) {
    }
    
    CgaMultivector generateRandomMultivector() 
    {
        CgaMultivector result;
        
        result.scalar() = uniform_dist_(rng_);
        
        result.e1() = uniform_dist_(rng_) * 0.5f;
        result.e2() = uniform_dist_(rng_) * 0.5f;
        result.e3() = uniform_dist_(rng_) * 0.5f;
        result.eo() = uniform_dist_(rng_) * 0.5f;
        result.ei() = uniform_dist_(rng_) * 0.5f;
        
        for (int i = 6; i <= 15; ++i) 
        {
            result[i] = uniform_dist_(rng_) * 0.1f;
        }
        
        for (int i = 16; i <= 25; ++i) 
        {
            result[i] = uniform_dist_(rng_) * 0.05f;
        }
        
        for (int i = 26; i < CgaMultivector::kNumComponents; ++i) 
        {
            result[i] = uniform_dist_(rng_) * 0.01f;
        }
        
        return result;
    }
    
    vector<CgaMultivector> generateCornerCases() 
    {
        vector<CgaMultivector> cases;
        
        CgaMultivector zero;
        cases.push_back(zero);
        
        CgaMultivector one;
        one.scalar() = 1.0f;
        cases.push_back(one);
        
        CgaMultivector minus_one;
        minus_one.scalar() = -1.0f;
        cases.push_back(minus_one);
        
        for (int i = 1; i < CgaMultivector::kNumComponents; ++i) 
        {
            CgaMultivector unit_element;
            unit_element[i] = 1.0f;
            cases.push_back(unit_element);
            
            CgaMultivector neg_unit_element;
            neg_unit_element[i] = -1.0f;
            cases.push_back(neg_unit_element);
        }
        
        CgaMultivector small_scalar;
        small_scalar.scalar() = 1e-3f;
        cases.push_back(small_scalar);
        
        CgaMultivector large_scalar;
        large_scalar.scalar() = 10.0f;
        cases.push_back(large_scalar);
        
        CgaMultivector cga_point;

        cga_point.e1() = 1.0f;
        cga_point.e2() = 2.0f;
        cga_point.e3() = 3.0f;
        cga_point.eo() = 1.0f;
        cga_point.ei() = 7.0f;
        
        cases.push_back(cga_point);
        
        return cases;
    }
    
    vector<uint16_t> convertMultivectorToQ511Array(CgaMultivector& mv) 
    {
        vector<uint16_t> result(CgaMultivector::kNumComponents);
        
        for (int i = 0; i < CgaMultivector::kNumComponents; ++i) {
            int16_t fixed_val = FixedPointQ511::floatToQ511(mv[i]);
            result[i] = static_cast<uint16_t>(fixed_val);
        }
        
        return result;
    }
    
    CgaMultivector computeGoldenReference(GAFunction op, CgaMultivector& a, 
                                         CgaMultivector& b) 
    {
        switch (op) 
        {
            case GA_FUNCT_ADD:
                return a + b;
                
            case GA_FUNCT_SUB:
                return a - b;
                
            case GA_FUNCT_MUL:
                return a.geometricProduct(b);
                
            case GA_FUNCT_WEDGE:
                return a.wedgeProduct(b);
                
            case GA_FUNCT_DOT:
                return a.dotProduct(b);
                
            case GA_FUNCT_REV:
                return a.reverse();
                
            case GA_FUNCT_DUAL:
                return a.dual();
                
            case GA_FUNCT_NORM: {
                CgaMultivector result;
                result.scalar() = a.norm();
                return result;
            }
            
            default:
                return a;
        }
    }
    
    void generateTestSuite(int num_random_tests) 
    {
        const int kCgaComponents = CgaMultivector::kNumComponents;
        const int kMaxCornerTests = 8;
        
        if (system("mkdir -p vectors") != 0) {
            printf("Warning: Could not create vectors directory\n");
        }
        
        FILE* input_file = fopen("vectors/cga_test_inputs.mem", "w");
        FILE* output_file = fopen("vectors/cga_test_outputs.mem", "w");
        FILE* control_file = fopen("vectors/cga_test_control.mem", "w");
        
        if (!input_file || !output_file || !control_file) {
            printf("Error: Could not create test vector files\n");
            if (input_file) fclose(input_file);
            if (output_file) fclose(output_file);
            if (control_file) fclose(control_file);
            return;
        }
        
        int test_count = 0;
        
        vector<CgaMultivector> corners = generateCornerCases();
        for (int op = GA_FUNCT_ADD; op <= GA_FUNCT_NORM; ++op) 
        {
            size_t corner_limit = min(corners.size(), 
                                    static_cast<size_t>(kMaxCornerTests));
            
            for (size_t i = 0; i < corner_limit; ++i) 
            {
                for (size_t j = 0; j < corner_limit; ++j) 
                {
                    CgaMultivector operand_a = corners[i];
                    CgaMultivector operand_b = corners[j];

                    CgaMultivector expected_result = computeGoldenReference(
                        static_cast<GAFunction>(op), operand_a, operand_b);
                    
                    vector<uint16_t> a_q511 = convertMultivectorToQ511Array(operand_a);
                    vector<uint16_t> b_q511 = convertMultivectorToQ511Array(operand_b);
                    vector<uint16_t> expected_q511 = convertMultivectorToQ511Array(expected_result);
                    
                    // Write input vectors (A then B)
                    for (int k = 0; k < kCgaComponents; k++) 
                    {
                        fprintf(input_file, "%04x", a_q511[k]);
                    }

                    for (int k = 0; k < kCgaComponents; k++) 
                    {
                        fprintf(input_file, "%04x", b_q511[k]);
                    }

                    fprintf(input_file, "\n");
                    
                    for (int k = 0; k < kCgaComponents; k++) 
                    {
                        fprintf(output_file, "%04x", expected_q511[k]);
                    }

                    fprintf(output_file, "\n");
                    fprintf(control_file, "%d\n", op);
                    
                    test_count++;
                    
                    if (test_count <= 10) 
                    {
                        printf("Test %d: op=%d, a[0]=%f, b[0]=%f, result[0]=%f\n", 
                               test_count, op, operand_a.scalar(), operand_b.scalar(), 
                               expected_result.scalar());
                    }
                }
            }
        }
        
        for (int i = 0; i < num_random_tests; ++i) 
        {
            int op = rng_() % 8;

            CgaMultivector operand_a = generateRandomMultivector();
            CgaMultivector operand_b = generateRandomMultivector();
            CgaMultivector expected_result = computeGoldenReference(
                static_cast<GAFunction>(op), operand_a, operand_b);
            
            vector<uint16_t> a_q511 = convertMultivectorToQ511Array(operand_a);
            vector<uint16_t> b_q511 = convertMultivectorToQ511Array(operand_b);
            vector<uint16_t> expected_q511 = convertMultivectorToQ511Array(expected_result);
            
            for (int k = 0; k < kCgaComponents; k++) 
            {
                fprintf(input_file, "%04x", a_q511[k]);
            }

            for (int k = 0; k < kCgaComponents; k++) 
            {
                fprintf(input_file, "%04x", b_q511[k]);
            }

            fprintf(input_file, "\n");
            
            for (int k = 0; k < kCgaComponents; k++) 
            {
                fprintf(output_file, "%04x", expected_q511[k]);
            }

            fprintf(output_file, "\n");
            
            fprintf(control_file, "%d\n", op);
            test_count++;
        }
        
        printf("Generated %d CGA test vectors with Q5.11 fixed-point quantization\n", 
               test_count);
        printf("Multivector format: %d components × 16 bits = %d bytes each\n", 
               kCgaComponents, kCgaComponents * 2);
        printf("Input format: %d hex characters (%d bytes A + %d bytes B)\n", 
               kCgaComponents * 4, kCgaComponents * 2, kCgaComponents * 2);
        printf("Output format: %d hex characters (%d bytes result)\n", 
               kCgaComponents * 2, kCgaComponents * 2);
        
        fclose(input_file);
        fclose(output_file);
        fclose(control_file);
    }
};

int main(int argc, char* argv[]) 
{
    printf("CGA Coprocessor Test Vector Generator\n");
    printf("====================================\n");
    printf("32-component Conformal Geometric Algebra\n");
    printf("Q5.11 Fixed-Point Quantization\n");
    printf("Manual CGA Implementation\n\n");
    
    int num_random_tests = 200;
    
    if (argc > 1) {
        num_random_tests = atoi(argv[1]);
        if (num_random_tests <= 0) {
            printf("Error: Invalid number of random tests: %s\n", argv[1]);
            return 1;
        }
    }
    
    CgaTestVectorGenerator generator;
    generator.generateTestSuite(num_random_tests);
    
    printf("\nTest vector generation complete!\n");
    printf("Files generated:\n");
    printf("  - vectors/cga_test_inputs.mem\n");
    printf("  - vectors/cga_test_outputs.mem\n");  
    printf("  - vectors/cga_test_control.mem\n");
    
    return 0;
}
