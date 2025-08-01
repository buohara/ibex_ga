#include <iostream>
#include <random>
#include <vector>
#include <string>
#include <iomanip>
#include <cmath>
#include <cstdio>
#include <limits>
#include <algorithm>

using namespace std;

#include "../versor/include/vsr/vsr.h"
using namespace vsr;
using namespace vsr::nga;

enum GAFunction 
{
    GA_FUNCT_ADD       = 0,
    GA_FUNCT_SUB       = 1,
    GA_FUNCT_GP        = 2,
    GA_FUNCT_WEDGE     = 3,
    GA_FUNCT_DOT       = 4,
    GA_FUNCT_DUAL      = 5,
    GA_FUNCT_REV       = 6,
    GA_FUNCT_NORM      = 7,
    GA_FUNCT_INV       = 8,
    GA_FUNCT_EXP       = 9,
    GA_FUNCT_LOG       = 10,
    GA_FUNCT_SQRT      = 11,
    GA_FUNCT_TRS       = 12,
    GA_FUNCT_ROT       = 13,
    GA_FUNCT_DLT       = 14,
    GA_FUNCT_MTR       = 15
};

/**
 * Q5.11 Fixed-Point arithmetic utilities for hardware implementation
 */
class FixedPointQ511 
{
public:
    static int16_t floatToQ511(float f) 
    {
        const float MAX_FLOAT = 15.9995f;
        const float MIN_FLOAT = -16.0f;
        const int FRAC_BITS = 11;
        
        f = max(MIN_FLOAT, min(MAX_FLOAT, f));
        return static_cast<int16_t>(f * (1 << FRAC_BITS));
    }
    
    static float q511ToFloat(int16_t q) 
    {
        const int FRAC_BITS = 11;
        return static_cast<float>(q) / (1 << FRAC_BITS);
    }
};

/**
 * Conformal Geometric Algebra Test Vector Generator
 */
class CgaTestVectorGenerator 
{
private:
    mt19937 rng;
    uniform_real_distribution<float> uniformDist;
    normal_distribution<float> normalDist;
    
public:
    CgaTestVectorGenerator() : 
        rng(random_device{}()),
        uniformDist(-4.0f, 4.0f),
        normalDist(0.0f, 1.0f) 
    {
    }
    
    /**
     * Generate random CGA multivector with 32 components
     * @return Random CGA multivector for testing
     */
    NVec<5> generateRandomMultivector() 
    {
        NVec<5> result;
        result.reset();
        
        result[0] = uniformDist(rng);
        
        for (int i = 1; i <= 5 && i < result.Num; ++i) 
        {
            result[i] = uniformDist(rng) * 0.5f;
        }
        
        for (int i = 6; i <= 15 && i < result.Num; ++i) 
        {
            result[i] = uniformDist(rng) * 0.1f;
        }
        
        for (int i = 16; i < result.Num && i < 32; ++i) 
        {
            result[i] = uniformDist(rng) * 0.01f;
        }
        
        return result;
    }
    
    /**
     * Generate geometric corner cases for comprehensive CGA testing
     * @return Vector of corner case multivectors
     */
    vector<NVec<5>> generateCornerCases() 
    {
        vector<NVec<5>> cases;
        
        NVec<5> zero; 
        zero.reset();
        cases.push_back(zero);
        
        NVec<5> one; 
        one.reset(); 
        one[0] = 1.0f;
        cases.push_back(one);
        
        NVec<5> minusOne; 
        minusOne.reset(); 
        minusOne[0] = -1.0f;
        cases.push_back(minusOne);
        
        for (int i = 1; i <= 3 && i < one.Num; ++i) 
        {
            NVec<5> unitVec; 
            unitVec.reset(); 
            unitVec[i] = 1.0f;
            cases.push_back(unitVec);
            
            NVec<5> negUnitVec; 
            negUnitVec.reset(); 
            negUnitVec[i] = -1.0f;
            cases.push_back(negUnitVec);
        }
        
        if (one.Num > 4) 
        {
            NVec<5> origin; 
            origin.reset(); 
            origin[4] = 1.0f;
            cases.push_back(origin);
            
            if (one.Num > 5) 
            {
                NVec<5> infinity; 
                infinity.reset(); 
                infinity[5] = 1.0f;
                cases.push_back(infinity);
            }
        }
        
        NVec<5> smallValue; 
        smallValue.reset(); 
        smallValue[0] = 1e-3f;
        cases.push_back(smallValue);
        
        NVec<5> largeValue; 
        largeValue.reset(); 
        largeValue[0] = 10.0f;
        cases.push_back(largeValue);
        
        return cases;
    }
    
    /**
     * Convert CGA multivector to Q5.11 fixed-point array
     * @param mv Input CGA multivector
     * @return Array of 32 Q5.11 values
     */
    vector<uint16_t> convertMultivectorToQ511Array(const NVec<5>& mv) 
    {
        const int CGA_COMPONENTS = 32;
        vector<uint16_t> result(CGA_COMPONENTS, 0);
        
        int componentsToConvert = min(CGA_COMPONENTS, mv.Num);
        for (int i = 0; i < componentsToConvert; ++i) 
        {
            int16_t fixedVal = FixedPointQ511::floatToQ511(mv[i]);
            result[i] = static_cast<uint16_t>(fixedVal);
        }
        
        return result;
    }
    
    /**
     * Compute golden reference using Versor CGA operations
     * @param op Geometric algebra operation to perform
     * @param a First operand multivector
     * @param b Second operand multivector
     * @return Expected result for hardware verification
     */
    NVec<5> computeGoldenReference(GAFunction op, const NVec<5>& a, const NVec<5>& b) 
    {
        switch (op) 
        {
            case GA_FUNCT_ADD:

                return a + b;
                
            case GA_FUNCT_SUB:

                return a - b;
                
            case GA_FUNCT_GP:

                return a * b;
                
            case GA_FUNCT_WEDGE:

                return a ^ b;
                
            // case GA_FUNCT_DOT:

            //     return a | b;
                
            case GA_FUNCT_REV:

                return ~a;
                
            case GA_FUNCT_DUAL:

                return !a;
                
            case GA_FUNCT_NORM: 
            {
                NVec<5> result; 
                result.reset();
                NVec<5> normSquared = a * ~a;
                float normVal = sqrt(abs(normSquared[0]));
                result[0] = normVal;
                return result;
            }
            
            case GA_FUNCT_INV: 
            {
                NVec<5> dualA = !a;
                NVec<5> denominator = dualA * a;
                if (abs(denominator[0]) > 1e-6f) 
                {
                    return dualA / denominator[0];
                }
                NVec<5> zeroResult; 
                zeroResult.reset();
                return zeroResult;
            }
            
            // case GA_FUNCT_TRS: 
            // {
            //     NVec<5> translator = NVec<5>(1.0f) + 0.5f * b * Inf(1);
            //     return translator * a * ~translator;
            // }
            
            // case GA_FUNCT_ROT: 
            // {
            //     float angle = 0.0f;

            //     for (int i = 6; i <= 8 && i < b.Num; ++i) 
            //         angle += b[i] * b[i];

            //     angle = sqrt(angle);
                
            //     if (angle > 1e-6f) 
            //     {
            //         NVec<5> rotor = cos(angle/2) + sin(angle/2) * (b / angle);
            //         return rotor * a * ~rotor;
            //     }

            //     return a;
            // }
            
            case GA_FUNCT_DLT: 
            {
                float scale = abs(b[0]) > 1e-6f ? b[0] : 1.0f;
                return a * scale;
            }
            
            case GA_FUNCT_MTR: 
            {
                NVec<5> normalizedB = b;
                float normB = sqrt(abs((b * ~b)[0]));
                if (normB > 1e-6f) 
                {
                    normalizedB = b / normB;
                }
                return normalizedB * a * ~normalizedB;
            }
            
            default:
                return a;
        }
    }
    
    /**
     * Generate comprehensive CGA test suite with corner cases and random tests
     * @param numRandomTests Number of random test vectors to generate
     */
    void generateTestSuite(int numRandomTests) 
    {
        const int CGA_COMPONENTS = 32;
        const int MAX_CORNER_TESTS = 5;
        
        if (system("mkdir -p vectors") != 0) 
        {
            printf("Warning: Could not create vectors directory\n");
        }
        
        FILE* inputFile = fopen("vectors/cga_test_inputs.mem", "w");
        FILE* outputFile = fopen("vectors/cga_test_outputs.mem", "w");
        FILE* controlFile = fopen("vectors/cga_test_control.mem", "w");
        
        if (!inputFile || !outputFile || !controlFile) 
        {
            printf("Error: Could not create test vector files\n");
            if (inputFile) fclose(inputFile);
            if (outputFile) fclose(outputFile);
            if (controlFile) fclose(controlFile);
            return;
        }
        
        int testCount = 0;
        
        vector<NVec<5>> corners = generateCornerCases();
        for (int op = GA_FUNCT_ADD; op <= GA_FUNCT_NORM; ++op) 
        {
            size_t cornerLimit = min(corners.size(), 
                                   static_cast<size_t>(MAX_CORNER_TESTS));
            
            for (size_t i = 0; i < cornerLimit; ++i) 
            {
                for (size_t j = 0; j < cornerLimit; ++j) 
                {
                    NVec<5> operandA = corners[i];
                    NVec<5> operandB = corners[j];
                    NVec<5> expectedResult = computeGoldenReference(
                        static_cast<GAFunction>(op), operandA, operandB);
                    
                    vector<uint16_t> aQ511 = convertMultivectorToQ511Array(operandA);
                    vector<uint16_t> bQ511 = convertMultivectorToQ511Array(operandB);
                    vector<uint16_t> expectedQ511 = convertMultivectorToQ511Array(expectedResult);
                    
                    for (int k = 0; k < CGA_COMPONENTS; k++) 
                    {
                        fprintf(inputFile, "%04x", aQ511[k]);
                    }
                    for (int k = 0; k < CGA_COMPONENTS; k++) 
                    {
                        fprintf(inputFile, "%04x", bQ511[k]);
                    }
                    fprintf(inputFile, "\n");
                    
                    for (int k = 0; k < CGA_COMPONENTS; k++) 
                    {
                        fprintf(outputFile, "%04x", expectedQ511[k]);
                    }
                    fprintf(outputFile, "\n");
                    
                    fprintf(controlFile, "%d\n", op);
                    
                    testCount++;
                    
                    if (testCount <= 10) 
                    {
                        printf("Test %d: op=%d, a[0]=%f, b[0]=%f, result[0]=%f\n", 
                               testCount, op, operandA[0], operandB[0], 
                               expectedResult[0]);
                    }
                }
            }
        }
        
        for (int i = 0; i < numRandomTests; ++i) 
        {
            int op = rng() % 8;
            NVec<5> operandA = generateRandomMultivector();
            NVec<5> operandB = generateRandomMultivector();
            NVec<5> expectedResult = computeGoldenReference(
                static_cast<GAFunction>(op), operandA, operandB);
            
            vector<uint16_t> aQ511 = convertMultivectorToQ511Array(operandA);
            vector<uint16_t> bQ511 = convertMultivectorToQ511Array(operandB);
            vector<uint16_t> expectedQ511 = convertMultivectorToQ511Array(expectedResult);
            
            for (int k = 0; k < CGA_COMPONENTS; k++) 
            {
                fprintf(inputFile, "%04x", aQ511[k]);
            }
            for (int k = 0; k < CGA_COMPONENTS; k++) 
            {
                fprintf(inputFile, "%04x", bQ511[k]);
            }
            fprintf(inputFile, "\n");
            
            for (int k = 0; k < CGA_COMPONENTS; k++) 
            {
                fprintf(outputFile, "%04x", expectedQ511[k]);
            }
            fprintf(outputFile, "\n");
            
            fprintf(controlFile, "%d\n", op);
            testCount++;
        }
        
        printf("Generated %d CGA test vectors with Q5.11 fixed-point quantization\n", 
               testCount);
        printf("Multivector format: %d components × 16 bits = %d bytes each\n", 
               CGA_COMPONENTS, CGA_COMPONENTS * 2);
        printf("Input format: %d hex characters (%d bytes A + %d bytes B)\n", 
               CGA_COMPONENTS * 4, CGA_COMPONENTS * 2, CGA_COMPONENTS * 2);
        printf("Output format: %d hex characters (%d bytes result)\n", 
               CGA_COMPONENTS * 2, CGA_COMPONENTS * 2);
        
        fclose(inputFile);
        fclose(outputFile);
        fclose(controlFile);
    }
};

/**
 * Main function - generates CGA test vectors with command line options
 */
int main(int argc, char* argv[]) 
{
    printf("CGA Coprocessor Test Vector Generator\n");
    printf("====================================\n");
    printf("32-component Conformal Geometric Algebra\n");
    printf("Q5.11 Fixed-Point Quantization\n");
    printf("Using Versor library for golden reference\n\n");
    
    int numRandomTests = 200;
    if (argc > 1) 
    {
        numRandomTests = atoi(argv[1]);
        if (numRandomTests <= 0) 
        {
            printf("Error: Invalid number of random tests: %s\n", argv[1]);
            return 1;
        }
    }
    
    CgaTestVectorGenerator generator;
    generator.generateTestSuite(numRandomTests);
    
    printf("\nTest vector generation complete!\n");
    printf("Files generated:\n");
    printf("  - vectors/cga_test_inputs.mem\n");
    printf("  - vectors/cga_test_outputs.mem\n");  
    printf("  - vectors/cga_test_control.mem\n");
    
    return 0;
}
