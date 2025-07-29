#include <iostream>
#include <random>
#include <vector>
#include <string>
#include <iomanip>
#include <cmath>
#include <cstdio>
#include <limits>

using namespace std;

#include "../versor/include/vsr/vsr.h"
using namespace vsr;
using namespace vsr::nga;

enum GAFunction 
{
    GA_FUNCT_ADD       = 0,
    GA_FUNCT_SUB       = 1,
    GA_FUNCT_MUL       = 2,
    GA_FUNCT_WEDGE     = 3,
    GA_FUNCT_DOT       = 4,
    GA_FUNCT_DUAL      = 5,
    GA_FUNCT_REV       = 6,
    GA_FUNCT_NORM      = 7,
    GA_FUNCT_LOAD      = 8,
    GA_FUNCT_STORE     = 9,
    GA_FUNCT_ROTATE    = 10,
    GA_FUNCT_REFLECT   = 11
};

class GATestVectorGenerator 
{
private:
    mt19937 rng;
    uniform_real_distribution<float> uniformDist;
    normal_distribution<float> normalDist;
    
public:
    GATestVectorGenerator() : 
        rng(random_device{}()),
        uniformDist(-10.0f, 10.0f),
        normalDist(0.0f, 1.0f) 
    {
    }
    
    /**
     * Generate random NGA multivector using Versor library
     * @return Random multivector with mixed-grade elements for testing
     */
    NVec<5> RandomMultivector() 
    {
        NVec<5> result;
        result.reset();
        
        result[0] = uniformDist(rng);
        
        for (int i = 1; i < result.Num; ++i) 
        {
            result[i] = uniformDist(rng) * 0.1f;
        }
        return result;
    }
    
    /**
     * Generate corner case NGA multivectors for comprehensive testing
     * @return Vector containing special geometric algebra test cases
     */
    vector<NVec<5>> CornerCases() 
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
        
        for (int i = 1; i < min(6, one.Num); ++i) 
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
        
        NVec<5> smallValue;
        smallValue.reset();
        smallValue[0] = 1e-6f;
        cases.push_back(smallValue);
        
        NVec<5> largeValue;
        largeValue.reset();
        largeValue[0] = 100.0f;
        cases.push_back(largeValue);
        
        return cases;
    }
    
    /**
     * Convert NGA multivector to 32-bit float representation
     * @param mv The multivector to convert
     * @return 32-bit unsigned integer representation of significant component
     */
    uint32_t MultivectorToUint32(const NVec<5>& mv) 
    {
        union 
        { 
            float f; 
            uint32_t u; 
        } converter;
        
        float maxVal     = 0.0f;
        int maxIdx       = 0;
        
        for (int i = 0; i < mv.Num; ++i) 
        {
            if (abs(mv[i]) > abs(maxVal)) 
            {
                maxVal = mv[i];
                maxIdx = i;
            }
        }
        
        converter.f = maxVal;
        return converter.u;
    }
    
    /**
     * Compute golden reference using Versor NGA operations
     * @param op The geometric algebra operation to perform
     * @param a First operand multivector
     * @param b Second operand multivector
     * @return Expected result multivector for hardware verification
     */
    NVec<5> ComputeGolden(GAFunction op, const NVec<5>& a, const NVec<5>& b) 
    {
        switch (op) 
        {
            case GA_FUNCT_ADD:
                return a + b;
                
            case GA_FUNCT_SUB:
                return a - b;
                
            case GA_FUNCT_MUL:
                return a * b;
                
            case GA_FUNCT_WEDGE:
                return a ^ b;
                
            case GA_FUNCT_DOT:
                return a <= b;
                
            case GA_FUNCT_REV:
                return ~a;
                
            case GA_FUNCT_DUAL:
                return !a;
                
            case GA_FUNCT_NORM:
            {
                NVec<5> result;
                result.reset();
                NVec<5> temp = a * ~a;
                result[0] = sqrt(abs(temp[0]));
                return result;
            }
                
            case GA_FUNCT_ROTATE: 
            {
                return a;
            }
                
            case GA_FUNCT_REFLECT: 
            {
                return a;
            }
                
            default:
                return a;
        }
    }
    
    /**
     * Generate comprehensive test vector suite and write to memory files
     * @param numRandomTests Number of random test cases to generate
     */
    void GenerateTestSuite(int numRandomTests = 100) 
    {
        system("mkdir -p vectors");
        
        FILE* inputFile     = fopen("vectors/ga_test_inputs.mem", "w");
        FILE* outputFile    = fopen("vectors/ga_test_outputs.mem", "w");
        FILE* controlFile   = fopen("vectors/ga_test_control.mem", "w");
        
        if (!inputFile || !outputFile || !controlFile) 
        {
            printf("Error: Could not create test vector files\n");
            return;
        }
        
        int testCount = 0;
        
        vector<NVec<5>> corners = CornerCases();
        for (int op = GA_FUNCT_ADD; op <= GA_FUNCT_NORM; ++op) 
        {
            for (size_t i = 0; i < corners.size() && i < 5; ++i) 
            {
                for (size_t j = 0; j < corners.size() && j < 5; ++j) 
                {
                    NVec<5> a        = corners[i];
                    NVec<5> b        = corners[j];
                    NVec<5> expected = ComputeGolden(static_cast<GAFunction>(op), a, b);
                    
                    fprintf(inputFile, "%08x %08x\n", 
                           MultivectorToUint32(a), MultivectorToUint32(b));
                    fprintf(outputFile, "%08x\n", 
                           MultivectorToUint32(expected));
                    fprintf(controlFile, "%d\n", op);
                    
                    testCount++;
                    
                    printf("Test %d: op=%d, a[0]=%f, b[0]=%f, result[0]=%f\n", 
                           testCount, op, a[0], b[0], expected[0]);
                }
            }
        }
        
        for (int i = 0; i < numRandomTests; ++i) 
        {
            int op           = rng() % 8;
            NVec<5> a        = RandomMultivector();
            NVec<5> b        = RandomMultivector();
            NVec<5> expected = ComputeGolden(static_cast<GAFunction>(op), a, b);
            
            fprintf(inputFile, "%08x %08x\n", 
                   MultivectorToUint32(a), MultivectorToUint32(b));
            fprintf(outputFile, "%08x\n", 
                   MultivectorToUint32(expected));
            fprintf(controlFile, "%d\n", op);
            
            testCount++;
        }
        
        printf("Generated %d test vectors using Versor NGA\n", testCount);
        
        fclose(inputFile);
        fclose(outputFile);
        fclose(controlFile);
    }
};

int main() 
{
    printf("GA Coprocessor Test Vector Generator\n");
    printf("====================================\n");
    printf("Using Versor library for NGA golden reference calculations\n");
    
    GATestVectorGenerator generator;
    generator.GenerateTestSuite(100);
    
    printf("Test vector generation complete!\n");
    printf("Files generated:\n");
    printf("  - vectors/ga_test_inputs.mem\n");
    printf("  - vectors/ga_test_outputs.mem\n");
    printf("  - vectors/ga_test_control.mem\n");
    
    return 0;
}
