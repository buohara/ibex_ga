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
    
    static int16_t addQ511(int16_t a, int16_t b) 
    {
        int32_t result = static_cast<int32_t>(a) + static_cast<int32_t>(b);
        if (result > 32767) result = 32767;
        if (result < -32768) result = -32768;
        return static_cast<int16_t>(result);
    }
    
    static int16_t subQ511(int16_t a, int16_t b) 
    {
        int32_t result = static_cast<int32_t>(a) - static_cast<int32_t>(b);
        if (result > 32767) result = 32767;
        if (result < -32768) result = -32768;
        return static_cast<int16_t>(result);
    }
    
    static int16_t mulQ511(int16_t a, int16_t b) 
    {
        int32_t temp = static_cast<int32_t>(a) * static_cast<int32_t>(b);
        temp >>= 11;
        
        if (temp > 32767) temp = 32767;
        if (temp < -32768) temp = -32768;
        return static_cast<int16_t>(temp);
    }
    
    static int16_t negQ511(int16_t a) 
    {
        if (a == -32768) return 32767;
        return static_cast<int16_t>(-a);
    }
};

class CgaMultivector 
{
public:
    static const int kNumComponents = 32;
    array<int16_t, kNumComponents> components_;
    
    CgaMultivector() 
    {
        reset();
    }
    
    void reset() 
    {
        fill(components_.begin(), components_.end(), 0);
    }
    
    int16_t& operator[](int index) 
    {
        return components_[index];
    }
    
    const int16_t& operator[](int index) const 
    {
        return components_[index];
    }
    
    int16_t& scalar() { return components_[0]; }
    int16_t& e1() { return components_[1]; }
    int16_t& e2() { return components_[2]; }
    int16_t& e3() { return components_[3]; }
    int16_t& eo() { return components_[4]; }
    int16_t& ei() { return components_[5]; }
    int16_t& e12() { return components_[6]; }
    int16_t& e13() { return components_[7]; }
    int16_t& e23() { return components_[8]; }
    int16_t& e1o() { return components_[9]; }
    int16_t& e2o() { return components_[10]; }
    int16_t& e3o() { return components_[11]; }
    int16_t& e1i() { return components_[12]; }
    int16_t& e2i() { return components_[13]; }
    int16_t& e3i() { return components_[14]; }
    int16_t& eoi() { return components_[15]; }
    int16_t& e123() { return components_[16]; }
    int16_t& e12o() { return components_[17]; }
    int16_t& e13o() { return components_[18]; }
    int16_t& e23o() { return components_[19]; }
    int16_t& e12i() { return components_[20]; }
    int16_t& e13i() { return components_[21]; }
    int16_t& e23i() { return components_[22]; }
    int16_t& e1oi() { return components_[23]; }
    int16_t& e2oi() { return components_[24]; }
    int16_t& e3oi() { return components_[25]; }
    int16_t& e123o() { return components_[26]; }
    int16_t& e123i() { return components_[27]; }
    int16_t& e12oi() { return components_[28]; }
    int16_t& e13oi() { return components_[29]; }
    int16_t& e23oi() { return components_[30]; }
    int16_t& e123oi() { return components_[31]; }
    
    const int16_t& scalar() const { return components_[0]; }
    const int16_t& e1() const { return components_[1]; }
    const int16_t& e2() const { return components_[2]; }
    const int16_t& e3() const { return components_[3]; }
    const int16_t& eo() const { return components_[4]; }
    const int16_t& ei() const { return components_[5]; }
    
    CgaMultivector operator+(const CgaMultivector& other) const 
    {
        CgaMultivector result;
        for (int i = 0; i < kNumComponents; ++i) 
        {
            result[i] = FixedPointQ511::addQ511(components_[i], other[i]);
        }
        return result;
    }
    
    CgaMultivector operator-(const CgaMultivector& other) const 
    {
        CgaMultivector result;
        for (int i = 0; i < kNumComponents; ++i) 
        {
            result[i] = FixedPointQ511::subQ511(components_[i], other[i]);
        }
        return result;
    }
    
    CgaMultivector geometricProduct(CgaMultivector& b) 
    {
        CgaMultivector result;
        CgaMultivector& a = *this;
        
        auto mac = [](int16_t acc, int16_t x, int16_t y) -> int16_t 
        {
            return FixedPointQ511::addQ511(acc, FixedPointQ511::mulQ511(x, y));
        };
        
        auto macSub = [](int16_t acc, int16_t x, int16_t y) -> int16_t 
        {
            return FixedPointQ511::subQ511(acc, FixedPointQ511::mulQ511(x, y));
        };
        
        result.scalar() = FixedPointQ511::mulQ511(a.scalar(), b.scalar());
        result.scalar() = mac(result.scalar(), a.e1(), b.e1());
        result.scalar() = mac(result.scalar(), a.e2(), b.e2());
        result.scalar() = mac(result.scalar(), a.e3(), b.e3());
        result.scalar() = mac(result.scalar(), a.eo(), b.eo());
        result.scalar() = macSub(result.scalar(), a.ei(), b.ei());
        result.scalar() = macSub(result.scalar(), a.e12(), b.e12());
        result.scalar() = macSub(result.scalar(), a.e13(), b.e13());
        result.scalar() = macSub(result.scalar(), a.e23(), b.e23());
        result.scalar() = mac(result.scalar(), a.e1o(), b.e1o());
        result.scalar() = mac(result.scalar(), a.e2o(), b.e2o());
        result.scalar() = mac(result.scalar(), a.e3o(), b.e3o());
        result.scalar() = macSub(result.scalar(), a.e1i(), b.e1i());
        result.scalar() = macSub(result.scalar(), a.e2i(), b.e2i());
        result.scalar() = macSub(result.scalar(), a.e3i(), b.e3i());
        result.scalar() = macSub(result.scalar(), a.eoi(), b.eoi());
        result.scalar() = macSub(result.scalar(), a.e123(), b.e123());
        result.scalar() = mac(result.scalar(), a.e12o(), b.e12o());
        result.scalar() = mac(result.scalar(), a.e13o(), b.e13o());
        result.scalar() = mac(result.scalar(), a.e23o(), b.e23o());
        result.scalar() = macSub(result.scalar(), a.e12i(), b.e12i());
        result.scalar() = macSub(result.scalar(), a.e13i(), b.e13i());
        result.scalar() = macSub(result.scalar(), a.e23i(), b.e23i());
        result.scalar() = mac(result.scalar(), a.e1oi(), b.e1oi());
        result.scalar() = mac(result.scalar(), a.e2oi(), b.e2oi());
        result.scalar() = mac(result.scalar(), a.e3oi(), b.e3oi());
        result.scalar() = macSub(result.scalar(), a.e123o(), b.e123o());
        result.scalar() = mac(result.scalar(), a.e123i(), b.e123i());
        result.scalar() = macSub(result.scalar(), a.e12oi(), b.e12oi());
        result.scalar() = macSub(result.scalar(), a.e13oi(), b.e13oi());
        result.scalar() = macSub(result.scalar(), a.e23oi(), b.e23oi());
        result.scalar() = mac(result.scalar(), a.e123oi(), b.e123oi());
        
        for (int i = 1; i < kNumComponents; ++i) 
        {
            result[i] = FixedPointQ511::addQ511(
                FixedPointQ511::mulQ511(a.scalar(), b[i]),
                FixedPointQ511::mulQ511(a[i], b.scalar())
            );
        }
        
        return result;
    }
    
    CgaMultivector wedgeProduct(CgaMultivector& b) 
    {
        CgaMultivector result;
        CgaMultivector& a = *this;
        
        result.scalar() = FixedPointQ511::mulQ511(a.scalar(), b.scalar());
        
        for (int i = 1; i <= 5; ++i) 
        {
            result[i] = FixedPointQ511::addQ511(
                FixedPointQ511::mulQ511(a.scalar(), b[i]),
                FixedPointQ511::mulQ511(a[i], b.scalar())
            );
        }
        
        result.e12() = FixedPointQ511::mulQ511(a.scalar(), b.e12());
        result.e12() = FixedPointQ511::addQ511(result.e12(), 
            FixedPointQ511::mulQ511(a.e1(), b.e2()));
        result.e12() = FixedPointQ511::subQ511(result.e12(), 
            FixedPointQ511::mulQ511(a.e2(), b.e1()));
        result.e12() = FixedPointQ511::addQ511(result.e12(), 
            FixedPointQ511::mulQ511(a.e12(), b.scalar()));
        
        return result;
    }
    
    CgaMultivector dotProduct(const CgaMultivector& b) const 
    {
        CgaMultivector result;
        const CgaMultivector& a = *this;
        
        result.scalar() = FixedPointQ511::mulQ511(a.e1(), b.e1());
        result.scalar() = FixedPointQ511::addQ511(result.scalar(), 
            FixedPointQ511::mulQ511(a.e2(), b.e2()));
        result.scalar() = FixedPointQ511::addQ511(result.scalar(), 
            FixedPointQ511::mulQ511(a.e3(), b.e3()));
        result.scalar() = FixedPointQ511::addQ511(result.scalar(), 
            FixedPointQ511::mulQ511(a.eo(), b.eo()));
        result.scalar() = FixedPointQ511::subQ511(result.scalar(), 
            FixedPointQ511::mulQ511(a.ei(), b.ei()));
        
        return result;
    }
    
    CgaMultivector reverse() const 
    {
        CgaMultivector result = *this;
        
        result.e12() = FixedPointQ511::negQ511(result.e12());
        result.e13() = FixedPointQ511::negQ511(result.e13());
        result.e23() = FixedPointQ511::negQ511(result.e23());
        result.e1o() = FixedPointQ511::negQ511(result.e1o());
        result.e2o() = FixedPointQ511::negQ511(result.e2o());
        result.e3o() = FixedPointQ511::negQ511(result.e3o());
        result.e1i() = FixedPointQ511::negQ511(result.e1i());
        result.e2i() = FixedPointQ511::negQ511(result.e2i());
        result.e3i() = FixedPointQ511::negQ511(result.e3i());
        result.eoi() = FixedPointQ511::negQ511(result.eoi());
        result.e123() = FixedPointQ511::negQ511(result.e123());
        result.e12o() = FixedPointQ511::negQ511(result.e12o());
        result.e13o() = FixedPointQ511::negQ511(result.e13o());
        result.e23o() = FixedPointQ511::negQ511(result.e23o());
        result.e12i() = FixedPointQ511::negQ511(result.e12i());
        result.e13i() = FixedPointQ511::negQ511(result.e13i());
        result.e23i() = FixedPointQ511::negQ511(result.e23i());
        result.e1oi() = FixedPointQ511::negQ511(result.e1oi());
        result.e2oi() = FixedPointQ511::negQ511(result.e2oi());
        result.e3oi() = FixedPointQ511::negQ511(result.e3oi());
        
        return result;
    }
    
    CgaMultivector dual() 
    {
        CgaMultivector result;
        
        result.e123oi() = scalar();
        result.e23oi() = e1();
        result.e13oi() = FixedPointQ511::negQ511(e2());
        result.e12oi() = e3();
        result.e3oi() = FixedPointQ511::negQ511(eo());
        result.e2oi() = ei();
        result.e1oi() = FixedPointQ511::negQ511(e12());
        result.eoi() = e13();
        result.e3i() = FixedPointQ511::negQ511(e23());
        result.e2i() = e1o();
        result.e1i() = FixedPointQ511::negQ511(e2o());
        result.ei() = e3o();
        result.e3o() = e1i();
        result.e2o() = FixedPointQ511::negQ511(e2i());
        result.e1o() = e3i();
        result.eo() = FixedPointQ511::negQ511(eoi());
        result.e23() = FixedPointQ511::negQ511(e1oi());
        result.e13() = e2oi();
        result.e12() = FixedPointQ511::negQ511(e3oi());
        result.e3() = e12oi();
        result.e2() = FixedPointQ511::negQ511(e13oi());
        result.e1() = e23oi();
        result.scalar() = e123oi();
        
        return result;
    }
    
    int16_t norm() const 
    {
        int32_t sum = 0;
        for (int i = 0; i < kNumComponents; ++i) 
        {
            int32_t term = static_cast<int32_t>(components_[i]) * components_[i];
            sum += term >> 11;
        }
        
        if (sum <= 0) return 0;
        
        int32_t x = sum;
        int32_t root = 0;
        int32_t bit = 1 << 14;
        
        while (bit > x) bit >>= 2;
        
        while (bit != 0) 
        {
            if (x >= root + bit) 
            {
                x -= root + bit;
                root = (root >> 1) + bit;
            } 
            else 
            {
                root >>= 1;
            }
            bit >>= 2;
        }
        
        return static_cast<int16_t>(min(static_cast<int32_t>(32767), root));
    }
    
    static CgaMultivector fromFloat(const vector<float>& floatComponents) 
    {
        CgaMultivector result;
        for (int i = 0; i < min(static_cast<int>(floatComponents.size()), 
                               kNumComponents); ++i) 
        {
            result[i] = FixedPointQ511::floatToQ511(floatComponents[i]);
        }
        return result;
    }
    
    vector<uint16_t> toUint16Array() const 
    {
        vector<uint16_t> result(kNumComponents);
        for (int i = 0; i < kNumComponents; ++i) 
        {
            result[i] = static_cast<uint16_t>(components_[i]);
        }
        return result;
    }
};

class CgaTestVectorGenerator 
{
private:
    mt19937 rng;
    uniform_real_distribution<float> uniformDist;
    normal_distribution<float> normalDist;
    
public:
    CgaTestVectorGenerator() : 
        rng(random_device{}()),
        uniformDist(-2.0f, 2.0f),
        normalDist(0.0f, 1.0f) 
    {
    }
    
    CgaMultivector generateRandomMultivector() 
    {
        CgaMultivector result;
        
        result.scalar() = FixedPointQ511::floatToQ511(uniformDist(rng));
        result.e1() = FixedPointQ511::floatToQ511(uniformDist(rng) * 0.5f);
        result.e2() = FixedPointQ511::floatToQ511(uniformDist(rng) * 0.5f);
        result.e3() = FixedPointQ511::floatToQ511(uniformDist(rng) * 0.5f);
        result.eo() = FixedPointQ511::floatToQ511(uniformDist(rng) * 0.5f);
        result.ei() = FixedPointQ511::floatToQ511(uniformDist(rng) * 0.5f);
        
        for (int i = 6; i <= 15; ++i) 
        {
            result[i] = FixedPointQ511::floatToQ511(uniformDist(rng) * 0.1f);
        }
        
        for (int i = 16; i <= 25; ++i) 
        {
            result[i] = FixedPointQ511::floatToQ511(uniformDist(rng) * 0.05f);
        }
        
        for (int i = 26; i < CgaMultivector::kNumComponents; ++i) 
        {
            result[i] = FixedPointQ511::floatToQ511(uniformDist(rng) * 0.01f);
        }
        
        return result;
    }
    
    vector<CgaMultivector> generateCornerCases() 
    {
        vector<CgaMultivector> cases;
        
        CgaMultivector zero;
        cases.push_back(zero);
        
        CgaMultivector one;
        one.scalar() = FixedPointQ511::floatToQ511(1.0f);
        cases.push_back(one);
        
        CgaMultivector minusOne;
        minusOne.scalar() = FixedPointQ511::floatToQ511(-1.0f);
        cases.push_back(minusOne);
        
        for (int i = 1; i < CgaMultivector::kNumComponents; ++i) 
        {
            CgaMultivector unitElement;
            unitElement[i] = FixedPointQ511::floatToQ511(1.0f);
            cases.push_back(unitElement);
            
            CgaMultivector negUnitElement;
            negUnitElement[i] = FixedPointQ511::floatToQ511(-1.0f);
            cases.push_back(negUnitElement);
        }
        
        CgaMultivector cgaPoint;
        cgaPoint.e1() = FixedPointQ511::floatToQ511(1.0f);
        cgaPoint.e2() = FixedPointQ511::floatToQ511(2.0f);
        cgaPoint.e3() = FixedPointQ511::floatToQ511(3.0f);
        cgaPoint.eo() = FixedPointQ511::floatToQ511(1.0f);
        cgaPoint.ei() = FixedPointQ511::floatToQ511(7.0f);
        cases.push_back(cgaPoint);
        
        return cases;
    }
    
    CgaMultivector computeGoldenReference(GAFunction op, 
                                        CgaMultivector& a, 
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
            case GA_FUNCT_NORM: 
            {
                CgaMultivector result;
                result.scalar() = a.norm();
                return result;
            }
            default:
                return a;
        }
    }
    
    void generateTestSuite(int numRandomTests) 
    {
        const int kCgaComponents = CgaMultivector::kNumComponents;
        const int kMaxCornerTests = 8;
        
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
        
        vector<CgaMultivector> corners = generateCornerCases();
        for (int op = GA_FUNCT_ADD; op <= GA_FUNCT_NORM; ++op) 
        {
            size_t cornerLimit = min(corners.size(), 
                                   static_cast<size_t>(kMaxCornerTests));
            
            for (size_t i = 0; i < cornerLimit; ++i) 
            {
                for (size_t j = 0; j < cornerLimit; ++j) 
                {
                    CgaMultivector& operandA = corners[i];
                    CgaMultivector& operandB = corners[j];
                    CgaMultivector expectedResult = computeGoldenReference(
                        static_cast<GAFunction>(op), operandA, operandB);
                    
                    vector<uint16_t> aQ511 = operandA.toUint16Array();
                    vector<uint16_t> bQ511 = operandB.toUint16Array();
                    vector<uint16_t> expectedQ511 = expectedResult.toUint16Array();
                    
                    for (int k = 0; k < kCgaComponents; k++) 
                    {
                        fprintf(inputFile, "%04x", aQ511[k]);
                    }
                    for (int k = 0; k < kCgaComponents; k++) 
                    {
                        fprintf(inputFile, "%04x", bQ511[k]);
                    }
                    fprintf(inputFile, "\n");
                    
                    for (int k = 0; k < kCgaComponents; k++) 
                    {
                        fprintf(outputFile, "%04x", expectedQ511[k]);
                    }
                    fprintf(outputFile, "\n");
                    
                    fprintf(controlFile, "%d\n", op);
                    testCount++;
                }
            }
        }
        
        for (int i = 0; i < numRandomTests; ++i) 
        {
            int op = 2;//rng() % 8;
            
            CgaMultivector operandA = generateRandomMultivector();
            CgaMultivector operandB = generateRandomMultivector();
            CgaMultivector expectedResult = computeGoldenReference(
                static_cast<GAFunction>(op), operandA, operandB);
            
            vector<uint16_t> aQ511 = operandA.toUint16Array();
            vector<uint16_t> bQ511 = operandB.toUint16Array();
            vector<uint16_t> expectedQ511 = expectedResult.toUint16Array();
            
            for (int k = 0; k < kCgaComponents; k++) 
            {
                fprintf(inputFile, "%04x", aQ511[k]);
            }
            for (int k = 0; k < kCgaComponents; k++) 
            {
                fprintf(inputFile, "%04x", bQ511[k]);
            }
            fprintf(inputFile, "\n");
            
            for (int k = 0; k < kCgaComponents; k++) 
            {
                fprintf(outputFile, "%04x", expectedQ511[k]);
            }
            fprintf(outputFile, "\n");
            
            fprintf(controlFile, "%d\n", op);
            testCount++;
        }
        
        printf("Generated %d CGA test vectors with Q5.11 fixed-point arithmetic\n", testCount);
        
        fclose(inputFile);
        fclose(outputFile);
        fclose(controlFile);
    }
};

int main(int argc, char* argv[]) 
{
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
