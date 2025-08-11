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
        temp += (1 << (11-1));
        temp >>= 11;
        
        if (temp > 32767)
            temp = 32767;
        
        if (temp < -32768)
            temp = -32768;
        
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

        result.scalar() = 0;
        result.scalar() = mac(result.scalar(), a.scalar(), b.scalar());
        result.scalar() = mac(result.scalar(), a.e1(), b.e1());
        result.scalar() = mac(result.scalar(), a.e2(), b.e2());
        result.scalar() = mac(result.scalar(), a.e12(), b.e12());
        result.scalar() = mac(result.scalar(), a.e3(), b.e3());
        result.scalar() = mac(result.scalar(), a.e13(), b.e13());
        result.scalar() = mac(result.scalar(), a.e23(), b.e23());
        result.scalar() = mac(result.scalar(), a.e123(), b.e123());
        result.scalar() = macSub(result.scalar(), a.eo(), b.ei());
        result.scalar() = macSub(result.scalar(), a.e1o(), b.e1i());
        result.scalar() = macSub(result.scalar(), a.e2o(), b.e2i());
        result.scalar() = macSub(result.scalar(), a.e12o(), b.e12i());
        result.scalar() = macSub(result.scalar(), a.e3o(), b.e3i());
        result.scalar() = macSub(result.scalar(), a.e13o(), b.e13i());
        result.scalar() = macSub(result.scalar(), a.e23o(), b.e23i());
        result.scalar() = macSub(result.scalar(), a.e123o(), b.e123i());
        result.scalar() = macSub(result.scalar(), a.ei(), b.eo());
        result.scalar() = macSub(result.scalar(), a.e1i(), b.e1o());
        result.scalar() = macSub(result.scalar(), a.e2i(), b.e2o());
        result.scalar() = macSub(result.scalar(), a.e12i(), b.e12o());
        result.scalar() = macSub(result.scalar(), a.e3i(), b.e3o());
        result.scalar() = macSub(result.scalar(), a.e13i(), b.e13o());
        result.scalar() = macSub(result.scalar(), a.e23i(), b.e23o());
        result.scalar() = macSub(result.scalar(), a.e123i(), b.e123o());
        result.scalar() = macSub(result.scalar(), a.eoi(), b.scalar());
        result.scalar() = macSub(result.scalar(), a.eoi(), b.eoi());
        result.scalar() = macSub(result.scalar(), a.e1oi(), b.e1());
        result.scalar() = macSub(result.scalar(), a.e1oi(), b.e1oi());
        result.scalar() = macSub(result.scalar(), a.e2oi(), b.e2());
        result.scalar() = macSub(result.scalar(), a.e2oi(), b.e2oi());
        result.scalar() = macSub(result.scalar(), a.e12oi(), b.e12());
        result.scalar() = macSub(result.scalar(), a.e12oi(), b.e12oi());
        result.scalar() = macSub(result.scalar(), a.e3oi(), b.e3());
        result.scalar() = macSub(result.scalar(), a.e3oi(), b.e3oi());
        result.scalar() = macSub(result.scalar(), a.e13oi(), b.e13());
        result.scalar() = macSub(result.scalar(), a.e13oi(), b.e13oi());
        result.scalar() = macSub(result.scalar(), a.e23oi(), b.e23());
        result.scalar() = macSub(result.scalar(), a.e23oi(), b.e23oi());
        result.scalar() = macSub(result.scalar(), a.e123oi(), b.e123());
        result.scalar() = macSub(result.scalar(), a.e123oi(), b.e123oi());

        result.e1() = 0;
        result.e1() = mac(result.e1(), a.scalar(), b.e1());
        result.e1() = mac(result.e1(), a.e1(), b.scalar());
        result.e1() = macSub(result.e1(), a.e2(), b.e12());
        result.e1() = macSub(result.e1(), a.e12(), b.e2());
        result.e1() = macSub(result.e1(), a.e3(), b.e13());
        result.e1() = macSub(result.e1(), a.e13(), b.e3());
        result.e1() = mac(result.e1(), a.e23(), b.e123());
        result.e1() = mac(result.e1(), a.e123(), b.e23());
        result.e1() = mac(result.e1(), a.eo(), b.e1i());
        result.e1() = mac(result.e1(), a.e1o(), b.ei());
        result.e1() = macSub(result.e1(), a.e2o(), b.e12i());
        result.e1() = macSub(result.e1(), a.e12o(), b.e2i());
        result.e1() = macSub(result.e1(), a.e3o(), b.e13i());
        result.e1() = macSub(result.e1(), a.e13o(), b.e3i());
        result.e1() = mac(result.e1(), a.e23o(), b.e123i());
        result.e1() = mac(result.e1(), a.e123o(), b.e23i());
        result.e1() = mac(result.e1(), a.ei(), b.e1o());
        result.e1() = mac(result.e1(), a.e1i(), b.eo());
        result.e1() = macSub(result.e1(), a.e2i(), b.e12o());
        result.e1() = macSub(result.e1(), a.e12i(), b.e2o());
        result.e1() = macSub(result.e1(), a.e3i(), b.e13o());
        result.e1() = macSub(result.e1(), a.e13i(), b.e3o());
        result.e1() = mac(result.e1(), a.e23i(), b.e123o());
        result.e1() = mac(result.e1(), a.e123i(), b.e23o());
        result.e1() = macSub(result.e1(), a.eoi(), b.e1());
        result.e1() = macSub(result.e1(), a.eoi(), b.e1oi());
        result.e1() = macSub(result.e1(), a.e1oi(), b.scalar());
        result.e1() = macSub(result.e1(), a.e1oi(), b.eoi());
        result.e1() = mac(result.e1(), a.e2oi(), b.e12());
        result.e1() = mac(result.e1(), a.e2oi(), b.e12oi());
        result.e1() = mac(result.e1(), a.e12oi(), b.e2());
        result.e1() = mac(result.e1(), a.e12oi(), b.e2oi());
        result.e1() = mac(result.e1(), a.e3oi(), b.e13());
        result.e1() = mac(result.e1(), a.e3oi(), b.e13oi());
        result.e1() = mac(result.e1(), a.e13oi(), b.e3());
        result.e1() = mac(result.e1(), a.e13oi(), b.e3oi());
        result.e1() = macSub(result.e1(), a.e23oi(), b.e123());
        result.e1() = macSub(result.e1(), a.e23oi(), b.e123oi());
        result.e1() = macSub(result.e1(), a.e123oi(), b.e23());
        result.e1() = macSub(result.e1(), a.e123oi(), b.e23oi());

        result.e2() = 0;
        result.e2() = mac(result.e2(), a.scalar(), b.e2());
        result.e2() = mac(result.e2(), a.e1(), b.e12());
        result.e2() = mac(result.e2(), a.e2(), b.scalar());
        result.e2() = mac(result.e2(), a.e12(), b.e1());
        result.e2() = macSub(result.e2(), a.e3(), b.e23());
        result.e2() = macSub(result.e2(), a.e13(), b.e123());
        result.e2() = macSub(result.e2(), a.e23(), b.e3());
        result.e2() = macSub(result.e2(), a.e123(), b.e13());
        result.e2() = mac(result.e2(), a.eo(), b.e2i());
        result.e2() = mac(result.e2(), a.e1o(), b.e12i());
        result.e2() = mac(result.e2(), a.e2o(), b.ei());
        result.e2() = mac(result.e2(), a.e12o(), b.e1i());
        result.e2() = macSub(result.e2(), a.e3o(), b.e23i());
        result.e2() = macSub(result.e2(), a.e13o(), b.e123i());
        result.e2() = macSub(result.e2(), a.e23o(), b.e3i());
        result.e2() = macSub(result.e2(), a.e123o(), b.e13i());
        result.e2() = mac(result.e2(), a.ei(), b.e2o());
        result.e2() = mac(result.e2(), a.e1i(), b.e12o());
        result.e2() = mac(result.e2(), a.e2i(), b.eo());
        result.e2() = mac(result.e2(), a.e12i(), b.e1o());
        result.e2() = macSub(result.e2(), a.e3i(), b.e23o());
        result.e2() = macSub(result.e2(), a.e13i(), b.e123o());
        result.e2() = macSub(result.e2(), a.e23i(), b.e3o());
        result.e2() = macSub(result.e2(), a.e123i(), b.e13o());
        result.e2() = macSub(result.e2(), a.eoi(), b.e2());
        result.e2() = macSub(result.e2(), a.eoi(), b.e2oi());
        result.e2() = macSub(result.e2(), a.e1oi(), b.e12());
        result.e2() = macSub(result.e2(), a.e1oi(), b.e12oi());
        result.e2() = macSub(result.e2(), a.e2oi(), b.scalar());
        result.e2() = macSub(result.e2(), a.e2oi(), b.eoi());
        result.e2() = macSub(result.e2(), a.e12oi(), b.e1());
        result.e2() = macSub(result.e2(), a.e12oi(), b.e1oi());
        result.e2() = mac(result.e2(), a.e3oi(), b.e23());
        result.e2() = mac(result.e2(), a.e3oi(), b.e23oi());
        result.e2() = mac(result.e2(), a.e13oi(), b.e123());
        result.e2() = mac(result.e2(), a.e13oi(), b.e123oi());
        result.e2() = mac(result.e2(), a.e23oi(), b.e3());
        result.e2() = mac(result.e2(), a.e23oi(), b.e3oi());
        result.e2() = mac(result.e2(), a.e123oi(), b.e13());
        result.e2() = mac(result.e2(), a.e123oi(), b.e13oi());

        result.e12() = 0;
        result.e12() = mac(result.e12(), a.scalar(), b.e12());
        result.e12() = mac(result.e12(), a.e1(), b.e2());
        result.e12() = macSub(result.e12(), a.e2(), b.e1());
        result.e12() = macSub(result.e12(), a.e12(), b.scalar());
        result.e12() = mac(result.e12(), a.e3(), b.e123());
        result.e12() = mac(result.e12(), a.e13(), b.e23());
        result.e12() = macSub(result.e12(), a.e23(), b.e13());
        result.e12() = macSub(result.e12(), a.e123(), b.e3());
        result.e12() = macSub(result.e12(), a.eo(), b.e12i());
        result.e12() = macSub(result.e12(), a.e1o(), b.e2i());
        result.e12() = mac(result.e12(), a.e2o(), b.e1i());
        result.e12() = mac(result.e12(), a.e12o(), b.ei());
        result.e12() = macSub(result.e12(), a.e3o(), b.e123i());
        result.e12() = macSub(result.e12(), a.e13o(), b.e23i());
        result.e12() = mac(result.e12(), a.e23o(), b.e13i());
        result.e12() = mac(result.e12(), a.e123o(), b.e3i());
        result.e12() = macSub(result.e12(), a.ei(), b.e12o());
        result.e12() = macSub(result.e12(), a.e1i(), b.e2o());
        result.e12() = mac(result.e12(), a.e2i(), b.e1o());
        result.e12() = mac(result.e12(), a.e12i(), b.eo());
        result.e12() = macSub(result.e12(), a.e3i(), b.e123o());
        result.e12() = macSub(result.e12(), a.e13i(), b.e23o());
        result.e12() = mac(result.e12(), a.e23i(), b.e13o());
        result.e12() = mac(result.e12(), a.e123i(), b.e3o());
        result.e12() = macSub(result.e12(), a.eoi(), b.e12());
        result.e12() = macSub(result.e12(), a.eoi(), b.e12oi());
        result.e12() = macSub(result.e12(), a.e1oi(), b.e2());
        result.e12() = macSub(result.e12(), a.e1oi(), b.e2oi());
        result.e12() = mac(result.e12(), a.e2oi(), b.e1());
        result.e12() = mac(result.e12(), a.e2oi(), b.e1oi());
        result.e12() = mac(result.e12(), a.e12oi(), b.scalar());
        result.e12() = mac(result.e12(), a.e12oi(), b.eoi());
        result.e12() = macSub(result.e12(), a.e3oi(), b.e123());
        result.e12() = macSub(result.e12(), a.e3oi(), b.e123oi());
        result.e12() = macSub(result.e12(), a.e13oi(), b.e23());
        result.e12() = macSub(result.e12(), a.e13oi(), b.e23oi());
        result.e12() = mac(result.e12(), a.e23oi(), b.e13());
        result.e12() = mac(result.e12(), a.e23oi(), b.e13oi());
        result.e12() = mac(result.e12(), a.e123oi(), b.e3());
        result.e12() = mac(result.e12(), a.e123oi(), b.e3oi());

        result.e3() = 0;
        result.e3() = mac(result.e3(), a.scalar(), b.e3());
        result.e3() = mac(result.e3(), a.e1(), b.e13());
        result.e3() = mac(result.e3(), a.e2(), b.e23());
        result.e3() = mac(result.e3(), a.e12(), b.e123());
        result.e3() = mac(result.e3(), a.e3(), b.scalar());
        result.e3() = mac(result.e3(), a.e13(), b.e1());
        result.e3() = mac(result.e3(), a.e23(), b.e2());
        result.e3() = mac(result.e3(), a.e123(), b.e12());
        result.e3() = mac(result.e3(), a.eo(), b.e3i());
        result.e3() = mac(result.e3(), a.e1o(), b.e13i());
        result.e3() = mac(result.e3(), a.e2o(), b.e23i());
        result.e3() = mac(result.e3(), a.e12o(), b.e123i());
        result.e3() = mac(result.e3(), a.e3o(), b.ei());
        result.e3() = mac(result.e3(), a.e13o(), b.e1i());
        result.e3() = mac(result.e3(), a.e23o(), b.e2i());
        result.e3() = mac(result.e3(), a.e123o(), b.e12i());
        result.e3() = mac(result.e3(), a.ei(), b.e3o());
        result.e3() = mac(result.e3(), a.e1i(), b.e13o());
        result.e3() = mac(result.e3(), a.e2i(), b.e23o());
        result.e3() = mac(result.e3(), a.e12i(), b.e123o());
        result.e3() = mac(result.e3(), a.e3i(), b.eo());
        result.e3() = mac(result.e3(), a.e13i(), b.e1o());
        result.e3() = mac(result.e3(), a.e23i(), b.e2o());
        result.e3() = mac(result.e3(), a.e123i(), b.e12o());
        result.e3() = macSub(result.e3(), a.eoi(), b.e3());
        result.e3() = macSub(result.e3(), a.eoi(), b.e3oi());
        result.e3() = macSub(result.e3(), a.e1oi(), b.e13());
        result.e3() = macSub(result.e3(), a.e1oi(), b.e13oi());
        result.e3() = macSub(result.e3(), a.e2oi(), b.e23());
        result.e3() = macSub(result.e3(), a.e2oi(), b.e23oi());
        result.e3() = macSub(result.e3(), a.e12oi(), b.e123());
        result.e3() = macSub(result.e3(), a.e12oi(), b.e123oi());
        result.e3() = macSub(result.e3(), a.e3oi(), b.scalar());
        result.e3() = macSub(result.e3(), a.e3oi(), b.eoi());
        result.e3() = macSub(result.e3(), a.e13oi(), b.e1());
        result.e3() = macSub(result.e3(), a.e13oi(), b.e1oi());
        result.e3() = macSub(result.e3(), a.e23oi(), b.e2());
        result.e3() = macSub(result.e3(), a.e23oi(), b.e2oi());
        result.e3() = macSub(result.e3(), a.e123oi(), b.e12());
        result.e3() = macSub(result.e3(), a.e123oi(), b.e12oi());

        result.e13() = 0;
        result.e13() = mac(result.e13(), a.scalar(), b.e13());
        result.e13() = mac(result.e13(), a.e1(), b.e3());
        result.e13() = macSub(result.e13(), a.e2(), b.e123());
        result.e13() = macSub(result.e13(), a.e12(), b.e23());
        result.e13() = macSub(result.e13(), a.e3(), b.e1());
        result.e13() = macSub(result.e13(), a.e13(), b.scalar());
        result.e13() = mac(result.e13(), a.e23(), b.e12());
        result.e13() = mac(result.e13(), a.e123(), b.e2());
        result.e13() = macSub(result.e13(), a.eo(), b.e13i());
        result.e13() = macSub(result.e13(), a.e1o(), b.e3i());
        result.e13() = mac(result.e13(), a.e2o(), b.e123i());
        result.e13() = mac(result.e13(), a.e12o(), b.e23i());
        result.e13() = mac(result.e13(), a.e3o(), b.e1i());
        result.e13() = mac(result.e13(), a.e13o(), b.ei());
        result.e13() = macSub(result.e13(), a.e23o(), b.e12i());
        result.e13() = macSub(result.e13(), a.e123o(), b.e2i());
        result.e13() = macSub(result.e13(), a.ei(), b.e13o());
        result.e13() = macSub(result.e13(), a.e1i(), b.e3o());
        result.e13() = mac(result.e13(), a.e2i(), b.e123o());
        result.e13() = mac(result.e13(), a.e12i(), b.e23o());
        result.e13() = mac(result.e13(), a.e3i(), b.e1o());
        result.e13() = mac(result.e13(), a.e13i(), b.eo());
        result.e13() = macSub(result.e13(), a.e23i(), b.e12o());
        result.e13() = macSub(result.e13(), a.e123i(), b.e2o());
        result.e13() = macSub(result.e13(), a.eoi(), b.e13());
        result.e13() = macSub(result.e13(), a.eoi(), b.e13oi());
        result.e13() = macSub(result.e13(), a.e1oi(), b.e3());
        result.e13() = macSub(result.e13(), a.e1oi(), b.e3oi());
        result.e13() = mac(result.e13(), a.e2oi(), b.e123());
        result.e13() = mac(result.e13(), a.e2oi(), b.e123oi());
        result.e13() = mac(result.e13(), a.e12oi(), b.e23());
        result.e13() = mac(result.e13(), a.e12oi(), b.e23oi());
        result.e13() = mac(result.e13(), a.e3oi(), b.e1());
        result.e13() = mac(result.e13(), a.e3oi(), b.e1oi());
        result.e13() = mac(result.e13(), a.e13oi(), b.scalar());
        result.e13() = mac(result.e13(), a.e13oi(), b.eoi());
        result.e13() = macSub(result.e13(), a.e23oi(), b.e12());
        result.e13() = macSub(result.e13(), a.e23oi(), b.e12oi());
        result.e13() = macSub(result.e13(), a.e123oi(), b.e2());
        result.e13() = macSub(result.e13(), a.e123oi(), b.e2oi());

        result.e23() = 0;
        result.e23() = mac(result.e23(), a.scalar(), b.e23());
        result.e23() = mac(result.e23(), a.e1(), b.e123());
        result.e23() = mac(result.e23(), a.e2(), b.e3());
        result.e23() = mac(result.e23(), a.e12(), b.e13());
        result.e23() = macSub(result.e23(), a.e3(), b.e2());
        result.e23() = macSub(result.e23(), a.e13(), b.e12());
        result.e23() = macSub(result.e23(), a.e23(), b.scalar());
        result.e23() = macSub(result.e23(), a.e123(), b.e1());
        result.e23() = macSub(result.e23(), a.eo(), b.e23i());
        result.e23() = macSub(result.e23(), a.e1o(), b.e123i());
        result.e23() = macSub(result.e23(), a.e2o(), b.e3i());
        result.e23() = macSub(result.e23(), a.e12o(), b.e13i());
        result.e23() = mac(result.e23(), a.e3o(), b.e2i());
        result.e23() = mac(result.e23(), a.e13o(), b.e12i());
        result.e23() = mac(result.e23(), a.e23o(), b.ei());
        result.e23() = mac(result.e23(), a.e123o(), b.e1i());
        result.e23() = macSub(result.e23(), a.ei(), b.e23o());
        result.e23() = macSub(result.e23(), a.e1i(), b.e123o());
        result.e23() = macSub(result.e23(), a.e2i(), b.e3o());
        result.e23() = macSub(result.e23(), a.e12i(), b.e13o());
        result.e23() = mac(result.e23(), a.e3i(), b.e2o());
        result.e23() = mac(result.e23(), a.e13i(), b.e12o());
        result.e23() = mac(result.e23(), a.e23i(), b.eo());
        result.e23() = mac(result.e23(), a.e123i(), b.e1o());
        result.e23() = macSub(result.e23(), a.eoi(), b.e23());
        result.e23() = macSub(result.e23(), a.eoi(), b.e23oi());
        result.e23() = macSub(result.e23(), a.e1oi(), b.e123());
        result.e23() = macSub(result.e23(), a.e1oi(), b.e123oi());
        result.e23() = macSub(result.e23(), a.e2oi(), b.e3());
        result.e23() = macSub(result.e23(), a.e2oi(), b.e3oi());
        result.e23() = macSub(result.e23(), a.e12oi(), b.e13());
        result.e23() = macSub(result.e23(), a.e12oi(), b.e13oi());
        result.e23() = mac(result.e23(), a.e3oi(), b.e2());
        result.e23() = mac(result.e23(), a.e3oi(), b.e2oi());
        result.e23() = mac(result.e23(), a.e13oi(), b.e12());
        result.e23() = mac(result.e23(), a.e13oi(), b.e12oi());
        result.e23() = mac(result.e23(), a.e23oi(), b.scalar());
        result.e23() = mac(result.e23(), a.e23oi(), b.eoi());
        result.e23() = mac(result.e23(), a.e123oi(), b.e1());
        result.e23() = mac(result.e23(), a.e123oi(), b.e1oi());

        result.e123() = 0;
        result.e123() = mac(result.e123(), a.scalar(), b.e123());
        result.e123() = mac(result.e123(), a.e1(), b.e23());
        result.e123() = macSub(result.e123(), a.e2(), b.e13());
        result.e123() = macSub(result.e123(), a.e12(), b.e3());
        result.e123() = mac(result.e123(), a.e3(), b.e12());
        result.e123() = mac(result.e123(), a.e13(), b.e2());
        result.e123() = macSub(result.e123(), a.e23(), b.e1());
        result.e123() = macSub(result.e123(), a.e123(), b.scalar());
        result.e123() = mac(result.e123(), a.eo(), b.e123i());
        result.e123() = mac(result.e123(), a.e1o(), b.e23i());
        result.e123() = macSub(result.e123(), a.e2o(), b.e13i());
        result.e123() = macSub(result.e123(), a.e12o(), b.e3i());
        result.e123() = mac(result.e123(), a.e3o(), b.e12i());
        result.e123() = mac(result.e123(), a.e13o(), b.e2i());
        result.e123() = macSub(result.e123(), a.e23o(), b.e1i());
        result.e123() = macSub(result.e123(), a.e123o(), b.ei());
        result.e123() = mac(result.e123(), a.ei(), b.e123o());
        result.e123() = mac(result.e123(), a.e1i(), b.e23o());
        result.e123() = macSub(result.e123(), a.e2i(), b.e13o());
        result.e123() = macSub(result.e123(), a.e12i(), b.e3o());
        result.e123() = mac(result.e123(), a.e3i(), b.e12o());
        result.e123() = mac(result.e123(), a.e13i(), b.e2o());
        result.e123() = macSub(result.e123(), a.e23i(), b.e1o());
        result.e123() = macSub(result.e123(), a.e123i(), b.eo());
        result.e123() = macSub(result.e123(), a.eoi(), b.e123());
        result.e123() = macSub(result.e123(), a.eoi(), b.e123oi());
        result.e123() = macSub(result.e123(), a.e1oi(), b.e23());
        result.e123() = macSub(result.e123(), a.e1oi(), b.e23oi());
        result.e123() = mac(result.e123(), a.e2oi(), b.e13());
        result.e123() = mac(result.e123(), a.e2oi(), b.e13oi());
        result.e123() = mac(result.e123(), a.e12oi(), b.e3());
        result.e123() = mac(result.e123(), a.e12oi(), b.e3oi());
        result.e123() = macSub(result.e123(), a.e3oi(), b.e12());
        result.e123() = macSub(result.e123(), a.e3oi(), b.e12oi());
        result.e123() = macSub(result.e123(), a.e13oi(), b.e2());
        result.e123() = macSub(result.e123(), a.e13oi(), b.e2oi());
        result.e123() = mac(result.e123(), a.e23oi(), b.e1());
        result.e123() = mac(result.e123(), a.e23oi(), b.e1oi());
        result.e123() = mac(result.e123(), a.e123oi(), b.scalar());
        result.e123() = mac(result.e123(), a.e123oi(), b.eoi());

        result.eo() = 0;
        result.eo() = mac(result.eo(), a.scalar(), b.eo());
        result.eo() = mac(result.eo(), a.e1(), b.e1o());
        result.eo() = mac(result.eo(), a.e2(), b.e2o());
        result.eo() = mac(result.eo(), a.e12(), b.e12o());
        result.eo() = mac(result.eo(), a.e3(), b.e3o());
        result.eo() = mac(result.eo(), a.e13(), b.e13o());
        result.eo() = mac(result.eo(), a.e23(), b.e23o());
        result.eo() = mac(result.eo(), a.e123(), b.e123o());
        result.eo() = mac(result.eo(), a.eo(), b.scalar());
        result.eo() = mac(result.eo(), a.eo(), b.eoi());
        result.eo() = mac(result.eo(), a.e1o(), b.e1());
        result.eo() = mac(result.eo(), a.e1o(), b.e1oi());
        result.eo() = mac(result.eo(), a.e2o(), b.e2());
        result.eo() = mac(result.eo(), a.e2o(), b.e2oi());
        result.eo() = mac(result.eo(), a.e12o(), b.e12());
        result.eo() = mac(result.eo(), a.e12o(), b.e12oi());
        result.eo() = mac(result.eo(), a.e3o(), b.e3());
        result.eo() = mac(result.eo(), a.e3o(), b.e3oi());
        result.eo() = mac(result.eo(), a.e13o(), b.e13());
        result.eo() = mac(result.eo(), a.e13o(), b.e13oi());
        result.eo() = mac(result.eo(), a.e23o(), b.e23());
        result.eo() = mac(result.eo(), a.e23o(), b.e23oi());
        result.eo() = mac(result.eo(), a.e123o(), b.e123());
        result.eo() = mac(result.eo(), a.e123o(), b.e123oi());

        result.e1o() = 0;
        result.e1o() = mac(result.e1o(), a.scalar(), b.e1o());
        result.e1o() = mac(result.e1o(), a.e1(), b.eo());
        result.e1o() = macSub(result.e1o(), a.e2(), b.e12o());
        result.e1o() = macSub(result.e1o(), a.e12(), b.e2o());
        result.e1o() = macSub(result.e1o(), a.e3(), b.e13o());
        result.e1o() = macSub(result.e1o(), a.e13(), b.e3o());
        result.e1o() = mac(result.e1o(), a.e23(), b.e123o());
        result.e1o() = mac(result.e1o(), a.e123(), b.e23o());
        result.e1o() = macSub(result.e1o(), a.eo(), b.e1());
        result.e1o() = macSub(result.e1o(), a.eo(), b.e1oi());
        result.e1o() = macSub(result.e1o(), a.e1o(), b.scalar());
        result.e1o() = macSub(result.e1o(), a.e1o(), b.eoi());
        result.e1o() = mac(result.e1o(), a.e2o(), b.e12());
        result.e1o() = mac(result.e1o(), a.e2o(), b.e12oi());
        result.e1o() = mac(result.e1o(), a.e12o(), b.e2());
        result.e1o() = mac(result.e1o(), a.e12o(), b.e2oi());
        result.e1o() = mac(result.e1o(), a.e3o(), b.e13());
        result.e1o() = mac(result.e1o(), a.e3o(), b.e13oi());
        result.e1o() = mac(result.e1o(), a.e13o(), b.e3());
        result.e1o() = mac(result.e1o(), a.e13o(), b.e3oi());
        result.e1o() = macSub(result.e1o(), a.e23o(), b.e123());
        result.e1o() = macSub(result.e1o(), a.e23o(), b.e123oi());
        result.e1o() = macSub(result.e1o(), a.e123o(), b.e23());
        result.e1o() = macSub(result.e1o(), a.e123o(), b.e23oi());

        result.e2o() = 0;
        result.e2o() = mac(result.e2o(), a.scalar(), b.e2o());
        result.e2o() = mac(result.e2o(), a.e1(), b.e12o());
        result.e2o() = mac(result.e2o(), a.e2(), b.eo());
        result.e2o() = mac(result.e2o(), a.e12(), b.e1o());
        result.e2o() = macSub(result.e2o(), a.e3(), b.e23o());
        result.e2o() = macSub(result.e2o(), a.e13(), b.e123o());
        result.e2o() = macSub(result.e2o(), a.e23(), b.e3o());
        result.e2o() = macSub(result.e2o(), a.e123(), b.e13o());
        result.e2o() = macSub(result.e2o(), a.eo(), b.e2());
        result.e2o() = macSub(result.e2o(), a.eo(), b.e2oi());
        result.e2o() = macSub(result.e2o(), a.e1o(), b.e12());
        result.e2o() = macSub(result.e2o(), a.e1o(), b.e12oi());
        result.e2o() = macSub(result.e2o(), a.e2o(), b.scalar());
        result.e2o() = macSub(result.e2o(), a.e2o(), b.eoi());
        result.e2o() = macSub(result.e2o(), a.e12o(), b.e1());
        result.e2o() = macSub(result.e2o(), a.e12o(), b.e1oi());
        result.e2o() = mac(result.e2o(), a.e3o(), b.e23());
        result.e2o() = mac(result.e2o(), a.e3o(), b.e23oi());
        result.e2o() = mac(result.e2o(), a.e13o(), b.e123());
        result.e2o() = mac(result.e2o(), a.e13o(), b.e123oi());
        result.e2o() = mac(result.e2o(), a.e23o(), b.e3());
        result.e2o() = mac(result.e2o(), a.e23o(), b.e3oi());
        result.e2o() = mac(result.e2o(), a.e123o(), b.e13());
        result.e2o() = mac(result.e2o(), a.e123o(), b.e13oi());

        result.e12o() = 0;
        result.e12o() = mac(result.e12o(), a.scalar(), b.e12o());
        result.e12o() = mac(result.e12o(), a.e1(), b.e2o());
        result.e12o() = macSub(result.e12o(), a.e2(), b.e1o());
        result.e12o() = macSub(result.e12o(), a.e12(), b.eo());
        result.e12o() = mac(result.e12o(), a.e3(), b.e123o());
        result.e12o() = mac(result.e12o(), a.e13(), b.e23o());
        result.e12o() = macSub(result.e12o(), a.e23(), b.e13o());
        result.e12o() = macSub(result.e12o(), a.e123(), b.e3o());
        result.e12o() = mac(result.e12o(), a.eo(), b.e12());
        result.e12o() = mac(result.e12o(), a.eo(), b.e12oi());
        result.e12o() = mac(result.e12o(), a.e1o(), b.e2());
        result.e12o() = mac(result.e12o(), a.e1o(), b.e2oi());
        result.e12o() = macSub(result.e12o(), a.e2o(), b.e1());
        result.e12o() = macSub(result.e12o(), a.e2o(), b.e1oi());
        result.e12o() = macSub(result.e12o(), a.e12o(), b.scalar());
        result.e12o() = macSub(result.e12o(), a.e12o(), b.eoi());
        result.e12o() = mac(result.e12o(), a.e3o(), b.e123());
        result.e12o() = mac(result.e12o(), a.e3o(), b.e123oi());
        result.e12o() = mac(result.e12o(), a.e13o(), b.e23());
        result.e12o() = mac(result.e12o(), a.e13o(), b.e23oi());
        result.e12o() = macSub(result.e12o(), a.e23o(), b.e13());
        result.e12o() = macSub(result.e12o(), a.e23o(), b.e13oi());
        result.e12o() = macSub(result.e12o(), a.e123o(), b.e3());
        result.e12o() = macSub(result.e12o(), a.e123o(), b.e3oi());

        result.e3o() = 0;
        result.e3o() = mac(result.e3o(), a.scalar(), b.e3o());
        result.e3o() = mac(result.e3o(), a.e1(), b.e13o());
        result.e3o() = mac(result.e3o(), a.e2(), b.e23o());
        result.e3o() = mac(result.e3o(), a.e12(), b.e123o());
        result.e3o() = mac(result.e3o(), a.e3(), b.eo());
        result.e3o() = mac(result.e3o(), a.e13(), b.e1o());
        result.e3o() = mac(result.e3o(), a.e23(), b.e2o());
        result.e3o() = mac(result.e3o(), a.e123(), b.e12o());
        result.e3o() = macSub(result.e3o(), a.eo(), b.e3());
        result.e3o() = macSub(result.e3o(), a.eo(), b.e3oi());
        result.e3o() = macSub(result.e3o(), a.e1o(), b.e13());
        result.e3o() = macSub(result.e3o(), a.e1o(), b.e13oi());
        result.e3o() = macSub(result.e3o(), a.e2o(), b.e23());
        result.e3o() = macSub(result.e3o(), a.e2o(), b.e23oi());
        result.e3o() = macSub(result.e3o(), a.e12o(), b.e123());
        result.e3o() = macSub(result.e3o(), a.e12o(), b.e123oi());
        result.e3o() = macSub(result.e3o(), a.e3o(), b.scalar());
        result.e3o() = macSub(result.e3o(), a.e3o(), b.eoi());
        result.e3o() = macSub(result.e3o(), a.e13o(), b.e1());
        result.e3o() = macSub(result.e3o(), a.e13o(), b.e1oi());
        result.e3o() = macSub(result.e3o(), a.e23o(), b.e2());
        result.e3o() = macSub(result.e3o(), a.e23o(), b.e2oi());
        result.e3o() = macSub(result.e3o(), a.e123o(), b.e12());
        result.e3o() = macSub(result.e3o(), a.e123o(), b.e12oi());

        result.e13o() = 0;
        result.e13o() = mac(result.e13o(), a.scalar(), b.e13o());
        result.e13o() = mac(result.e13o(), a.e1(), b.e3o());
        result.e13o() = macSub(result.e13o(), a.e2(), b.e123o());
        result.e13o() = macSub(result.e13o(), a.e12(), b.e23o());
        result.e13o() = macSub(result.e13o(), a.e3(), b.e1o());
        result.e13o() = macSub(result.e13o(), a.e13(), b.eo());
        result.e13o() = mac(result.e13o(), a.e23(), b.e12o());
        result.e13o() = mac(result.e13o(), a.e123(), b.e2o());
        result.e13o() = mac(result.e13o(), a.eo(), b.e13());
        result.e13o() = mac(result.e13o(), a.eo(), b.e13oi());
        result.e13o() = mac(result.e13o(), a.e1o(), b.e3());
        result.e13o() = mac(result.e13o(), a.e1o(), b.e3oi());
        result.e13o() = macSub(result.e13o(), a.e2o(), b.e123());
        result.e13o() = macSub(result.e13o(), a.e2o(), b.e123oi());
        result.e13o() = macSub(result.e13o(), a.e12o(), b.e23());
        result.e13o() = macSub(result.e13o(), a.e12o(), b.e23oi());
        result.e13o() = macSub(result.e13o(), a.e3o(), b.e1());
        result.e13o() = macSub(result.e13o(), a.e3o(), b.e1oi());
        result.e13o() = macSub(result.e13o(), a.e13o(), b.scalar());
        result.e13o() = macSub(result.e13o(), a.e13o(), b.eoi());
        result.e13o() = mac(result.e13o(), a.e23o(), b.e12());
        result.e13o() = mac(result.e13o(), a.e23o(), b.e12oi());
        result.e13o() = mac(result.e13o(), a.e123o(), b.e2());
        result.e13o() = mac(result.e13o(), a.e123o(), b.e2oi());

        result.e23o() = 0;
        result.e23o() = mac(result.e23o(), a.scalar(), b.e23o());
        result.e23o() = mac(result.e23o(), a.e1(), b.e123o());
        result.e23o() = mac(result.e23o(), a.e2(), b.e3o());
        result.e23o() = mac(result.e23o(), a.e12(), b.e13o());
        result.e23o() = macSub(result.e23o(), a.e3(), b.e2o());
        result.e23o() = macSub(result.e23o(), a.e13(), b.e12o());
        result.e23o() = macSub(result.e23o(), a.e23(), b.eo());
        result.e23o() = macSub(result.e23o(), a.e123(), b.e1o());
        result.e23o() = mac(result.e23o(), a.eo(), b.e23());
        result.e23o() = mac(result.e23o(), a.eo(), b.e23oi());
        result.e23o() = mac(result.e23o(), a.e1o(), b.e123());
        result.e23o() = mac(result.e23o(), a.e1o(), b.e123oi());
        result.e23o() = mac(result.e23o(), a.e2o(), b.e3());
        result.e23o() = mac(result.e23o(), a.e2o(), b.e3oi());
        result.e23o() = mac(result.e23o(), a.e12o(), b.e13());
        result.e23o() = mac(result.e23o(), a.e12o(), b.e13oi());
        result.e23o() = macSub(result.e23o(), a.e3o(), b.e2());
        result.e23o() = macSub(result.e23o(), a.e3o(), b.e2oi());
        result.e23o() = macSub(result.e23o(), a.e13o(), b.e12());
        result.e23o() = macSub(result.e23o(), a.e13o(), b.e12oi());
        result.e23o() = macSub(result.e23o(), a.e23o(), b.scalar());
        result.e23o() = macSub(result.e23o(), a.e23o(), b.eoi());
        result.e23o() = macSub(result.e23o(), a.e123o(), b.e1());
        result.e23o() = macSub(result.e23o(), a.e123o(), b.e1oi());

        result.e123o() = 0;
        result.e123o() = mac(result.e123o(), a.scalar(), b.e123o());
        result.e123o() = mac(result.e123o(), a.e1(), b.e23o());
        result.e123o() = macSub(result.e123o(), a.e2(), b.e13o());
        result.e123o() = macSub(result.e123o(), a.e12(), b.e3o());
        result.e123o() = mac(result.e123o(), a.e3(), b.e12o());
        result.e123o() = mac(result.e123o(), a.e13(), b.e2o());
        result.e123o() = macSub(result.e123o(), a.e23(), b.e1o());
        result.e123o() = macSub(result.e123o(), a.e123(), b.eo());
        result.e123o() = macSub(result.e123o(), a.eo(), b.e123());
        result.e123o() = macSub(result.e123o(), a.eo(), b.e123oi());
        result.e123o() = macSub(result.e123o(), a.e1o(), b.e23());
        result.e123o() = macSub(result.e123o(), a.e1o(), b.e23oi());
        result.e123o() = mac(result.e123o(), a.e2o(), b.e13());
        result.e123o() = mac(result.e123o(), a.e2o(), b.e13oi());
        result.e123o() = mac(result.e123o(), a.e12o(), b.e3());
        result.e123o() = mac(result.e123o(), a.e12o(), b.e3oi());
        result.e123o() = macSub(result.e123o(), a.e3o(), b.e12());
        result.e123o() = macSub(result.e123o(), a.e3o(), b.e12oi());
        result.e123o() = macSub(result.e123o(), a.e13o(), b.e2());
        result.e123o() = macSub(result.e123o(), a.e13o(), b.e2oi());
        result.e123o() = mac(result.e123o(), a.e23o(), b.e1());
        result.e123o() = mac(result.e123o(), a.e23o(), b.e1oi());
        result.e123o() = mac(result.e123o(), a.e123o(), b.scalar());
        result.e123o() = mac(result.e123o(), a.e123o(), b.eoi());

        result.ei() = 0;
        result.ei() = mac(result.ei(), a.scalar(), b.ei());
        result.ei() = mac(result.ei(), a.e1(), b.e1i());
        result.ei() = mac(result.ei(), a.e2(), b.e2i());
        result.ei() = mac(result.ei(), a.e12(), b.e12i());
        result.ei() = mac(result.ei(), a.e3(), b.e3i());
        result.ei() = mac(result.ei(), a.e13(), b.e13i());
        result.ei() = mac(result.ei(), a.e23(), b.e23i());
        result.ei() = mac(result.ei(), a.e123(), b.e123i());
        result.ei() = mac(result.ei(), a.ei(), b.scalar());
        result.ei() = macSub(result.ei(), a.ei(), b.eoi());
        result.ei() = mac(result.ei(), a.e1i(), b.e1());
        result.ei() = macSub(result.ei(), a.e1i(), b.e1oi());
        result.ei() = mac(result.ei(), a.e2i(), b.e2());
        result.ei() = macSub(result.ei(), a.e2i(), b.e2oi());
        result.ei() = mac(result.ei(), a.e12i(), b.e12());
        result.ei() = macSub(result.ei(), a.e12i(), b.e12oi());
        result.ei() = mac(result.ei(), a.e3i(), b.e3());
        result.ei() = macSub(result.ei(), a.e3i(), b.e3oi());
        result.ei() = mac(result.ei(), a.e13i(), b.e13());
        result.ei() = macSub(result.ei(), a.e13i(), b.e13oi());
        result.ei() = mac(result.ei(), a.e23i(), b.e23());
        result.ei() = macSub(result.ei(), a.e23i(), b.e23oi());
        result.ei() = mac(result.ei(), a.e123i(), b.e123());
        result.ei() = macSub(result.ei(), a.e123i(), b.e123oi());
        result.ei() = macSub(result.ei(), a.eoi(), b.ei());
        result.ei() = macSub(result.ei(), a.eoi(), b.ei());
        result.ei() = macSub(result.ei(), a.e1oi(), b.e1i());
        result.ei() = macSub(result.ei(), a.e1oi(), b.e1i());
        result.ei() = macSub(result.ei(), a.e2oi(), b.e2i());
        result.ei() = macSub(result.ei(), a.e2oi(), b.e2i());
        result.ei() = macSub(result.ei(), a.e12oi(), b.e12i());
        result.ei() = macSub(result.ei(), a.e12oi(), b.e12i());
        result.ei() = macSub(result.ei(), a.e3oi(), b.e3i());
        result.ei() = macSub(result.ei(), a.e3oi(), b.e3i());
        result.ei() = macSub(result.ei(), a.e13oi(), b.e13i());
        result.ei() = macSub(result.ei(), a.e13oi(), b.e13i());
        result.ei() = macSub(result.ei(), a.e23oi(), b.e23i());
        result.ei() = macSub(result.ei(), a.e23oi(), b.e23i());
        result.ei() = macSub(result.ei(), a.e123oi(), b.e123i());
        result.ei() = macSub(result.ei(), a.e123oi(), b.e123i());

        result.e1i() = 0;
        result.e1i() = mac(result.e1i(), a.scalar(), b.e1i());
        result.e1i() = mac(result.e1i(), a.e1(), b.ei());
        result.e1i() = macSub(result.e1i(), a.e2(), b.e12i());
        result.e1i() = macSub(result.e1i(), a.e12(), b.e2i());
        result.e1i() = macSub(result.e1i(), a.e3(), b.e13i());
        result.e1i() = macSub(result.e1i(), a.e13(), b.e3i());
        result.e1i() = mac(result.e1i(), a.e23(), b.e123i());
        result.e1i() = mac(result.e1i(), a.e123(), b.e23i());
        result.e1i() = macSub(result.e1i(), a.ei(), b.e1());
        result.e1i() = mac(result.e1i(), a.ei(), b.e1oi());
        result.e1i() = macSub(result.e1i(), a.e1i(), b.scalar());
        result.e1i() = mac(result.e1i(), a.e1i(), b.eoi());
        result.e1i() = mac(result.e1i(), a.e2i(), b.e12());
        result.e1i() = macSub(result.e1i(), a.e2i(), b.e12oi());
        result.e1i() = mac(result.e1i(), a.e12i(), b.e2());
        result.e1i() = macSub(result.e1i(), a.e12i(), b.e2oi());
        result.e1i() = mac(result.e1i(), a.e3i(), b.e13());
        result.e1i() = macSub(result.e1i(), a.e3i(), b.e13oi());
        result.e1i() = mac(result.e1i(), a.e13i(), b.e3());
        result.e1i() = macSub(result.e1i(), a.e13i(), b.e3oi());
        result.e1i() = macSub(result.e1i(), a.e23i(), b.e123());
        result.e1i() = mac(result.e1i(), a.e23i(), b.e123oi());
        result.e1i() = macSub(result.e1i(), a.e123i(), b.e23());
        result.e1i() = mac(result.e1i(), a.e123i(), b.e23oi());
        result.e1i() = macSub(result.e1i(), a.eoi(), b.e1i());
        result.e1i() = macSub(result.e1i(), a.eoi(), b.e1i());
        result.e1i() = macSub(result.e1i(), a.e1oi(), b.ei());
        result.e1i() = macSub(result.e1i(), a.e1oi(), b.ei());
        result.e1i() = mac(result.e1i(), a.e2oi(), b.e12i());
        result.e1i() = mac(result.e1i(), a.e2oi(), b.e12i());
        result.e1i() = mac(result.e1i(), a.e12oi(), b.e2i());
        result.e1i() = mac(result.e1i(), a.e12oi(), b.e2i());
        result.e1i() = mac(result.e1i(), a.e3oi(), b.e13i());
        result.e1i() = mac(result.e1i(), a.e3oi(), b.e13i());
        result.e1i() = mac(result.e1i(), a.e13oi(), b.e3i());
        result.e1i() = mac(result.e1i(), a.e13oi(), b.e3i());
        result.e1i() = macSub(result.e1i(), a.e23oi(), b.e123i());
        result.e1i() = macSub(result.e1i(), a.e23oi(), b.e123i());
        result.e1i() = macSub(result.e1i(), a.e123oi(), b.e23i());
        result.e1i() = macSub(result.e1i(), a.e123oi(), b.e23i());

        result.e2i() = 0;
        result.e2i() = mac(result.e2i(), a.scalar(), b.e2i());
        result.e2i() = mac(result.e2i(), a.e1(), b.e12i());
        result.e2i() = mac(result.e2i(), a.e2(), b.ei());
        result.e2i() = mac(result.e2i(), a.e12(), b.e1i());
        result.e2i() = macSub(result.e2i(), a.e3(), b.e23i());
        result.e2i() = macSub(result.e2i(), a.e13(), b.e123i());
        result.e2i() = macSub(result.e2i(), a.e23(), b.e3i());
        result.e2i() = macSub(result.e2i(), a.e123(), b.e13i());
        result.e2i() = macSub(result.e2i(), a.ei(), b.e2());
        result.e2i() = mac(result.e2i(), a.ei(), b.e2oi());
        result.e2i() = macSub(result.e2i(), a.e1i(), b.e12());
        result.e2i() = mac(result.e2i(), a.e1i(), b.e12oi());
        result.e2i() = macSub(result.e2i(), a.e2i(), b.scalar());
        result.e2i() = mac(result.e2i(), a.e2i(), b.eoi());
        result.e2i() = macSub(result.e2i(), a.e12i(), b.e1());
        result.e2i() = mac(result.e2i(), a.e12i(), b.e1oi());
        result.e2i() = mac(result.e2i(), a.e3i(), b.e23());
        result.e2i() = macSub(result.e2i(), a.e3i(), b.e23oi());
        result.e2i() = mac(result.e2i(), a.e13i(), b.e123());
        result.e2i() = macSub(result.e2i(), a.e13i(), b.e123oi());
        result.e2i() = mac(result.e2i(), a.e23i(), b.e3());
        result.e2i() = macSub(result.e2i(), a.e23i(), b.e3oi());
        result.e2i() = mac(result.e2i(), a.e123i(), b.e13());
        result.e2i() = macSub(result.e2i(), a.e123i(), b.e13oi());
        result.e2i() = macSub(result.e2i(), a.eoi(), b.e2i());
        result.e2i() = macSub(result.e2i(), a.eoi(), b.e2i());
        result.e2i() = macSub(result.e2i(), a.e1oi(), b.e12i());
        result.e2i() = macSub(result.e2i(), a.e1oi(), b.e12i());
        result.e2i() = macSub(result.e2i(), a.e2oi(), b.ei());
        result.e2i() = macSub(result.e2i(), a.e2oi(), b.ei());
        result.e2i() = macSub(result.e2i(), a.e12oi(), b.e1i());
        result.e2i() = macSub(result.e2i(), a.e12oi(), b.e1i());
        result.e2i() = mac(result.e2i(), a.e3oi(), b.e23i());
        result.e2i() = mac(result.e2i(), a.e3oi(), b.e23i());
        result.e2i() = mac(result.e2i(), a.e13oi(), b.e123i());
        result.e2i() = mac(result.e2i(), a.e13oi(), b.e123i());
        result.e2i() = mac(result.e2i(), a.e23oi(), b.e3i());
        result.e2i() = mac(result.e2i(), a.e23oi(), b.e3i());
        result.e2i() = mac(result.e2i(), a.e123oi(), b.e13i());
        result.e2i() = mac(result.e2i(), a.e123oi(), b.e13i());

        result.e12i() = 0;
        result.e12i() = mac(result.e12i(), a.scalar(), b.e12i());
        result.e12i() = mac(result.e12i(), a.e1(), b.e2i());
        result.e12i() = macSub(result.e12i(), a.e2(), b.e1i());
        result.e12i() = macSub(result.e12i(), a.e12(), b.ei());
        result.e12i() = mac(result.e12i(), a.e3(), b.e123i());
        result.e12i() = mac(result.e12i(), a.e13(), b.e23i());
        result.e12i() = macSub(result.e12i(), a.e23(), b.e13i());
        result.e12i() = macSub(result.e12i(), a.e123(), b.e3i());
        result.e12i() = mac(result.e12i(), a.ei(), b.e12());
        result.e12i() = macSub(result.e12i(), a.ei(), b.e12oi());
        result.e12i() = mac(result.e12i(), a.e1i(), b.e2());
        result.e12i() = macSub(result.e12i(), a.e1i(), b.e2oi());
        result.e12i() = macSub(result.e12i(), a.e2i(), b.e1());
        result.e12i() = mac(result.e12i(), a.e2i(), b.e1oi());
        result.e12i() = macSub(result.e12i(), a.e12i(), b.scalar());
        result.e12i() = mac(result.e12i(), a.e12i(), b.eoi());
        result.e12i() = mac(result.e12i(), a.e3i(), b.e123());
        result.e12i() = macSub(result.e12i(), a.e3i(), b.e123oi());
        result.e12i() = mac(result.e12i(), a.e13i(), b.e23());
        result.e12i() = macSub(result.e12i(), a.e13i(), b.e23oi());
        result.e12i() = macSub(result.e12i(), a.e23i(), b.e13());
        result.e12i() = mac(result.e12i(), a.e23i(), b.e13oi());
        result.e12i() = macSub(result.e12i(), a.e123i(), b.e3());
        result.e12i() = mac(result.e12i(), a.e123i(), b.e3oi());
        result.e12i() = macSub(result.e12i(), a.eoi(), b.e12i());
        result.e12i() = macSub(result.e12i(), a.eoi(), b.e12i());
        result.e12i() = macSub(result.e12i(), a.e1oi(), b.e2i());
        result.e12i() = macSub(result.e12i(), a.e1oi(), b.e2i());
        result.e12i() = mac(result.e12i(), a.e2oi(), b.e1i());
        result.e12i() = mac(result.e12i(), a.e2oi(), b.e1i());
        result.e12i() = mac(result.e12i(), a.e12oi(), b.ei());
        result.e12i() = mac(result.e12i(), a.e12oi(), b.ei());
        result.e12i() = macSub(result.e12i(), a.e3oi(), b.e123i());
        result.e12i() = macSub(result.e12i(), a.e3oi(), b.e123i());
        result.e12i() = macSub(result.e12i(), a.e13oi(), b.e23i());
        result.e12i() = macSub(result.e12i(), a.e13oi(), b.e23i());
        result.e12i() = mac(result.e12i(), a.e23oi(), b.e13i());
        result.e12i() = mac(result.e12i(), a.e23oi(), b.e13i());
        result.e12i() = mac(result.e12i(), a.e123oi(), b.e3i());
        result.e12i() = mac(result.e12i(), a.e123oi(), b.e3i());

        result.e3i() = 0;
        result.e3i() = mac(result.e3i(), a.scalar(), b.e3i());
        result.e3i() = mac(result.e3i(), a.e1(), b.e13i());
        result.e3i() = mac(result.e3i(), a.e2(), b.e23i());
        result.e3i() = mac(result.e3i(), a.e12(), b.e123i());
        result.e3i() = mac(result.e3i(), a.e3(), b.ei());
        result.e3i() = mac(result.e3i(), a.e13(), b.e1i());
        result.e3i() = mac(result.e3i(), a.e23(), b.e2i());
        result.e3i() = mac(result.e3i(), a.e123(), b.e12i());
        result.e3i() = macSub(result.e3i(), a.ei(), b.e3());
        result.e3i() = mac(result.e3i(), a.ei(), b.e3oi());
        result.e3i() = macSub(result.e3i(), a.e1i(), b.e13());
        result.e3i() = mac(result.e3i(), a.e1i(), b.e13oi());
        result.e3i() = macSub(result.e3i(), a.e2i(), b.e23());
        result.e3i() = mac(result.e3i(), a.e2i(), b.e23oi());
        result.e3i() = macSub(result.e3i(), a.e12i(), b.e123());
        result.e3i() = mac(result.e3i(), a.e12i(), b.e123oi());
        result.e3i() = macSub(result.e3i(), a.e3i(), b.scalar());
        result.e3i() = mac(result.e3i(), a.e3i(), b.eoi());
        result.e3i() = macSub(result.e3i(), a.e13i(), b.e1());
        result.e3i() = mac(result.e3i(), a.e13i(), b.e1oi());
        result.e3i() = macSub(result.e3i(), a.e23i(), b.e2());
        result.e3i() = mac(result.e3i(), a.e23i(), b.e2oi());
        result.e3i() = macSub(result.e3i(), a.e123i(), b.e12());
        result.e3i() = mac(result.e3i(), a.e123i(), b.e12oi());
        result.e3i() = macSub(result.e3i(), a.eoi(), b.e3i());
        result.e3i() = macSub(result.e3i(), a.eoi(), b.e3i());
        result.e3i() = macSub(result.e3i(), a.e1oi(), b.e13i());
        result.e3i() = macSub(result.e3i(), a.e1oi(), b.e13i());
        result.e3i() = macSub(result.e3i(), a.e2oi(), b.e23i());
        result.e3i() = macSub(result.e3i(), a.e2oi(), b.e23i());
        result.e3i() = macSub(result.e3i(), a.e12oi(), b.e123i());
        result.e3i() = macSub(result.e3i(), a.e12oi(), b.e123i());
        result.e3i() = macSub(result.e3i(), a.e3oi(), b.ei());
        result.e3i() = macSub(result.e3i(), a.e3oi(), b.ei());
        result.e3i() = macSub(result.e3i(), a.e13oi(), b.e1i());
        result.e3i() = macSub(result.e3i(), a.e13oi(), b.e1i());
        result.e3i() = macSub(result.e3i(), a.e23oi(), b.e2i());
        result.e3i() = macSub(result.e3i(), a.e23oi(), b.e2i());
        result.e3i() = macSub(result.e3i(), a.e123oi(), b.e12i());
        result.e3i() = macSub(result.e3i(), a.e123oi(), b.e12i());

        result.e13i() = 0;
        result.e13i() = mac(result.e13i(), a.scalar(), b.e13i());
        result.e13i() = mac(result.e13i(), a.e1(), b.e3i());
        result.e13i() = macSub(result.e13i(), a.e2(), b.e123i());
        result.e13i() = macSub(result.e13i(), a.e12(), b.e23i());
        result.e13i() = macSub(result.e13i(), a.e3(), b.e1i());
        result.e13i() = macSub(result.e13i(), a.e13(), b.ei());
        result.e13i() = mac(result.e13i(), a.e23(), b.e12i());
        result.e13i() = mac(result.e13i(), a.e123(), b.e2i());
        result.e13i() = mac(result.e13i(), a.ei(), b.e13());
        result.e13i() = macSub(result.e13i(), a.ei(), b.e13oi());
        result.e13i() = mac(result.e13i(), a.e1i(), b.e3());
        result.e13i() = macSub(result.e13i(), a.e1i(), b.e3oi());
        result.e13i() = macSub(result.e13i(), a.e2i(), b.e123());
        result.e13i() = mac(result.e13i(), a.e2i(), b.e123oi());
        result.e13i() = macSub(result.e13i(), a.e12i(), b.e23());
        result.e13i() = mac(result.e13i(), a.e12i(), b.e23oi());
        result.e13i() = macSub(result.e13i(), a.e3i(), b.e1());
        result.e13i() = mac(result.e13i(), a.e3i(), b.e1oi());
        result.e13i() = macSub(result.e13i(), a.e13i(), b.scalar());
        result.e13i() = mac(result.e13i(), a.e13i(), b.eoi());
        result.e13i() = mac(result.e13i(), a.e23i(), b.e12());
        result.e13i() = macSub(result.e13i(), a.e23i(), b.e12oi());
        result.e13i() = mac(result.e13i(), a.e123i(), b.e2());
        result.e13i() = macSub(result.e13i(), a.e123i(), b.e2oi());
        result.e13i() = macSub(result.e13i(), a.eoi(), b.e13i());
        result.e13i() = macSub(result.e13i(), a.eoi(), b.e13i());
        result.e13i() = macSub(result.e13i(), a.e1oi(), b.e3i());
        result.e13i() = macSub(result.e13i(), a.e1oi(), b.e3i());
        result.e13i() = mac(result.e13i(), a.e2oi(), b.e123i());
        result.e13i() = mac(result.e13i(), a.e2oi(), b.e123i());
        result.e13i() = mac(result.e13i(), a.e12oi(), b.e23i());
        result.e13i() = mac(result.e13i(), a.e12oi(), b.e23i());
        result.e13i() = mac(result.e13i(), a.e3oi(), b.e1i());
        result.e13i() = mac(result.e13i(), a.e3oi(), b.e1i());
        result.e13i() = mac(result.e13i(), a.e13oi(), b.ei());
        result.e13i() = mac(result.e13i(), a.e13oi(), b.ei());
        result.e13i() = macSub(result.e13i(), a.e23oi(), b.e12i());
        result.e13i() = macSub(result.e13i(), a.e23oi(), b.e12i());
        result.e13i() = macSub(result.e13i(), a.e123oi(), b.e2i());
        result.e13i() = macSub(result.e13i(), a.e123oi(), b.e2i());

        result.e23i() = 0;
        result.e23i() = mac(result.e23i(), a.scalar(), b.e23i());
        result.e23i() = mac(result.e23i(), a.e1(), b.e123i());
        result.e23i() = mac(result.e23i(), a.e2(), b.e3i());
        result.e23i() = mac(result.e23i(), a.e12(), b.e13i());
        result.e23i() = macSub(result.e23i(), a.e3(), b.e2i());
        result.e23i() = macSub(result.e23i(), a.e13(), b.e12i());
        result.e23i() = macSub(result.e23i(), a.e23(), b.ei());
        result.e23i() = macSub(result.e23i(), a.e123(), b.e1i());
        result.e23i() = mac(result.e23i(), a.ei(), b.e23());
        result.e23i() = macSub(result.e23i(), a.ei(), b.e23oi());
        result.e23i() = mac(result.e23i(), a.e1i(), b.e123());
        result.e23i() = macSub(result.e23i(), a.e1i(), b.e123oi());
        result.e23i() = mac(result.e23i(), a.e2i(), b.e3());
        result.e23i() = macSub(result.e23i(), a.e2i(), b.e3oi());
        result.e23i() = mac(result.e23i(), a.e12i(), b.e13());
        result.e23i() = macSub(result.e23i(), a.e12i(), b.e13oi());
        result.e23i() = macSub(result.e23i(), a.e3i(), b.e2());
        result.e23i() = mac(result.e23i(), a.e3i(), b.e2oi());
        result.e23i() = macSub(result.e23i(), a.e13i(), b.e12());
        result.e23i() = mac(result.e23i(), a.e13i(), b.e12oi());
        result.e23i() = macSub(result.e23i(), a.e23i(), b.scalar());
        result.e23i() = mac(result.e23i(), a.e23i(), b.eoi());
        result.e23i() = macSub(result.e23i(), a.e123i(), b.e1());
        result.e23i() = mac(result.e23i(), a.e123i(), b.e1oi());
        result.e23i() = macSub(result.e23i(), a.eoi(), b.e23i());
        result.e23i() = macSub(result.e23i(), a.eoi(), b.e23i());
        result.e23i() = macSub(result.e23i(), a.e1oi(), b.e123i());
        result.e23i() = macSub(result.e23i(), a.e1oi(), b.e123i());
        result.e23i() = macSub(result.e23i(), a.e2oi(), b.e3i());
        result.e23i() = macSub(result.e23i(), a.e2oi(), b.e3i());
        result.e23i() = macSub(result.e23i(), a.e12oi(), b.e13i());
        result.e23i() = macSub(result.e23i(), a.e12oi(), b.e13i());
        result.e23i() = mac(result.e23i(), a.e3oi(), b.e2i());
        result.e23i() = mac(result.e23i(), a.e3oi(), b.e2i());
        result.e23i() = mac(result.e23i(), a.e13oi(), b.e12i());
        result.e23i() = mac(result.e23i(), a.e13oi(), b.e12i());
        result.e23i() = mac(result.e23i(), a.e23oi(), b.ei());
        result.e23i() = mac(result.e23i(), a.e23oi(), b.ei());
        result.e23i() = mac(result.e23i(), a.e123oi(), b.e1i());
        result.e23i() = mac(result.e23i(), a.e123oi(), b.e1i());

        result.e123i() = 0;
        result.e123i() = mac(result.e123i(), a.scalar(), b.e123i());
        result.e123i() = mac(result.e123i(), a.e1(), b.e23i());
        result.e123i() = macSub(result.e123i(), a.e2(), b.e13i());
        result.e123i() = macSub(result.e123i(), a.e12(), b.e3i());
        result.e123i() = mac(result.e123i(), a.e3(), b.e12i());
        result.e123i() = mac(result.e123i(), a.e13(), b.e2i());
        result.e123i() = macSub(result.e123i(), a.e23(), b.e1i());
        result.e123i() = macSub(result.e123i(), a.e123(), b.ei());
        result.e123i() = macSub(result.e123i(), a.ei(), b.e123());
        result.e123i() = mac(result.e123i(), a.ei(), b.e123oi());
        result.e123i() = macSub(result.e123i(), a.e1i(), b.e23());
        result.e123i() = mac(result.e123i(), a.e1i(), b.e23oi());
        result.e123i() = mac(result.e123i(), a.e2i(), b.e13());
        result.e123i() = macSub(result.e123i(), a.e2i(), b.e13oi());
        result.e123i() = mac(result.e123i(), a.e12i(), b.e3());
        result.e123i() = macSub(result.e123i(), a.e12i(), b.e3oi());
        result.e123i() = macSub(result.e123i(), a.e3i(), b.e12());
        result.e123i() = mac(result.e123i(), a.e3i(), b.e12oi());
        result.e123i() = macSub(result.e123i(), a.e13i(), b.e2());
        result.e123i() = mac(result.e123i(), a.e13i(), b.e2oi());
        result.e123i() = mac(result.e123i(), a.e23i(), b.e1());
        result.e123i() = macSub(result.e123i(), a.e23i(), b.e1oi());
        result.e123i() = mac(result.e123i(), a.e123i(), b.scalar());
        result.e123i() = macSub(result.e123i(), a.e123i(), b.eoi());
        result.e123i() = macSub(result.e123i(), a.eoi(), b.e123i());
        result.e123i() = macSub(result.e123i(), a.eoi(), b.e123i());
        result.e123i() = macSub(result.e123i(), a.e1oi(), b.e23i());
        result.e123i() = macSub(result.e123i(), a.e1oi(), b.e23i());
        result.e123i() = mac(result.e123i(), a.e2oi(), b.e13i());
        result.e123i() = mac(result.e123i(), a.e2oi(), b.e13i());
        result.e123i() = mac(result.e123i(), a.e12oi(), b.e3i());
        result.e123i() = mac(result.e123i(), a.e12oi(), b.e3i());
        result.e123i() = macSub(result.e123i(), a.e3oi(), b.e12i());
        result.e123i() = macSub(result.e123i(), a.e3oi(), b.e12i());
        result.e123i() = macSub(result.e123i(), a.e13oi(), b.e2i());
        result.e123i() = macSub(result.e123i(), a.e13oi(), b.e2i());
        result.e123i() = mac(result.e123i(), a.e23oi(), b.e1i());
        result.e123i() = mac(result.e123i(), a.e23oi(), b.e1i());
        result.e123i() = mac(result.e123i(), a.e123oi(), b.ei());
        result.e123i() = mac(result.e123i(), a.e123oi(), b.ei());

        result.eoi() = 0;
        result.eoi() = mac(result.eoi(), a.scalar(), b.eoi());
        result.eoi() = mac(result.eoi(), a.e1(), b.e1oi());
        result.eoi() = mac(result.eoi(), a.e2(), b.e2oi());
        result.eoi() = mac(result.eoi(), a.e12(), b.e12oi());
        result.eoi() = mac(result.eoi(), a.e3(), b.e3oi());
        result.eoi() = mac(result.eoi(), a.e13(), b.e13oi());
        result.eoi() = mac(result.eoi(), a.e23(), b.e23oi());
        result.eoi() = mac(result.eoi(), a.e123(), b.e123oi());
        result.eoi() = mac(result.eoi(), a.eo(), b.ei());
        result.eoi() = mac(result.eoi(), a.e1o(), b.e1i());
        result.eoi() = mac(result.eoi(), a.e2o(), b.e2i());
        result.eoi() = mac(result.eoi(), a.e12o(), b.e12i());
        result.eoi() = mac(result.eoi(), a.e3o(), b.e3i());
        result.eoi() = mac(result.eoi(), a.e13o(), b.e13i());
        result.eoi() = mac(result.eoi(), a.e23o(), b.e23i());
        result.eoi() = mac(result.eoi(), a.e123o(), b.e123i());
        result.eoi() = macSub(result.eoi(), a.ei(), b.eo());
        result.eoi() = macSub(result.eoi(), a.e1i(), b.e1o());
        result.eoi() = macSub(result.eoi(), a.e2i(), b.e2o());
        result.eoi() = macSub(result.eoi(), a.e12i(), b.e12o());
        result.eoi() = macSub(result.eoi(), a.e3i(), b.e3o());
        result.eoi() = macSub(result.eoi(), a.e13i(), b.e13o());
        result.eoi() = macSub(result.eoi(), a.e23i(), b.e23o());
        result.eoi() = macSub(result.eoi(), a.e123i(), b.e123o());
        result.eoi() = macSub(result.eoi(), a.eoi(), b.scalar());
        result.eoi() = macSub(result.eoi(), a.eoi(), b.eoi());
        result.eoi() = macSub(result.eoi(), a.e1oi(), b.e1());
        result.eoi() = macSub(result.eoi(), a.e1oi(), b.e1oi());
        result.eoi() = macSub(result.eoi(), a.e2oi(), b.e2());
        result.eoi() = macSub(result.eoi(), a.e2oi(), b.e2oi());
        result.eoi() = macSub(result.eoi(), a.e12oi(), b.e12());
        result.eoi() = macSub(result.eoi(), a.e12oi(), b.e12oi());
        result.eoi() = macSub(result.eoi(), a.e3oi(), b.e3());
        result.eoi() = macSub(result.eoi(), a.e3oi(), b.e3oi());
        result.eoi() = macSub(result.eoi(), a.e13oi(), b.e13());
        result.eoi() = macSub(result.eoi(), a.e13oi(), b.e13oi());
        result.eoi() = macSub(result.eoi(), a.e23oi(), b.e23());
        result.eoi() = macSub(result.eoi(), a.e23oi(), b.e23oi());
        result.eoi() = macSub(result.eoi(), a.e123oi(), b.e123());
        result.eoi() = macSub(result.eoi(), a.e123oi(), b.e123oi());

        result.e1oi() = 0;
        result.e1oi() = mac(result.e1oi(), a.scalar(), b.e1oi());
        result.e1oi() = mac(result.e1oi(), a.e1(), b.eoi());
        result.e1oi() = macSub(result.e1oi(), a.e2(), b.e12oi());
        result.e1oi() = macSub(result.e1oi(), a.e12(), b.e2oi());
        result.e1oi() = macSub(result.e1oi(), a.e3(), b.e13oi());
        result.e1oi() = macSub(result.e1oi(), a.e13(), b.e3oi());
        result.e1oi() = mac(result.e1oi(), a.e23(), b.e123oi());
        result.e1oi() = mac(result.e1oi(), a.e123(), b.e23oi());
        result.e1oi() = macSub(result.e1oi(), a.eo(), b.e1i());
        result.e1oi() = macSub(result.e1oi(), a.e1o(), b.ei());
        result.e1oi() = mac(result.e1oi(), a.e2o(), b.e12i());
        result.e1oi() = mac(result.e1oi(), a.e12o(), b.e2i());
        result.e1oi() = mac(result.e1oi(), a.e3o(), b.e13i());
        result.e1oi() = mac(result.e1oi(), a.e13o(), b.e3i());
        result.e1oi() = macSub(result.e1oi(), a.e23o(), b.e123i());
        result.e1oi() = macSub(result.e1oi(), a.e123o(), b.e23i());
        result.e1oi() = mac(result.e1oi(), a.ei(), b.e1o());
        result.e1oi() = mac(result.e1oi(), a.e1i(), b.eo());
        result.e1oi() = macSub(result.e1oi(), a.e2i(), b.e12o());
        result.e1oi() = macSub(result.e1oi(), a.e12i(), b.e2o());
        result.e1oi() = macSub(result.e1oi(), a.e3i(), b.e13o());
        result.e1oi() = macSub(result.e1oi(), a.e13i(), b.e3o());
        result.e1oi() = mac(result.e1oi(), a.e23i(), b.e123o());
        result.e1oi() = mac(result.e1oi(), a.e123i(), b.e23o());
        result.e1oi() = macSub(result.e1oi(), a.eoi(), b.e1());
        result.e1oi() = macSub(result.e1oi(), a.eoi(), b.e1oi());
        result.e1oi() = macSub(result.e1oi(), a.e1oi(), b.scalar());
        result.e1oi() = macSub(result.e1oi(), a.e1oi(), b.eoi());
        result.e1oi() = mac(result.e1oi(), a.e2oi(), b.e12());
        result.e1oi() = mac(result.e1oi(), a.e2oi(), b.e12oi());
        result.e1oi() = mac(result.e1oi(), a.e12oi(), b.e2());
        result.e1oi() = mac(result.e1oi(), a.e12oi(), b.e2oi());
        result.e1oi() = mac(result.e1oi(), a.e3oi(), b.e13());
        result.e1oi() = mac(result.e1oi(), a.e3oi(), b.e13oi());
        result.e1oi() = mac(result.e1oi(), a.e13oi(), b.e3());
        result.e1oi() = mac(result.e1oi(), a.e13oi(), b.e3oi());
        result.e1oi() = macSub(result.e1oi(), a.e23oi(), b.e123());
        result.e1oi() = macSub(result.e1oi(), a.e23oi(), b.e123oi());
        result.e1oi() = macSub(result.e1oi(), a.e123oi(), b.e23());
        result.e1oi() = macSub(result.e1oi(), a.e123oi(), b.e23oi());

        result.e2oi() = 0;
        result.e2oi() = mac(result.e2oi(), a.scalar(), b.e2oi());
        result.e2oi() = mac(result.e2oi(), a.e1(), b.e12oi());
        result.e2oi() = mac(result.e2oi(), a.e2(), b.eoi());
        result.e2oi() = mac(result.e2oi(), a.e12(), b.e1oi());
        result.e2oi() = macSub(result.e2oi(), a.e3(), b.e23oi());
        result.e2oi() = macSub(result.e2oi(), a.e13(), b.e123oi());
        result.e2oi() = macSub(result.e2oi(), a.e23(), b.e3oi());
        result.e2oi() = macSub(result.e2oi(), a.e123(), b.e13oi());
        result.e2oi() = macSub(result.e2oi(), a.eo(), b.e2i());
        result.e2oi() = macSub(result.e2oi(), a.e1o(), b.e12i());
        result.e2oi() = macSub(result.e2oi(), a.e2o(), b.ei());
        result.e2oi() = macSub(result.e2oi(), a.e12o(), b.e1i());
        result.e2oi() = mac(result.e2oi(), a.e3o(), b.e23i());
        result.e2oi() = mac(result.e2oi(), a.e13o(), b.e123i());
        result.e2oi() = mac(result.e2oi(), a.e23o(), b.e3i());
        result.e2oi() = mac(result.e2oi(), a.e123o(), b.e13i());
        result.e2oi() = mac(result.e2oi(), a.ei(), b.e2o());
        result.e2oi() = mac(result.e2oi(), a.e1i(), b.e12o());
        result.e2oi() = mac(result.e2oi(), a.e2i(), b.eo());
        result.e2oi() = mac(result.e2oi(), a.e12i(), b.e1o());
        result.e2oi() = macSub(result.e2oi(), a.e3i(), b.e23o());
        result.e2oi() = macSub(result.e2oi(), a.e13i(), b.e123o());
        result.e2oi() = macSub(result.e2oi(), a.e23i(), b.e3o());
        result.e2oi() = macSub(result.e2oi(), a.e123i(), b.e13o());
        result.e2oi() = macSub(result.e2oi(), a.eoi(), b.e2());
        result.e2oi() = macSub(result.e2oi(), a.eoi(), b.e2oi());
        result.e2oi() = macSub(result.e2oi(), a.e1oi(), b.e12());
        result.e2oi() = macSub(result.e2oi(), a.e1oi(), b.e12oi());
        result.e2oi() = macSub(result.e2oi(), a.e2oi(), b.scalar());
        result.e2oi() = macSub(result.e2oi(), a.e2oi(), b.eoi());
        result.e2oi() = macSub(result.e2oi(), a.e12oi(), b.e1());
        result.e2oi() = macSub(result.e2oi(), a.e12oi(), b.e1oi());
        result.e2oi() = mac(result.e2oi(), a.e3oi(), b.e23());
        result.e2oi() = mac(result.e2oi(), a.e3oi(), b.e23oi());
        result.e2oi() = mac(result.e2oi(), a.e13oi(), b.e123());
        result.e2oi() = mac(result.e2oi(), a.e13oi(), b.e123oi());
        result.e2oi() = mac(result.e2oi(), a.e23oi(), b.e3());
        result.e2oi() = mac(result.e2oi(), a.e23oi(), b.e3oi());
        result.e2oi() = mac(result.e2oi(), a.e123oi(), b.e13());
        result.e2oi() = mac(result.e2oi(), a.e123oi(), b.e13oi());

        result.e12oi() = 0;
        result.e12oi() = mac(result.e12oi(), a.scalar(), b.e12oi());
        result.e12oi() = mac(result.e12oi(), a.e1(), b.e2oi());
        result.e12oi() = macSub(result.e12oi(), a.e2(), b.e1oi());
        result.e12oi() = macSub(result.e12oi(), a.e12(), b.eoi());
        result.e12oi() = mac(result.e12oi(), a.e3(), b.e123oi());
        result.e12oi() = mac(result.e12oi(), a.e13(), b.e23oi());
        result.e12oi() = macSub(result.e12oi(), a.e23(), b.e13oi());
        result.e12oi() = macSub(result.e12oi(), a.e123(), b.e3oi());
        result.e12oi() = mac(result.e12oi(), a.eo(), b.e12i());
        result.e12oi() = mac(result.e12oi(), a.e1o(), b.e2i());
        result.e12oi() = macSub(result.e12oi(), a.e2o(), b.e1i());
        result.e12oi() = macSub(result.e12oi(), a.e12o(), b.ei());
        result.e12oi() = mac(result.e12oi(), a.e3o(), b.e123i());
        result.e12oi() = mac(result.e12oi(), a.e13o(), b.e23i());
        result.e12oi() = macSub(result.e12oi(), a.e23o(), b.e13i());
        result.e12oi() = macSub(result.e12oi(), a.e123o(), b.e3i());
        result.e12oi() = macSub(result.e12oi(), a.ei(), b.e12o());
        result.e12oi() = macSub(result.e12oi(), a.e1i(), b.e2o());
        result.e12oi() = mac(result.e12oi(), a.e2i(), b.e1o());
        result.e12oi() = mac(result.e12oi(), a.e12i(), b.eo());
        result.e12oi() = macSub(result.e12oi(), a.e3i(), b.e123o());
        result.e12oi() = macSub(result.e12oi(), a.e13i(), b.e23o());
        result.e12oi() = mac(result.e12oi(), a.e23i(), b.e13o());
        result.e12oi() = mac(result.e12oi(), a.e123i(), b.e3o());
        result.e12oi() = macSub(result.e12oi(), a.eoi(), b.e12());
        result.e12oi() = macSub(result.e12oi(), a.eoi(), b.e12oi());
        result.e12oi() = macSub(result.e12oi(), a.e1oi(), b.e2());
        result.e12oi() = macSub(result.e12oi(), a.e1oi(), b.e2oi());
        result.e12oi() = mac(result.e12oi(), a.e2oi(), b.e1());
        result.e12oi() = mac(result.e12oi(), a.e2oi(), b.e1oi());
        result.e12oi() = mac(result.e12oi(), a.e12oi(), b.scalar());
        result.e12oi() = mac(result.e12oi(), a.e12oi(), b.eoi());
        result.e12oi() = macSub(result.e12oi(), a.e3oi(), b.e123());
        result.e12oi() = macSub(result.e12oi(), a.e3oi(), b.e123oi());
        result.e12oi() = macSub(result.e12oi(), a.e13oi(), b.e23());
        result.e12oi() = macSub(result.e12oi(), a.e13oi(), b.e23oi());
        result.e12oi() = mac(result.e12oi(), a.e23oi(), b.e13());
        result.e12oi() = mac(result.e12oi(), a.e23oi(), b.e13oi());
        result.e12oi() = mac(result.e12oi(), a.e123oi(), b.e3());
        result.e12oi() = mac(result.e12oi(), a.e123oi(), b.e3oi());

        result.e3oi() = 0;
        result.e3oi() = mac(result.e3oi(), a.scalar(), b.e3oi());
        result.e3oi() = mac(result.e3oi(), a.e1(), b.e13oi());
        result.e3oi() = mac(result.e3oi(), a.e2(), b.e23oi());
        result.e3oi() = mac(result.e3oi(), a.e12(), b.e123oi());
        result.e3oi() = mac(result.e3oi(), a.e3(), b.eoi());
        result.e3oi() = mac(result.e3oi(), a.e13(), b.e1oi());
        result.e3oi() = mac(result.e3oi(), a.e23(), b.e2oi());
        result.e3oi() = mac(result.e3oi(), a.e123(), b.e12oi());
        result.e3oi() = macSub(result.e3oi(), a.eo(), b.e3i());
        result.e3oi() = macSub(result.e3oi(), a.e1o(), b.e13i());
        result.e3oi() = macSub(result.e3oi(), a.e2o(), b.e23i());
        result.e3oi() = macSub(result.e3oi(), a.e12o(), b.e123i());
        result.e3oi() = macSub(result.e3oi(), a.e3o(), b.ei());
        result.e3oi() = macSub(result.e3oi(), a.e13o(), b.e1i());
        result.e3oi() = macSub(result.e3oi(), a.e23o(), b.e2i());
        result.e3oi() = macSub(result.e3oi(), a.e123o(), b.e12i());
        result.e3oi() = mac(result.e3oi(), a.ei(), b.e3o());
        result.e3oi() = mac(result.e3oi(), a.e1i(), b.e13o());
        result.e3oi() = mac(result.e3oi(), a.e2i(), b.e23o());
        result.e3oi() = mac(result.e3oi(), a.e12i(), b.e123o());
        result.e3oi() = mac(result.e3oi(), a.e3i(), b.eo());
        result.e3oi() = mac(result.e3oi(), a.e13i(), b.e1o());
        result.e3oi() = mac(result.e3oi(), a.e23i(), b.e2o());
        result.e3oi() = mac(result.e3oi(), a.e123i(), b.e12o());
        result.e3oi() = macSub(result.e3oi(), a.eoi(), b.e3());
        result.e3oi() = macSub(result.e3oi(), a.eoi(), b.e3oi());
        result.e3oi() = macSub(result.e3oi(), a.e1oi(), b.e13());
        result.e3oi() = macSub(result.e3oi(), a.e1oi(), b.e13oi());
        result.e3oi() = macSub(result.e3oi(), a.e2oi(), b.e23());
        result.e3oi() = macSub(result.e3oi(), a.e2oi(), b.e23oi());
        result.e3oi() = macSub(result.e3oi(), a.e12oi(), b.e123());
        result.e3oi() = macSub(result.e3oi(), a.e12oi(), b.e123oi());
        result.e3oi() = macSub(result.e3oi(), a.e3oi(), b.scalar());
        result.e3oi() = macSub(result.e3oi(), a.e3oi(), b.eoi());
        result.e3oi() = macSub(result.e3oi(), a.e13oi(), b.e1());
        result.e3oi() = macSub(result.e3oi(), a.e13oi(), b.e1oi());
        result.e3oi() = macSub(result.e3oi(), a.e23oi(), b.e2());
        result.e3oi() = macSub(result.e3oi(), a.e23oi(), b.e2oi());
        result.e3oi() = macSub(result.e3oi(), a.e123oi(), b.e12());
        result.e3oi() = macSub(result.e3oi(), a.e123oi(), b.e12oi());

        result.e13oi() = 0;
        result.e13oi() = mac(result.e13oi(), a.scalar(), b.e13oi());
        result.e13oi() = mac(result.e13oi(), a.e1(), b.e3oi());
        result.e13oi() = macSub(result.e13oi(), a.e2(), b.e123oi());
        result.e13oi() = macSub(result.e13oi(), a.e12(), b.e23oi());
        result.e13oi() = macSub(result.e13oi(), a.e3(), b.e1oi());
        result.e13oi() = macSub(result.e13oi(), a.e13(), b.eoi());
        result.e13oi() = mac(result.e13oi(), a.e23(), b.e12oi());
        result.e13oi() = mac(result.e13oi(), a.e123(), b.e2oi());
        result.e13oi() = mac(result.e13oi(), a.eo(), b.e13i());
        result.e13oi() = mac(result.e13oi(), a.e1o(), b.e3i());
        result.e13oi() = macSub(result.e13oi(), a.e2o(), b.e123i());
        result.e13oi() = macSub(result.e13oi(), a.e12o(), b.e23i());
        result.e13oi() = macSub(result.e13oi(), a.e3o(), b.e1i());
        result.e13oi() = macSub(result.e13oi(), a.e13o(), b.ei());
        result.e13oi() = mac(result.e13oi(), a.e23o(), b.e12i());
        result.e13oi() = mac(result.e13oi(), a.e123o(), b.e2i());
        result.e13oi() = macSub(result.e13oi(), a.ei(), b.e13o());
        result.e13oi() = macSub(result.e13oi(), a.e1i(), b.e3o());
        result.e13oi() = mac(result.e13oi(), a.e2i(), b.e123o());
        result.e13oi() = mac(result.e13oi(), a.e12i(), b.e23o());
        result.e13oi() = mac(result.e13oi(), a.e3i(), b.e1o());
        result.e13oi() = mac(result.e13oi(), a.e13i(), b.eo());
        result.e13oi() = macSub(result.e13oi(), a.e23i(), b.e12o());
        result.e13oi() = macSub(result.e13oi(), a.e123i(), b.e2o());
        result.e13oi() = macSub(result.e13oi(), a.eoi(), b.e13());
        result.e13oi() = macSub(result.e13oi(), a.eoi(), b.e13oi());
        result.e13oi() = macSub(result.e13oi(), a.e1oi(), b.e3());
        result.e13oi() = macSub(result.e13oi(), a.e1oi(), b.e3oi());
        result.e13oi() = mac(result.e13oi(), a.e2oi(), b.e123());
        result.e13oi() = mac(result.e13oi(), a.e2oi(), b.e123oi());
        result.e13oi() = mac(result.e13oi(), a.e12oi(), b.e23());
        result.e13oi() = mac(result.e13oi(), a.e12oi(), b.e23oi());
        result.e13oi() = mac(result.e13oi(), a.e3oi(), b.e1());
        result.e13oi() = mac(result.e13oi(), a.e3oi(), b.e1oi());
        result.e13oi() = mac(result.e13oi(), a.e13oi(), b.scalar());
        result.e13oi() = mac(result.e13oi(), a.e13oi(), b.eoi());
        result.e13oi() = macSub(result.e13oi(), a.e23oi(), b.e12());
        result.e13oi() = macSub(result.e13oi(), a.e23oi(), b.e12oi());
        result.e13oi() = macSub(result.e13oi(), a.e123oi(), b.e2());
        result.e13oi() = macSub(result.e13oi(), a.e123oi(), b.e2oi());

        result.e23oi() = 0;
        result.e23oi() = mac(result.e23oi(), a.scalar(), b.e23oi());
        result.e23oi() = mac(result.e23oi(), a.e1(), b.e123oi());
        result.e23oi() = mac(result.e23oi(), a.e2(), b.e3oi());
        result.e23oi() = mac(result.e23oi(), a.e12(), b.e13oi());
        result.e23oi() = macSub(result.e23oi(), a.e3(), b.e2oi());
        result.e23oi() = macSub(result.e23oi(), a.e13(), b.e12oi());
        result.e23oi() = macSub(result.e23oi(), a.e23(), b.eoi());
        result.e23oi() = macSub(result.e23oi(), a.e123(), b.e1oi());
        result.e23oi() = mac(result.e23oi(), a.eo(), b.e23i());
        result.e23oi() = mac(result.e23oi(), a.e1o(), b.e123i());
        result.e23oi() = mac(result.e23oi(), a.e2o(), b.e3i());
        result.e23oi() = mac(result.e23oi(), a.e12o(), b.e13i());
        result.e23oi() = macSub(result.e23oi(), a.e3o(), b.e2i());
        result.e23oi() = macSub(result.e23oi(), a.e13o(), b.e12i());
        result.e23oi() = macSub(result.e23oi(), a.e23o(), b.ei());
        result.e23oi() = macSub(result.e23oi(), a.e123o(), b.e1i());
        result.e23oi() = macSub(result.e23oi(), a.ei(), b.e23o());
        result.e23oi() = macSub(result.e23oi(), a.e1i(), b.e123o());
        result.e23oi() = macSub(result.e23oi(), a.e2i(), b.e3o());
        result.e23oi() = macSub(result.e23oi(), a.e12i(), b.e13o());
        result.e23oi() = mac(result.e23oi(), a.e3i(), b.e2o());
        result.e23oi() = mac(result.e23oi(), a.e13i(), b.e12o());
        result.e23oi() = mac(result.e23oi(), a.e23i(), b.eo());
        result.e23oi() = mac(result.e23oi(), a.e123i(), b.e1o());
        result.e23oi() = macSub(result.e23oi(), a.eoi(), b.e23());
        result.e23oi() = macSub(result.e23oi(), a.eoi(), b.e23oi());
        result.e23oi() = macSub(result.e23oi(), a.e1oi(), b.e123());
        result.e23oi() = macSub(result.e23oi(), a.e1oi(), b.e123oi());
        result.e23oi() = macSub(result.e23oi(), a.e2oi(), b.e3());
        result.e23oi() = macSub(result.e23oi(), a.e2oi(), b.e3oi());
        result.e23oi() = macSub(result.e23oi(), a.e12oi(), b.e13());
        result.e23oi() = macSub(result.e23oi(), a.e12oi(), b.e13oi());
        result.e23oi() = mac(result.e23oi(), a.e3oi(), b.e2());
        result.e23oi() = mac(result.e23oi(), a.e3oi(), b.e2oi());
        result.e23oi() = mac(result.e23oi(), a.e13oi(), b.e12());
        result.e23oi() = mac(result.e23oi(), a.e13oi(), b.e12oi());
        result.e23oi() = mac(result.e23oi(), a.e23oi(), b.scalar());
        result.e23oi() = mac(result.e23oi(), a.e23oi(), b.eoi());
        result.e23oi() = mac(result.e23oi(), a.e123oi(), b.e1());
        result.e23oi() = mac(result.e23oi(), a.e123oi(), b.e1oi());

        result.e123oi() = 0;
        result.e123oi() = mac(result.e123oi(), a.scalar(), b.e123oi());
        result.e123oi() = mac(result.e123oi(), a.e1(), b.e23oi());
        result.e123oi() = macSub(result.e123oi(), a.e2(), b.e13oi());
        result.e123oi() = macSub(result.e123oi(), a.e12(), b.e3oi());
        result.e123oi() = mac(result.e123oi(), a.e3(), b.e12oi());
        result.e123oi() = mac(result.e123oi(), a.e13(), b.e2oi());
        result.e123oi() = macSub(result.e123oi(), a.e23(), b.e1oi());
        result.e123oi() = macSub(result.e123oi(), a.e123(), b.eoi());
        result.e123oi() = macSub(result.e123oi(), a.eo(), b.e123i());
        result.e123oi() = macSub(result.e123oi(), a.e1o(), b.e23i());
        result.e123oi() = mac(result.e123oi(), a.e2o(), b.e13i());
        result.e123oi() = mac(result.e123oi(), a.e12o(), b.e3i());
        result.e123oi() = macSub(result.e123oi(), a.e3o(), b.e12i());
        result.e123oi() = macSub(result.e123oi(), a.e13o(), b.e2i());
        result.e123oi() = mac(result.e123oi(), a.e23o(), b.e1i());
        result.e123oi() = mac(result.e123oi(), a.e123o(), b.ei());
        result.e123oi() = mac(result.e123oi(), a.ei(), b.e123o());
        result.e123oi() = mac(result.e123oi(), a.e1i(), b.e23o());
        result.e123oi() = macSub(result.e123oi(), a.e2i(), b.e13o());
        result.e123oi() = macSub(result.e123oi(), a.e12i(), b.e3o());
        result.e123oi() = mac(result.e123oi(), a.e3i(), b.e12o());
        result.e123oi() = mac(result.e123oi(), a.e13i(), b.e2o());
        result.e123oi() = macSub(result.e123oi(), a.e23i(), b.e1o());
        result.e123oi() = macSub(result.e123oi(), a.e123i(), b.eo());
        result.e123oi() = macSub(result.e123oi(), a.eoi(), b.e123());
        result.e123oi() = macSub(result.e123oi(), a.eoi(), b.e123oi());
        result.e123oi() = macSub(result.e123oi(), a.e1oi(), b.e23());
        result.e123oi() = macSub(result.e123oi(), a.e1oi(), b.e23oi());
        result.e123oi() = mac(result.e123oi(), a.e2oi(), b.e13());
        result.e123oi() = mac(result.e123oi(), a.e2oi(), b.e13oi());
        result.e123oi() = mac(result.e123oi(), a.e12oi(), b.e3());
        result.e123oi() = mac(result.e123oi(), a.e12oi(), b.e3oi());
        result.e123oi() = macSub(result.e123oi(), a.e3oi(), b.e12());
        result.e123oi() = macSub(result.e123oi(), a.e3oi(), b.e12oi());
        result.e123oi() = macSub(result.e123oi(), a.e13oi(), b.e2());
        result.e123oi() = macSub(result.e123oi(), a.e13oi(), b.e2oi());
        result.e123oi() = mac(result.e123oi(), a.e23oi(), b.e1());
        result.e123oi() = mac(result.e123oi(), a.e23oi(), b.e1oi());
        result.e123oi() = mac(result.e123oi(), a.e123oi(), b.scalar());
        result.e123oi() = mac(result.e123oi(), a.e123oi(), b.eoi());

        return result;
    }
    
    CgaMultivector wedgeProduct(CgaMultivector& b) 
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

        result.scalar() = 0;
        result.scalar() = mac(result.scalar(), a.scalar(), b.scalar());

        result.e1() = 0;
        result.e1() = mac(result.e1(), a.scalar(), b.e1());
        result.e1() = mac(result.e1(), a.e1(), b.scalar());

        result.e2() = 0;
        result.e2() = mac(result.e2(), a.scalar(), b.e2());
        result.e2() = mac(result.e2(), a.e2(), b.scalar());

        result.e12() = 0;
        result.e12() = mac(result.e12(), a.scalar(), b.e12());
        result.e12() = mac(result.e12(), a.e1(), b.e2());
        result.e12() = macSub(result.e12(), a.e2(), b.e1());
        result.e12() = macSub(result.e12(), a.e12(), b.scalar());

        result.e3() = 0;
        result.e3() = mac(result.e3(), a.scalar(), b.e3());
        result.e3() = mac(result.e3(), a.e3(), b.scalar());

        result.e13() = 0;
        result.e13() = mac(result.e13(), a.scalar(), b.e13());
        result.e13() = mac(result.e13(), a.e1(), b.e3());
        result.e13() = macSub(result.e13(), a.e3(), b.e1());
        result.e13() = macSub(result.e13(), a.e13(), b.scalar());

        result.e23() = 0;
        result.e23() = mac(result.e23(), a.scalar(), b.e23());
        result.e23() = mac(result.e23(), a.e2(), b.e3());
        result.e23() = macSub(result.e23(), a.e3(), b.e2());
        result.e23() = macSub(result.e23(), a.e23(), b.scalar());

        result.e123() = 0;
        result.e123() = mac(result.e123(), a.scalar(), b.e123());
        result.e123() = mac(result.e123(), a.e1(), b.e23());
        result.e123() = macSub(result.e123(), a.e2(), b.e13());
        result.e123() = macSub(result.e123(), a.e12(), b.e3());
        result.e123() = mac(result.e123(), a.e3(), b.e12());
        result.e123() = mac(result.e123(), a.e13(), b.e2());
        result.e123() = macSub(result.e123(), a.e23(), b.e1());
        result.e123() = macSub(result.e123(), a.e123(), b.scalar());

        result.eo() = 0;
        result.eo() = mac(result.eo(), a.scalar(), b.eo());
        result.eo() = mac(result.eo(), a.eo(), b.scalar());

        result.e1o() = 0;
        result.e1o() = mac(result.e1o(), a.scalar(), b.e1o());
        result.e1o() = mac(result.e1o(), a.e1(), b.eo());
        result.e1o() = macSub(result.e1o(), a.eo(), b.e1());
        result.e1o() = macSub(result.e1o(), a.e1o(), b.scalar());

        result.e2o() = 0;
        result.e2o() = mac(result.e2o(), a.scalar(), b.e2o());
        result.e2o() = mac(result.e2o(), a.e2(), b.eo());
        result.e2o() = macSub(result.e2o(), a.eo(), b.e2());
        result.e2o() = macSub(result.e2o(), a.e2o(), b.scalar());

        result.e12o() = 0;
        result.e12o() = mac(result.e12o(), a.scalar(), b.e12o());
        result.e12o() = mac(result.e12o(), a.e1(), b.e2o());
        result.e12o() = macSub(result.e12o(), a.e2(), b.e1o());
        result.e12o() = macSub(result.e12o(), a.e12(), b.eo());
        result.e12o() = mac(result.e12o(), a.eo(), b.e12());
        result.e12o() = mac(result.e12o(), a.e1o(), b.e2());
        result.e12o() = macSub(result.e12o(), a.e2o(), b.e1());
        result.e12o() = macSub(result.e12o(), a.e12o(), b.scalar());

        result.e3o() = 0;
        result.e3o() = mac(result.e3o(), a.scalar(), b.e3o());
        result.e3o() = mac(result.e3o(), a.e3(), b.eo());
        result.e3o() = macSub(result.e3o(), a.eo(), b.e3());
        result.e3o() = macSub(result.e3o(), a.e3o(), b.scalar());

        result.e13o() = 0;
        result.e13o() = mac(result.e13o(), a.scalar(), b.e13o());
        result.e13o() = mac(result.e13o(), a.e1(), b.e3o());
        result.e13o() = macSub(result.e13o(), a.e3(), b.e1o());
        result.e13o() = macSub(result.e13o(), a.e13(), b.eo());
        result.e13o() = mac(result.e13o(), a.eo(), b.e13());
        result.e13o() = mac(result.e13o(), a.e1o(), b.e3());
        result.e13o() = macSub(result.e13o(), a.e3o(), b.e1());
        result.e13o() = macSub(result.e13o(), a.e13o(), b.scalar());

        result.e23o() = 0;
        result.e23o() = mac(result.e23o(), a.scalar(), b.e23o());
        result.e23o() = mac(result.e23o(), a.e2(), b.e3o());
        result.e23o() = macSub(result.e23o(), a.e3(), b.e2o());
        result.e23o() = macSub(result.e23o(), a.e23(), b.eo());
        result.e23o() = mac(result.e23o(), a.eo(), b.e23());
        result.e23o() = mac(result.e23o(), a.e2o(), b.e3());
        result.e23o() = macSub(result.e23o(), a.e3o(), b.e2());
        result.e23o() = macSub(result.e23o(), a.e23o(), b.scalar());

        result.e123o() = 0;
        result.e123o() = mac(result.e123o(), a.scalar(), b.e123o());
        result.e123o() = mac(result.e123o(), a.e1(), b.e23o());
        result.e123o() = macSub(result.e123o(), a.e2(), b.e13o());
        result.e123o() = macSub(result.e123o(), a.e12(), b.e3o());
        result.e123o() = mac(result.e123o(), a.e3(), b.e12o());
        result.e123o() = mac(result.e123o(), a.e13(), b.e2o());
        result.e123o() = macSub(result.e123o(), a.e23(), b.e1o());
        result.e123o() = macSub(result.e123o(), a.e123(), b.eo());
        result.e123o() = macSub(result.e123o(), a.eo(), b.e123());
        result.e123o() = macSub(result.e123o(), a.e1o(), b.e23());
        result.e123o() = mac(result.e123o(), a.e2o(), b.e13());
        result.e123o() = mac(result.e123o(), a.e12o(), b.e3());
        result.e123o() = macSub(result.e123o(), a.e3o(), b.e12());
        result.e123o() = macSub(result.e123o(), a.e13o(), b.e2());
        result.e123o() = mac(result.e123o(), a.e23o(), b.e1());
        result.e123o() = mac(result.e123o(), a.e123o(), b.scalar());

        result.ei() = 0;
        result.ei() = mac(result.ei(), a.scalar(), b.ei());
        result.ei() = mac(result.ei(), a.ei(), b.scalar());

        result.e1i() = 0;
        result.e1i() = mac(result.e1i(), a.scalar(), b.e1i());
        result.e1i() = mac(result.e1i(), a.e1(), b.ei());
        result.e1i() = macSub(result.e1i(), a.ei(), b.e1());
        result.e1i() = macSub(result.e1i(), a.e1i(), b.scalar());

        result.e2i() = 0;
        result.e2i() = mac(result.e2i(), a.scalar(), b.e2i());
        result.e2i() = mac(result.e2i(), a.e2(), b.ei());
        result.e2i() = macSub(result.e2i(), a.ei(), b.e2());
        result.e2i() = macSub(result.e2i(), a.e2i(), b.scalar());

        result.e12i() = 0;
        result.e12i() = mac(result.e12i(), a.scalar(), b.e12i());
        result.e12i() = mac(result.e12i(), a.e1(), b.e2i());
        result.e12i() = macSub(result.e12i(), a.e2(), b.e1i());
        result.e12i() = macSub(result.e12i(), a.e12(), b.ei());
        result.e12i() = mac(result.e12i(), a.ei(), b.e12());
        result.e12i() = mac(result.e12i(), a.e1i(), b.e2());
        result.e12i() = macSub(result.e12i(), a.e2i(), b.e1());
        result.e12i() = macSub(result.e12i(), a.e12i(), b.scalar());

        result.e3i() = 0;
        result.e3i() = mac(result.e3i(), a.scalar(), b.e3i());
        result.e3i() = mac(result.e3i(), a.e3(), b.ei());
        result.e3i() = macSub(result.e3i(), a.ei(), b.e3());
        result.e3i() = macSub(result.e3i(), a.e3i(), b.scalar());

        result.e13i() = 0;
        result.e13i() = mac(result.e13i(), a.scalar(), b.e13i());
        result.e13i() = mac(result.e13i(), a.e1(), b.e3i());
        result.e13i() = macSub(result.e13i(), a.e3(), b.e1i());
        result.e13i() = macSub(result.e13i(), a.e13(), b.ei());
        result.e13i() = mac(result.e13i(), a.ei(), b.e13());
        result.e13i() = mac(result.e13i(), a.e1i(), b.e3());
        result.e13i() = macSub(result.e13i(), a.e3i(), b.e1());
        result.e13i() = macSub(result.e13i(), a.e13i(), b.scalar());

        result.e23i() = 0;
        result.e23i() = mac(result.e23i(), a.scalar(), b.e23i());
        result.e23i() = mac(result.e23i(), a.e2(), b.e3i());
        result.e23i() = macSub(result.e23i(), a.e3(), b.e2i());
        result.e23i() = macSub(result.e23i(), a.e23(), b.ei());
        result.e23i() = mac(result.e23i(), a.ei(), b.e23());
        result.e23i() = mac(result.e23i(), a.e2i(), b.e3());
        result.e23i() = macSub(result.e23i(), a.e3i(), b.e2());
        result.e23i() = macSub(result.e23i(), a.e23i(), b.scalar());

        result.e123i() = 0;
        result.e123i() = mac(result.e123i(), a.scalar(), b.e123i());
        result.e123i() = mac(result.e123i(), a.e1(), b.e23i());
        result.e123i() = macSub(result.e123i(), a.e2(), b.e13i());
        result.e123i() = macSub(result.e123i(), a.e12(), b.e3i());
        result.e123i() = mac(result.e123i(), a.e3(), b.e12i());
        result.e123i() = mac(result.e123i(), a.e13(), b.e2i());
        result.e123i() = macSub(result.e123i(), a.e23(), b.e1i());
        result.e123i() = macSub(result.e123i(), a.e123(), b.ei());
        result.e123i() = macSub(result.e123i(), a.ei(), b.e123());
        result.e123i() = macSub(result.e123i(), a.e1i(), b.e23());
        result.e123i() = mac(result.e123i(), a.e2i(), b.e13());
        result.e123i() = mac(result.e123i(), a.e12i(), b.e3());
        result.e123i() = macSub(result.e123i(), a.e3i(), b.e12());
        result.e123i() = macSub(result.e123i(), a.e13i(), b.e2());
        result.e123i() = mac(result.e123i(), a.e23i(), b.e1());
        result.e123i() = mac(result.e123i(), a.e123i(), b.scalar());

        result.eoi() = 0;
        result.eoi() = mac(result.eoi(), a.scalar(), b.eoi());
        result.eoi() = mac(result.eoi(), a.eo(), b.ei());
        result.eoi() = macSub(result.eoi(), a.ei(), b.eo());
        result.eoi() = macSub(result.eoi(), a.eoi(), b.scalar());

        result.e1oi() = 0;
        result.e1oi() = mac(result.e1oi(), a.scalar(), b.e1oi());
        result.e1oi() = mac(result.e1oi(), a.e1(), b.eoi());
        result.e1oi() = macSub(result.e1oi(), a.eo(), b.e1i());
        result.e1oi() = macSub(result.e1oi(), a.e1o(), b.ei());
        result.e1oi() = mac(result.e1oi(), a.ei(), b.e1o());
        result.e1oi() = mac(result.e1oi(), a.e1i(), b.eo());
        result.e1oi() = macSub(result.e1oi(), a.eoi(), b.e1());
        result.e1oi() = macSub(result.e1oi(), a.e1oi(), b.scalar());

        result.e2oi() = 0;
        result.e2oi() = mac(result.e2oi(), a.scalar(), b.e2oi());
        result.e2oi() = mac(result.e2oi(), a.e2(), b.eoi());
        result.e2oi() = macSub(result.e2oi(), a.eo(), b.e2i());
        result.e2oi() = macSub(result.e2oi(), a.e2o(), b.ei());
        result.e2oi() = mac(result.e2oi(), a.ei(), b.e2o());
        result.e2oi() = mac(result.e2oi(), a.e2i(), b.eo());
        result.e2oi() = macSub(result.e2oi(), a.eoi(), b.e2());
        result.e2oi() = macSub(result.e2oi(), a.e2oi(), b.scalar());

        result.e12oi() = 0;
        result.e12oi() = mac(result.e12oi(), a.scalar(), b.e12oi());
        result.e12oi() = mac(result.e12oi(), a.e1(), b.e2oi());
        result.e12oi() = macSub(result.e12oi(), a.e2(), b.e1oi());
        result.e12oi() = macSub(result.e12oi(), a.e12(), b.eoi());
        result.e12oi() = mac(result.e12oi(), a.eo(), b.e12i());
        result.e12oi() = mac(result.e12oi(), a.e1o(), b.e2i());
        result.e12oi() = macSub(result.e12oi(), a.e2o(), b.e1i());
        result.e12oi() = macSub(result.e12oi(), a.e12o(), b.ei());
        result.e12oi() = macSub(result.e12oi(), a.ei(), b.e12o());
        result.e12oi() = macSub(result.e12oi(), a.e1i(), b.e2o());
        result.e12oi() = mac(result.e12oi(), a.e2i(), b.e1o());
        result.e12oi() = mac(result.e12oi(), a.e12i(), b.eo());
        result.e12oi() = macSub(result.e12oi(), a.eoi(), b.e12());
        result.e12oi() = macSub(result.e12oi(), a.e1oi(), b.e2());
        result.e12oi() = mac(result.e12oi(), a.e2oi(), b.e1());
        result.e12oi() = mac(result.e12oi(), a.e12oi(), b.scalar());

        result.e3oi() = 0;
        result.e3oi() = mac(result.e3oi(), a.scalar(), b.e3oi());
        result.e3oi() = mac(result.e3oi(), a.e3(), b.eoi());
        result.e3oi() = macSub(result.e3oi(), a.eo(), b.e3i());
        result.e3oi() = macSub(result.e3oi(), a.e3o(), b.ei());
        result.e3oi() = mac(result.e3oi(), a.ei(), b.e3o());
        result.e3oi() = mac(result.e3oi(), a.e3i(), b.eo());
        result.e3oi() = macSub(result.e3oi(), a.eoi(), b.e3());
        result.e3oi() = macSub(result.e3oi(), a.e3oi(), b.scalar());

        result.e13oi() = 0;
        result.e13oi() = mac(result.e13oi(), a.scalar(), b.e13oi());
        result.e13oi() = mac(result.e13oi(), a.e1(), b.e3oi());
        result.e13oi() = macSub(result.e13oi(), a.e3(), b.e1oi());
        result.e13oi() = macSub(result.e13oi(), a.e13(), b.eoi());
        result.e13oi() = mac(result.e13oi(), a.eo(), b.e13i());
        result.e13oi() = mac(result.e13oi(), a.e1o(), b.e3i());
        result.e13oi() = macSub(result.e13oi(), a.e3o(), b.e1i());
        result.e13oi() = macSub(result.e13oi(), a.e13o(), b.ei());
        result.e13oi() = macSub(result.e13oi(), a.ei(), b.e13o());
        result.e13oi() = macSub(result.e13oi(), a.e1i(), b.e3o());
        result.e13oi() = mac(result.e13oi(), a.e3i(), b.e1o());
        result.e13oi() = mac(result.e13oi(), a.e13i(), b.eo());
        result.e13oi() = macSub(result.e13oi(), a.eoi(), b.e13());
        result.e13oi() = macSub(result.e13oi(), a.e1oi(), b.e3());
        result.e13oi() = mac(result.e13oi(), a.e3oi(), b.e1());
        result.e13oi() = mac(result.e13oi(), a.e13oi(), b.scalar());

        result.e23oi() = 0;
        result.e23oi() = mac(result.e23oi(), a.scalar(), b.e23oi());
        result.e23oi() = mac(result.e23oi(), a.e2(), b.e3oi());
        result.e23oi() = macSub(result.e23oi(), a.e3(), b.e2oi());
        result.e23oi() = macSub(result.e23oi(), a.e23(), b.eoi());
        result.e23oi() = mac(result.e23oi(), a.eo(), b.e23i());
        result.e23oi() = mac(result.e23oi(), a.e2o(), b.e3i());
        result.e23oi() = macSub(result.e23oi(), a.e3o(), b.e2i());
        result.e23oi() = macSub(result.e23oi(), a.e23o(), b.ei());
        result.e23oi() = macSub(result.e23oi(), a.ei(), b.e23o());
        result.e23oi() = macSub(result.e23oi(), a.e2i(), b.e3o());
        result.e23oi() = mac(result.e23oi(), a.e3i(), b.e2o());
        result.e23oi() = mac(result.e23oi(), a.e23i(), b.eo());
        result.e23oi() = macSub(result.e23oi(), a.eoi(), b.e23());
        result.e23oi() = macSub(result.e23oi(), a.e2oi(), b.e3());
        result.e23oi() = mac(result.e23oi(), a.e3oi(), b.e2());
        result.e23oi() = mac(result.e23oi(), a.e23oi(), b.scalar());

        result.e123oi() = 0;
        result.e123oi() = mac(result.e123oi(), a.scalar(), b.e123oi());
        result.e123oi() = mac(result.e123oi(), a.e1(), b.e23oi());
        result.e123oi() = macSub(result.e123oi(), a.e2(), b.e13oi());
        result.e123oi() = macSub(result.e123oi(), a.e12(), b.e3oi());
        result.e123oi() = mac(result.e123oi(), a.e3(), b.e12oi());
        result.e123oi() = mac(result.e123oi(), a.e13(), b.e2oi());
        result.e123oi() = macSub(result.e123oi(), a.e23(), b.e1oi());
        result.e123oi() = macSub(result.e123oi(), a.e123(), b.eoi());
        result.e123oi() = macSub(result.e123oi(), a.eo(), b.e123i());
        result.e123oi() = macSub(result.e123oi(), a.e1o(), b.e23i());
        result.e123oi() = mac(result.e123oi(), a.e2o(), b.e13i());
        result.e123oi() = mac(result.e123oi(), a.e12o(), b.e3i());
        result.e123oi() = macSub(result.e123oi(), a.e3o(), b.e12i());
        result.e123oi() = macSub(result.e123oi(), a.e13o(), b.e2i());
        result.e123oi() = mac(result.e123oi(), a.e23o(), b.e1i());
        result.e123oi() = mac(result.e123oi(), a.e123o(), b.ei());
        result.e123oi() = mac(result.e123oi(), a.ei(), b.e123o());
        result.e123oi() = mac(result.e123oi(), a.e1i(), b.e23o());
        result.e123oi() = macSub(result.e123oi(), a.e2i(), b.e13o());
        result.e123oi() = macSub(result.e123oi(), a.e12i(), b.e3o());
        result.e123oi() = mac(result.e123oi(), a.e3i(), b.e12o());
        result.e123oi() = mac(result.e123oi(), a.e13i(), b.e2o());
        result.e123oi() = macSub(result.e123oi(), a.e23i(), b.e1o());
        result.e123oi() = macSub(result.e123oi(), a.e123i(), b.eo());
        result.e123oi() = macSub(result.e123oi(), a.eoi(), b.e123());
        result.e123oi() = macSub(result.e123oi(), a.e1oi(), b.e23());
        result.e123oi() = mac(result.e123oi(), a.e2oi(), b.e13());
        result.e123oi() = mac(result.e123oi(), a.e12oi(), b.e3());
        result.e123oi() = macSub(result.e123oi(), a.e3oi(), b.e12());
        result.e123oi() = macSub(result.e123oi(), a.e13oi(), b.e2());
        result.e123oi() = mac(result.e123oi(), a.e23oi(), b.e1());
        result.e123oi() = mac(result.e123oi(), a.e123oi(), b.scalar());
        
        return result;
    }
    
    CgaMultivector dotProduct(CgaMultivector& b) 
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

        result.scalar() = 0;
        result.scalar() = mac(result.scalar(), a.scalar(), b.scalar());
        result.scalar() = mac(result.scalar(), a.e1(), b.e1());
        result.scalar() = mac(result.scalar(), a.e2(), b.e2());
        result.scalar() = macSub(result.scalar(), a.e12(), b.e12());
        result.scalar() = mac(result.scalar(), a.e3(), b.e3());
        result.scalar() = macSub(result.scalar(), a.e13(), b.e13());
        result.scalar() = macSub(result.scalar(), a.e23(), b.e23());
        result.scalar() = macSub(result.scalar(), a.e123(), b.e123());
        result.scalar() = macSub(result.scalar(), a.eo(), b.ei());
        result.scalar() = mac(result.scalar(), a.e1o(), b.e1i());
        result.scalar() = mac(result.scalar(), a.e2o(), b.e2i());
        result.scalar() = mac(result.scalar(), a.e12o(), b.e12i());
        result.scalar() = mac(result.scalar(), a.e3o(), b.e3i());
        result.scalar() = mac(result.scalar(), a.e13o(), b.e13i());
        result.scalar() = mac(result.scalar(), a.e23o(), b.e23i());
        result.scalar() = macSub(result.scalar(), a.e123o(), b.e123i());
        result.scalar() = macSub(result.scalar(), a.ei(), b.eo());
        result.scalar() = mac(result.scalar(), a.e1i(), b.e1o());
        result.scalar() = mac(result.scalar(), a.e2i(), b.e2o());
        result.scalar() = mac(result.scalar(), a.e12i(), b.e12o());
        result.scalar() = mac(result.scalar(), a.e3i(), b.e3o());
        result.scalar() = mac(result.scalar(), a.e13i(), b.e13o());
        result.scalar() = mac(result.scalar(), a.e23i(), b.e23o());
        result.scalar() = macSub(result.scalar(), a.e123i(), b.e123o());
        result.scalar() = mac(result.scalar(), a.eoi(), b.eoi());
        result.scalar() = mac(result.scalar(), a.e1oi(), b.e1oi());
        result.scalar() = mac(result.scalar(), a.e2oi(), b.e2oi());
        result.scalar() = macSub(result.scalar(), a.e12oi(), b.e12oi());
        result.scalar() = mac(result.scalar(), a.e3oi(), b.e3oi());
        result.scalar() = macSub(result.scalar(), a.e13oi(), b.e13oi());
        result.scalar() = macSub(result.scalar(), a.e23oi(), b.e23oi());
        result.scalar() = macSub(result.scalar(), a.e123oi(), b.e123oi());

        result.e1() = 0;
        result.e1() = mac(result.e1(), a.scalar(), b.e1());
        result.e1() = mac(result.e1(), a.e1(), b.scalar());
        result.e1() = macSub(result.e1(), a.e2(), b.e12());
        result.e1() = mac(result.e1(), a.e12(), b.e2());
        result.e1() = macSub(result.e1(), a.e3(), b.e13());
        result.e1() = mac(result.e1(), a.e13(), b.e3());
        result.e1() = macSub(result.e1(), a.e23(), b.e123());
        result.e1() = macSub(result.e1(), a.e123(), b.e23());
        result.e1() = mac(result.e1(), a.eo(), b.e1i());
        result.e1() = macSub(result.e1(), a.e1o(), b.ei());
        result.e1() = mac(result.e1(), a.e2o(), b.e12i());
        result.e1() = mac(result.e1(), a.e12o(), b.e2i());
        result.e1() = mac(result.e1(), a.e3o(), b.e13i());
        result.e1() = mac(result.e1(), a.e13o(), b.e3i());
        result.e1() = macSub(result.e1(), a.e23o(), b.e123i());
        result.e1() = mac(result.e1(), a.e123o(), b.e23i());
        result.e1() = mac(result.e1(), a.ei(), b.e1o());
        result.e1() = macSub(result.e1(), a.e1i(), b.eo());
        result.e1() = mac(result.e1(), a.e2i(), b.e12o());
        result.e1() = mac(result.e1(), a.e12i(), b.e2o());
        result.e1() = mac(result.e1(), a.e3i(), b.e13o());
        result.e1() = mac(result.e1(), a.e13i(), b.e3o());
        result.e1() = macSub(result.e1(), a.e23i(), b.e123o());
        result.e1() = mac(result.e1(), a.e123i(), b.e23o());
        result.e1() = macSub(result.e1(), a.eoi(), b.e1());
        result.e1() = mac(result.e1(), a.eoi(), b.e1oi());
        result.e1() = mac(result.e1(), a.e1oi(), b.eoi());
        result.e1() = mac(result.e1(), a.e2oi(), b.e12());
        result.e1() = macSub(result.e1(), a.e2oi(), b.e12oi());
        result.e1() = mac(result.e1(), a.e12oi(), b.e2oi());
        result.e1() = mac(result.e1(), a.e3oi(), b.e13());
        result.e1() = macSub(result.e1(), a.e3oi(), b.e13oi());
        result.e1() = mac(result.e1(), a.e13oi(), b.e3oi());
        result.e1() = mac(result.e1(), a.e23oi(), b.e123());
        result.e1() = macSub(result.e1(), a.e23oi(), b.e123oi());
        result.e1() = macSub(result.e1(), a.e123oi(), b.e23oi());

        result.e2() = 0;
        result.e2() = mac(result.e2(), a.scalar(), b.e2());
        result.e2() = mac(result.e2(), a.e1(), b.e12());
        result.e2() = mac(result.e2(), a.e2(), b.scalar());
        result.e2() = macSub(result.e2(), a.e12(), b.e1());
        result.e2() = macSub(result.e2(), a.e3(), b.e23());
        result.e2() = mac(result.e2(), a.e13(), b.e123());
        result.e2() = mac(result.e2(), a.e23(), b.e3());
        result.e2() = mac(result.e2(), a.e123(), b.e13());
        result.e2() = mac(result.e2(), a.eo(), b.e2i());
        result.e2() = macSub(result.e2(), a.e1o(), b.e12i());
        result.e2() = macSub(result.e2(), a.e2o(), b.ei());
        result.e2() = macSub(result.e2(), a.e12o(), b.e1i());
        result.e2() = mac(result.e2(), a.e3o(), b.e23i());
        result.e2() = mac(result.e2(), a.e13o(), b.e123i());
        result.e2() = mac(result.e2(), a.e23o(), b.e3i());
        result.e2() = macSub(result.e2(), a.e123o(), b.e13i());
        result.e2() = mac(result.e2(), a.ei(), b.e2o());
        result.e2() = macSub(result.e2(), a.e1i(), b.e12o());
        result.e2() = macSub(result.e2(), a.e2i(), b.eo());
        result.e2() = macSub(result.e2(), a.e12i(), b.e1o());
        result.e2() = mac(result.e2(), a.e3i(), b.e23o());
        result.e2() = mac(result.e2(), a.e13i(), b.e123o());
        result.e2() = mac(result.e2(), a.e23i(), b.e3o());
        result.e2() = macSub(result.e2(), a.e123i(), b.e13o());
        result.e2() = macSub(result.e2(), a.eoi(), b.e2());
        result.e2() = mac(result.e2(), a.eoi(), b.e2oi());
        result.e2() = macSub(result.e2(), a.e1oi(), b.e12());
        result.e2() = mac(result.e2(), a.e1oi(), b.e12oi());
        result.e2() = mac(result.e2(), a.e2oi(), b.eoi());
        result.e2() = macSub(result.e2(), a.e12oi(), b.e1oi());
        result.e2() = mac(result.e2(), a.e3oi(), b.e23());
        result.e2() = macSub(result.e2(), a.e3oi(), b.e23oi());
        result.e2() = macSub(result.e2(), a.e13oi(), b.e123());
        result.e2() = mac(result.e2(), a.e13oi(), b.e123oi());
        result.e2() = mac(result.e2(), a.e23oi(), b.e3oi());
        result.e2() = mac(result.e2(), a.e123oi(), b.e13oi());

        result.e12() = 0;
        result.e12() = mac(result.e12(), a.scalar(), b.e12());
        result.e12() = mac(result.e12(), a.e12(), b.scalar());
        result.e12() = mac(result.e12(), a.e3(), b.e123());
        result.e12() = mac(result.e12(), a.e123(), b.e3());
        result.e12() = macSub(result.e12(), a.eo(), b.e12i());
        result.e12() = macSub(result.e12(), a.e12o(), b.ei());
        result.e12() = mac(result.e12(), a.e3o(), b.e123i());
        result.e12() = mac(result.e12(), a.e123o(), b.e3i());
        result.e12() = macSub(result.e12(), a.ei(), b.e12o());
        result.e12() = macSub(result.e12(), a.e12i(), b.eo());
        result.e12() = mac(result.e12(), a.e3i(), b.e123o());
        result.e12() = mac(result.e12(), a.e123i(), b.e3o());
        result.e12() = mac(result.e12(), a.eoi(), b.e12oi());
        result.e12() = macSub(result.e12(), a.e1oi(), b.e2());
        result.e12() = mac(result.e12(), a.e2oi(), b.e1());
        result.e12() = mac(result.e12(), a.e12oi(), b.eoi());
        result.e12() = mac(result.e12(), a.e3oi(), b.e123oi());
        result.e12() = mac(result.e12(), a.e13oi(), b.e23());
        result.e12() = macSub(result.e12(), a.e23oi(), b.e13());
        result.e12() = mac(result.e12(), a.e123oi(), b.e3oi());

        result.e3() = 0;
        result.e3() = mac(result.e3(), a.scalar(), b.e3());
        result.e3() = mac(result.e3(), a.e1(), b.e13());
        result.e3() = mac(result.e3(), a.e2(), b.e23());
        result.e3() = macSub(result.e3(), a.e12(), b.e123());
        result.e3() = mac(result.e3(), a.e3(), b.scalar());
        result.e3() = macSub(result.e3(), a.e13(), b.e1());
        result.e3() = macSub(result.e3(), a.e23(), b.e2());
        result.e3() = macSub(result.e3(), a.e123(), b.e12());
        result.e3() = mac(result.e3(), a.eo(), b.e3i());
        result.e3() = macSub(result.e3(), a.e1o(), b.e13i());
        result.e3() = macSub(result.e3(), a.e2o(), b.e23i());
        result.e3() = macSub(result.e3(), a.e12o(), b.e123i());
        result.e3() = macSub(result.e3(), a.e3o(), b.ei());
        result.e3() = macSub(result.e3(), a.e13o(), b.e1i());
        result.e3() = macSub(result.e3(), a.e23o(), b.e2i());
        result.e3() = mac(result.e3(), a.e123o(), b.e12i());
        result.e3() = mac(result.e3(), a.ei(), b.e3o());
        result.e3() = macSub(result.e3(), a.e1i(), b.e13o());
        result.e3() = macSub(result.e3(), a.e2i(), b.e23o());
        result.e3() = macSub(result.e3(), a.e12i(), b.e123o());
        result.e3() = macSub(result.e3(), a.e3i(), b.eo());
        result.e3() = macSub(result.e3(), a.e13i(), b.e1o());
        result.e3() = macSub(result.e3(), a.e23i(), b.e2o());
        result.e3() = mac(result.e3(), a.e123i(), b.e12o());
        result.e3() = macSub(result.e3(), a.eoi(), b.e3());
        result.e3() = mac(result.e3(), a.eoi(), b.e3oi());
        result.e3() = macSub(result.e3(), a.e1oi(), b.e13());
        result.e3() = mac(result.e3(), a.e1oi(), b.e13oi());
        result.e3() = macSub(result.e3(), a.e2oi(), b.e23());
        result.e3() = mac(result.e3(), a.e2oi(), b.e23oi());
        result.e3() = mac(result.e3(), a.e12oi(), b.e123());
        result.e3() = macSub(result.e3(), a.e12oi(), b.e123oi());
        result.e3() = mac(result.e3(), a.e3oi(), b.eoi());
        result.e3() = macSub(result.e3(), a.e13oi(), b.e1oi());
        result.e3() = macSub(result.e3(), a.e23oi(), b.e2oi());
        result.e3() = macSub(result.e3(), a.e123oi(), b.e12oi());

        result.e13() = 0;
        result.e13() = mac(result.e13(), a.scalar(), b.e13());
        result.e13() = macSub(result.e13(), a.e2(), b.e123());
        result.e13() = mac(result.e13(), a.e13(), b.scalar());
        result.e13() = macSub(result.e13(), a.e123(), b.e2());
        result.e13() = macSub(result.e13(), a.eo(), b.e13i());
        result.e13() = macSub(result.e13(), a.e2o(), b.e123i());
        result.e13() = macSub(result.e13(), a.e13o(), b.ei());
        result.e13() = macSub(result.e13(), a.e123o(), b.e2i());
        result.e13() = macSub(result.e13(), a.ei(), b.e13o());
        result.e13() = macSub(result.e13(), a.e2i(), b.e123o());
        result.e13() = macSub(result.e13(), a.e13i(), b.eo());
        result.e13() = macSub(result.e13(), a.e123i(), b.e2o());
        result.e13() = mac(result.e13(), a.eoi(), b.e13oi());
        result.e13() = macSub(result.e13(), a.e1oi(), b.e3());
        result.e13() = macSub(result.e13(), a.e2oi(), b.e123oi());
        result.e13() = macSub(result.e13(), a.e12oi(), b.e23());
        result.e13() = mac(result.e13(), a.e3oi(), b.e1());
        result.e13() = mac(result.e13(), a.e13oi(), b.eoi());
        result.e13() = mac(result.e13(), a.e23oi(), b.e12());
        result.e13() = macSub(result.e13(), a.e123oi(), b.e2oi());

        result.e23() = 0;
        result.e23() = mac(result.e23(), a.scalar(), b.e23());
        result.e23() = mac(result.e23(), a.e1(), b.e123());
        result.e23() = mac(result.e23(), a.e23(), b.scalar());
        result.e23() = mac(result.e23(), a.e123(), b.e1());
        result.e23() = macSub(result.e23(), a.eo(), b.e23i());
        result.e23() = mac(result.e23(), a.e1o(), b.e123i());
        result.e23() = macSub(result.e23(), a.e23o(), b.ei());
        result.e23() = mac(result.e23(), a.e123o(), b.e1i());
        result.e23() = macSub(result.e23(), a.ei(), b.e23o());
        result.e23() = mac(result.e23(), a.e1i(), b.e123o());
        result.e23() = macSub(result.e23(), a.e23i(), b.eo());
        result.e23() = mac(result.e23(), a.e123i(), b.e1o());
        result.e23() = mac(result.e23(), a.eoi(), b.e23oi());
        result.e23() = mac(result.e23(), a.e1oi(), b.e123oi());
        result.e23() = macSub(result.e23(), a.e2oi(), b.e3());
        result.e23() = mac(result.e23(), a.e12oi(), b.e13());
        result.e23() = mac(result.e23(), a.e3oi(), b.e2());
        result.e23() = macSub(result.e23(), a.e13oi(), b.e12());
        result.e23() = mac(result.e23(), a.e23oi(), b.eoi());
        result.e23() = mac(result.e23(), a.e123oi(), b.e1oi());

        result.e123() = 0;
        result.e123() = mac(result.e123(), a.scalar(), b.e123());
        result.e123() = mac(result.e123(), a.e123(), b.scalar());
        result.e123() = mac(result.e123(), a.eo(), b.e123i());
        result.e123() = macSub(result.e123(), a.e123o(), b.ei());
        result.e123() = mac(result.e123(), a.ei(), b.e123o());
        result.e123() = macSub(result.e123(), a.e123i(), b.eo());
        result.e123() = mac(result.e123(), a.eoi(), b.e123oi());
        result.e123() = macSub(result.e123(), a.e12oi(), b.e3());
        result.e123() = mac(result.e123(), a.e13oi(), b.e2());
        result.e123() = macSub(result.e123(), a.e23oi(), b.e1());
        result.e123() = mac(result.e123(), a.e123oi(), b.eoi());

        result.eo() = 0;
        result.eo() = mac(result.eo(), a.scalar(), b.eo());
        result.eo() = mac(result.eo(), a.e1(), b.e1o());
        result.eo() = mac(result.eo(), a.e2(), b.e2o());
        result.eo() = macSub(result.eo(), a.e12(), b.e12o());
        result.eo() = mac(result.eo(), a.e3(), b.e3o());
        result.eo() = macSub(result.eo(), a.e13(), b.e13o());
        result.eo() = macSub(result.eo(), a.e23(), b.e23o());
        result.eo() = macSub(result.eo(), a.e123(), b.e123o());
        result.eo() = mac(result.eo(), a.eo(), b.scalar());
        result.eo() = mac(result.eo(), a.eo(), b.eoi());
        result.eo() = macSub(result.eo(), a.e1o(), b.e1());
        result.eo() = macSub(result.eo(), a.e1o(), b.e1oi());
        result.eo() = macSub(result.eo(), a.e2o(), b.e2());
        result.eo() = macSub(result.eo(), a.e2o(), b.e2oi());
        result.eo() = macSub(result.eo(), a.e12o(), b.e12());
        result.eo() = macSub(result.eo(), a.e12o(), b.e12oi());
        result.eo() = macSub(result.eo(), a.e3o(), b.e3());
        result.eo() = macSub(result.eo(), a.e3o(), b.e3oi());
        result.eo() = macSub(result.eo(), a.e13o(), b.e13());
        result.eo() = macSub(result.eo(), a.e13o(), b.e13oi());
        result.eo() = macSub(result.eo(), a.e23o(), b.e23());
        result.eo() = macSub(result.eo(), a.e23o(), b.e23oi());
        result.eo() = mac(result.eo(), a.e123o(), b.e123());
        result.eo() = mac(result.eo(), a.e123o(), b.e123oi());
        result.eo() = macSub(result.eo(), a.eoi(), b.eo());
        result.eo() = macSub(result.eo(), a.eoi(), b.eo());
        result.eo() = macSub(result.eo(), a.e1oi(), b.e1o());
        result.eo() = macSub(result.eo(), a.e1oi(), b.e1o());
        result.eo() = macSub(result.eo(), a.e2oi(), b.e2o());
        result.eo() = macSub(result.eo(), a.e2oi(), b.e2o());
        result.eo() = mac(result.eo(), a.e12oi(), b.e12o());
        result.eo() = mac(result.eo(), a.e12oi(), b.e12o());
        result.eo() = macSub(result.eo(), a.e3oi(), b.e3o());
        result.eo() = macSub(result.eo(), a.e3oi(), b.e3o());
        result.eo() = mac(result.eo(), a.e13oi(), b.e13o());
        result.eo() = mac(result.eo(), a.e13oi(), b.e13o());
        result.eo() = mac(result.eo(), a.e23oi(), b.e23o());
        result.eo() = mac(result.eo(), a.e23oi(), b.e23o());
        result.eo() = mac(result.eo(), a.e123oi(), b.e123o());
        result.eo() = mac(result.eo(), a.e123oi(), b.e123o());

        result.e1o() = 0;
        result.e1o() = mac(result.e1o(), a.scalar(), b.e1o());
        result.e1o() = macSub(result.e1o(), a.e2(), b.e12o());
        result.e1o() = macSub(result.e1o(), a.e3(), b.e13o());
        result.e1o() = macSub(result.e1o(), a.e23(), b.e123o());
        result.e1o() = macSub(result.e1o(), a.eo(), b.e1oi());
        result.e1o() = mac(result.e1o(), a.e1o(), b.scalar());
        result.e1o() = macSub(result.e1o(), a.e2o(), b.e12oi());
        result.e1o() = macSub(result.e1o(), a.e12o(), b.e2());
        result.e1o() = macSub(result.e1o(), a.e3o(), b.e13oi());
        result.e1o() = macSub(result.e1o(), a.e13o(), b.e3());
        result.e1o() = mac(result.e1o(), a.e23o(), b.e123oi());
        result.e1o() = macSub(result.e1o(), a.e123o(), b.e23());
        result.e1o() = macSub(result.e1o(), a.e1oi(), b.eo());
        result.e1o() = macSub(result.e1o(), a.e1oi(), b.eo());
        result.e1o() = macSub(result.e1o(), a.e12oi(), b.e2o());
        result.e1o() = macSub(result.e1o(), a.e12oi(), b.e2o());
        result.e1o() = macSub(result.e1o(), a.e13oi(), b.e3o());
        result.e1o() = macSub(result.e1o(), a.e13oi(), b.e3o());
        result.e1o() = mac(result.e1o(), a.e123oi(), b.e23o());
        result.e1o() = mac(result.e1o(), a.e123oi(), b.e23o());

        result.e2o() = 0;
        result.e2o() = mac(result.e2o(), a.scalar(), b.e2o());
        result.e2o() = mac(result.e2o(), a.e1(), b.e12o());
        result.e2o() = macSub(result.e2o(), a.e3(), b.e23o());
        result.e2o() = mac(result.e2o(), a.e13(), b.e123o());
        result.e2o() = macSub(result.e2o(), a.eo(), b.e2oi());
        result.e2o() = mac(result.e2o(), a.e1o(), b.e12oi());
        result.e2o() = mac(result.e2o(), a.e2o(), b.scalar());
        result.e2o() = mac(result.e2o(), a.e12o(), b.e1());
        result.e2o() = macSub(result.e2o(), a.e3o(), b.e23oi());
        result.e2o() = macSub(result.e2o(), a.e13o(), b.e123oi());
        result.e2o() = macSub(result.e2o(), a.e23o(), b.e3());
        result.e2o() = mac(result.e2o(), a.e123o(), b.e13());
        result.e2o() = macSub(result.e2o(), a.e2oi(), b.eo());
        result.e2o() = macSub(result.e2o(), a.e2oi(), b.eo());
        result.e2o() = mac(result.e2o(), a.e12oi(), b.e1o());
        result.e2o() = mac(result.e2o(), a.e12oi(), b.e1o());
        result.e2o() = macSub(result.e2o(), a.e23oi(), b.e3o());
        result.e2o() = macSub(result.e2o(), a.e23oi(), b.e3o());
        result.e2o() = macSub(result.e2o(), a.e123oi(), b.e13o());
        result.e2o() = macSub(result.e2o(), a.e123oi(), b.e13o());

        result.e12o() = 0;
        result.e12o() = mac(result.e12o(), a.scalar(), b.e12o());
        result.e12o() = mac(result.e12o(), a.e3(), b.e123o());
        result.e12o() = mac(result.e12o(), a.eo(), b.e12oi());
        result.e12o() = mac(result.e12o(), a.e12o(), b.scalar());
        result.e12o() = macSub(result.e12o(), a.e3o(), b.e123oi());
        result.e12o() = macSub(result.e12o(), a.e123o(), b.e3());
        result.e12o() = macSub(result.e12o(), a.e12oi(), b.eo());
        result.e12o() = macSub(result.e12o(), a.e12oi(), b.eo());
        result.e12o() = macSub(result.e12o(), a.e123oi(), b.e3o());
        result.e12o() = macSub(result.e12o(), a.e123oi(), b.e3o());

        result.e3o() = 0;
        result.e3o() = mac(result.e3o(), a.scalar(), b.e3o());
        result.e3o() = mac(result.e3o(), a.e1(), b.e13o());
        result.e3o() = mac(result.e3o(), a.e2(), b.e23o());
        result.e3o() = macSub(result.e3o(), a.e12(), b.e123o());
        result.e3o() = macSub(result.e3o(), a.eo(), b.e3oi());
        result.e3o() = mac(result.e3o(), a.e1o(), b.e13oi());
        result.e3o() = mac(result.e3o(), a.e2o(), b.e23oi());
        result.e3o() = mac(result.e3o(), a.e12o(), b.e123oi());
        result.e3o() = mac(result.e3o(), a.e3o(), b.scalar());
        result.e3o() = mac(result.e3o(), a.e13o(), b.e1());
        result.e3o() = mac(result.e3o(), a.e23o(), b.e2());
        result.e3o() = macSub(result.e3o(), a.e123o(), b.e12());
        result.e3o() = macSub(result.e3o(), a.e3oi(), b.eo());
        result.e3o() = macSub(result.e3o(), a.e3oi(), b.eo());
        result.e3o() = mac(result.e3o(), a.e13oi(), b.e1o());
        result.e3o() = mac(result.e3o(), a.e13oi(), b.e1o());
        result.e3o() = mac(result.e3o(), a.e23oi(), b.e2o());
        result.e3o() = mac(result.e3o(), a.e23oi(), b.e2o());
        result.e3o() = mac(result.e3o(), a.e123oi(), b.e12o());
        result.e3o() = mac(result.e3o(), a.e123oi(), b.e12o());

        result.e13o() = 0;
        result.e13o() = mac(result.e13o(), a.scalar(), b.e13o());
        result.e13o() = macSub(result.e13o(), a.e2(), b.e123o());
        result.e13o() = mac(result.e13o(), a.eo(), b.e13oi());
        result.e13o() = mac(result.e13o(), a.e2o(), b.e123oi());
        result.e13o() = mac(result.e13o(), a.e13o(), b.scalar());
        result.e13o() = mac(result.e13o(), a.e123o(), b.e2());
        result.e13o() = macSub(result.e13o(), a.e13oi(), b.eo());
        result.e13o() = macSub(result.e13o(), a.e13oi(), b.eo());
        result.e13o() = mac(result.e13o(), a.e123oi(), b.e2o());
        result.e13o() = mac(result.e13o(), a.e123oi(), b.e2o());

        result.e23o() = 0;
        result.e23o() = mac(result.e23o(), a.scalar(), b.e23o());
        result.e23o() = mac(result.e23o(), a.e1(), b.e123o());
        result.e23o() = mac(result.e23o(), a.eo(), b.e23oi());
        result.e23o() = macSub(result.e23o(), a.e1o(), b.e123oi());
        result.e23o() = mac(result.e23o(), a.e23o(), b.scalar());
        result.e23o() = macSub(result.e23o(), a.e123o(), b.e1());
        result.e23o() = macSub(result.e23o(), a.e23oi(), b.eo());
        result.e23o() = macSub(result.e23o(), a.e23oi(), b.eo());
        result.e23o() = macSub(result.e23o(), a.e123oi(), b.e1o());
        result.e23o() = macSub(result.e23o(), a.e123oi(), b.e1o());

        result.e123o() = 0;
        result.e123o() = mac(result.e123o(), a.scalar(), b.e123o());
        result.e123o() = macSub(result.e123o(), a.eo(), b.e123oi());
        result.e123o() = mac(result.e123o(), a.e123o(), b.scalar());
        result.e123o() = macSub(result.e123o(), a.e123oi(), b.eo());
        result.e123o() = macSub(result.e123o(), a.e123oi(), b.eo());

        result.ei() = 0;
        result.ei() = mac(result.ei(), a.scalar(), b.ei());
        result.ei() = mac(result.ei(), a.e1(), b.e1i());
        result.ei() = mac(result.ei(), a.e2(), b.e2i());
        result.ei() = macSub(result.ei(), a.e12(), b.e12i());
        result.ei() = mac(result.ei(), a.e3(), b.e3i());
        result.ei() = macSub(result.ei(), a.e13(), b.e13i());
        result.ei() = macSub(result.ei(), a.e23(), b.e23i());
        result.ei() = macSub(result.ei(), a.e123(), b.e123i());
        result.ei() = mac(result.ei(), a.ei(), b.scalar());
        result.ei() = macSub(result.ei(), a.ei(), b.eoi());
        result.ei() = macSub(result.ei(), a.e1i(), b.e1());
        result.ei() = mac(result.ei(), a.e1i(), b.e1oi());
        result.ei() = macSub(result.ei(), a.e2i(), b.e2());
        result.ei() = mac(result.ei(), a.e2i(), b.e2oi());
        result.ei() = macSub(result.ei(), a.e12i(), b.e12());
        result.ei() = mac(result.ei(), a.e12i(), b.e12oi());
        result.ei() = macSub(result.ei(), a.e3i(), b.e3());
        result.ei() = mac(result.ei(), a.e3i(), b.e3oi());
        result.ei() = macSub(result.ei(), a.e13i(), b.e13());
        result.ei() = mac(result.ei(), a.e13i(), b.e13oi());
        result.ei() = macSub(result.ei(), a.e23i(), b.e23());
        result.ei() = mac(result.ei(), a.e23i(), b.e23oi());
        result.ei() = mac(result.ei(), a.e123i(), b.e123());
        result.ei() = macSub(result.ei(), a.e123i(), b.e123oi());

        result.e1i() = 0;
        result.e1i() = mac(result.e1i(), a.scalar(), b.e1i());
        result.e1i() = macSub(result.e1i(), a.e2(), b.e12i());
        result.e1i() = macSub(result.e1i(), a.e3(), b.e13i());
        result.e1i() = macSub(result.e1i(), a.e23(), b.e123i());
        result.e1i() = mac(result.e1i(), a.ei(), b.e1oi());
        result.e1i() = mac(result.e1i(), a.e1i(), b.scalar());
        result.e1i() = mac(result.e1i(), a.e2i(), b.e12oi());
        result.e1i() = macSub(result.e1i(), a.e12i(), b.e2());
        result.e1i() = mac(result.e1i(), a.e3i(), b.e13oi());
        result.e1i() = macSub(result.e1i(), a.e13i(), b.e3());
        result.e1i() = macSub(result.e1i(), a.e23i(), b.e123oi());
        result.e1i() = macSub(result.e1i(), a.e123i(), b.e23());

        result.e2i() = 0;
        result.e2i() = mac(result.e2i(), a.scalar(), b.e2i());
        result.e2i() = mac(result.e2i(), a.e1(), b.e12i());
        result.e2i() = macSub(result.e2i(), a.e3(), b.e23i());
        result.e2i() = mac(result.e2i(), a.e13(), b.e123i());
        result.e2i() = mac(result.e2i(), a.ei(), b.e2oi());
        result.e2i() = macSub(result.e2i(), a.e1i(), b.e12oi());
        result.e2i() = mac(result.e2i(), a.e2i(), b.scalar());
        result.e2i() = mac(result.e2i(), a.e12i(), b.e1());
        result.e2i() = mac(result.e2i(), a.e3i(), b.e23oi());
        result.e2i() = mac(result.e2i(), a.e13i(), b.e123oi());
        result.e2i() = macSub(result.e2i(), a.e23i(), b.e3());
        result.e2i() = mac(result.e2i(), a.e123i(), b.e13());

        result.e12i() = 0;
        result.e12i() = mac(result.e12i(), a.scalar(), b.e12i());
        result.e12i() = mac(result.e12i(), a.e3(), b.e123i());
        result.e12i() = macSub(result.e12i(), a.ei(), b.e12oi());
        result.e12i() = mac(result.e12i(), a.e12i(), b.scalar());
        result.e12i() = mac(result.e12i(), a.e3i(), b.e123oi());
        result.e12i() = macSub(result.e12i(), a.e123i(), b.e3());

        result.e3i() = 0;
        result.e3i() = mac(result.e3i(), a.scalar(), b.e3i());
        result.e3i() = mac(result.e3i(), a.e1(), b.e13i());
        result.e3i() = mac(result.e3i(), a.e2(), b.e23i());
        result.e3i() = macSub(result.e3i(), a.e12(), b.e123i());
        result.e3i() = mac(result.e3i(), a.ei(), b.e3oi());
        result.e3i() = macSub(result.e3i(), a.e1i(), b.e13oi());
        result.e3i() = macSub(result.e3i(), a.e2i(), b.e23oi());
        result.e3i() = macSub(result.e3i(), a.e12i(), b.e123oi());
        result.e3i() = mac(result.e3i(), a.e3i(), b.scalar());
        result.e3i() = mac(result.e3i(), a.e13i(), b.e1());
        result.e3i() = mac(result.e3i(), a.e23i(), b.e2());
        result.e3i() = macSub(result.e3i(), a.e123i(), b.e12());

        result.e13i() = 0;
        result.e13i() = mac(result.e13i(), a.scalar(), b.e13i());
        result.e13i() = macSub(result.e13i(), a.e2(), b.e123i());
        result.e13i() = macSub(result.e13i(), a.ei(), b.e13oi());
        result.e13i() = macSub(result.e13i(), a.e2i(), b.e123oi());
        result.e13i() = mac(result.e13i(), a.e13i(), b.scalar());
        result.e13i() = mac(result.e13i(), a.e123i(), b.e2());

        result.e23i() = 0;
        result.e23i() = mac(result.e23i(), a.scalar(), b.e23i());
        result.e23i() = mac(result.e23i(), a.e1(), b.e123i());
        result.e23i() = macSub(result.e23i(), a.ei(), b.e23oi());
        result.e23i() = mac(result.e23i(), a.e1i(), b.e123oi());
        result.e23i() = mac(result.e23i(), a.e23i(), b.scalar());
        result.e23i() = macSub(result.e23i(), a.e123i(), b.e1());

        result.e123i() = 0;
        result.e123i() = mac(result.e123i(), a.scalar(), b.e123i());
        result.e123i() = mac(result.e123i(), a.ei(), b.e123oi());
        result.e123i() = mac(result.e123i(), a.e123i(), b.scalar());

        result.eoi() = 0;
        result.eoi() = mac(result.eoi(), a.scalar(), b.eoi());
        result.eoi() = mac(result.eoi(), a.e1(), b.e1oi());
        result.eoi() = mac(result.eoi(), a.e2(), b.e2oi());
        result.eoi() = macSub(result.eoi(), a.e12(), b.e12oi());
        result.eoi() = mac(result.eoi(), a.e3(), b.e3oi());
        result.eoi() = macSub(result.eoi(), a.e13(), b.e13oi());
        result.eoi() = macSub(result.eoi(), a.e23(), b.e23oi());
        result.eoi() = macSub(result.eoi(), a.e123(), b.e123oi());
        result.eoi() = mac(result.eoi(), a.eoi(), b.scalar());
        result.eoi() = mac(result.eoi(), a.e1oi(), b.e1());
        result.eoi() = mac(result.eoi(), a.e2oi(), b.e2());
        result.eoi() = macSub(result.eoi(), a.e12oi(), b.e12());
        result.eoi() = mac(result.eoi(), a.e3oi(), b.e3());
        result.eoi() = macSub(result.eoi(), a.e13oi(), b.e13());
        result.eoi() = macSub(result.eoi(), a.e23oi(), b.e23());
        result.eoi() = macSub(result.eoi(), a.e123oi(), b.e123());

        result.e1oi() = 0;
        result.e1oi() = mac(result.e1oi(), a.scalar(), b.e1oi());
        result.e1oi() = macSub(result.e1oi(), a.e2(), b.e12oi());
        result.e1oi() = macSub(result.e1oi(), a.e3(), b.e13oi());
        result.e1oi() = macSub(result.e1oi(), a.e23(), b.e123oi());
        result.e1oi() = mac(result.e1oi(), a.e1oi(), b.scalar());
        result.e1oi() = mac(result.e1oi(), a.e12oi(), b.e2());
        result.e1oi() = mac(result.e1oi(), a.e13oi(), b.e3());
        result.e1oi() = macSub(result.e1oi(), a.e123oi(), b.e23());

        result.e2oi() = 0;
        result.e2oi() = mac(result.e2oi(), a.scalar(), b.e2oi());
        result.e2oi() = mac(result.e2oi(), a.e1(), b.e12oi());
        result.e2oi() = macSub(result.e2oi(), a.e3(), b.e23oi());
        result.e2oi() = mac(result.e2oi(), a.e13(), b.e123oi());
        result.e2oi() = mac(result.e2oi(), a.e2oi(), b.scalar());
        result.e2oi() = macSub(result.e2oi(), a.e12oi(), b.e1());
        result.e2oi() = mac(result.e2oi(), a.e23oi(), b.e3());
        result.e2oi() = mac(result.e2oi(), a.e123oi(), b.e13());

        result.e12oi() = 0;
        result.e12oi() = mac(result.e12oi(), a.scalar(), b.e12oi());
        result.e12oi() = mac(result.e12oi(), a.e3(), b.e123oi());
        result.e12oi() = mac(result.e12oi(), a.e12oi(), b.scalar());
        result.e12oi() = mac(result.e12oi(), a.e123oi(), b.e3());

        result.e3oi() = 0;
        result.e3oi() = mac(result.e3oi(), a.scalar(), b.e3oi());
        result.e3oi() = mac(result.e3oi(), a.e1(), b.e13oi());
        result.e3oi() = mac(result.e3oi(), a.e2(), b.e23oi());
        result.e3oi() = macSub(result.e3oi(), a.e12(), b.e123oi());
        result.e3oi() = mac(result.e3oi(), a.e3oi(), b.scalar());
        result.e3oi() = macSub(result.e3oi(), a.e13oi(), b.e1());
        result.e3oi() = macSub(result.e3oi(), a.e23oi(), b.e2());
        result.e3oi() = macSub(result.e3oi(), a.e123oi(), b.e12());

        result.e13oi() = 0;
        result.e13oi() = mac(result.e13oi(), a.scalar(), b.e13oi());
        result.e13oi() = macSub(result.e13oi(), a.e2(), b.e123oi());
        result.e13oi() = mac(result.e13oi(), a.e13oi(), b.scalar());
        result.e13oi() = macSub(result.e13oi(), a.e123oi(), b.e2());

        result.e23oi() = 0;
        result.e23oi() = mac(result.e23oi(), a.scalar(), b.e23oi());
        result.e23oi() = mac(result.e23oi(), a.e1(), b.e123oi());
        result.e23oi() = mac(result.e23oi(), a.e23oi(), b.scalar());
        result.e23oi() = mac(result.e23oi(), a.e123oi(), b.e1());

        result.e123oi() = 0;
        result.e123oi() = mac(result.e123oi(), a.scalar(), b.e123oi());
        result.e123oi() = mac(result.e123oi(), a.e123oi(), b.scalar());

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
        result.e23oi()  = e1();
        result.e13oi()  = FixedPointQ511::negQ511(e2());
        result.e12oi()  = e3();
        result.e3oi()   = FixedPointQ511::negQ511(eo());
        result.e2oi()   = ei();
        result.e1oi()   = FixedPointQ511::negQ511(e12());
        result.eoi()    = e13();
        result.e3i()    = FixedPointQ511::negQ511(e23());
        result.e2i()    = e1o();
        result.e1i()    = FixedPointQ511::negQ511(e2o());
        result.ei()     = e3o();
        result.e3o()    = e1i();
        result.e2o()    = FixedPointQ511::negQ511(e2i());
        result.e1o()    = e3i();
        result.eo()     = FixedPointQ511::negQ511(eoi());
        result.e23()    = FixedPointQ511::negQ511(e1oi());
        result.e13()    = e2oi();
        result.e12()    = FixedPointQ511::negQ511(e3oi());
        result.e3()     = e12oi();
        result.e2()     = FixedPointQ511::negQ511(e13oi());
        result.e1()     = e23oi();
        result.scalar() = e123oi();
        
        return result;
    }
    
    int16_t norm() 
    {
        auto mac = [](int16_t acc, int16_t x, int16_t y) -> int16_t 
        {
            return FixedPointQ511::addQ511(acc, FixedPointQ511::mulQ511(x, y));
        };
        
        int16_t acc = 0;
        CgaMultivector& a = *this;

        acc = mac(acc, a.scalar(), a.scalar());
        acc = mac(acc, a.e1(), a.e1());
        acc = mac(acc, a.e2(), a.e2());
        acc = mac(acc, a.e12(), a.e12());
        acc = mac(acc, a.e3(), a.e3());
        acc = mac(acc, a.e13(), a.e13());
        acc = mac(acc, a.e23(), a.e23());
        acc = mac(acc, a.e123(), a.e123());
        acc = mac(acc, a.eo(), a.eo());
        acc = mac(acc, a.e1o(), a.e1o());
        acc = mac(acc, a.e2o(), a.e2o());
        acc = mac(acc, a.e12o(), a.e12o());
        acc = mac(acc, a.e3o(), a.e3o());
        acc = mac(acc, a.e13o(), a.e13o());
        acc = mac(acc, a.e23o(), a.e23o());
        acc = mac(acc, a.e123o(), a.e123o());
        acc = mac(acc, a.ei(), a.ei());
        acc = mac(acc, a.e1i(), a.e1i());
        acc = mac(acc, a.e2i(), a.e2i());
        acc = mac(acc, a.e12i(), a.e12i());
        acc = mac(acc, a.e3i(), a.e3i());
        acc = mac(acc, a.e13i(), a.e13i());
        acc = mac(acc, a.e23i(), a.e23i());
        acc = mac(acc, a.e123i(), a.e123i());
        acc = mac(acc, a.eoi(), a.eoi());
        acc = mac(acc, a.e1oi(), a.e1oi());
        acc = mac(acc, a.e2oi(), a.e2oi());
        acc = mac(acc, a.e12oi(), a.e12oi());
        acc = mac(acc, a.e3oi(), a.e3oi());
        acc = mac(acc, a.e13oi(), a.e13oi());
        acc = mac(acc, a.e23oi(), a.e23oi());
        acc = mac(acc, a.e123oi(), a.e123oi());

        return acc;
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
            int op = 5;//rng() % 8;
            
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
