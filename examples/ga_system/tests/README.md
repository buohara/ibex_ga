# GA Coprocessor Test Suite

This directory contains a comprehensive test suite for the GA (Geometric Algebra) coprocessor, designed to verify the correctness of all GA operations defined in `ga_pkg.sv`.

## Build System Overview

The GA system uses a comprehensive hardware verification approach with multi-stage build process:

### Build Order:
1. **Build Versor Library** - Compiles the Versor Conformal Geometric Algebra C++ library
2. **Compile Test Generator** - Builds the C++ test vector generator with Versor linking
3. **Generate Test Vectors** - Uses Versor as golden reference to create comprehensive test vectors  
4. **Build Ibex+GA System** - FuseSoC builds the Ibex CPU with GA coprocessor for Verilator simulation
5. **Build Test Suite** - FuseSoC builds unit and integration testbenches with test vectors

This approach provides **complete hardware verification** without requiring software integration testing.

### Command Flow:
```bash
# Complete build with testbenches (recommended)
make build-ga-system
```

This executes:
```bash
cd examples/ga_system/versor && ./build.sh --math          # Build Versor CGA library
cd examples/ga_system/tests && make generate_test_vectors  # Compile C++ generator
cd examples/ga_system/tests && make test_vectors           # Generate test vectors  
fusesoc run --target=sim --setup --build lowrisc:ibex:ibex_ga_system        # Build simulation
fusesoc run --target=unit_test --setup --build lowrisc:ibex:ga_test_suite   # Build unit tests
fusesoc run --target=integration_test --setup --build lowrisc:ibex:ga_test_suite  # Build integration tests
```

### Running Tests:
```bash
# Run complete hardware test suite
make run-ga-tests

# Run with coverage analysis for synthesis confidence
make ga-test-coverage
```

## Hardware-First Verification Approach

This test suite focuses on **comprehensive hardware verification** using:

- **Mathematical Golden Reference**: Versor CGA library provides exact expected results
- **Comprehensive Test Coverage**: Corner cases + thousands of random test vectors  
- **Direct Hardware Testing**: SystemVerilog testbenches directly stimulate GA coprocessor
- **Synthesis-Ready Verification**: Thorough testing ensures FPGA synthesis confidence

Perfect for hardware designers who need to verify GA coprocessor functionality before FPGA deployment.

## Quick Start

### Full Build (Recommended):
```bash
# From ibex root directory
make build-ga-system
```

### Individual Components:
```bash
# Just generate test vectors (from tests/ directory)
make test_vectors

# Just build Versor library (from versor/ directory) 
./build.sh --math
```

## Using Versor for Golden Reference

The test vector generator uses [Versor](https://github.com/wolftype/versor) Conformal Geometric Algebra library for exact GA calculations as the golden reference.

### How it Works:

1. **Versor Library Build**: The `build-ga-system` target first builds the Versor C++ library
2. **CGA Test Generation**: Our C++ generator uses Versor's CGA types and operations
3. **Golden Reference**: Versor provides mathematically correct results for verification
4. **Fallback Mode**: If Versor isn't built, uses simplified GA implementation

### Test Vector Generation:

```bash
# Automatic (part of build-ga-system)
make build-ga-system

# Manual (from tests/ directory)  
make test_vectors
```

### Versor Integration Details:

- **CGA Support**: Uses 5D Conformal Geometric Algebra for 3D + rotation/translation
- **6-DOF Robotics**: Perfect for robotic applications requiring combined rotation/translation
- **Corner Cases**: Includes rotors, translators, motors, points, spheres, planes
- **High Precision**: Double-precision floating point for accurate golden reference

## Test Structure

### Files Generated:
- `vectors/ga_test_inputs.mem` - Input operand pairs (32-bit hex format)
- `vectors/ga_test_outputs.mem` - Expected results from golden reference
- `vectors/ga_test_control.mem` - GA operation codes
- `vectors/ga_test_debug.txt` - Human-readable debug information

### Test Coverage:
- **Corner Cases**: Zero, unit elements, infinity, NaN, etc.
- **Random Cases**: Thousands of randomized test vectors
- **All Operations**: ADD, SUB, MUL (geometric), WEDGE, DOT, REV, DUAL, NORM

### Testbenches:
- `rtl/tb_ga_operations.sv` - Unit tests for individual operations
- `rtl/tb_ga_coprocessor.sv` - Full integration tests with assertions

## GA Operations Tested

Based on `ga_funct_e` in `ga_pkg.sv`:

| Code | Operation | Description |
|------|-----------|-------------|
| 0x0  | ADD       | Geometric addition |
| 0x1  | SUB       | Geometric subtraction |
| 0x2  | MUL       | Geometric product |
| 0x3  | WEDGE     | Outer (wedge) product |
| 0x4  | DOT       | Inner (dot) product |
| 0x5  | DUAL      | Dual operation |
| 0x6  | REV       | Reverse operation |
| 0x7  | NORM      | Norm calculation |

## Advanced Usage

### Custom Test Generation:
```cpp
GATestVectorGenerator generator;
generator.generate_test_suite(5000);  // Generate 5000 random tests
```

### Verilator High-Performance Testing:
```bash
make verilator_tests
```

### Coverage Analysis:
```bash
make coverage
```

### Performance Benchmarking:
```bash
make benchmark
```

## Integration with FuseSoC

The test suite is also available as a FuseSoC core:

```bash
# Run unit tests
fusesoc run --target=unit_test lowrisc:ibex:ga_test_suite

# Run integration tests  
fusesoc run --target=integration_test lowrisc:ibex:ga_test_suite
```

## Assertion-Based Verification

The testbenches include comprehensive SystemVerilog assertions:

- **Protocol compliance** (request/response timing)
- **No spurious responses**
- **Timeout detection**
- **Busy flag consistency**
- **Function code bounds checking**

## Requirements

- **C++ compiler** with C++17 support
- **CMake** (for Versor library build)
- **SystemVerilog simulator** (Icarus Verilog, ModelSim, or Verilator)  
- **Versor library** (automatically built by `build-ga-system`)
- **FuseSoC** (for Ibex+GA system build)

## Troubleshooting

### Versor not built:
```
Warning: Versor not built - using simplified GA implementation
```
**Solution**: Run `make build-ga-system` from ibex root, or manually build Versor:
```bash
cd examples/ga_system/versor && ./build.sh --math
```

### CMake errors in Versor build:
```
CMake Error: ext/gtest does not contain CMakeLists.txt
```
**Solution**: This is expected - Versor's testing components are disabled for integration.

### Simulation errors:
```bash
# Check for RTL issues (from ibex root)
make lint
```

### Memory file not found:
```bash
# Regenerate test vectors (from tests/ directory)
make clean test_vectors
```

## File Structure

```
tests/
├── Makefile              # Build system
├── README.md             # This file
├── generate_test_vectors.cpp  # C++ test vector generator
├── ga_test_suite.core    # FuseSoC core definition
├── demo_test_generation.sh    # Quick demo script
├── vectors/              # Generated test vectors
│   ├── ga_test_inputs.mem
│   ├── ga_test_outputs.mem
│   ├── ga_test_control.mem
│   └── ga_test_debug.txt
└── rtl/                  # SystemVerilog testbenches
    ├── tb_ga_operations.sv
    └── tb_ga_coprocessor.sv
```
