#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Quick test script to demonstrate GA coprocessor testing with Versor CGA

set -e

echo "GA Coprocessor Test Vector Generation Demo"
echo "=========================================="

# Check if we're in the right directory
if [ ! -f "generate_test_vectors.cpp" ]; then
    echo "Error: Please run from the tests directory"
    echo "Expected to find generate_test_vectors.cpp"
    exit 1
fi

# Check if Versor is built
echo "Checking Versor library..."
if [ -f "../versor/build/libvsr.a" ]; then
    echo "✓ Versor library found - using CGA implementation"
else
    echo "⚠ Versor library not found - will use simplified GA fallback"
    echo "  Run 'make build-ga-system' from ibex root to build Versor"
fi

# Generate test vectors
echo ""
echo "Generating test vectors with Versor CGA..."
make test_vectors

echo ""
echo "Generated test vector files:"
if [ -d "vectors" ]; then
    ls -la vectors/
    echo ""
    echo "Sample of generated test vectors:"
    echo "First 5 input/output pairs:"
    echo "Inputs (operand_a operand_b):"
    head -5 vectors/ga_test_inputs.mem 2>/dev/null || echo "No input file generated"
    echo ""
    echo "Expected outputs:"
    head -5 vectors/ga_test_outputs.mem 2>/dev/null || echo "No output file generated"
    echo ""
    echo "Operations:"
    head -5 vectors/ga_test_control.mem 2>/dev/null || echo "No control file generated"
else
    echo "Error: vectors directory not created"
    exit 1
fi

echo ""
echo "Test vector generation complete!"
echo ""
echo "Next steps:"
echo "  1. Run 'make build-ga-system' from ibex root for full system build"
echo "  2. Use generated vectors for SystemVerilog testbench verification"
echo "  3. Check vectors/ directory for .mem files ready for \$readmemh"
echo ""
echo "Note: The C++ generator uses Versor library for mathematically correct CGA operations"
