# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Simple Makefile for GA test vector generation only
# Main SystemVerilog build is handled by FuseSoC via main Makefile

# Tools
CXX = g++

# Directories
VECTORS_DIR = vectors

# Compiler flags
CXXFLAGS = -std=c++17 -O2 -Wall -Wextra

# Versor configuration  
VERSOR_INCLUDE = ../versor/include
VERSOR_BUILD_DIR = ../versor/build

# Check if Versor is built
VERSOR_BUILT := $(shell test -f "$(VERSOR_BUILD_DIR)/libvsr.a" && echo "true" || echo "false")

# Default target - just generate test vectors
all: test_vectors

# Generate test vectors using Versor CGA as golden reference
test_vectors: $(VECTORS_DIR)/ga_test_inputs.mem

$(VECTORS_DIR)/ga_test_inputs.mem: generate_test_vectors
	@echo "Generating CGA test vectors..."
	@mkdir -p $(VECTORS_DIR)
	@./generate_test_vectors

generate_test_vectors: generate_test_vectors.cpp
	@echo "Compiling test vector generator..."
	@if [ "$(VERSOR_BUILT)" = "false" ]; then \
		echo "Warning: Versor not built - using simplified GA implementation"; \
		$(CXX) $(CXXFLAGS) -DUSE_SIMPLIFIED_GA -o $@ $<; \
	else \
		echo "Using Versor Conformal Geometric Algebra library"; \
		$(CXX) $(CXXFLAGS) -I$(VERSOR_INCLUDE) -L$(VERSOR_BUILD_DIR) -lvsr -o $@ $<; \
	fi

# Clean targets
clean:
	rm -f generate_test_vectors

clean_vectors:
	rm -rf $(VECTORS_DIR)

clean_all: clean clean_vectors

help:
	@echo "GA Test Vector Generator"
	@echo "======================="
	@echo ""
	@echo "This Makefile only handles test vector generation."
	@echo "Use the main Makefile's 'build-ga-system' target for full builds."
	@echo ""
	@echo "Targets:"
	@echo "  test_vectors     - Generate CGA test vectors using Versor"
	@echo "  clean           - Clean compiled generator"
	@echo "  clean_all       - Clean everything including vectors"
	@echo "  help            - Show this help"

.PHONY: all test_vectors clean clean_vectors clean_all help
