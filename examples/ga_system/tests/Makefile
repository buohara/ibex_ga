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
CXXFLAGS = -std=c++17 -O0 -g3 -Wall -Wextra -DDEBUG

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
		$(CXX) $(CXXFLAGS) -o $@ $<; \
	fi

# Simulation configuration
RTL_DIR = ../rtl
TB_DIR = rtl
WAVES ?= 0

# Verilator flags with proper package includes and timing
VERILATOR_FLAGS = --cc --binary --build -Wall --top-module tb_ga_coprocessor
VERILATOR_FLAGS += +incdir+$(RTL_DIR) +incdir+$(TB_DIR)
VERILATOR_FLAGS += +incdir+../../../rtl
VERILATOR_FLAGS += -CFLAGS "-std=c++14" -Wno-UNUSED -Wno-UNDRIVEN
VERILATOR_FLAGS += --timing  # Enable timing for Verilator compatibility
VERILATOR_FLAGS += -Wno-DECLFILENAME -Wno-TIMESCALEMOD

ifeq ($(WAVES),1)
    VERILATOR_FLAGS += --trace
endif

# Main simulation target - fix duplicate package issue
simulate: test_vectors $(RTL_DIR)/*.sv $(TB_DIR)/tb_ga_coprocessor.sv
	@echo "Running Verilator simulation..."
	verilator $(VERILATOR_FLAGS) \
		../../../rtl/ibex_pkg.sv \
		$(RTL_DIR)/ga_pkg.sv \
		$(RTL_DIR)/ga_alu.sv \
		$(RTL_DIR)/ga_coprocessor.sv \
		$(RTL_DIR)/ga_register_file.sv \
		$(TB_DIR)/tb_ga_coprocessor.sv
	@echo "Executing simulation..."
	./obj_dir/Vtb_ga_coprocessor $(if $(filter 1,$(WAVES)),+WAVES)
	@echo ""
	@echo "=== Simulation Complete ==="
	@echo "Results: ga_test_verbose.log"
	@if [ -f ga_coprocessor_test.vcd ]; then \
		echo "Waveform: ga_coprocessor_test.vcd (view with: gtkwave ga_coprocessor_test.vcd)"; \
	fi

# Clean artifacts
clean:
	rm -rf obj_dir/
	rm -f *.log *.vcd
	rm -rf $(VECTORS_DIR)

# Help
help:
	@echo "Verilator Simulation:"
	@echo "  make simulate          - Run simulation"
	@echo "  make simulate WAVES=1  - Run with waveforms"
	@echo "  make clean            - Clean artifacts"
	@echo ""
	@echo "View waveforms: gtkwave ga_coprocessor_test.vcd"

.PHONY: all test_vectors clean clean_vectors clean_all help simulate
