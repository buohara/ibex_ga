// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "ibex_ga_system.h"

#include <iostream>
#include <iomanip>
#include <sstream>

ibex_ga_system::ibex_ga_system(const char *name) 
    : ibex_simple_system(name),
      ga_ops_total_(0),
      ga_ops_add_(0),
      ga_ops_mul_(0),
      ga_ops_geometric_(0),
      ga_cycles_busy_(0),
      ga_stalls_(0),
      ga_debug_enabled_(false) {
  
  std::cout << "Initializing Ibex GA System: " << name << std::endl;
  init_ga_monitoring();
}

ibex_ga_system::~ibex_ga_system() {
  if (ga_debug_enabled_) {
    print_ga_stats();
  }
}

int ibex_ga_system::main(int argc, char **argv) {
  // Parse GA-specific command line arguments
  for (int i = 1; i < argc; i++) {
    std::string arg(argv[i]);
    
    if (arg == "--ga-debug") {
      ga_debug_enabled_ = true;
      std::cout << "GA debug mode enabled" << std::endl;
    } else if (arg == "--ga-stats") {
      // Enable performance statistics collection
      std::cout << "GA performance statistics enabled" << std::endl;
    } else if (arg.find("--ga-cmd=") == 0) {
      std::string cmd = arg.substr(9);
      process_ga_debug_cmd(cmd);
    }
  }

  // Call parent class main function
  int result = ibex_simple_system::main(argc, argv);
  
  // Print GA-specific results
  if (ga_debug_enabled_) {
    print_ga_stats();
  }
  
  return result;
}

void ibex_ga_system::init_ga_monitoring() {
  // Initialize GA register dump storage
  ga_register_dump_.resize(32, 0);
  
  std::cout << "GA monitoring initialized" << std::endl;
}

void ibex_ga_system::print_ga_stats() {
  std::cout << "\n=== GA Coprocessor Statistics ===" << std::endl;
  std::cout << "Total GA Operations:     " << std::setw(10) << ga_ops_total_ << std::endl;
  std::cout << "  Addition Operations:   " << std::setw(10) << ga_ops_add_ << std::endl;
  std::cout << "  Multiplication Ops:    " << std::setw(10) << ga_ops_mul_ << std::endl;
  std::cout << "  Geometric Product Ops: " << std::setw(10) << ga_ops_geometric_ << std::endl;
  std::cout << "Cycles GA Busy:          " << std::setw(10) << ga_cycles_busy_ << std::endl;
  std::cout << "Pipeline Stalls:         " << std::setw(10) << ga_stalls_ << std::endl;
  
  if (ga_ops_total_ > 0) {
    double efficiency = static_cast<double>(ga_ops_total_) / 
                       static_cast<double>(ga_cycles_busy_);
    std::cout << "GA Efficiency:           " << std::setw(10) << std::fixed 
              << std::setprecision(2) << efficiency << " ops/cycle" << std::endl;
  }
  
  std::cout << "=================================" << std::endl;
}

void ibex_ga_system::process_ga_debug_cmd(const std::string& cmd) {
  std::istringstream iss(cmd);
  std::string operation;
  iss >> operation;
  
  if (operation == "dump_regs") {
    std::cout << "GA Register Dump:" << std::endl;
    for (size_t i = 0; i < ga_register_dump_.size(); i++) {
      std::cout << "GA[" << std::setw(2) << i << "] = 0x" 
                << std::hex << std::setw(8) << std::setfill('0') 
                << ga_register_dump_[i] << std::dec << std::setfill(' ') << std::endl;
    }
  } else if (operation == "reset_stats") {
    ga_ops_total_ = 0;
    ga_ops_add_ = 0;
    ga_ops_mul_ = 0;
    ga_ops_geometric_ = 0;
    ga_cycles_busy_ = 0;
    ga_stalls_ = 0;
    std::cout << "GA statistics reset" << std::endl;
  } else if (operation == "help") {
    std::cout << "GA Debug Commands:" << std::endl;
    std::cout << "  dump_regs    - Dump GA register file" << std::endl;
    std::cout << "  reset_stats  - Reset performance counters" << std::endl;
    std::cout << "  help         - Show this help" << std::endl;
  } else {
    std::cout << "Unknown GA debug command: " << operation << std::endl;
    std::cout << "Use 'help' for available commands" << std::endl;
  }
}
