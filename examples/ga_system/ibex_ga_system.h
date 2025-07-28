// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef IBEX_GA_SYSTEM_H_
#define IBEX_GA_SYSTEM_H_

#include <memory>
#include <string>
#include <vector>

#include "ibex_simple_system.h"

/**
 * Ibex GA System simulation class
 * 
 * Extends the basic Ibex simple system with Geometric Algebra coprocessor
 * functionality and specialized debugging/monitoring capabilities.
 */
class ibex_ga_system : public ibex_simple_system {
 public:
  /**
   * Constructor
   * @param name Name of the top-level module
   */
  ibex_ga_system(const char *name);

  /**
   * Destructor
   */
  ~ibex_ga_system();

  /**
   * Main simulation entry point
   * @param argc Command line argument count
   * @param argv Command line arguments
   * @return Exit code
   */
  int main(int argc, char **argv);

 protected:
  /**
   * Initialize GA-specific monitoring
   */
  void init_ga_monitoring();

  /**
   * Print GA performance statistics
   */
  void print_ga_stats();

  /**
   * Process GA debug commands
   * @param cmd Debug command string
   */
  void process_ga_debug_cmd(const std::string& cmd);

 private:
  // GA performance counters
  uint32_t ga_ops_total_;
  uint32_t ga_ops_add_;
  uint32_t ga_ops_mul_;
  uint32_t ga_ops_geometric_;
  uint32_t ga_cycles_busy_;
  uint32_t ga_stalls_;

  // GA debug state
  bool ga_debug_enabled_;
  std::vector<uint32_t> ga_register_dump_;
};

#endif  // IBEX_GA_SYSTEM_H_
