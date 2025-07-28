// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "Vibex_ga_system.h"
#include "verilated.h"
#include "verilated_fst_c.h"
#include <iostream>

int main(int argc, char **argv) {
  // Initialize Verilator
  Verilated::commandArgs(argc, argv);
  
  // Create instance of GA system model
  Vibex_ga_system* ga_system = new Vibex_ga_system("ga_system");
  
  // Enable tracing
  Verilated::traceEverOn(true);
  VerilatedFstC* tfp = new VerilatedFstC;
  ga_system->trace(tfp, 99);
  tfp->open("ga_system.fst");
  
  // Simple test: reset and run for a few cycles
  int cycle_count = 0;
  const int max_cycles = 1000;
  
  // Initialize inputs
  ga_system->clk_i = 0;
  ga_system->rst_ni = 0;
  ga_system->instr_gnt_i = 1;
  ga_system->instr_rvalid_i = 0;
  ga_system->instr_err_i = 0;
  ga_system->data_gnt_i = 1;
  ga_system->data_rvalid_i = 0;
  ga_system->data_err_i = 0;
  ga_system->irq_software_i = 0;
  ga_system->irq_timer_i = 0;
  ga_system->irq_external_i = 0;
  ga_system->irq_nm_i = 0;
  ga_system->debug_req_i = 0;
  ga_system->fetch_enable_i = 0xA;  // MuBi4True
  
  // Reset cycle
  for (int i = 0; i < 10; i++) {
    ga_system->clk_i = !ga_system->clk_i;
    ga_system->eval();
    tfp->dump(cycle_count++);
  }
  
  // Release reset
  ga_system->rst_ni = 1;
  
  // Run simulation
  while (cycle_count < max_cycles && !Verilated::gotFinish()) {
    ga_system->clk_i = !ga_system->clk_i;
    
    // Respond to instruction requests (simple memory behavior)
    if (ga_system->instr_req_o && ga_system->clk_i) {
      ga_system->instr_rvalid_i = 1;
      ga_system->instr_rdata_i = 0x00000013; // NOP instruction
    } else {
      ga_system->instr_rvalid_i = 0;
    }
    
    ga_system->eval();
    tfp->dump(cycle_count++);
  }
  
  // Clean up
  tfp->close();
  delete tfp;
  delete ga_system;
  
  std::cout << "GA system simulation completed after " << cycle_count/2 << " clock cycles" << std::endl;
  return 0;
}
