// Copyright lowRISC contributors.
// Copyright 2017 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * GA-Extended Package with constants used by Ibex + GA coprocessor
 * This file extends the original ibex_pkg.sv with GA-specific enums
 */

// Import the original ibex package
`include "ibex_pkg.sv"
import ga_pkg::*;  // Import GA-specific types

package ibex_pkg;

  // Re-export all original ibex_pkg contents
  export ibex_pkg::*;

  /////////////
  // GA Extended Opcodes //
  /////////////

  typedef enum logic [6:0] {
    // Original RISC-V opcodes
    OPCODE_LOAD     = 7'h03,
    OPCODE_MISC_MEM = 7'h0f,
    OPCODE_OP_IMM   = 7'h13,
    OPCODE_AUIPC    = 7'h17,
    OPCODE_STORE    = 7'h23,
    OPCODE_OP       = 7'h33,
    OPCODE_LUI      = 7'h37,
    OPCODE_BRANCH   = 7'h63,
    OPCODE_JALR     = 7'h67,
    OPCODE_JAL      = 7'h6f,
    OPCODE_SYSTEM   = 7'h73,
    
    // GA Custom opcodes (CUSTOM-0 through CUSTOM-3)
    OPCODE_GA_CUSTOM_0 = 7'h0B,  // custom-0 (main GA operations)
    OPCODE_GA_CUSTOM_1 = 7'h2B,  // custom-1 (extended GA operations)
    OPCODE_GA_CUSTOM_2 = 7'h5B,  // custom-2 (GA memory operations)
    OPCODE_GA_CUSTOM_3 = 7'h7B   // custom-3 (GA control/status)
  } opcode_e;

  ////////////////////
  // GA Extended ALU operations //
  ////////////////////

  typedef enum logic [6:0] {
    // Original ALU operations
    ALU_ADD,
    ALU_SUB,
    ALU_XOR,
    ALU_OR,
    ALU_AND,
    ALU_XNOR,
    ALU_ORN,
    ALU_ANDN,
    
    // Shifts
    ALU_SRA,
    ALU_SRL,
    ALU_SLL,
    
    // Comparisons
    ALU_LT,
    ALU_LTU,
    ALU_GE,
    ALU_GEU,
    ALU_EQ,
    ALU_NE,
    
    // GA-specific ALU operations
    ALU_GA_ADD,           // GA Addition
    ALU_GA_SUB,           // GA Subtraction  
    ALU_GA_GEOMETRIC,     // GA Geometric Product
    ALU_GA_WEDGE,         // GA Wedge (Outer) Product
    ALU_GA_DOT,           // GA Dot (Inner) Product
    ALU_GA_DUAL,          // GA Dual
    ALU_GA_REVERSE,       // GA Reverse
    ALU_GA_MAGNITUDE,     // GA Magnitude
    ALU_GA_NORMALIZE      // GA Normalize
  } alu_op_e;

  ////////////////////
  // GA Extended Register File Write Data Selection //
  ////////////////////

  typedef enum logic [1:0] {
    RF_WD_EX,       // Write data from execute stage
    RF_WD_CSR,      // Write data from CSR
    RF_WD_GA_ALU,   // Write data from GA ALU
    RF_WD_GA_LOAD   // Write data from GA register file load
  } rf_wd_sel_e;

  ////////////////////
  // GA Control Signals //
  ////////////////////

  typedef enum logic [2:0] {
    GA_OP_NONE,           // No GA operation
    GA_OP_ARITH,          // GA arithmetic operation
    GA_OP_LOAD_REG,       // Load from GA register file
    GA_OP_STORE_REG,      // Store to GA register file
    GA_OP_LOAD_MEM,       // Load GA data from memory
    GA_OP_STORE_MEM,      // Store GA data to memory
    GA_OP_STATUS,         // GA status/control operation
    GA_OP_CONFIG          // GA configuration operation
  } ga_op_sel_e;

  ////////////////////
  // GA Instruction Format //
  ////////////////////

  typedef struct packed {
    logic [6:0]  funct7;      // Function field 7 bits
    logic [4:0]  rs2;         // Source register 2
    logic [4:0]  rs1;         // Source register 1  
    logic [2:0]  funct3;      // Function field 3 bits
    logic [4:0]  rd;          // Destination register
    logic [6:0]  opcode;      // Opcode
  } ga_instr_r_t;

  typedef struct packed {
    logic [11:0] imm;         // Immediate value
    logic [4:0]  rs1;         // Source register 1
    logic [2:0]  funct3;      // Function field 3 bits
    logic [4:0]  rd;          // Destination register
    logic [6:0]  opcode;      // Opcode
  } ga_instr_i_t;

  ////////////////////
  // GA Function Codes //
  ////////////////////

  // GA CUSTOM-0 function codes (7'h0B)
  typedef enum logic [2:0] {
    GA_FUNCT3_ADD     = 3'b000,  // GA Addition
    GA_FUNCT3_SUB     = 3'b001,  // GA Subtraction
    GA_FUNCT3_MUL     = 3'b010,  // GA Geometric Product
    GA_FUNCT3_WEDGE   = 3'b011,  // GA Wedge Product
    GA_FUNCT3_DOT     = 3'b100,  // GA Dot Product
    GA_FUNCT3_DUAL    = 3'b101,  // GA Dual
    GA_FUNCT3_REV     = 3'b110,  // GA Reverse
    GA_FUNCT3_NORM    = 3'b111   // GA Normalize
  } ga_funct3_arith_e;

  // GA CUSTOM-1 function codes (7'h2B) - Register file operations
  typedef enum logic [2:0] {
    GA_FUNCT3_LOAD_REG  = 3'b000,  // Load from GA register file
    GA_FUNCT3_STORE_REG = 3'b001,  // Store to GA register file
    GA_FUNCT3_MOVE_REG  = 3'b010,  // Move between GA registers
    GA_FUNCT3_SWAP_REG  = 3'b011,  // Swap GA registers
    GA_FUNCT3_COPY_REG  = 3'b100,  // Copy GA register
    GA_FUNCT3_CLEAR_REG = 3'b101,  // Clear GA register
    GA_FUNCT3_RESERVED1 = 3'b110,  // Reserved
    GA_FUNCT3_RESERVED2 = 3'b111   // Reserved
  } ga_funct3_reg_e;

  // GA CUSTOM-2 function codes (7'h5B) - Memory operations
  typedef enum logic [2:0] {
    GA_FUNCT3_LOAD_MEM   = 3'b000,  // Load multivector from memory
    GA_FUNCT3_STORE_MEM  = 3'b001,  // Store multivector to memory
    GA_FUNCT3_LOAD_VECTOR= 3'b010,  // Load vector from memory
    GA_FUNCT3_STORE_VECTOR=3'b011,  // Store vector to memory
    GA_FUNCT3_LOAD_SCALAR= 3'b100,  // Load scalar from memory
    GA_FUNCT3_STORE_SCALAR=3'b101,  // Store scalar to memory
    GA_FUNCT3_RESERVED3  = 3'b110,  // Reserved
    GA_FUNCT3_RESERVED4  = 3'b111   // Reserved
  } ga_funct3_mem_e;

  // GA CUSTOM-3 function codes (7'h7B) - Control/Status
  typedef enum logic [2:0] {
    GA_FUNCT3_CONFIG     = 3'b000,  // Configure GA coprocessor
    GA_FUNCT3_STATUS     = 3'b001,  // Read GA status
    GA_FUNCT3_RESET      = 3'b010,  // Reset GA coprocessor
    GA_FUNCT3_ENABLE     = 3'b011,  // Enable GA coprocessor
    GA_FUNCT3_DISABLE    = 3'b100,  // Disable GA coprocessor
    GA_FUNCT3_FLUSH      = 3'b101,  // Flush GA pipeline
    GA_FUNCT3_RESERVED5  = 3'b110,  // Reserved
    GA_FUNCT3_RESERVED6  = 3'b111   // Reserved
  } ga_funct3_ctrl_e;

endpackage
