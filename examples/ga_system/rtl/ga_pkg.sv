// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Package with constants and types used by GA coprocessor
 */
package ga_pkg;

  import ibex_pkg::*;

  /////////////////////////
  // GA Operation Types  //
  /////////////////////////

  // GA function codes for CUSTOM-0 opcode (7'h0B)
  typedef enum logic [3:0] {
    GA_FUNCT_ADD       = 4'b0000,  // Geometric addition
    GA_FUNCT_SUB       = 4'b0001,  // Geometric subtraction  
    GA_FUNCT_MUL       = 4'b0010,  // Geometric product
    GA_FUNCT_WEDGE     = 4'b0011,  // Outer (wedge) product
    GA_FUNCT_DOT       = 4'b0100,  // Inner (dot) product
    GA_FUNCT_DUAL      = 4'b0101,  // Dual operation
    GA_FUNCT_REV       = 4'b0110,  // Reverse operation
    GA_FUNCT_NORM      = 4'b0111,  // Norm calculation
    GA_FUNCT_LOAD      = 4'b1000,  // Load from GA register
    GA_FUNCT_STORE     = 4'b1001,  // Store to GA register
    GA_FUNCT_ROTATE    = 4'b1010,  // Rotor application
    GA_FUNCT_REFLECT   = 4'b1011   // Reflection operation
  } ga_funct_e;

  /////////////////////////
  // GA Data Structures  //
  /////////////////////////

  // GA Multivector representation (configurable width)
  parameter int GA_MV_WIDTH = 32;  // Can be extended to 64, 128, etc.
  
  typedef struct packed {
    logic [GA_MV_WIDTH-1:0] scalar;      // Grade 0 (scalar part)
    logic [GA_MV_WIDTH-1:0] vector_x;    // Grade 1 (e1)
    logic [GA_MV_WIDTH-1:0] vector_y;    // Grade 1 (e2) 
    logic [GA_MV_WIDTH-1:0] vector_z;    // Grade 1 (e3)
    logic [GA_MV_WIDTH-1:0] bivector_xy; // Grade 2 (e12)
    logic [GA_MV_WIDTH-1:0] bivector_xz; // Grade 2 (e13)
    logic [GA_MV_WIDTH-1:0] bivector_yz; // Grade 2 (e23)
    logic [GA_MV_WIDTH-1:0] trivector;   // Grade 3 (e123)
  } ga_multivector_t;

  // Compressed representation for 32-bit operations
  typedef struct packed {
    logic [31:0] data;
    logic [2:0]  grade;    // Which grade this represents
    logic [2:0]  basis;    // Which basis element within the grade
  } ga_element_t;

  /////////////////////////////////
  // GA Coprocessor Interfaces   //
  /////////////////////////////////

  // Request interface from Ibex core to GA coprocessor
  typedef struct packed {
    logic                valid;
    logic [31:0]         operand_a;    // First operand
    logic [31:0]         operand_b;    // Second operand  
    logic [4:0]          rd_addr;      // Destination register
    logic [4:0]          ga_reg_a;     // GA register A address
    logic [4:0]          ga_reg_b;     // GA register B address
    ga_funct_e           funct;        // GA operation
    logic                we;           // Write enable
    logic                use_ga_regs;  // Use GA register file vs CPU regs
  } ga_req_t;

  // Response interface from GA coprocessor to Ibex core  
  typedef struct packed {
    logic                valid;
    logic                ready;        // Ready to accept new request
    logic [31:0]         result;       // Result data
    logic                error;        // Operation error
    logic                busy;         // Multi-cycle operation in progress
    logic                overflow;     // Arithmetic overflow
    logic                underflow;    // Arithmetic underflow
  } ga_resp_t;

  ///////////////////////////
  // GA Configuration      //
  ///////////////////////////

  // GA register file size (number of multivectors)
  parameter int GA_NUM_REGS = 32;
  parameter int GA_REG_ADDR_WIDTH = $clog2(GA_NUM_REGS);

  // GA arithmetic precision
  typedef enum logic [1:0] {
    GA_PRECISION_FP32  = 2'b00,  // IEEE 754 single precision
    GA_PRECISION_FP64  = 2'b01,  // IEEE 754 double precision  
    GA_PRECISION_FIXED = 2'b10,  // Fixed-point arithmetic
    GA_PRECISION_INT   = 2'b11   // Integer arithmetic
  } ga_precision_e;

  // GA algebra type
  typedef enum logic [2:0] {
    GA_ALGEBRA_3D      = 3'b000,  // 3D Euclidean (e1,e2,e3)
    GA_ALGEBRA_2D      = 3'b001,  // 2D Euclidean (e1,e2)
    GA_ALGEBRA_4D_STA  = 3'b010,  // 4D Spacetime (e0,e1,e2,e3)
    GA_ALGEBRA_5D_CGA  = 3'b011,  // 5D Conformal (e0,e1,e2,e3,einf)
    GA_ALGEBRA_CUSTOM  = 3'b111   // User-defined metric
  } ga_algebra_e;

  ////////////////////////////
  // GA Performance Counters //
  ////////////////////////////
  
  typedef struct packed {
    logic [31:0] ga_ops_total;       // Total GA operations
    logic [31:0] ga_ops_add;         // Addition operations
    logic [31:0] ga_ops_mul;         // Multiplication operations  
    logic [31:0] ga_ops_geometric;   // Geometric product operations
    logic [31:0] ga_cycles_busy;     // Cycles coprocessor was busy
    logic [31:0] ga_stalls;          // Pipeline stalls due to GA ops
  } ga_perf_counters_t;

  /////////////////////////
  // GA Helper Functions //
  /////////////////////////

  // Extract grade from multivector
  function automatic logic [2:0] ga_get_grade(ga_multivector_t mv);
    // Implementation would analyze which components are non-zero
    return 3'b000; // Placeholder
  endfunction

  // Check if multivector is pure scalar
  function automatic logic ga_is_scalar(ga_multivector_t mv);
    return (mv.vector_x == 0) && (mv.vector_y == 0) && (mv.vector_z == 0) &&
           (mv.bivector_xy == 0) && (mv.bivector_xz == 0) && (mv.bivector_yz == 0) &&
           (mv.trivector == 0);
  endfunction

  // Check if multivector is pure vector
  function automatic logic ga_is_vector(ga_multivector_t mv);
    return (mv.scalar == 0) && 
           (mv.bivector_xy == 0) && (mv.bivector_xz == 0) && (mv.bivector_yz == 0) &&
           (mv.trivector == 0);
  endfunction

endpackage
