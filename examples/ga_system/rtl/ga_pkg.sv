// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Package with constants and types used by GA coprocessor
 */

package ga_pkg;

  import ibex_pkg::*;

  typedef enum logic [3:0]
  {
    GA_FUNCT_ADD       = 4'b0000,
    GA_FUNCT_SUB       = 4'b0001,
    GA_FUNCT_MUL       = 4'b0010,
    GA_FUNCT_WEDGE     = 4'b0011,
    GA_FUNCT_DOT       = 4'b0100,
    GA_FUNCT_DUAL      = 4'b0101,
    GA_FUNCT_REV       = 4'b0110,
    GA_FUNCT_NORM      = 4'b0111,
    GA_FUNCT_LOAD      = 4'b1000,
    GA_FUNCT_STORE     = 4'b1001,
    GA_FUNCT_ROTATE    = 4'b1010,
    GA_FUNCT_REFLECT   = 4'b1011
  } ga_funct_e;

  parameter int GA_MV_WIDTH = 32;
  
  typedef struct packed
  {
    logic [GA_MV_WIDTH-1:0] scalar;
    logic [GA_MV_WIDTH-1:0] vector_x;
    logic [GA_MV_WIDTH-1:0] vector_y;
    logic [GA_MV_WIDTH-1:0] vector_z;
    logic [GA_MV_WIDTH-1:0] bivector_xy;
    logic [GA_MV_WIDTH-1:0] bivector_xz;
    logic [GA_MV_WIDTH-1:0] bivector_yz;
    logic [GA_MV_WIDTH-1:0] trivector;
  } ga_multivector_t;

  typedef struct packed
  {
    logic [31:0] data;
    logic [2:0]  grade;
    logic [2:0]  basis;
  } ga_element_t;

  typedef struct packed
  {
    logic                valid;
    logic [31:0]         operand_a;
    logic [31:0]         operand_b;
    logic [4:0]          rd_addr;
    logic [4:0]          ga_reg_a;
    logic [4:0]          ga_reg_b;
    ga_funct_e           funct;
    logic                we;
    logic                use_ga_regs;
  } ga_req_t;

  typedef struct packed 
  {
    logic                valid;
    logic                ready;
    logic [31:0]         result;
    logic                error;
    logic                busy;
    logic                overflow;
    logic                underflow;
  } ga_resp_t;

  parameter int GA_NUM_REGS       = 32;
  parameter int GA_REG_ADDR_WIDTH = $clog2(GA_NUM_REGS);

  typedef enum logic [1:0] 
  {
    GA_PRECISION_FP32  = 2'b00,
    GA_PRECISION_FP64  = 2'b01,
    GA_PRECISION_FIXED = 2'b10,
    GA_PRECISION_INT   = 2'b11
  } ga_precision_e;

  typedef enum logic [2:0] 
  {
    GA_ALGEBRA_3D      = 3'b000,
    GA_ALGEBRA_2D      = 3'b001,
    GA_ALGEBRA_4D_STA  = 3'b010,
    GA_ALGEBRA_5D_CGA  = 3'b011,
    GA_ALGEBRA_CUSTOM  = 3'b111
  } ga_algebra_e;
  
  typedef struct packed 
  {
    logic [31:0] ga_ops_total;
    logic [31:0] ga_ops_add;
    logic [31:0] ga_ops_mul;
    logic [31:0] ga_ops_geometric;
    logic [31:0] ga_cycles_busy;
    logic [31:0] ga_stalls;
  } ga_perf_counters_t;

  function automatic logic [2:0] ga_get_grade(ga_multivector_t mv);

    return 3'b000;
    
  endfunction

  function automatic logic ga_is_scalar(ga_multivector_t mv);

    return (mv.vector_x == 0) && (mv.vector_y == 0) && (mv.vector_z == 0) &&
           (mv.bivector_xy == 0) && (mv.bivector_xz == 0) && (mv.bivector_yz == 0) &&
           (mv.trivector == 0);

  endfunction

  function automatic logic ga_is_vector(ga_multivector_t mv);

    return (mv.scalar == 0) && 
           (mv.bivector_xy == 0) && (mv.bivector_xz == 0) && (mv.bivector_yz == 0) &&
           (mv.trivector == 0);

  endfunction

endpackage
