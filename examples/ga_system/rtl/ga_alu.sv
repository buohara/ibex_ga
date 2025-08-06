// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Geometric Algebra Arithmetic Logic Unit
 * 
 * This module implements the core arithmetic operations for geometric algebra
 * including geometric product, outer product, inner product, and other GA operations.
 */

module ga_alu
  import ibex_pkg::*;
  import ga_pkg::*;
#(
  parameter int unsigned DataWidth    = 32,
  parameter ga_precision_e Precision  = GA_PRECISION_FIXED,
  parameter ga_algebra_e Algebra      = GA_ALGEBRA_5D_CGA
) (
  input  logic                clk_i,
  input  logic                rst_ni,
  input  ga_multivector_t     operand_a_i,
  input  ga_multivector_t     operand_b_i,
  input  ga_funct_e           operation_i,
  input  logic                valid_i,
  output logic                ready_o,
  output ga_multivector_t     result_o,
  output logic                valid_o,
  output logic                error_o
);
  typedef enum logic [1:0]
  {
    ALU_IDLE,
    ALU_COMPUTE,
    ALU_DONE
  } alu_state_e;

  alu_state_e alu_state_q, alu_state_d;
  ga_multivector_t result_d, result_q;
  logic error_d, error_q;
  logic [DataWidth-1:0] temp_scalar;
  logic [DataWidth-1:0] temp_vector_x, temp_vector_y, temp_vector_z;
  logic [DataWidth-1:0] temp_bivector_xy, temp_bivector_xz, temp_bivector_yz;
  logic [DataWidth-1:0] temp_trivector;

  always_ff @(posedge clk_i or negedge rst_ni) begin

    if (!rst_ni) begin

      alu_state_q <= ALU_IDLE;
      result_q    <= '0;
      error_q     <= 1'b0;
    
    end else begin
      
      alu_state_q <= alu_state_d;
      result_q    <= result_d;
      error_q     <= error_d;

    end

  end

  always_comb begin

    alu_state_d = alu_state_q;
    result_d    = result_q;
    error_d     = error_q;
    ready_o     = 1'b0;
    valid_o     = 1'b0;

    case (alu_state_q)

      ALU_IDLE: begin

        ready_o = 1'b1;

        if (valid_i) begin
          
          alu_state_d = ALU_COMPUTE;
          error_d     = 1'b0;
          valid_o     = 1'b0;
          
        end

      end

      ALU_COMPUTE: begin

        result_d    = computeGaOperation(operand_a_i, operand_b_i, operation_i);
        alu_state_d = ALU_DONE;

      end

      ALU_DONE: begin

        valid_o     = 1'b1;
        alu_state_d = ALU_IDLE;

      end

      default: begin

        alu_state_d = ALU_IDLE;

      end
    endcase
  end

  function automatic ga_multivector_t computeGaOperation(
    ga_multivector_t a,
    ga_multivector_t b,
    ga_funct_e op
  );
    ga_multivector_t result;
    result = '0;

    case (op)

      GA_FUNCT_ADD: begin

        result.scalar       = a.scalar + b.scalar;
        result.e1           = a.e1 + b.e1;
        result.e2           = a.e2 + b.e2;
        result.e3           = a.e3 + b.e3;
        result.eo           = a.eo + b.eo;
        result.ei           = a.ei + b.ei;
        result.e12          = a.e12 + b.e12;
        result.e13          = a.e13 + b.e13;
        result.e23          = a.e23 + b.e23;
        result.e1o          = a.e1o + b.e1o;
        result.e2o          = a.e2o + b.e2o;
        result.e3o          = a.e3o + b.e3o;
        result.e1i          = a.e1i + b.e1i;
        result.e2i          = a.e2i + b.e2i;
        result.e3i          = a.e3i + b.e3i;
        result.eoi          = a.eoi + b.eoi;
        result.e123         = a.e123 + b.e123;
        result.e12o         = a.e12o + b.e12o;
        result.e13o         = a.e13o + b.e13o;
        result.e23o         = a.e23o + b.e23o;
        result.e12i         = a.e12i + b.e12i;
        result.e13i         = a.e13i + b.e13i;
        result.e23i         = a.e23i + b.e23i;
        result.e1oi         = a.e1oi + b.e1oi;
        result.e2oi         = a.e2oi + b.e2oi;
        result.e3oi         = a.e3oi + b.e3oi;
        result.e123o        = a.e123o + b.e123o;
        result.e123i        = a.e123i + b.e123i;
        result.e12oi        = a.e12oi + b.e12oi;
        result.e13oi        = a.e13oi + b.e13oi;
        result.e23oi        = a.e23oi + b.e23oi;
        result.e123oi       = a.e123oi + b.e123oi;

        $display("ga_alu add: a=%128h, b=%128h, res=%128h", a, b, result);

      end

      GA_FUNCT_SUB: begin

        result.scalar      = a.scalar - b.scalar;
        result.e1          = a.e1 - b.e1;
        result.e2          = a.e2 - b.e2;
        result.e3          = a.e3 - b.e3;
        result.eo          = a.eo - b.eo;
        result.ei          = a.ei - b.ei;
        result.e12         = a.e12 - b.e12;
        result.e13         = a.e13 - b.e13;
        result.e23         = a.e23 - b.e23;
        result.e1o         = a.e1o - b.e1o;
        result.e2o         = a.e2o - b.e2o;
        result.e3o         = a.e3o - b.e3o;
        result.e1i         = a.e1i - b.e1i;
        result.e2i         = a.e2i - b.e2i;
        result.e3i         = a.e3i - b.e3i;
        result.eoi         = a.eoi - b.eoi;
        result.e123        = a.e123 - b.e123;
        result.e12o        = a.e12o - b.e12o;
        result.e13o        = a.e13o - b.e13o;
        result.e23o        = a.e23o - b.e23o;
        result.e12i        = a.e12i - b.e12i;
        result.e13i        = a.e13i - b.e13i;
        result.e23i        = a.e23i - b.e23i;
        result.e1oi        = a.e1oi - b.e1oi;
        result.e2oi        = a.e2oi - b.e2oi;
        result.e3oi        = a.e3oi - b.e3oi;
        result.e123o       = a.e123o - b.e123o;
        result.e123i       = a.e123i - b.e123i;
        result.e12oi       = a.e12oi - b.e12oi;
        result.e13oi       = a.e13oi - b.e13oi;
        result.e23oi       = a.e23oi - b.e23oi;
        result.e123oi      = a.e123oi - b.e123oi;

        $display("ga_alu sub: a=%128h, b=%128h, res=%128h", a, b, result);

      end

      GA_FUNCT_MUL: begin
        result = geometricProduct(a, b);
      end

      GA_FUNCT_WEDGE: begin
        result = wedgeProduct(a, b);
      end

      GA_FUNCT_DOT: begin
        result = dotProduct(a, b);
      end

      GA_FUNCT_DUAL: begin
        result = dualOperation(a);
      end

      GA_FUNCT_REV: begin
        result = reverseOperation(a);
      end

      GA_FUNCT_NORM: begin
        result = normCalculation(a);
      end

      GA_FUNCT_ROTATE: begin
        result = rotorApplication(a, b);
      end

      GA_FUNCT_REFLECT: begin
        result = reflectionOperation(a, b);
      end

      default: begin
        result = '0;
      end
    endcase

    return result;
  endfunction

  function automatic ga_multivector_t geometricProduct(
    ga_multivector_t a,
    ga_multivector_t b
  );
    ga_multivector_t result;
    
    result = '0;
  
    result.scalar = a.scalar * b.scalar + 
                    a.e1 * b.e1 + a.e2 * b.e2 + a.e3 * b.e3 +
                    a.eo * b.eo - a.ei * b.ei -
                    a.e12 * b.e12 - a.e13 * b.e13 - a.e23 * b.e23 +
                    a.e1o * b.e1o + a.e2o * b.e2o + a.e3o * b.e3o -
                    a.e1i * b.e1i - a.e2i * b.e2i - a.e3i * b.e3i -
                    a.eoi * b.eoi - a.e123 * b.e123 -
                    a.e12o * b.e12o - a.e13o * b.e13o - a.e23o * b.e23o +
                    a.e12i * b.e12i + a.e13i * b.e13i + a.e23i * b.e23i +
                    a.e1oi * b.e1oi + a.e2oi * b.e2oi + a.e3oi * b.e3oi +
                    a.e123o * b.e123o - a.e123i * b.e123i +
                    a.e12oi * b.e12oi + a.e13oi * b.e13oi + a.e23oi * b.e23oi -
                    a.e123oi * b.e123oi;

    result.e1 = a.scalar * b.e1 + a.e1 * b.scalar -
                a.e2 * b.e12 + a.e3 * b.e13 + a.eo * b.e1o - a.ei * b.e1i +
                a.e12 * b.e2 - a.e13 * b.e3 - a.e1o * b.eo + a.e1i * b.ei +
                a.e23 * b.e123 - a.e2o * b.e12o + a.e3o * b.e13o +
                a.e2i * b.e12i - a.e3i * b.e13i - a.eoi * b.e1oi +
                a.e123 * b.e23 + a.e12o * b.e2o - a.e13o * b.e3o -
                a.e12i * b.e2i + a.e13i * b.e3i + a.e1oi * b.eoi -
                a.e2oi * b.e12oi + a.e3oi * b.e13oi + a.e123o * b.e123o -
                a.e123i * b.e123i - a.e12oi * b.e2oi + a.e13oi * b.e3oi +
                a.e23oi * b.e123oi - a.e123oi * b.e23oi;

    result.e2 = a.scalar * b.e2 + a.e1 * b.e12 + a.e2 * b.scalar -
                a.e3 * b.e23 + a.eo * b.e2o - a.ei * b.e2i -
                a.e12 * b.e1 + a.e23 * b.e3 - a.e2o * b.eo + a.e2i * b.ei -
                a.e13 * b.e123 + a.e1o * b.e12o + a.e3o * b.e23o -
                a.e1i * b.e12i + a.e3i * b.e23i - a.eoi * b.e2oi -
                a.e123 * b.e13 - a.e12o * b.e1o + a.e23o * b.e3o +
                a.e12i * b.e1i - a.e23i * b.e3i + a.e2oi * b.eoi +
                a.e1oi * b.e12oi + a.e3oi * b.e23oi + a.e123o * b.e123o -
                a.e123i * b.e123i + a.e12oi * b.e1oi - a.e23oi * b.e3oi -
                a.e13oi * b.e123oi + a.e123oi * b.e13oi;

    result.e3 = a.scalar * b.e3 - a.e1 * b.e13 + a.e2 * b.e23 +
                a.e3 * b.scalar + a.eo * b.e3o - a.ei * b.e3i +
                a.e13 * b.e1 - a.e23 * b.e2 - a.e3o * b.eo + a.e3i * b.ei +
                a.e12 * b.e123 - a.e1o * b.e13o + a.e2o * b.e23o +
                a.e1i * b.e13i - a.e2i * b.e23i - a.eoi * b.e3oi +
                a.e123 * b.e12 + a.e13o * b.e1o - a.e23o * b.e2o -
                a.e13i * b.e1i + a.e23i * b.e2i + a.e3oi * b.eoi -
                a.e1oi * b.e13oi + a.e2oi * b.e23oi + a.e123o * b.e123o -
                a.e123i * b.e123i + a.e13oi * b.e1oi - a.e23oi * b.e2oi +
                a.e12oi * b.e123oi - a.e123oi * b.e12oi;

    result.eo = a.scalar * b.eo + a.e1 * b.e1o + a.e2 * b.e2o +
                a.e3 * b.e3o + a.eo * b.scalar - a.ei * b.eoi +
                a.e12 * b.e12o + a.e13 * b.e13o + a.e23 * b.e23o +
                a.e1o * b.e1 + a.e2o * b.e2 + a.e3o * b.e3 -
                a.e1i * b.e1oi - a.e2i * b.e2oi - a.e3i * b.e3oi -
                a.eoi * b.ei + a.e123 * b.e123o + a.e12o * b.e12 +
                a.e13o * b.e13 + a.e23o * b.e23 - a.e12i * b.e12oi -
                a.e13i * b.e13oi - a.e23i * b.e23oi - a.e1oi * b.e1i -
                a.e2oi * b.e2i - a.e3oi * b.e3i + a.e123o * b.e123 -
                a.e123i * b.e123oi - a.e12oi * b.e12i - a.e13oi * b.e13i -
                a.e23oi * b.e23i - a.e123oi * b.e123i;

    result.ei = a.scalar * b.ei + a.e1 * b.e1i + a.e2 * b.e2i +
                a.e3 * b.e3i - a.eo * b.eoi + a.ei * b.scalar +
                a.e12 * b.e12i + a.e13 * b.e13i + a.e23 * b.e23i -
                a.e1o * b.e1oi - a.e2o * b.e2oi - a.e3o * b.e3oi +
                a.e1i * b.e1 + a.e2i * b.e2 + a.e3i * b.e3 +
                a.eoi * b.eo + a.e123 * b.e123i + a.e12o * b.e12oi +
                a.e13o * b.e13oi + a.e23o * b.e23oi + a.e12i * b.e12 +
                a.e13i * b.e13 + a.e23i * b.e23 + a.e1oi * b.e1o +
                a.e2oi * b.e2o + a.e3oi * b.e3o - a.e123o * b.e123oi +
                a.e123i * b.e123 + a.e12oi * b.e12o + a.e13oi * b.e13o +
                a.e23oi * b.e23o + a.e123oi * b.e123o;

    result.e12 = a.scalar * b.e12 + a.e1 * b.e2 - a.e2 * b.e1 +
                a.eo * b.e12o - a.ei * b.e12i + a.e12 * b.scalar +
                a.e3 * b.e123 - a.e1o * b.e2o + a.e2o * b.e1o +
                a.e1i * b.e2i - a.e2i * b.e1i - a.eoi * b.e12oi +
                a.e123 * b.e3 - a.e3o * b.e123o + a.e3i * b.e123i -
                a.e12o * b.eo + a.e12i * b.ei + a.e1oi * b.e2oi -
                a.e2oi * b.e1oi - a.e123o * b.e3o + a.e123i * b.e3i +
                a.e12oi * b.eoi + a.e3oi * b.e123oi - a.e123oi * b.e3oi;

    result.e13 = a.scalar * b.e13 + a.e1 * b.e3 - a.e3 * b.e1 +
                a.eo * b.e13o - a.ei * b.e13i + a.e13 * b.scalar -
                a.e2 * b.e123 - a.e1o * b.e3o + a.e3o * b.e1o +
                a.e1i * b.e3i - a.e3i * b.e1i - a.eoi * b.e13oi -
                a.e123 * b.e2 + a.e2o * b.e123o - a.e2i * b.e123i -
                a.e13o * b.eo + a.e13i * b.ei + a.e1oi * b.e3oi -
                a.e3oi * b.e1oi + a.e123o * b.e2o - a.e123i * b.e2i +
                a.e13oi * b.eoi - a.e2oi * b.e123oi + a.e123oi * b.e2oi;

    result.e23 = a.scalar * b.e23 + a.e2 * b.e3 - a.e3 * b.e2 +
                a.eo * b.e23o - a.ei * b.e23i + a.e23 * b.scalar +
                a.e1 * b.e123 - a.e2o * b.e3o + a.e3o * b.e2o +
                a.e2i * b.e3i - a.e3i * b.e2i - a.eoi * b.e23oi +
                a.e123 * b.e1 - a.e1o * b.e123o + a.e1i * b.e123i -
                a.e23o * b.eo + a.e23i * b.ei + a.e2oi * b.e3oi -
                a.e3oi * b.e2oi - a.e123o * b.e1o + a.e123i * b.e1i +
                a.e23oi * b.eoi + a.e1oi * b.e123oi - a.e123oi * b.e1oi;

    result.e1o = a.scalar * b.e1o + a.e1 * b.eo - a.eo * b.e1 +
                a.e2 * b.e12o - a.e3 * b.e13o - a.ei * b.e1oi +
                a.e1o * b.scalar - a.e12 * b.e2o + a.e13 * b.e3o +
                a.e2o * b.e12 - a.e3o * b.e13 + a.e1i * b.eoi -
                a.eoi * b.e1i + a.e23 * b.e123o + a.e2i * b.e12oi -
                a.e3i * b.e13oi + a.e123 * b.e23o - a.e12o * b.e2 +
                a.e13o * b.e3 - a.e23o * b.e123 + a.e12i * b.e2oi -
                a.e13i * b.e3oi + a.e1oi * b.ei + a.e2oi * b.e12i -
                a.e3oi * b.e13i + a.e123o * b.e23 - a.e123i * b.e23oi -
                a.e12oi * b.e2i + a.e13oi * b.e3i - a.e23oi * b.e123i +
                a.e123oi * b.e23i;

    result.e2o = a.scalar * b.e2o + a.e2 * b.eo - a.eo * b.e2 -
                a.e1 * b.e12o + a.e3 * b.e23o - a.ei * b.e2oi +
                a.e2o * b.scalar + a.e12 * b.e1o - a.e23 * b.e3o -
                a.e1o * b.e12 + a.e3o * b.e23 + a.e2i * b.eoi -
                a.eoi * b.e2i - a.e13 * b.e123o - a.e1i * b.e12oi +
                a.e3i * b.e23oi - a.e123 * b.e13o + a.e12o * b.e1 -
                a.e23o * b.e3 + a.e13o * b.e123 - a.e12i * b.e1oi +
                a.e23i * b.e3oi + a.e2oi * b.ei - a.e1oi * b.e12i +
                a.e3oi * b.e23i - a.e123o * b.e13 + a.e123i * b.e13oi +
                a.e12oi * b.e1i - a.e23oi * b.e3i + a.e13oi * b.e123i -
                a.e123oi * b.e13i;

    result.e3o = a.scalar * b.e3o + a.e3 * b.eo - a.eo * b.e3 +
                a.e1 * b.e13o - a.e2 * b.e23o - a.ei * b.e3oi +
                a.e3o * b.scalar - a.e13 * b.e1o + a.e23 * b.e2o +
                a.e1o * b.e13 - a.e2o * b.e23 + a.e3i * b.eoi -
                a.eoi * b.e3i + a.e12 * b.e123o + a.e1i * b.e13oi -
                a.e2i * b.e23oi + a.e123 * b.e12o - a.e13o * b.e1 +
                a.e23o * b.e2 - a.e12o * b.e123 + a.e13i * b.e1oi -
                a.e23i * b.e2oi + a.e3oi * b.ei + a.e1oi * b.e13i -
                a.e2oi * b.e23i + a.e123o * b.e12 - a.e123i * b.e12oi -
                a.e13oi * b.e1i + a.e23oi * b.e2i - a.e12oi * b.e123i +
                a.e123oi * b.e12i;

    result.e1i = a.scalar * b.e1i + a.e1 * b.ei - a.ei * b.e1 +
                a.e2 * b.e12i - a.e3 * b.e13i + a.eo * b.e1oi +
                a.e1i * b.scalar - a.e12 * b.e2i + a.e13 * b.e3i +
                a.e2i * b.e12 - a.e3i * b.e13 - a.e1o * b.eoi +
                a.eoi * b.e1o + a.e23 * b.e123i + a.e2o * b.e12oi -
                a.e3o * b.e13oi + a.e123 * b.e23i - a.e12i * b.e2 +
                a.e13i * b.e3 - a.e23i * b.e123 + a.e12o * b.e2oi -
                a.e13o * b.e3oi + a.e1oi * b.eo + a.e2oi * b.e12o -
                a.e3oi * b.e13o + a.e123i * b.e23 - a.e123o * b.e23oi -
                a.e12oi * b.e2o + a.e13oi * b.e3o - a.e23oi * b.e123o +
                a.e123oi * b.e23o;

    result.e2i = a.scalar * b.e2i + a.e2 * b.ei - a.ei * b.e2 -
                a.e1 * b.e12i + a.e3 * b.e23i + a.eo * b.e2oi +
                a.e2i * b.scalar + a.e12 * b.e1i - a.e23 * b.e3i -
                a.e1i * b.e12 + a.e3i * b.e23 - a.e2o * b.eoi +
                a.eoi * b.e2o - a.e13 * b.e123i - a.e1o * b.e12oi +
                a.e3o * b.e23oi - a.e123 * b.e13i + a.e12i * b.e1 -
                a.e23i * b.e3 + a.e13i * b.e123 - a.e12o * b.e1oi +
                a.e23o * b.e3oi + a.e2oi * b.eo - a.e1oi * b.e12o +
                a.e3oi * b.e23o - a.e123i * b.e13 + a.e123o * b.e13oi +
                a.e12oi * b.e1o - a.e23oi * b.e3o + a.e13oi * b.e123o -
                a.e123oi * b.e13o;

    result.e3i = a.scalar * b.e3i + a.e3 * b.ei - a.ei * b.e3 +
                a.e1 * b.e13i - a.e2 * b.e23i + a.eo * b.e3oi +
                a.e3i * b.scalar - a.e13 * b.e1i + a.e23 * b.e2i +
                a.e1i * b.e13 - a.e2i * b.e23 - a.e3o * b.eoi +
                a.eoi * b.e3o + a.e12 * b.e123i + a.e1o * b.e13oi -
                a.e2o * b.e23oi + a.e123 * b.e12i - a.e13i * b.e1 +
                a.e23i * b.e2 - a.e12i * b.e123 + a.e13o * b.e1oi -
                a.e23o * b.e2oi + a.e3oi * b.eo + a.e1oi * b.e13o -
                a.e2oi * b.e23o + a.e123i * b.e12 - a.e123o * b.e12oi -
                a.e13oi * b.e1o + a.e23oi * b.e2o - a.e12oi * b.e123o +
                a.e123oi * b.e12o;

    result.eoi = a.scalar * b.eoi + a.eo * b.ei - a.ei * b.eo +
                a.e1 * b.e1oi + a.e2 * b.e2oi + a.e3 * b.e3oi +
                a.eoi * b.scalar + a.e1o * b.e1i + a.e2o * b.e2i +
                a.e3o * b.e3i - a.e1i * b.e1o - a.e2i * b.e2o -
                a.e3i * b.e3o + a.e12 * b.e12oi + a.e13 * b.e13oi +
                a.e23 * b.e23oi + a.e1oi * b.e1 + a.e2oi * b.e2 +
                a.e3oi * b.e3 + a.e12o * b.e12i + a.e13o * b.e13i +
                a.e23o * b.e23i - a.e12i * b.e12o - a.e13i * b.e13o -
                a.e23i * b.e23o + a.e123 * b.e123oi + a.e12oi * b.e12 +
                a.e13oi * b.e13 + a.e23oi * b.e23 + a.e123o * b.e123i -
                a.e123i * b.e123o + a.e123oi * b.e123;

    result.e123 = a.scalar * b.e123 + a.e1 * b.e23 + a.e2 * b.e13 +
                  a.e3 * b.e12 + a.eo * b.e123o - a.ei * b.e123i +
                  a.e12 * b.e3 + a.e13 * b.e2 + a.e23 * b.e1 +
                  a.e123 * b.scalar - a.e1o * b.e23o + a.e2o * b.e13o -
                  a.e3o * b.e12o + a.e1i * b.e23i - a.e2i * b.e13i +
                  a.e3i * b.e12i - a.eoi * b.e123oi + a.e12o * b.e3o +
                  a.e13o * b.e2o + a.e23o * b.e1o - a.e12i * b.e3i -
                  a.e13i * b.e2i - a.e23i * b.e1i + a.e1oi * b.e23oi -
                  a.e2oi * b.e13oi + a.e3oi * b.e12oi - a.e123o * b.eo +
                  a.e123i * b.ei + a.e12oi * b.e3oi + a.e13oi * b.e2oi +
                  a.e23oi * b.e1oi - a.e123oi * b.eoi;

    result.e12o = a.scalar * b.e12o + a.e12o * b.scalar +
                  a.e1 * b.e2o + a.e2 * b.e1o - a.eo * b.e12 -
                  a.e12 * b.eo + a.e1o * b.e2 + a.e2o * b.e1;
                  
    result.e13o = a.scalar * b.e13o + a.e13o * b.scalar +
                  a.e1 * b.e3o + a.e3 * b.e1o - a.eo * b.e13 -
                  a.e13 * b.eo + a.e1o * b.e3 + a.e3o * b.e1;
                  
    result.e23o = a.scalar * b.e23o + a.e23o * b.scalar +
                  a.e2 * b.e3o + a.e3 * b.e2o - a.eo * b.e23 -
                  a.e23 * b.eo + a.e2o * b.e3 + a.e3o * b.e2;
                  
    result.e12i = a.scalar * b.e12i + a.e12i * b.scalar +
                  a.e1 * b.e2i + a.e2 * b.e1i + a.ei * b.e12 +
                  a.e12 * b.ei + a.e1i * b.e2 + a.e2i * b.e1;
                  
    result.e13i = a.scalar * b.e13i + a.e13i * b.scalar +
                  a.e1 * b.e3i + a.e3 * b.e1i + a.ei * b.e13 +
                  a.e13 * b.ei + a.e1i * b.e3 + a.e3i * b.e1;
                  
    result.e23i = a.scalar * b.e23i + a.e23i * b.scalar +
                  a.e2 * b.e3i + a.e3 * b.e2i + a.ei * b.e23 +
                  a.e23 * b.ei + a.e2i * b.e3 + a.e3i * b.e2;
                  
    result.e1oi = a.scalar * b.e1oi + a.e1oi * b.scalar +
                  a.e1 * b.eoi + a.eo * b.e1i - a.ei * b.e1o +
                  a.eoi * b.e1 + a.e1o * b.ei + a.e1i * b.eo;
                  
    result.e2oi = a.scalar * b.e2oi + a.e2oi * b.scalar +
                  a.e2 * b.eoi + a.eo * b.e2i - a.ei * b.e2o +
                  a.eoi * b.e2 + a.e2o * b.ei + a.e2i * b.eo;
                  
    result.e3oi = a.scalar * b.e3oi + a.e3oi * b.scalar +
                  a.e3 * b.eoi + a.eo * b.e3i - a.ei * b.e3o +
                  a.eoi * b.e3 + a.e3o * b.ei + a.e3i * b.eo;

    result.e123o = a.scalar * b.e123o + a.e123o * b.scalar +
                  a.e123 * b.eo + a.eo * b.e123;
                  
    result.e123i = a.scalar * b.e123i + a.e123i * b.scalar +
                  a.e123 * b.ei - a.ei * b.e123;
                  
    result.e12oi = a.scalar * b.e12oi + a.e12oi * b.scalar +
                  a.e12 * b.eoi + a.eoi * b.e12;
                  
    result.e13oi = a.scalar * b.e13oi + a.e13oi * b.scalar +
                  a.e13 * b.eoi + a.eoi * b.e13;
                  
    result.e23oi = a.scalar * b.e23oi + a.e23oi * b.scalar +
                  a.e23 * b.eoi + a.eoi * b.e23;

    result.e123oi = a.scalar * b.e123oi + a.e123oi * b.scalar +
                    a.e123 * b.eoi - a.eoi * b.e123;

    $display("ga_alu geometric product: a=%128h, b=%128h, res=%128h", a, b, result);

    return result;

  endfunction

  function automatic ga_multivector_t wedgeProduct(
    ga_multivector_t a,
    ga_multivector_t b
  );
    ga_multivector_t result;
    
    result.scalar = a.scalar * b.scalar;
    
    result.e1 = a.scalar * b.e1 + a.e1 * b.scalar;
    result.e2 = a.scalar * b.e2 + a.e2 * b.scalar;
    result.e3 = a.scalar * b.e3 + a.e3 * b.scalar;
    result.eo = a.scalar * b.eo + a.eo * b.scalar;
    result.ei = a.scalar * b.ei + a.ei * b.scalar;
    
    result.e12 = a.scalar * b.e12 + a.e1 * b.e2 - a.e2 * b.e1 + a.e12 * b.scalar;
    result.e13 = a.scalar * b.e13 + a.e1 * b.e3 - a.e3 * b.e1 + a.e13 * b.scalar;
    result.e23 = a.scalar * b.e23 + a.e2 * b.e3 - a.e3 * b.e2 + a.e23 * b.scalar;
    result.e1o = a.scalar * b.e1o + a.e1 * b.eo - a.eo * b.e1 + a.e1o * b.scalar;
    result.e2o = a.scalar * b.e2o + a.e2 * b.eo - a.eo * b.e2 + a.e2o * b.scalar;
    result.e3o = a.scalar * b.e3o + a.e3 * b.eo - a.eo * b.e3 + a.e3o * b.scalar;
    result.e1i = a.scalar * b.e1i + a.e1 * b.ei - a.ei * b.e1 + a.e1i * b.scalar;
    result.e2i = a.scalar * b.e2i + a.e2 * b.ei - a.ei * b.e2 + a.e2i * b.scalar;
    result.e3i = a.scalar * b.e3i + a.e3 * b.ei - a.ei * b.e3 + a.e3i * b.scalar;
    result.eoi = a.scalar * b.eoi + a.eo * b.ei - a.ei * b.eo + a.eoi * b.scalar;
    
    result.e123 = a.scalar * b.e123 + a.e1 * b.e23 - a.e2 * b.e13 + a.e3 * b.e12 + 
                  a.e12 * b.e3 - a.e13 * b.e2 + a.e23 * b.e1 + a.e123 * b.scalar;
    result.e12o = a.scalar * b.e12o + a.e1 * b.e2o - a.e2 * b.e1o + a.eo * b.e12 + 
                  a.e12 * b.eo - a.e1o * b.e2 + a.e2o * b.e1 + a.e12o * b.scalar;
    result.e13o = a.scalar * b.e13o + a.e1 * b.e3o - a.e3 * b.e1o + a.eo * b.e13 + 
                  a.e13 * b.eo - a.e1o * b.e3 + a.e3o * b.e1 + a.e13o * b.scalar;
    result.e23o = a.scalar * b.e23o + a.e2 * b.e3o - a.e3 * b.e2o + a.eo * b.e23 + 
                  a.e23 * b.eo - a.e2o * b.e3 + a.e3o * b.e2 + a.e23o * b.scalar;
    result.e12i = a.scalar * b.e12i + a.e1 * b.e2i - a.e2 * b.e1i + a.ei * b.e12 + 
                  a.e12 * b.ei - a.e1i * b.e2 + a.e2i * b.e1 + a.e12i * b.scalar;
    result.e13i = a.scalar * b.e13i + a.e1 * b.e3i - a.e3 * b.e1i + a.ei * b.e13 + 
                  a.e13 * b.ei - a.e1i * b.e3 + a.e3i * b.e1 + a.e13i * b.scalar;
    result.e23i = a.scalar * b.e23i + a.e2 * b.e3i - a.e3 * b.e2i + a.ei * b.e23 + 
                  a.e23 * b.ei - a.e2i * b.e3 + a.e3i * b.e2 + a.e23i * b.scalar;
    result.e1oi = a.scalar * b.e1oi + a.e1 * b.eoi - a.eo * b.e1i + a.ei * b.e1o + 
                  a.e1o * b.ei - a.e1i * b.eo + a.eoi * b.e1 + a.e1oi * b.scalar;
    result.e2oi = a.scalar * b.e2oi + a.e2 * b.eoi - a.eo * b.e2i + a.ei * b.e2o + 
                  a.e2o * b.ei - a.e2i * b.eo + a.eoi * b.e2 + a.e2oi * b.scalar;
    result.e3oi = a.scalar * b.e3oi + a.e3 * b.eoi - a.eo * b.e3i + a.ei * b.e3o + 
                  a.e3o * b.ei - a.e3i * b.eo + a.eoi * b.e3 + a.e3oi * b.scalar;
    
    result.e123o = a.scalar * b.e123o + a.e123 * b.eo + a.eo * b.e123 + a.e123o * b.scalar;
    result.e123i = a.scalar * b.e123i + a.e123 * b.ei + a.ei * b.e123 + a.e123i * b.scalar;
    result.e12oi = a.scalar * b.e12oi + a.e12 * b.eoi + a.eoi * b.e12 + a.e12oi * b.scalar;
    result.e13oi = a.scalar * b.e13oi + a.e13 * b.eoi + a.eoi * b.e13 + a.e13oi * b.scalar;
    result.e23oi = a.scalar * b.e23oi + a.e23 * b.eoi + a.eoi * b.e23 + a.e23oi * b.scalar;
    
    result.e123oi = a.scalar * b.e123oi + a.e123oi * b.scalar;
    
    $display("ga_alu wedge product: a=%128h, b=%128h, res=%128h", a, b, result);
    
    return result;

  endfunction

  function automatic ga_multivector_t dotProduct(
    ga_multivector_t a,
    ga_multivector_t b
  );
    ga_multivector_t result;
    result = '0;

    result.scalar = a.e1 * b.e1 + a.e2 * b.e2 + a.e3 * b.e3 + 
                    a.eo * b.eo - a.ei * b.ei;
    
    result.e1 = a.e12 * b.e2 - a.e13 * b.e3 + a.e1o * b.eo - a.e1i * b.ei;
    result.e2 = -a.e12 * b.e1 + a.e23 * b.e3 + a.e2o * b.eo - a.e2i * b.ei;
    result.e3 = a.e13 * b.e1 - a.e23 * b.e2 + a.e3o * b.eo - a.e3i * b.ei;
    result.eo = a.e1o * b.e1 + a.e2o * b.e2 + a.e3o * b.e3 + a.eoi * b.ei;
    result.ei = -a.e1i * b.e1 - a.e2i * b.e2 - a.e3i * b.e3 + a.eoi * b.eo;
    
    result.e1 += a.e1 * b.e1o + a.e2 * b.e12 - a.e3 * b.e13 + a.eo * b.e1o - a.ei * b.e1i;
    result.e2 += -a.e1 * b.e12 + a.e2 * b.e2o + a.e3 * b.e23 + a.eo * b.e2o - a.ei * b.e2i;
    result.e3 += a.e1 * b.e13 - a.e2 * b.e23 + a.e3 * b.e3o + a.eo * b.e3o - a.ei * b.e3i;
    result.eo += a.e1 * b.e1o + a.e2 * b.e2o + a.e3 * b.e3o + a.ei * b.eoi;
    result.ei += -a.e1 * b.e1i - a.e2 * b.e2i - a.e3 * b.e3i + a.eo * b.eoi;
    
    result.e12 = a.e123 * b.e3 + a.e12o * b.eo - a.e12i * b.ei;
    result.e13 = -a.e123 * b.e2 + a.e13o * b.eo - a.e13i * b.ei;
    result.e23 = a.e123 * b.e1 + a.e23o * b.eo - a.e23i * b.ei;
    result.e1o = a.e12o * b.e2 - a.e13o * b.e3 + a.e1oi * b.ei;
    result.e2o = -a.e12o * b.e1 + a.e23o * b.e3 + a.e2oi * b.ei;
    result.e3o = a.e13o * b.e1 - a.e23o * b.e2 + a.e3oi * b.ei;
    result.e1i = -a.e12i * b.e2 + a.e13i * b.e3 + a.e1oi * b.eo;
    result.e2i = a.e12i * b.e1 - a.e23i * b.e3 + a.e2oi * b.eo;
    result.e3i = -a.e13i * b.e1 + a.e23i * b.e2 + a.e3oi * b.eo;
    result.eoi = a.e1oi * b.e1 + a.e2oi * b.e2 + a.e3oi * b.e3;
    
    result.e12 += a.e3 * b.e123 + a.eo * b.e12o - a.ei * b.e12i;
    result.e13 += -a.e2 * b.e123 + a.eo * b.e13o - a.ei * b.e13i;
    result.e23 += a.e1 * b.e123 + a.eo * b.e23o - a.ei * b.e23i;
    result.e1o += a.e2 * b.e12o - a.e3 * b.e13o + a.ei * b.e1oi;
    result.e2o += -a.e1 * b.e12o + a.e3 * b.e23o + a.ei * b.e2oi;
    result.e3o += a.e1 * b.e13o - a.e2 * b.e23o + a.ei * b.e3oi;
    result.e1i += -a.e2 * b.e12i + a.e3 * b.e13i + a.eo * b.e1oi;
    result.e2i += a.e1 * b.e12i - a.e3 * b.e23i + a.eo * b.e2oi;
    result.e3i += -a.e1 * b.e13i + a.e2 * b.e23i + a.eo * b.e3oi;
    result.eoi += a.e1 * b.e1oi + a.e2 * b.e2oi + a.e3 * b.e3oi;
    
    result.e123 = a.e123o * b.eo - a.e123i * b.ei;
    result.e12o = a.e12oi * b.ei;
    result.e13o = a.e13oi * b.ei;
    result.e23o = a.e23oi * b.ei;
    result.e12i = a.e12oi * b.eo;
    result.e13i = a.e13oi * b.eo;
    result.e23i = a.e23oi * b.eo;
    result.e1oi = a.e123oi * b.e23 - b.e123oi * a.e23;
    result.e2oi = -a.e123oi * b.e13 + b.e123oi * a.e13;
    result.e3oi = a.e123oi * b.e12 - b.e123oi * a.e12;
    
    $display("ga_alu dot product: a=%128h, b=%128h, res=%128h", a, b, result);
    
    return result;

  endfunction

  function automatic ga_multivector_t dualOperation(
    ga_multivector_t a
  );
    ga_multivector_t result;
    
    result        = '0;
    result.e123oi = a.scalar;
    result.e23oi  = a.e1;
    result.e13oi  = -a.e2;
    result.e12oi  = a.e3;
    result.e3oi   = -a.eo;
    result.e2oi   = a.ei;
    result.e1oi   = -a.e12;
    result.eoi    = a.e13;
    result.e3i    = -a.e23;
    result.e2i    = a.e1o;
    result.e1i    = -a.e2o;
    result.ei     = a.e3o;
    result.e3o    = a.e1i;
    result.e2o    = -a.e2i;
    result.e1o    = a.e3i;
    result.eo     = -a.eoi;
    result.e23    = -a.e1oi;
    result.e13    = a.e2oi;
    result.e12    = -a.e3oi;
    result.e3     = a.e12oi;
    result.e2     = -a.e13oi;
    result.e1     = a.e23oi;
    result.scalar = a.e123oi;
    
    return result;

  endfunction

  function automatic ga_multivector_t reverseOperation(
    ga_multivector_t a
  );
    ga_multivector_t result;
    
    result.scalar = a.scalar;
    result.e1     = a.e1;
    result.e2     = a.e2;
    result.e3     = a.e3;
    result.eo     = a.eo;
    result.ei     = a.ei;
    result.e12    = -a.e12;
    result.e13    = -a.e13;
    result.e23    = -a.e23;
    result.e1o    = -a.e1o;
    result.e2o    = -a.e2o;
    result.e3o    = -a.e3o;
    result.e1i    = -a.e1i;
    result.e2i    = -a.e2i;
    result.e3i    = -a.e3i;
    result.eoi    = -a.eoi;
    result.e123   = -a.e123;
    result.e12o   = -a.e12o;
    result.e13o   = -a.e13o;
    result.e23o   = -a.e23o;
    result.e12i   = -a.e12i;
    result.e13i   = -a.e13i;
    result.e23i   = -a.e23i;
    result.e1oi   = -a.e1oi;
    result.e2oi   = -a.e2oi;
    result.e3oi   = -a.e3oi;
    result.e123o  = a.e123o;
    result.e123i  = a.e123i;
    result.e12oi  = a.e12oi;
    result.e13oi  = a.e13oi;
    result.e23oi  = a.e23oi;
    result.e123oi = a.e123oi;
    
    return result;

  endfunction

  function automatic logic [DataWidth-1:0] normCalculation(
    ga_multivector_t a
  );
    logic [DataWidth-1:0] normSquared;
    
    normSquared = a.scalar * a.scalar +
                  a.e1 * a.e1 + a.e2 * a.e2 + a.e3 * a.e3 +
                  a.eo * a.eo + a.ei * a.ei +
                  a.e12 * a.e12 + a.e13 * a.e13 + a.e23 * a.e23 +
                  a.e1o * a.e1o + a.e2o * a.e2o + a.e3o * a.e3o +
                  a.e1i * a.e1i + a.e2i * a.e2i + a.e3i * a.e3i +
                  a.eoi * a.eoi + a.e123 * a.e123;
    
    return normSquared;

  endfunction

  function automatic ga_multivector_t rotorApplication(
    ga_multivector_t rotor,
    ga_multivector_t vector
  );
    ga_multivector_t revRotor = reverseOperation(rotor);
    ga_multivector_t temp = geometricProduct(rotor, vector);

    return geometricProduct(temp, revRotor);

  endfunction

  function automatic ga_multivector_t reflectionOperation(
    ga_multivector_t vector,
    ga_multivector_t normal
  );

    return vector;

  endfunction

  assign result_o = result_q;
  assign error_o = error_q;

endmodule
