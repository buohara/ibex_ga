module ga_even_alu
  import ga_pkg::*;
(
  input  logic            clk_i,
  input  logic            rst_ni,
  input  ga_multivector_t operand_a_i,
  input  ga_multivector_t operand_b_i,
  input  ga_funct_e       operation_i,
  input  logic            valid_i,
  output logic            ready_o,
  output logic            valid_o,
  output ga_multivector_t result_o,
  output logic            error_o
);
  typedef enum logic [1:0] {IDLE,BUSY,DONE} st_e;
  st_e st_q, st_d;

  ga_multivector_t r_q, r_d;
  ga_even_multivector_t a_e_q, b_e_q;
  ga_funct_e op_q;
  logic error_q, error_d;

  assign ready_o  = (st_q == IDLE);
  assign valid_o  = (st_q == DONE);
  assign result_o = r_q;
  assign error_o  = error_q;

  // Simple even add/sub (extend as needed)
  function automatic ga_even_multivector_t even_add(ga_even_multivector_t a, b);
    ga_even_multivector_t r;
    r = '0;
    r.scalar = a.scalar + b.scalar;
    r.e12    = a.e12    + b.e12;   r.e13   = a.e13   + b.e13;   r.e23   = a.e23   + b.e23;
    r.e1o    = a.e1o    + b.e1o;   r.e2o   = a.e2o   + b.e2o;   r.e3o   = a.e3o   + b.e3o; r.e123o = a.e123o + b.e123o;
    r.e1i    = a.e1i    + b.e1i;   r.e2i   = a.e2i   + b.e2i;   r.e3i   = a.e3i   + b.e3i;
    r.e12i   = a.e12i   + b.e12i;  r.e13i  = a.e13i  + b.e13i;  r.e23i  = a.e23i  + b.e23i; r.e123i = a.e123i + b.e123i;
    r.eoi    = a.eoi    + b.eoi;
    return r;
  endfunction

  // Placeholder even geometric product (reuse full, then mask)
  function automatic ga_even_multivector_t even_mul(ga_even_multivector_t a, b);
    ga_multivector_t full = geometricProduct(even_to_mv(a), even_to_mv(b));
    return mv_to_even(full);
  endfunction

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      st_q    <= IDLE;
      a_e_q   <= '0;
      b_e_q   <= '0;
      op_q    <= ga_funct_e'(0);
      r_q     <= '0;
      error_q <= 1'b0;
    end else begin
      st_q    <= st_d;
      if (ready_o && valid_i) begin
        a_e_q <= mv_to_even(operand_a_i);
        b_e_q <= mv_to_even(operand_b_i);
        op_q  <= operation_i;
      end
      r_q     <= r_d;
      error_q <= error_d;
    end
  end

  always_comb begin
    st_d    = st_q;
    r_d     = r_q;
    error_d = error_q;

    case (st_q)
      IDLE: if (valid_i) begin
        st_d    = BUSY;
        error_d = 1'b0;
      end
      BUSY: begin
        ga_even_multivector_t res_e = '0;
        unique case (op_q)
          GA_FUNCT_ADD:  res_e = even_add(a_e_q, b_e_q);
          GA_FUNCT_SUB:  res_e = even_add(a_e_q, even_mul(mv_to_even('0), b_e_q)); // replace with proper negate
          GA_FUNCT_MUL:  res_e = even_mul(a_e_q, b_e_q);
          GA_FUNCT_DUAL: res_e = mv_to_even(dualOperation(even_to_mv(a_e_q)));
          GA_FUNCT_REV:  res_e = mv_to_even(reverseOperation(even_to_mv(a_e_q)));
          GA_FUNCT_NORM: res_e = mv_to_even(normOperation(even_to_mv(a_e_q)));
          default: begin
            res_e   = '0;
            error_d = 1'b1;
          end
        endcase
        r_d  = even_to_mv(res_e);
        st_d = DONE;
      end
      DONE: st_d = IDLE;
    endcase
  end
endmodule