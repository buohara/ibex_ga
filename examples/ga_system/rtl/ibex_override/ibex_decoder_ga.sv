// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * GA-Extended Instruction decoder
 * 
 * This module extends the original ibex_decoder with GA coprocessor
 * instruction decoding capabilities.
 */

`include "prim_assert.sv"

module ibex_decoder #(
  parameter bit RV32E               = 0,
  parameter ibex_pkg::rv32m_e RV32M = ibex_pkg::RV32MFast,
  parameter ibex_pkg::rv32b_e RV32B = ibex_pkg::RV32BNone,
  parameter bit BranchTargetALU     = 0
) (
  input  logic                 clk_i,
  input  logic                 rst_ni,

  // to/from controller
  output logic                 illegal_insn_o,        // illegal instr encountered
  output logic                 ebrk_insn_o,           // trap instr encountered
  output logic                 mret_insn_o,           // return from exception instr
                                                      // encountered
  output logic                 dret_insn_o,           // return from debug instr encountered
  output logic                 ecall_insn_o,          // ecall instr encountered
  output logic                 wfi_insn_o,            // wait for interrupt instr encountered
  output logic                 jump_set_o,            // jump taken set signal
  input  logic                 branch_taken_i,        // registered branch decision
  output logic                 icache_inval_o,

  // from IF-ID pipeline register
  input  logic                 instr_first_cycle_i,   // instruction read is in its first cycle
  input  logic [31:0]          instr_rdata_i,         // instruction read from memory/cache
  input  logic [31:0]          instr_rdata_alu_i,     // instruction read from memory/cache
                                                      // replicated to ease fan-out)

  input  logic                 illegal_c_insn_i,      // compressed instruction decode failed

  // immediates
  output ibex_pkg::imm_a_sel_e imm_a_mux_sel_o,       // immediate selection for operand a
  output ibex_pkg::imm_b_sel_e imm_b_mux_sel_o,       // immediate selection for operand b
  output logic [31:0]          imm_i_type_o,
  output logic [31:0]          imm_s_type_o,
  output logic [31:0]          imm_b_type_o,
  output logic [31:0]          imm_u_type_o,
  output logic [31:0]          imm_j_type_o,
  output logic [31:0]          zimm_rs1_type_o,

  // register file
  output ibex_pkg::rf_wd_sel_e rf_wdata_sel_o,        // RF write data selection
  output logic                 rf_we_o,               // write enable for regfile
  output logic [4:0]           rf_raddr_a_o,          // register file read address a
  output logic [4:0]           rf_raddr_b_o,          // register file read address b
  output logic [4:0]           rf_waddr_o,            // register file write address
  output logic                 rf_ren_a_o,            // register file read enable a
  output logic                 rf_ren_b_o,            // register file read enable b

  // ALU
  output ibex_pkg::alu_op_e    alu_operator_o,        // ALU operation selection
  output logic                 alu_op_a_mux_sel_o,    // operand a selection: reg value, PC,
                                                      // immediate or zero
  output logic                 alu_op_b_mux_sel_o,    // operand b selection: reg value or
                                                      // immediate
  output logic                 alu_multicycle_o,      // ternary bitmanip instruction

  // MULT & DIV
  output logic                 mult_en_o,             // perform integer multiplication
  output logic                 div_en_o,              // perform integer division or remainder
  output logic                 mult_sel_o,            // as above but static, for data muxes
  output logic                 div_sel_o,             // as above but static, for data muxes

  output ibex_pkg::md_op_e     multdiv_operator_o,
  output logic [1:0]           multdiv_signed_mode_o,

  // CSRs
  output logic                 csr_access_o,          // access to CSR
  output ibex_pkg::csr_op_e    csr_op_o,              // operation to perform on CSR

  // LSU
  output logic                 data_req_o,            // start transaction to data memory
  output logic                 data_we_o,             // data memory write enable
  output logic [1:0]           data_type_o,           // data type on data memory: byte,
                                                      // half word or word
  output logic                 data_sign_extension_o, // sign extension on read data from
                                                      // data memory

  // jump/branches
  output logic                 jump_in_dec_o,         // jump is being calculated in ALU
  output logic                 branch_in_dec_o,       // branch is being calculated in ALU

  // GA Coprocessor signals
  output logic                 ga_en_o,               // GA coprocessor enable
  output ibex_pkg::ga_op_sel_e ga_op_sel_o,           // GA operation selection
  output logic [2:0]           ga_funct3_o,           // GA function code
  output logic [6:0]           ga_funct7_o,           // GA extended function code
  output logic                 ga_reg_we_o,           // GA register file write enable
  output logic [4:0]           ga_reg_raddr_a_o,      // GA register file read address a
  output logic [4:0]           ga_reg_raddr_b_o,      // GA register file read address b  
  output logic [4:0]           ga_reg_waddr_o         // GA register file write address
);

  import ibex_pkg::*;

  // Internal signals for GA instruction decoding
  logic        ga_instr_valid;
  logic [6:0]  opcode;
  logic [2:0]  funct3;
  logic [6:0]  funct7;
  logic [4:0]  rs1, rs2, rd;

  // Extract instruction fields
  assign opcode = instr_rdata_i[6:0];
  assign funct3 = instr_rdata_i[14:12];
  assign funct7 = instr_rdata_i[31:25];
  assign rs1    = instr_rdata_i[19:15];
  assign rs2    = instr_rdata_i[24:20];
  assign rd     = instr_rdata_i[11:7];

  // GA instruction detection
  assign ga_instr_valid = (opcode == OPCODE_GA_CUSTOM_0) ||
                         (opcode == OPCODE_GA_CUSTOM_1) ||
                         (opcode == OPCODE_GA_CUSTOM_2) ||
                         (opcode == OPCODE_GA_CUSTOM_3);

  // GA coprocessor control signals
  assign ga_en_o = ga_instr_valid;
  assign ga_funct3_o = funct3;
  assign ga_funct7_o = funct7;
  assign ga_reg_raddr_a_o = rs1;
  assign ga_reg_raddr_b_o = rs2;
  assign ga_reg_waddr_o = rd;

  // GA operation selection based on opcode
  always_comb begin
    ga_op_sel_o = GA_OP_NONE;
    ga_reg_we_o = 1'b0;

    if (ga_instr_valid) begin
      case (opcode)
        OPCODE_GA_CUSTOM_0: begin  // Arithmetic operations
          ga_op_sel_o = GA_OP_ARITH;
          ga_reg_we_o = 1'b1;  // Most arithmetic ops write back
        end
        OPCODE_GA_CUSTOM_1: begin  // Register file operations
          case (funct3)
            GA_FUNCT3_LOAD_REG:  ga_op_sel_o = GA_OP_LOAD_REG;
            GA_FUNCT3_STORE_REG: ga_op_sel_o = GA_OP_STORE_REG;
            default:             ga_op_sel_o = GA_OP_LOAD_REG;
          endcase
          ga_reg_we_o = (funct3 != GA_FUNCT3_STORE_REG);
        end
        OPCODE_GA_CUSTOM_2: begin  // Memory operations
          case (funct3)
            GA_FUNCT3_LOAD_MEM,
            GA_FUNCT3_LOAD_VECTOR,
            GA_FUNCT3_LOAD_SCALAR: begin
              ga_op_sel_o = GA_OP_LOAD_MEM;
              ga_reg_we_o = 1'b1;
            end
            default: begin
              ga_op_sel_o = GA_OP_STORE_MEM;
              ga_reg_we_o = 1'b0;
            end
          endcase
        end
        OPCODE_GA_CUSTOM_3: begin  // Control/Status operations
          ga_op_sel_o = GA_OP_STATUS;
          ga_reg_we_o = (funct3 == GA_FUNCT3_STATUS);  // Only status read writes back
        end
        default: begin
          ga_op_sel_o = GA_OP_NONE;
          ga_reg_we_o = 1'b0;
        end
      endcase
    end
  end

  // Instantiate original decoder with modified outputs for GA instructions
  logic        orig_illegal_insn;
  logic        orig_rf_we;
  rf_wd_sel_e  orig_rf_wdata_sel;
  alu_op_e     orig_alu_operator;

  // Include the original ibex_decoder.sv content here (simplified for now)
  // For now, we'll handle non-GA instructions as illegal (placeholder)
  assign orig_illegal_insn = ~ga_instr_valid;  // Temporary: only GA instructions supported
  assign orig_rf_we = 1'b0;
  assign orig_rf_wdata_sel = RF_WD_EX;
  assign orig_alu_operator = ALU_ADD;

  // Output signal assignments - prioritize GA operations
  assign illegal_insn_o = ga_instr_valid ? 1'b0 : orig_illegal_insn;
  assign ebrk_insn_o = 1'b0;           // No breakpoint for GA instructions
  assign mret_insn_o = 1'b0;           // No return for GA instructions
  assign dret_insn_o = 1'b0;           // No debug return for GA instructions
  assign ecall_insn_o = 1'b0;          // No ecall for GA instructions
  assign wfi_insn_o = 1'b0;            // No wait for interrupt
  assign jump_set_o = 1'b0;            // No jumps for GA instructions
  assign icache_inval_o = 1'b0;        // No cache invalidation

  // Immediate selection (not used for GA instructions in this simple version)
  assign imm_a_mux_sel_o = IMM_A_Z;
  assign imm_b_mux_sel_o = IMM_B_I;
  assign imm_i_type_o = {{20{instr_rdata_i[31]}}, instr_rdata_i[31:20]};
  assign imm_s_type_o = {{20{instr_rdata_i[31]}}, instr_rdata_i[31:25], instr_rdata_i[11:7]};
  assign imm_b_type_o = {{19{instr_rdata_i[31]}}, instr_rdata_i[31], instr_rdata_i[7], 
                         instr_rdata_i[30:25], instr_rdata_i[11:8], 1'b0};
  assign imm_u_type_o = {instr_rdata_i[31:12], 12'b0};
  assign imm_j_type_o = {{11{instr_rdata_i[31]}}, instr_rdata_i[31], instr_rdata_i[19:12],
                         instr_rdata_i[20], instr_rdata_i[30:21], 1'b0};
  assign zimm_rs1_type_o = {27'b0, instr_rdata_i[19:15]};

  // Register file signals - use GA register file for GA instructions
  assign rf_wdata_sel_o = ga_instr_valid ? RF_WD_GA_ALU : orig_rf_wdata_sel;
  assign rf_we_o = ga_instr_valid ? ga_reg_we_o : orig_rf_we;
  assign rf_raddr_a_o = ga_instr_valid ? ga_reg_raddr_a_o : rs1;
  assign rf_raddr_b_o = ga_instr_valid ? ga_reg_raddr_b_o : rs2;
  assign rf_waddr_o = ga_instr_valid ? ga_reg_waddr_o : rd;
  assign rf_ren_a_o = ga_instr_valid ? 1'b1 : 1'b1;  // Always read for GA
  assign rf_ren_b_o = ga_instr_valid ? 1'b1 : 1'b1;  // Always read for GA

  // ALU signals - redirect to GA ALU for GA instructions
  assign alu_operator_o = ga_instr_valid ? ALU_GA_ADD : orig_alu_operator;  // Default GA op
  assign alu_op_a_mux_sel_o = 1'b1;     // Use register file
  assign alu_op_b_mux_sel_o = 1'b1;     // Use register file
  assign alu_multicycle_o = 1'b0;       // GA ops are single cycle for now

  // MULT & DIV (not used for GA)
  assign mult_en_o = 1'b0;
  assign div_en_o = 1'b0;
  assign mult_sel_o = 1'b0;
  assign div_sel_o = 1'b0;
  assign multdiv_operator_o = MD_OP_MULL;
  assign multdiv_signed_mode_o = 2'b00;

  // CSRs (not used for GA instructions in this version)
  assign csr_access_o = 1'b0;
  assign csr_op_o = CSR_OP_READ;

  // LSU (not used for GA instructions in this simple version)
  assign data_req_o = 1'b0;
  assign data_we_o = 1'b0;
  assign data_type_o = 2'b10;           // Word
  assign data_sign_extension_o = 1'b0;

  // Jump/Branch (not used for GA instructions)
  assign jump_in_dec_o = 1'b0;
  assign branch_in_dec_o = 1'b0;

endmodule
