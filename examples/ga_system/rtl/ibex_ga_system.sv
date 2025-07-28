// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Ibex GA System Top Level
 * 
 * This is the top-level module that integrates the Ibex RISC-V core with
 * the Geometric Algebra coprocessor system.
 */

module ibex_ga_system
  import ibex_pkg::*;
  import ga_pkg::*;
#(
  parameter int unsigned MHPMCounterNum   = 0,
  parameter int unsigned MHPMCounterWidth = 40,
  parameter bit          PMPEnable        = 1'b0,
  parameter int unsigned PMPGranularity   = 0,
  parameter int unsigned PMPNumRegions    = 4,
  parameter int unsigned DmHaltAddr       = 32'h1A110800,
  parameter int unsigned DmExceptionAddr  = 32'h1A110808,
  parameter bit          RV32E            = 1'b0,
  parameter rv32m_e      RV32M            = RV32MFast,
  parameter rv32b_e      RV32B            = RV32BNone,
  parameter bit          BranchTargetALU  = 1'b0,
  parameter bit          WritebackStage   = 1'b0,
  parameter bit          ICache           = 1'b0,
  parameter bit          ICacheECC        = 1'b0,
  parameter bit          ICacheScramble   = 1'b0,
  parameter bit          BranchPredictor  = 1'b0,
  parameter bit          DbgTriggerEn     = 1'b0,
  parameter bit          SecureIbex       = 1'b0,
  
  // GA-specific parameters
  parameter int unsigned GARegFileSize    = 32,
  parameter bit          GAEnable         = 1'b1
) (
  // Clock and Reset
  input  logic        clk_i,
  input  logic        rst_ni,

  // Instruction memory interface
  output logic        instr_req_o,
  input  logic        instr_gnt_i,
  input  logic        instr_rvalid_i,
  output logic [31:0] instr_addr_o,
  input  logic [31:0] instr_rdata_i,
  input  logic        instr_err_i,

  // Data memory interface
  output logic        data_req_o,
  input  logic        data_gnt_i,
  input  logic        data_rvalid_i,
  output logic        data_we_o,
  output logic [3:0]  data_be_o,
  output logic [31:0] data_addr_o,
  output logic [31:0] data_wdata_o,
  input  logic [31:0] data_rdata_i,
  input  logic        data_err_i,

  // Interrupt inputs
  input  logic        irq_software_i,
  input  logic        irq_timer_i,
  input  logic        irq_external_i,
  input  logic [14:0] irq_fast_i,
  input  logic        irq_nm_i,

  // Debug Interface
  input  logic        debug_req_i,
  output crash_dump_t crash_dump_o,

  // CPU Control Signals
  input  ibex_mubi_t  fetch_enable_i,
  output logic        alert_minor_o,
  output logic        alert_major_internal_o,
  output logic        alert_major_bus_o,
  output ibex_mubi_t  core_busy_o,

  // GA Debug Interface
  output logic        ga_debug_req_o,
  input  logic        ga_debug_we_i,
  input  logic [4:0]  ga_debug_addr_i,
  input  logic [31:0] ga_debug_wdata_i,
  output logic [31:0] ga_debug_rdata_o,

  // GA Performance Monitoring
  output ga_perf_counters_t ga_perf_o
);

  ////////////////////////
  // Internal Signals   //
  ////////////////////////

  // GA Coprocessor Interface
  ga_req_t  ga_req;
  ga_resp_t ga_resp;

  // Core signals that would normally come from modified Ibex core
  logic        ga_req_valid;
  logic        ga_resp_ready;
  logic [31:0] ga_operand_a;
  logic [31:0] ga_operand_b;
  logic [4:0]  ga_rd_addr;
  logic [4:0]  ga_reg_a_addr;
  logic [4:0]  ga_reg_b_addr;
  ga_funct_e   ga_funct;
  logic        ga_we;
  logic        ga_use_ga_regs;

  ////////////////////////
  // Ibex Core Instance //
  ////////////////////////

  // For now, instantiate standard Ibex core
  // In a full implementation, this would be the modified core
  
  ibex_core_ga #(
    .PMPEnable        (PMPEnable),
    .PMPGranularity   (PMPGranularity),
    .PMPNumRegions    (PMPNumRegions),
    .MHPMCounterNum   (MHPMCounterNum),
    .MHPMCounterWidth (MHPMCounterWidth),
    .DmHaltAddr       (DmHaltAddr),
    .DmExceptionAddr  (DmExceptionAddr),
    .RV32E            (RV32E),
    .RV32M            (RV32M),
    .RV32B            (RV32B),
    .BranchTargetALU  (BranchTargetALU),
    .WritebackStage   (WritebackStage),
    .ICache           (ICache),
    .ICacheECC        (ICacheECC),
    .BranchPredictor  (BranchPredictor),
    .DbgTriggerEn     (DbgTriggerEn),
    .SecureIbex       (SecureIbex)
  ) u_ibex_core_ga (
    .clk_i               (clk_i),
    .rst_ni              (rst_ni),
    .hart_id_i           (32'b0),
    .boot_addr_i         (32'h00000000),

    // Instruction memory interface
    .instr_req_o         (instr_req_o),
    .instr_gnt_i         (instr_gnt_i),
    .instr_rvalid_i      (instr_rvalid_i),
    .instr_addr_o        (instr_addr_o),
    .instr_rdata_i       (instr_rdata_i),
    .instr_err_i         (instr_err_i),

    // Data memory interface
    .data_req_o          (data_req_o),
    .data_gnt_i          (data_gnt_i),
    .data_rvalid_i       (data_rvalid_i),
    .data_we_o           (data_we_o),
    .data_be_o           (data_be_o),
    .data_addr_o         (data_addr_o),
    .data_wdata_o        (data_wdata_o),
    .data_rdata_i        (data_rdata_i),
    .data_err_i          (data_err_i),

    // Debug signals (tie off unused ones)
    .dummy_instr_id_o    (),
    .dummy_instr_wb_o    (),
    .rf_raddr_a_o        (),
    .rf_raddr_b_o        (),
    .rf_waddr_wb_o       (),
    .rf_we_wb_o          (),
    .rf_wdata_wb_ecc_o   (),
    .rf_rdata_a_ecc_i    ('0),
    .rf_rdata_b_ecc_i    ('0),

    // Icache signals (tie off for basic system)
    .ic_tag_req_o        (),
    .ic_tag_write_o      (),
    .ic_tag_addr_o       (),
    .ic_tag_wdata_o      (),
    .ic_tag_rdata_i      ('{default:'0}),
    .ic_data_req_o       (),
    .ic_data_write_o     (),
    .ic_data_addr_o      (),
    .ic_data_wdata_o     (),
    .ic_data_rdata_i     ('{default:'0}),
    .ic_scr_key_valid_i  (1'b0),
    .ic_scr_key_req_o    (),

    // Interrupt inputs
    .irq_software_i      (irq_software_i),
    .irq_timer_i         (irq_timer_i),
    .irq_external_i      (irq_external_i),
    .irq_fast_i          (irq_fast_i),
    .irq_nm_i            (irq_nm_i),
    .irq_pending_o       (),

    // Debug Interface
    .debug_req_i         (debug_req_i),
    .crash_dump_o        (crash_dump_o),
    .double_fault_seen_o (),

    // CPU Control Signals
    .fetch_enable_i      (fetch_enable_i),
    .alert_minor_o       (alert_minor_o),
    .alert_major_internal_o (alert_major_internal_o),
    .alert_major_bus_o   (alert_major_bus_o),
    .core_busy_o         (core_busy_o)
  );

  ////////////////////////
  // GA Coprocessor     //
  ////////////////////////

  generate
    if (GAEnable) begin : gen_ga_coprocessor
      
      // Build GA request from decoded instruction
      // In a full implementation, this would come from the modified decoder
      always_comb begin
        ga_req.valid       = ga_req_valid;
        ga_req.operand_a   = ga_operand_a;
        ga_req.operand_b   = ga_operand_b;
        ga_req.rd_addr     = ga_rd_addr;
        ga_req.ga_reg_a    = ga_reg_a_addr;
        ga_req.ga_reg_b    = ga_reg_b_addr;
        ga_req.funct       = ga_funct;
        ga_req.we          = ga_we;
        ga_req.use_ga_regs = ga_use_ga_regs;
      end

      ga_coprocessor #(
        .GARegFileSize (GARegFileSize),
        .GADataWidth   (32),
        .GAPrecision   (GA_PRECISION_FP32),
        .GAAlgebra     (GA_ALGEBRA_3D)
      ) u_ga_coprocessor (
        .clk_i          (clk_i),
        .rst_ni         (rst_ni),
        .ga_req_i       (ga_req),
        .ga_resp_o      (ga_resp),
        .ga_debug_req_o (ga_debug_req_o),
        .ga_debug_we_i  (ga_debug_we_i),
        .ga_debug_addr_i(ga_debug_addr_i),
        .ga_debug_wdata_i(ga_debug_wdata_i),
        .ga_debug_rdata_o(ga_debug_rdata_o),
        .ga_perf_o      (ga_perf_o)
      );

    end else begin : gen_no_ga
      // Tie off GA signals when disabled
      assign ga_resp.valid     = 1'b0;
      assign ga_resp.result    = '0;
      assign ga_resp.error     = 1'b0;
      assign ga_resp.busy      = 1'b0;
      assign ga_resp.overflow  = 1'b0;
      assign ga_resp.underflow = 1'b0;
      
      assign ga_debug_req_o    = 1'b0;
      assign ga_debug_rdata_o  = '0;
      assign ga_perf_o         = '0;
    end
  endgenerate

  ////////////////////////
  // Placeholder Logic  //
  ////////////////////////

  // These signals would normally come from the modified Ibex decoder/core
  // For now, tie them off as placeholders
  assign ga_req_valid    = 1'b0;  // No GA instructions detected
  assign ga_resp_ready   = 1'b1;  // Always ready to accept results
  assign ga_operand_a    = '0;
  assign ga_operand_b    = '0;
  assign ga_rd_addr      = '0;
  assign ga_reg_a_addr   = '0;
  assign ga_reg_b_addr   = '0;
  assign ga_funct        = GA_FUNCT_ADD;
  assign ga_we           = 1'b0;
  assign ga_use_ga_regs  = 1'b0;

  ////////////////////////
  // Assertions         //
  ////////////////////////

  `ifdef ASSERT_ON
    // Check that GA coprocessor responds correctly
    assert property (@(posedge clk_i) disable iff (!rst_ni)
      (GAEnable && ga_req.valid && ga_resp.ready |-> ##[1:10] ga_resp.valid))
      else $error("GA coprocessor failed to respond");
  `endif

endmodule
