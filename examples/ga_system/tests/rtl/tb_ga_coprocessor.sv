// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Comprehensive testbench for GA coprocessor
 * Uses pre-generated test vectors - Verilator compatible version
 */

`timescale 1ns / 1ps

module tb_ga_coprocessor;

  import ga_pkg::*;

  parameter int NUM_TESTS = 1000;
  parameter int CLK_PERIOD = 10;
  
  logic clk;
  logic rst_n;
  
  initial begin
    clk = 0;
    forever #(CLK_PERIOD/2) clk = ~clk;
  end

  ga_req_t  ga_req;
  ga_resp_t ga_resp;
  
  logic [31:0] test_count;
  logic [31:0] pass_count;
  logic [31:0] fail_count;
  logic test_active;
  logic test_complete;
  
  logic [63:0] test_inputs_mem  [0:NUM_TESTS-1];
  logic [31:0] test_outputs_mem [0:NUM_TESTS-1];
  logic [3:0]  test_control_mem [0:NUM_TESTS-1];
  
  logic        unused_ga_debug_req;
  logic [31:0] unused_ga_debug_rdata;
  logic [191:0] unused_ga_perf;

  ga_coprocessor dut (
    .clk_i              (clk),
    .rst_ni             (rst_n),
    .ga_req_i           (ga_req),
    .ga_resp_o          (ga_resp),
    .ga_debug_req_o     (unused_ga_debug_req),
    .ga_debug_we_i      (1'b0),
    .ga_debug_addr_i    (5'b0),
    .ga_debug_wdata_i   (32'b0),
    .ga_debug_rdata_o   (unused_ga_debug_rdata),
    .ga_perf_o          (unused_ga_perf)
  );

  class GATestLogger;
    integer log_file;
    string operation_names[12] = {
      "ADD", "SUB", "MUL", "WEDGE", "DOT", "DUAL", 
      "REV", "NORM", "LOAD", "STORE", "ROTATE", "REFLECT"
    };
    
    int op_counts[12];
    int op_passes[12];
    int op_fails[12];
    
    function new();
      log_file = $fopen("ga_test_verbose.log", "w");
      if (log_file == 0) begin
        $error("Could not create verbose log file");
      end
      
      for (int i = 0; i < 12; i++) begin
        op_counts[i] = 0;
        op_passes[i] = 0;
        op_fails[i] = 0;
      end
      
      $fwrite(log_file, "=== GA Coprocessor Verbose Test Log ===\n");
      $fwrite(log_file, "Format: TEST_ID | OPERATION | OPERAND_A | OPERAND_B | EXPECTED | ACTUAL | STATUS\n");
      $fwrite(log_file, "================================================================================\n\n");
    endfunction
    
    function void log_test_result(
      int test_id, 
      int op_code, 
      logic [31:0] operand_a, 
      logic [31:0] operand_b,
      logic [31:0] expected,
      logic [31:0] actual,
      bit passed,
      bit error_flag,
      bit overflow_flag,
      bit underflow_flag
    );
      string status_str;
      string flags_str = "";
      
      op_counts[op_code]++;
      if (passed) op_passes[op_code]++;
      else op_fails[op_code]++;
      
      status_str = passed ? "PASS" : "FAIL";
      
      if (error_flag) flags_str = {flags_str, " ERROR"};
      if (overflow_flag) flags_str = {flags_str, " OVERFLOW"};
      if (underflow_flag) flags_str = {flags_str, " UNDERFLOW"};
      
      $fwrite(log_file, "%5d | %8s | %08x | %08x | %08x | %08x | %s%s\n",
              test_id, operation_names[op_code], operand_a, operand_b, 
              expected, actual, status_str, flags_str);
              
      if (test_id % 100 == 0) begin
        $fflush(log_file);
      end
    endfunction
    
    function void write_operation_summary();
      $fwrite(log_file, "\n\n=== Results by Operation ===\n");
      $fwrite(log_file, "Operation | Total | Passed | Failed | Pass Rate\n");
      $fwrite(log_file, "----------|-------|--------|--------|----------\n");
      
      for (int i = 0; i < 12; i++) begin
        if (op_counts[i] > 0) begin
          real pass_rate = (real'(op_passes[i]) / real'(op_counts[i])) * 100.0;
          $fwrite(log_file, "%8s  | %5d | %6d | %6d | %7.2f%%\n",
                  operation_names[i], op_counts[i], op_passes[i], op_fails[i], pass_rate);
        end
      end
      
      $fwrite(log_file, "\n=== Failed Tests by Operation ===\n");
      for (int op = 0; op < 12; op++) begin
        if (op_fails[op] > 0) begin
          $fwrite(log_file, "\n%s Failures (%d total):\n", operation_names[op], op_fails[op]);
          $fwrite(log_file, "Use 'grep \"| %s |.*FAIL\"' to find all %s failures\n", 
                  operation_names[op], operation_names[op]);
        end
      end
    endfunction
    
    function void close();
      write_operation_summary();
      $fclose(log_file);
    endfunction
  endclass

  GATestLogger logger;
  
  initial begin
    $display("Loading test vectors...");
    $readmemh("vectors/ga_test_inputs.mem", test_inputs_mem);
    $readmemh("vectors/ga_test_outputs.mem", test_outputs_mem);
    $readmemh("vectors/ga_test_control.mem", test_control_mem);
    $display("Test vectors loaded successfully");
  end
  
  initial begin
    $display("=== GA Coprocessor Test Suite ===");
    $display("Running %0d test vectors", NUM_TESTS);
    
    logger = new();
    
    rst_n         = 0;
    ga_req        = '0;
    test_count    = 0;
    pass_count    = 0;
    fail_count    = 0;
    test_active   = 0;
    test_complete = 0;
    
    repeat(10) @(posedge clk);
    rst_n = 1;
    repeat(5) @(posedge clk);
    
    test_active = 1;
    begin : test_loop

      int i;
      for (i = 0; i < NUM_TESTS; i++) begin
        
        run_single_test(i);
        test_count++;
        
        if (i % 50 == 0) begin
          $display("Progress: %0d/%0d tests completed", i, NUM_TESTS);
        end

        repeat(5) @(posedge clk);

      end

    end
    
    test_active   = 0;
    test_complete = 1;
    
    $display("\n=== Test Results ===");
    $display("Total tests:  %0d", test_count);
    $display("Passed:       %0d", pass_count);
    $display("Failed:       %0d", fail_count);
    $display("Pass rate:    %.2f%%", (real'(pass_count) / real'(test_count)) * 100.0);
    
    if (fail_count == 0) begin
      $display("*** ALL TESTS PASSED ***");
    end else begin
      $display("*** %0d TESTS FAILED ***", fail_count);
    end
    
    logger.close();
    $display("Verbose log written to: ga_test_verbose.log");
    
    $finish;
  end
  
  task run_single_test(int test_index);
    logic [31:0] operand_a, operand_b;
    logic [31:0] expected_result;
    logic [3:0]  function_code;
    logic [31:0] actual_result;
    logic        timeout;
    int          cycle_count;
    bit          test_passed;
    bit          should_continue;
    
    {operand_a, operand_b}  = test_inputs_mem[test_index];
    expected_result         = test_outputs_mem[test_index];
    function_code           = test_control_mem[test_index];
    
    should_continue = 1'b1;
    
    ga_req.valid            = 1'b1;
    ga_req.operand_a        = operand_a;
    ga_req.operand_b        = operand_b;
    ga_req.funct            = ga_funct_e'(function_code);
    ga_req.rd_addr          = 5'h0;
    ga_req.ga_reg_a         = 5'h0;
    ga_req.ga_reg_b         = 5'h1;
    ga_req.we               = 1'b1;
    ga_req.use_ga_regs      = 1'b0;

    @(posedge clk);
    
    if (should_continue) begin

      timeout     = 0;
      cycle_count = 0;
      
      while (!ga_resp.ready && !timeout && should_continue) begin
        
        @(posedge clk);
        cycle_count++;
        
        if (cycle_count > 100) begin

          timeout         = 1;
          should_continue = 1'b0;

        end

      end
      
      if (timeout) begin

        $error("Test %0d: Timeout waiting for ready", test_index);
        fail_count++;
        ga_req.valid    = 1'b0;
        should_continue = 1'b0;

      end

    end
    
    if (should_continue) begin

      ga_req.valid  = 1'b0;
      timeout       = 0;
      cycle_count   = 0;

      while (!ga_resp.valid && !timeout) begin

        @(posedge clk);
          cycle_count++;
        
        if (cycle_count > 100) begin

          timeout         = 1;
          should_continue = 1'b0;

        end
      
      end
      
      if (timeout) begin

        $error("Test %0d: Timeout waiting for response", test_index);
        fail_count++;
        should_continue = 1'b0;

      end

    end
    
    if (should_continue) begin

      actual_result = ga_resp.result;
      test_passed   = (actual_result == expected_result);

      if (test_passed) begin

        pass_count++;

        if (test_index < 10) begin

          $display("Test %0d PASS: op=%0d, a=%h, b=%h, expected=%h, actual=%h", 
                   test_index, function_code, operand_a, operand_b, expected_result, actual_result);

        end

      end else begin

        fail_count++;
        $display("Test %0d FAIL: op=%0d, a=%h, b=%h, expected=%h, actual=%h", 
               test_index, function_code, operand_a, operand_b, expected_result, actual_result);

      end
      
      logger.log_test_result(
        test_index, {28'b0, function_code}, operand_a, operand_b, 
        expected_result, actual_result, test_passed,
        ga_resp.error, ga_resp.overflow, ga_resp.underflow
      );
      
      if (ga_resp.error) begin
        $display("Warning: Test %0d: Error flag set", test_index);
      end

      if (ga_resp.overflow) begin
        $display("Warning: Test %0d: Overflow flag set", test_index);
      end

      if (ga_resp.underflow) begin
        $display("Warning: Test %0d: Underflow flag set", test_index);
      end
    end
    
    @(posedge clk);

  endtask
  
  logic [31:0] total_cycles;
  logic [31:0] busy_cycles;
  
  always_ff @(posedge clk or negedge rst_n) begin

    if (!rst_n) begin

      total_cycles <= 0;
      busy_cycles <= 0;

    end else if (test_active) begin

      total_cycles <= total_cycles + 1;

      if (ga_resp.busy) begin

        busy_cycles <= busy_cycles + 1;

      end

    end

  end
  
  always @(posedge test_complete) begin

    $display("\n=== Performance Metrics ===");
    $display("Total cycles:     %0d", total_cycles);
    $display("Busy cycles:      %0d", busy_cycles);
    $display("Utilization:      %.2f%%", (real'(busy_cycles) / real'(total_cycles)) * 100.0);
    $display("Avg cycles/test:  %.2f", real'(total_cycles) / real'(test_count));

  end
  
  initial begin

    if ($test$plusargs("WAVES")) begin

      $dumpfile("ga_coprocessor_test.vcd");
      $dumpvars(0, tb_ga_coprocessor);

    end

  end
  
  initial begin

    #(CLK_PERIOD * NUM_TESTS * 100);
    if (!test_complete) begin

      $error("Test suite timeout!");
      $finish;

    end

  end

endmodule
