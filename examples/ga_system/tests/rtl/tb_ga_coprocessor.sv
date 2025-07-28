// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Comprehensive testbench for GA coprocessor
 * Uses pre-generated test vectors and assertion-based verification
 */

`timescale 1ns / 1ps

module tb_ga_coprocessor;

  import ga_pkg::*;

  // Test parameters
  parameter int NUM_TESTS = 10000;
  parameter int CLK_PERIOD = 10;  // 100MHz clock
  
  // Clock and reset
  logic clk;
  logic rst_n;
  
  // GA coprocessor interface
  ga_req_t  ga_req;
  ga_resp_t ga_resp;
  
  // Test control
  logic [31:0] test_count;
  logic [31:0] pass_count;
  logic [31:0] fail_count;
  logic test_active;
  logic test_complete;
  
  // Test vector memories
  logic [63:0] test_inputs_mem  [0:NUM_TESTS-1];  // operand_a[31:0], operand_b[31:0]
  logic [31:0] test_outputs_mem [0:NUM_TESTS-1];  // expected result
  logic [3:0]  test_control_mem [0:NUM_TESTS-1];  // GA function code
  
  // Instantiate GA coprocessor
  ga_coprocessor dut (
    .clk_i          (clk),
    .rst_ni         (rst_n),
    .ga_req_i       (ga_req),
    .ga_resp_o      (ga_resp)
  );
  
  // Clock generation
  initial begin
    clk = 0;
    forever #(CLK_PERIOD/2) clk = ~clk;
  end
  
  // Load test vectors
  initial begin
    $display("Loading test vectors...");
    
    // Load input vectors (operand pairs)
    if (!$fopen("tests/vectors/ga_test_inputs.mem", "r")) begin
      $error("Could not open ga_test_inputs.mem");
      $finish;
    end
    $readmemh("tests/vectors/ga_test_inputs.mem", test_inputs_mem);
    
    // Load expected outputs
    if (!$fopen("tests/vectors/ga_test_outputs.mem", "r")) begin
      $error("Could not open ga_test_outputs.mem");
      $finish;
    end
    $readmemh("tests/vectors/ga_test_outputs.mem", test_outputs_mem);
    
    // Load control signals (function codes)
    if (!$fopen("tests/vectors/ga_test_control.mem", "r")) begin
      $error("Could not open ga_test_control.mem");
      $finish;
    end
    $readmemh("tests/vectors/ga_test_control.mem", test_control_mem);
    
    $display("Test vectors loaded successfully");
  end
  
  // Test sequence
  initial begin
    $display("=== GA Coprocessor Test Suite ===");
    $display("Running %0d test vectors", NUM_TESTS);
    
    // Initialize
    rst_n = 0;
    ga_req = '0;
    test_count = 0;
    pass_count = 0;
    fail_count = 0;
    test_active = 0;
    test_complete = 0;
    
    // Reset sequence
    repeat(10) @(posedge clk);
    rst_n = 1;
    repeat(5) @(posedge clk);
    
    // Run tests
    test_active = 1;
    for (int i = 0; i < NUM_TESTS; i++) begin
      run_single_test(i);
      test_count++;
      
      // Progress reporting
      if (i % 100 == 0) begin
        $display("Progress: %0d/%0d tests completed", i, NUM_TESTS);
      end
    end
    
    test_active = 0;
    test_complete = 1;
    
    // Final report
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
    
    $finish;
  end
  
  // Task to run a single test
  task run_single_test(int test_index);
    logic [31:0] operand_a, operand_b;
    logic [31:0] expected_result;
    logic [3:0]  function_code;
    logic [31:0] actual_result;
    logic        timeout;
    int          cycle_count;
    
    // Extract test data
    {operand_a, operand_b} = test_inputs_mem[test_index];
    expected_result = test_outputs_mem[test_index];
    function_code = test_control_mem[test_index];
    
    // Setup request
    ga_req.valid      = 1'b1;
    ga_req.operand_a  = operand_a;
    ga_req.operand_b  = operand_b;
    ga_req.funct      = ga_funct_e'(function_code);
    ga_req.rd_addr    = 5'h0;  // Use register 0 for testing
    ga_req.ga_reg_a   = 5'h0;
    ga_req.ga_reg_b   = 5'h1;
    ga_req.we         = 1'b1;
    ga_req.use_ga_regs = 1'b0; // Use CPU registers for simplicity
    
    @(posedge clk);
    
    // Wait for ready
    timeout = 0;
    cycle_count = 0;
    while (!ga_resp.ready && !timeout) begin
      @(posedge clk);
      cycle_count++;
      if (cycle_count > 100) timeout = 1;
    end
    
    if (timeout) begin
      $error("Test %0d: Timeout waiting for ready", test_index);
      fail_count++;
      ga_req.valid = 1'b0;
      return;
    end
    
    // Wait for valid response
    ga_req.valid = 1'b0;
    timeout = 0;
    cycle_count = 0;
    while (!ga_resp.valid && !timeout) begin
      @(posedge clk);
      cycle_count++;
      if (cycle_count > 100) timeout = 1;
    end
    
    if (timeout) begin
      $error("Test %0d: Timeout waiting for response", test_index);
      fail_count++;
      return;
    end
    
    // Check result
    actual_result = ga_resp.result;
    
    if (actual_result == expected_result) begin
      pass_count++;
      if (test_index < 10) begin  // Verbose for first few tests
        $display("Test %0d PASS: op=%0d, a=%h, b=%h, expected=%h, actual=%h", 
                 test_index, function_code, operand_a, operand_b, expected_result, actual_result);
      end
    end else begin
      fail_count++;
      $error("Test %0d FAIL: op=%0d, a=%h, b=%h, expected=%h, actual=%h", 
             test_index, function_code, operand_a, operand_b, expected_result, actual_result);
    end
    
    // Check for error flags
    if (ga_resp.error) begin
      $warning("Test %0d: Error flag set", test_index);
    end
    if (ga_resp.overflow) begin
      $warning("Test %0d: Overflow flag set", test_index);
    end
    if (ga_resp.underflow) begin
      $warning("Test %0d: Underflow flag set", test_index);
    end
    
    @(posedge clk);
  endtask
  
  // Assertion checks
  
  // Check that ready and valid are not both high when request is not valid
  property no_spurious_response;
    @(posedge clk) disable iff (!rst_n)
    !ga_req.valid |-> ##[1:10] !(ga_resp.valid && ga_resp.ready);
  endproperty
  assert property (no_spurious_response) else $error("Spurious response detected");
  
  // Check that response is valid within reasonable time after request
  property response_timeout;
    @(posedge clk) disable iff (!rst_n)
    ga_req.valid |-> ##[1:100] ga_resp.valid;
  endproperty
  assert property (response_timeout) else $error("Response timeout");
  
  // Check that ready goes high within reasonable time
  property ready_timeout;
    @(posedge clk) disable iff (!rst_n)
    ga_req.valid |-> ##[0:50] ga_resp.ready;
  endproperty
  assert property (ready_timeout) else $error("Ready timeout");
  
  // Check that busy flag behavior is consistent
  property busy_flag_consistency;
    @(posedge clk) disable iff (!rst_n)
    ga_resp.busy |-> !ga_resp.ready;
  endproperty
  assert property (busy_flag_consistency) else $error("Busy flag inconsistency");
  
  // Check function code bounds
  property valid_function_code;
    @(posedge clk) disable iff (!rst_n)
    ga_req.valid |-> (ga_req.funct <= GA_FUNCT_REFLECT);
  endproperty
  assert property (valid_function_code) else $error("Invalid function code");
  
  // Performance monitoring
  logic [31:0] total_cycles;
  logic [31:0] busy_cycles;
  
  always_ff @(posedge clk) begin
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
  
  // Final performance report
  always @(posedge test_complete) begin
    $display("\n=== Performance Metrics ===");
    $display("Total cycles:     %0d", total_cycles);
    $display("Busy cycles:      %0d", busy_cycles);
    $display("Utilization:      %.2f%%", (real'(busy_cycles) / real'(total_cycles)) * 100.0);
    $display("Avg cycles/test:  %.2f", real'(total_cycles) / real'(test_count));
  end
  
  // Waveform dumping
  initial begin
    if ($test$plusargs("WAVES")) begin
      $dumpfile("ga_coprocessor_test.vcd");
      $dumpvars(0, tb_ga_coprocessor);
    end
  end
  
  // Test timeout watchdog
  initial begin
    #(CLK_PERIOD * NUM_TESTS * 200);  // Conservative timeout
    if (!test_complete) begin
      $error("Test suite timeout!");
      $finish;
    end
  end

endmodule
