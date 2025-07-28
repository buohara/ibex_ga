// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Unit tests for individual GA operations
 * Tests each operation type with specific test cases
 */

`timescale 1ns / 1ps

module tb_ga_operations;

  import ga_pkg::*;

  // Test parameters
  parameter int CLK_PERIOD = 10;
  
  // Clock and reset
  logic clk;
  logic rst_n;
  
  // GA coprocessor interface
  ga_req_t  ga_req;
  ga_resp_t ga_resp;
  
  // Test results
  int tests_run = 0;
  int tests_passed = 0;
  int tests_failed = 0;
  
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
  
  // Test execution
  initial begin
    $display("=== GA Operations Unit Tests ===");
    
    // Initialize
    rst_n = 0;
    ga_req = '0;
    
    // Reset sequence
    repeat(10) @(posedge clk);
    rst_n = 1;
    repeat(5) @(posedge clk);
    
    // Run individual operation tests
    test_addition();
    test_subtraction();
    test_geometric_product();
    test_wedge_product();
    test_dot_product();
    test_reverse();
    test_norm();
    test_corner_cases();
    
    // Final report
    $display("\n=== Unit Test Results ===");
    $display("Tests run:    %0d", tests_run);
    $display("Passed:       %0d", tests_passed);
    $display("Failed:       %0d", tests_failed);
    $display("Success rate: %.1f%%", 
             (real'(tests_passed) / real'(tests_run)) * 100.0);
    
    if (tests_failed == 0) begin
      $display("*** ALL UNIT TESTS PASSED ***");
    end else begin
      $display("*** %0d UNIT TESTS FAILED ***", tests_failed);
    end
    
    $finish;
  end
  
  // Test addition operation
  task test_addition();
    $display("\n--- Testing GA Addition ---");
    
    // Test 1: Simple scalar addition
    test_operation(
      .op(GA_FUNCT_ADD),
      .operand_a(32'h3f800000),  // 1.0
      .operand_b(32'h40000000),  // 2.0
      .expected(32'h40400000),   // 3.0
      .test_name("Scalar addition 1+2=3")
    );
    
    // Test 2: Zero addition
    test_operation(
      .op(GA_FUNCT_ADD),
      .operand_a(32'h3f800000),  // 1.0
      .operand_b(32'h00000000),  // 0.0
      .expected(32'h3f800000),   // 1.0
      .test_name("Zero addition 1+0=1")
    );
    
    // Test 3: Negative addition
    test_operation(
      .op(GA_FUNCT_ADD),
      .operand_a(32'h3f800000),  // 1.0
      .operand_b(32'hbf800000),  // -1.0
      .expected(32'h00000000),   // 0.0
      .test_name("Negative addition 1+(-1)=0")
    );
  endtask
  
  // Test subtraction operation
  task test_subtraction();
    $display("\n--- Testing GA Subtraction ---");
    
    test_operation(
      .op(GA_FUNCT_SUB),
      .operand_a(32'h40400000),  // 3.0
      .operand_b(32'h3f800000),  // 1.0
      .expected(32'h40000000),   // 2.0
      .test_name("Scalar subtraction 3-1=2")
    );
    
    test_operation(
      .op(GA_FUNCT_SUB),
      .operand_a(32'h3f800000),  // 1.0
      .operand_b(32'h3f800000),  // 1.0
      .expected(32'h00000000),   // 0.0
      .test_name("Self subtraction 1-1=0")
    );
  endtask
  
  // Test geometric product
  task test_geometric_product();
    $display("\n--- Testing Geometric Product ---");
    
    test_operation(
      .op(GA_FUNCT_MUL),
      .operand_a(32'h40000000),  // 2.0
      .operand_b(32'h40400000),  // 3.0
      .expected(32'h40c00000),   // 6.0
      .test_name("Scalar product 2*3=6")
    );
    
    test_operation(
      .op(GA_FUNCT_MUL),
      .operand_a(32'h3f800000),  // 1.0
      .operand_b(32'h00000000),  // 0.0
      .expected(32'h00000000),   // 0.0
      .test_name("Zero product 1*0=0")
    );
  endtask
  
  // Test wedge product
  task test_wedge_product();
    $display("\n--- Testing Wedge Product ---");
    
    // For scalar inputs, wedge product should equal geometric product
    test_operation(
      .op(GA_FUNCT_WEDGE),
      .operand_a(32'h40000000),  // 2.0
      .operand_b(32'h40400000),  // 3.0
      .expected(32'h40c00000),   // 6.0
      .test_name("Scalar wedge 2^3=6")
    );
  endtask
  
  // Test dot product
  task test_dot_product();
    $display("\n--- Testing Dot Product ---");
    
    // For pure scalars, dot product should be zero
    test_operation(
      .op(GA_FUNCT_DOT),
      .operand_a(32'h40000000),  // 2.0
      .operand_b(32'h40400000),  // 3.0
      .expected(32'h00000000),   // 0.0
      .test_name("Scalar dot product=0")
    );
  endtask
  
  // Test reverse operation
  task test_reverse();
    $display("\n--- Testing Reverse ---");
    
    // Reverse of scalar should be unchanged
    test_operation(
      .op(GA_FUNCT_REV),
      .operand_a(32'h40000000),  // 2.0
      .operand_b(32'h00000000),  // unused
      .expected(32'h40000000),   // 2.0
      .test_name("Scalar reverse")
    );
  endtask
  
  // Test norm operation
  task test_norm();
    $display("\n--- Testing Norm ---");
    
    // Norm squared of scalar
    test_operation(
      .op(GA_FUNCT_NORM),
      .operand_a(32'h40000000),  // 2.0
      .operand_b(32'h00000000),  // unused
      .expected(32'h40800000),   // 4.0 (2^2)
      .test_name("Scalar norm squared")
    );
    
    test_operation(
      .op(GA_FUNCT_NORM),
      .operand_a(32'hbf800000),  // -1.0
      .operand_b(32'h00000000),  // unused
      .expected(32'h3f800000),   // 1.0 ((-1)^2)
      .test_name("Negative scalar norm")
    );
  endtask
  
  // Test corner cases
  task test_corner_cases();
    $display("\n--- Testing Corner Cases ---");
    
    // Test infinity
    test_operation(
      .op(GA_FUNCT_ADD),
      .operand_a(32'h7f800000),  // +inf
      .operand_b(32'h3f800000),  // 1.0
      .expected(32'h7f800000),   // +inf
      .test_name("Infinity addition")
    );
    
    // Test very small numbers
    test_operation(
      .op(GA_FUNCT_ADD),
      .operand_a(32'h00800000),  // Smallest normal float
      .operand_b(32'h00800000),  // Smallest normal float
      .expected(32'h01000000),   // 2 * smallest normal
      .test_name("Small number addition")
    );
    
    // Test NaN (should propagate)
    test_operation(
      .op(GA_FUNCT_ADD),
      .operand_a(32'h7fc00000),  // NaN
      .operand_b(32'h3f800000),  // 1.0
      .expected(32'h7fc00000),   // NaN (or any NaN)
      .test_name("NaN handling"),
      .check_nan(1)
    );
  endtask
  
  // Generic test operation task
  task test_operation(
    input ga_funct_e op,
    input logic [31:0] operand_a,
    input logic [31:0] operand_b,
    input logic [31:0] expected,
    input string test_name,
    input bit check_nan = 0
  );
    logic [31:0] result;
    logic timeout;
    int cycle_count;
    
    tests_run++;
    
    // Setup request
    ga_req.valid      = 1'b1;
    ga_req.operand_a  = operand_a;
    ga_req.operand_b  = operand_b;
    ga_req.funct      = op;
    ga_req.rd_addr    = 5'h0;
    ga_req.ga_reg_a   = 5'h0;
    ga_req.ga_reg_b   = 5'h1;
    ga_req.we         = 1'b1;
    ga_req.use_ga_regs = 1'b0;
    
    @(posedge clk);
    
    // Wait for ready
    timeout = 0;
    cycle_count = 0;
    while (!ga_resp.ready && !timeout) begin
      @(posedge clk);
      cycle_count++;
      if (cycle_count > 50) timeout = 1;
    end
    
    if (timeout) begin
      $display("  FAIL: %s - Timeout waiting for ready", test_name);
      tests_failed++;
      ga_req.valid = 1'b0;
      return;
    end
    
    // Wait for response
    ga_req.valid = 1'b0;
    timeout = 0;
    cycle_count = 0;
    while (!ga_resp.valid && !timeout) begin
      @(posedge clk);
      cycle_count++;
      if (cycle_count > 50) timeout = 1;
    end
    
    if (timeout) begin
      $display("  FAIL: %s - Timeout waiting for response", test_name);
      tests_failed++;
      return;
    end
    
    result = ga_resp.result;
    
    // Check result
    if (check_nan) begin
      // For NaN, just check if result is also NaN
      if (result[30:23] == 8'hFF && result[22:0] != 0) begin
        $display("  PASS: %s - NaN handled correctly", test_name);
        tests_passed++;
      end else begin
        $display("  FAIL: %s - Expected NaN, got %h", test_name, result);
        tests_failed++;
      end
    end else begin
      if (result == expected) begin
        $display("  PASS: %s", test_name);
        tests_passed++;
      end else begin
        $display("  FAIL: %s - Expected %h, got %h", test_name, expected, result);
        tests_failed++;
      end
    end
    
    @(posedge clk);
  endtask
  
  // Waveform dumping
  initial begin
    if ($test$plusargs("WAVES")) begin
      $dumpfile("ga_operations_test.vcd");
      $dumpvars(0, tb_ga_operations);
    end
  end

endmodule
