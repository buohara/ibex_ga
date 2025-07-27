# Coprocessor Integration Guide for Ibex RISC-V Core

## Overview
This guide outlines the steps to integrate any custom coprocessor or functional unit with the Ibex RISC-V core and extend the instruction set. It follows the standard interfaces and patterns used throughout the Ibex codebase.

## Integration Architecture

```
┌─────────────────┐    ┌──────────────────┐    ┌─────────────────┐
│   Ibex Core     │    │  Coprocessor     │    │   Custom        │
│                 │    │  Interface       │    │   Coprocessor   │
│  ┌───────────┐  │    │                  │    │                 │
│  │ Decoder   │──┼────┼─► Custom Instr   │    │  ┌───────────┐  │
│  └───────────┘  │    │   Decoder        │    │  │ Custom    │  │
│                 │    │                  │    │  │ Engine    │  │
│  ┌───────────┐  │    │  ┌─────────────┐ │    │  └───────────┘  │
│  │ ID Stage  │──┼────┼─►│ Control     │─┼────┼─►┌───────────┐  │
│  └───────────┘  │    │  │ Logic       │ │    │  │ Control   │  │
│                 │    │  └─────────────┘ │    │  │ Unit      │  │
│  ┌───────────┐  │    │                  │    │  └───────────┘  │
│  │ WB Stage  │◄─┼────┼─► Result Mux     │    │                 │
│  └───────────┘  │    │                  │    │  ┌───────────┐  │
│                 │    │                  │    │  │ Data Path │  │
│                 │    │                  │    │  └───────────┘  │
└─────────────────┘    └──────────────────┘    └─────────────────┘
```

## Step 1: Define Custom Instructions

### Custom Opcode Allocation
- Use RISC-V custom opcodes: `CUSTOM-0` (7'h0B), `CUSTOM-1` (7'h2B), `CUSTOM-2` (7'h5B), or `CUSTOM-3` (7'h7B)
- Define function codes for different operations within your custom opcode space
- Follow RISC-V instruction format conventions (R-type, I-type, etc.)

### Example Custom Instructions
```
CUSTOM_OP1  rd, rs1, rs2     # R-type: custom operation on two registers
CUSTOM_OP2  rd, rs1, imm     # I-type: custom operation with immediate
CUSTOM_LD   rd, rs1, imm     # Load from custom memory/registers
CUSTOM_ST   rs1, rs2, imm    # Store to custom memory/registers
```

## Step 2: Modify Package File (ibex_pkg.sv)

This is the **critical first step** for any Ibex extension. You must follow the established interface patterns.

Add to `rtl/ibex_pkg.sv`:

```systemverilog
// 1. Add your custom opcode to the opcode_e enum
typedef enum logic [6:0] {
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
  // Add your custom opcode here
  OPCODE_CUSTOM_0 = 7'h0B  // or 7'h2B, 7'h5B, 7'h7B
} opcode_e;

// 2. Extend RF write data selection (REQUIRED)
typedef enum logic [1:0] {  // Extended from 1 bit to 2 bits
  RF_WD_EX,        // Write data from execute stage (existing)
  RF_WD_CSR,       // Write data from CSR (existing)
  RF_WD_CUSTOM     // Write data from your custom extension
} rf_wd_sel_e;

// 3. Define your custom function codes
typedef enum logic [3:0] {
  CUSTOM_FUNCT_OP1    = 4'b0000,
  CUSTOM_FUNCT_OP2    = 4'b0001,
  CUSTOM_FUNCT_LOAD   = 4'b0010,
  CUSTOM_FUNCT_STORE  = 4'b0011
  // Add more as needed
} custom_funct_e;

// 4. Define custom data structures (if needed)
typedef struct packed {
  logic [31:0] data_a;
  logic [31:0] data_b;
  // Add fields as needed for your coprocessor
} custom_data_t;

// 5. Define standard request/response interface
typedef struct packed {
  logic                valid;
  logic                ready;
  logic [31:0]         operand_a;
  logic [31:0]         operand_b;
  logic [4:0]          rd_addr;
  logic [3:0]          funct;
  logic                we;
} custom_req_t;

typedef struct packed {
  logic                valid;
  logic [31:0]         result;
  logic                error;
  logic                busy;
} custom_resp_t;
```

## Step 3: Extend Decoder (ibex_decoder.sv)

The decoder must be modified to recognize your custom instructions and generate appropriate control signals.

Modify `rtl/ibex_decoder.sv`:

```systemverilog
// 1. Add custom control outputs to the module interface
module ibex_decoder #(
  // ... existing parameters ...
) (
  // ... existing ports ...
  
  // Add custom extension outputs
  output logic                 custom_en_o,
  output logic [3:0]           custom_funct_o,
  output logic [31:0]          custom_operand_a_o,
  output logic [31:0]          custom_operand_b_o,
  output logic                 custom_we_o
);

// 2. Add your custom opcode case in the main decoder
always_comb begin
  // ... existing decoder logic ...
  
  unique case (opcode)
    // ... existing opcodes ...
    
    OPCODE_CUSTOM_0: begin
      custom_en_o = 1'b1;
      custom_funct_o = instr[15:12]; // Use funct4 field
      rf_ren_a_o = 1'b1;  // Read register A
      rf_ren_b_o = 1'b1;  // Read register B (if needed)
      
      case (instr[15:12])
        CUSTOM_FUNCT_OP1: begin
          rf_we = 1'b1;
          rf_wdata_sel_o = RF_WD_CUSTOM;
          // Configure for your operation
        end
        
        CUSTOM_FUNCT_OP2: begin
          rf_we = 1'b1;
          rf_wdata_sel_o = RF_WD_CUSTOM;
          // Configure for your operation
        end
        
        CUSTOM_FUNCT_LOAD: begin
          rf_we = 1'b1;
          rf_wdata_sel_o = RF_WD_CUSTOM;
          rf_ren_b_o = 1'b0;  // Don't need rs2 for load
        end
        
        CUSTOM_FUNCT_STORE: begin
          rf_we = 1'b0;  // Store doesn't write to register
          rf_ren_a_o = 1'b1;  // Need address
          rf_ren_b_o = 1'b1;  // Need data to store
        end
        
        default: illegal_insn = 1'b1;
      endcase
    end
    
    // ... rest of existing opcodes ...
    
    default: begin
      illegal_insn = 1'b1;
    end
  endcase
end
```

**Key Points:**
- Use `rf_wdata_sel_o = RF_WD_CUSTOM` to route your results to register file
- Set `rf_we = 1'b1` when instruction writes to a register
- Set `rf_ren_a_o`/`rf_ren_b_o` when instruction reads from registers
- Mark illegal instructions with `illegal_insn = 1'b1`

## Step 4: Modify Core Interface (ibex_core.sv)

Add the coprocessor interface to the top-level core module.

Add to `rtl/ibex_core.sv`:

```systemverilog
module ibex_core import ibex_pkg::*; #(
  // ... existing parameters ...
) (
  // ... existing ports ...
  
  // Custom Coprocessor Interface
  output logic                custom_req_o,
  output custom_req_t         custom_req_data_o,
  input  custom_resp_t        custom_resp_i,
  input  logic                custom_ready_i,
  output logic                custom_valid_o
);

// Internal custom coprocessor signals  
logic              custom_en;
logic [3:0]        custom_funct;
logic [31:0]       custom_result;
logic              custom_valid;
logic              custom_ready;

// Connect to ID stage
assign custom_req_data_o.operand_a = rf_rdata_a_ecc;  // From register file
assign custom_req_data_o.operand_b = rf_rdata_b_ecc;  // From register file
assign custom_req_data_o.funct = custom_funct;
assign custom_req_data_o.rd_addr = rf_waddr_wb_o;
assign custom_req_data_o.valid = custom_en;
assign custom_req_data_o.we = rf_we_wb_o;

assign custom_req_o = custom_en;
assign custom_result = custom_resp_i.result;
assign custom_valid = custom_resp_i.valid;
```

**Integration with ID Stage:**
In the ID stage connections, add:
```systemverilog
// In the ID stage instantiation
.custom_en_o(custom_en),
.custom_funct_o(custom_funct),
.custom_result_i(custom_result),
.custom_valid_i(custom_valid)
```

## Step 5: Modify ID Stage (ibex_id_stage.sv)

The ID stage needs to handle the result multiplexing for your custom extension.

Add to `rtl/ibex_id_stage.sv`:

```systemverilog
// Add custom inputs/outputs to module interface
input  logic [31:0]          custom_result_i,
input  logic                 custom_valid_i,
output logic                 custom_en_o,
output logic [3:0]           custom_funct_o,

// In the register file write data multiplexer
always_comb begin
  unique case (rf_wdata_sel)
    RF_WD_EX:     rf_wdata_wb_ecc_o = rf_wdata_wb_ecc;
    RF_WD_CSR:    rf_wdata_wb_ecc_o = csr_rdata;
    RF_WD_CUSTOM: rf_wdata_wb_ecc_o = custom_result_i;  // Your custom result
    default:      rf_wdata_wb_ecc_o = rf_wdata_wb_ecc;
  endcase
end

// Connect decoder signals
assign custom_en_o = decoder_i.custom_en_o;
assign custom_funct_o = decoder_i.custom_funct_o;
```

**Key Interface Points:**
- Add `RF_WD_CUSTOM` case to result multiplexer
- Connect decoder control signals to outputs
- Handle custom result data routing

## Step 6: Create Coprocessor Interface Module (Optional)

If your coprocessor is complex or external, create a separate interface module.

Create `rtl/ibex_custom_copro_if.sv`:

```systemverilog
module ibex_custom_copro_if (
  input  logic           clk_i,
  input  logic           rst_ni,
  
  // From Ibex Core
  input  logic           custom_en_i,
  input  logic [3:0]     custom_funct_i,
  input  logic [31:0]    custom_op_a_i,
  input  logic [31:0]    custom_op_b_i,
  input  logic [31:0]    custom_imm_i,
  
  // To Ibex Core
  output logic [31:0]    custom_result_o,
  output logic           custom_valid_o,
  output logic           custom_ready_o,
  
  // External Coprocessor Interface
  output custom_req_t    copro_req_o,
  input  custom_resp_t   copro_resp_i
);
  
  // State machine for multi-cycle operations
  typedef enum logic [1:0] {
    IDLE,
    ACTIVE,
    WAIT_RESP
  } state_e;
  
  state_e state_q, state_d;
  
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      state_q <= IDLE;
    end else begin
      state_q <= state_d;
    end
  end
  
  always_comb begin
    state_d = state_q;
    custom_valid_o = 1'b0;
    custom_ready_o = 1'b1;
    
    copro_req_o.valid = 1'b0;
    copro_req_o.operand_a = custom_op_a_i;
    copro_req_o.operand_b = custom_op_b_i;
    copro_req_o.funct = custom_funct_i;
    
    case (state_q)
      IDLE: begin
        if (custom_en_i) begin
          copro_req_o.valid = 1'b1;
          if (copro_resp_i.busy) begin
            state_d = WAIT_RESP;
            custom_ready_o = 1'b0;
          end else begin
            state_d = ACTIVE;
          end
        end
      end
      
      ACTIVE: begin
        if (copro_resp_i.valid) begin
          custom_valid_o = 1'b1;
          custom_result_o = copro_resp_i.result;
          state_d = IDLE;
        end
      end
      
      WAIT_RESP: begin
        custom_ready_o = 1'b0;
        if (!copro_resp_i.busy) begin
          state_d = ACTIVE;
        end
      end
    endcase
  end
  
endmodule
```

## Step 7: Update Build Files

Modify `ibex_core.core`:

```yaml
files_rtl:
  depend:
    # ... existing dependencies ...
    - your_org:custom:custom_coprocessor  # Your coprocessor core (if external)
  files:
    # ... existing files ...
    - rtl/ibex_custom_copro_if.sv  # If using interface module
```

## Step 8: Add Tracer Support (ibex_tracer.sv)

For debugging and simulation, add instruction tracing support:

```systemverilog
// In the main decode case statement of ibex_tracer.sv
OPCODE_CUSTOM_0: begin
  unique casez (rvfi_insn[15:12])
    4'b0000: decode_r_insn("custom_op1");
    4'b0001: decode_i_insn("custom_op2");
    4'b0010: decode_i_insn("custom_load");
    4'b0011: decode_s_insn("custom_store");
    default: decode_mnemonic("INVALID");
  endcase
end
```

## Step 9: Create Test System

Create a test system in `examples/custom_system/`:

```
examples/custom_system/
├── README.md
├── ibex_custom_system.core     # FuseSoC core file
├── rtl/
│   ├── ibex_custom_system.sv   # Top-level system
│   └── custom_coprocessor.sv   # Your coprocessor (if internal)
└── sw/
    ├── custom_test/            # Test software
    └── custom_lib/             # Custom library functions
```

## Step 10: Software Support

Create software support in `examples/sw/custom_system/`:

```c
// custom_lib.h - Header file for custom coprocessor functions
#ifndef CUSTOM_LIB_H
#define CUSTOM_LIB_H

#include <stdint.h>

// Custom data structures (if needed)
typedef struct {
    uint32_t field_a;
    uint32_t field_b;
    // Add fields as needed
} custom_data_t;

// Custom coprocessor instruction macros
#define CUSTOM_OP1(rd, rs1, rs2) \
    asm volatile ("custom_op1 %0, %1, %2" : "=r"(rd) : "r"(rs1), "r"(rs2))

#define CUSTOM_OP2(rd, rs1, imm) \
    asm volatile ("custom_op2 %0, %1, %2" : "=r"(rd) : "r"(rs1), "i"(imm))

#define CUSTOM_LOAD(rd, rs1, imm) \
    asm volatile ("custom_load %0, %1, %2" : "=r"(rd) : "r"(rs1), "i"(imm))

#define CUSTOM_STORE(rs1, rs2, imm) \
    asm volatile ("custom_store %0, %1, %2" : : "r"(rs1), "r"(rs2), "i"(imm))

// Custom library functions
uint32_t custom_operation_1(uint32_t a, uint32_t b);
uint32_t custom_operation_2(uint32_t a, uint32_t imm);
void custom_load_data(uint32_t addr, uint32_t *data);
void custom_store_data(uint32_t addr, uint32_t data);

#endif
```

## Step 11: Build and Test

1. **Build the extended Ibex system:**
```bash
fusesoc --cores-root=. run --target=sim --setup --build \
    lowrisc:ibex:ibex_custom_system $(util/ibex_config.py small fusesoc_opts)
```

2. **Build and run custom test software:**
```bash
cd examples/sw/custom_system/custom_test
make
cd ../../../../
./build/lowrisc_ibex_ibex_custom_system_0/sim-verilator/Vibex_custom_system \
    examples/sw/custom_system/custom_test/custom_test.vmem
```

## Critical Implementation Requirements

### 1. **Standard Interface Compliance**
- **MUST** add your opcode to `opcode_e` enum in `ibex_pkg.sv`
- **MUST** extend `rf_wd_sel_e` enum to include your result path
- **MUST** use standard valid/ready handshaking for multi-cycle ops
- **MUST** implement proper illegal instruction detection

### 2. **Pipeline Integration Points**
- **Decoder**: Add opcode case and control signal generation
- **ID Stage**: Add result multiplexing for `RF_WD_CUSTOM`  
- **Core**: Add top-level interface ports
- **Tracer**: Add instruction decode for debugging

### 3. **Error Handling**
- Set `illegal_insn = 1'b1` for unrecognized function codes
- Implement timeout/error detection for external coprocessors
- Use `custom_resp_t.error` field for operation-specific errors

### 4. **Multi-cycle Operation Support**
- Use valid/ready handshaking protocol
- Implement state machine in interface module if needed
- Handle pipeline stalls appropriately

## Step 12: Integration Considerations

### Performance
- Consider pipeline stalls for multi-cycle operations
- Implement proper handshaking between core and coprocessor
- Add bypass logic for dependent operations
- Consider dedicated register files or memory interfaces

### Memory Interface  
- Handle custom memory access patterns
- Consider packed vs. unpacked data layouts
- Add DMA support for bulk operations if needed
- Implement cache-friendly access patterns

### Precision and Numerical Stability
- Handle floating-point precision appropriately
- Consider fixed-point arithmetic for area/power efficiency
- Implement proper rounding modes
- Add overflow/underflow detection

### Debug Support
- Extend RVFI interface for custom instructions:
```systemverilog
`ifdef RVFI
  output logic                 rvfi_custom_valid,
  output logic [31:0]          rvfi_custom_data,
  // Add other RVFI signals as needed
`endif
```
- Add debug register access to custom state
- Implement custom instruction tracing
- Add performance counters for custom operations

### Power Management
- Add clock gating for coprocessor when idle
- Implement fine-grained power domains for unused components
- Consider low-power modes for custom functionality

## Next Steps

1. **Define your custom instruction set** following RISC-V encoding conventions
2. **Implement your coprocessor RTL** with proper interface protocols
3. **Create the interface module** with standard request/response handling
4. **Modify the Ibex decoder and core files** following the patterns above
5. **Create comprehensive test cases** covering all custom operations
6. **Benchmark performance improvements** for your specific use case
7. **Validate against reference implementations** of your functionality

## Key Design Principles

1. **Follow Standard Interfaces**: Use the established `opcode_e`, `rf_wd_sel_e`, and request/response patterns
2. **Modularity**: Keep your extension as a separate module interfacing with the core
3. **Standard Protocols**: Use valid/ready handshaking for multi-cycle operations  
4. **Error Handling**: Implement proper error signaling and illegal instruction detection
5. **Pipeline Awareness**: Consider pipeline timing and stall conditions
6. **Configurability**: Make your extension optional via parameters

This integration approach provides a clean interface between Ibex and any custom coprocessor while maintaining the modularity and configurability of the Ibex design. The focus on standard interfaces ensures compatibility with the existing Ibex ecosystem and debugging infrastructure.
