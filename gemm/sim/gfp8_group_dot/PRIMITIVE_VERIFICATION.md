# ACX_INT_MULT_ADD Primitive Verification Analysis

**Analysis Date**: Tue Oct 14 21:54:50 PDT 2025  
**Question**: Is the simulation using actual Achronix MLP72 hardware primitives or behavioral models?  
**Answer**: **BEHAVIORAL SIMULATION MODEL** - Not actual hardware primitives  

## Executive Summary

**CRITICAL FINDING**: The GFP8 group dot simulation is using **behavioral simulation models** of the ACX_MLP72 primitives, NOT the actual hardware primitives. This is confirmed by:

1. **Simulation Log Evidence**: "SLP: 0 primitives" indicates no hardware primitives
2. **File Source Verification**: Using `speedster7t_sim_BRAM72K.sv` (simulation model)
3. **Model Origin**: Behavioral model copied from Achronix internal depot

## Detailed Analysis

### 1. Simulation Log Evidence

**Key Evidence from Simulation Output**:
```
SLP: 0 primitives and 11203 (100.00%) other processes in SLP
```

**Interpretation**: 
- **"0 primitives"** = No actual hardware primitives instantiated
- **"11203 other processes"** = Behavioral simulation logic only
- This confirms we're using behavioral models, not hardware primitives

### 2. File Source Verification

**Compilation Evidence**:
```
work/work.lib:A/ACX_MLP72=22|../../../../../../../../opt/achronix/ACE_10_3_1/Achronix-linux/libraries/speedster7t/sim/speedster7t_sim_BRAM72K.sv|5596|1*17732814
```

**Analysis**:
- **Source File**: `speedster7t_sim_BRAM72K.sv` (simulation model)
- **Location**: `/libraries/speedster7t/sim/` (simulation directory)
- **NOT**: `/libraries/speedster7t/syn/` (synthesis directory)

### 3. Model Origin Verification

**Source Comment in Simulation Model**:
```systemverilog
// copy of //depot/main/hardware/projects/yuma/alpha/rev0/asic/units/bmlp/primitives/ACX_MLP72.v#12
module ACX_MLP72
```

**Analysis**:
- **Origin**: Achronix internal depot (hardware primitive)
- **Purpose**: Behavioral simulation model for functional verification
- **Status**: NOT the actual hardware primitive used in synthesis

### 4. Architecture Flow Verification

**ACX_INT_MULT_ADD Implementation Chain**:
```
gfp8_group_dot_mlp.sv
  └── ACX_INT_MULT_ADD (4 instances)
      └── _ACX_INT_MLP_FABRIC
          └── ACX_MLP72 (behavioral simulation model)
```

**Key Files**:
- **RTL Source**: `/speedster7t/common/acx_integer.sv` (lines 266-719)
- **Simulation Model**: `/speedster7t/sim/speedster7t_sim_BRAM72K.sv` (line 5596)
- **Synthesis Model**: `/speedster7t/syn/speedster7t_user_macros_BRAM72K.sv` (line 4668)

### 5. Behavioral vs Hardware Primitive Comparison

| Aspect | Behavioral Model (Simulation) | Hardware Primitive (Synthesis) |
|--------|-------------------------------|--------------------------------|
| **File Location** | `/libraries/speedster7t/sim/` | `/libraries/speedster7t/syn/` |
| **Purpose** | Functional verification | Hardware implementation |
| **Timing** | Approximate/ideal | Actual hardware timing |
| **Resource Usage** | Not applicable | Actual MLP72 blocks |
| **Performance** | Behavioral accuracy | Hardware performance |
| **SLP Primitives** | 0 (behavioral only) | >0 (actual primitives) |

## Implications

### ✅ What This Simulation Validates

1. **Functional Correctness**: Arithmetic operations work correctly
2. **Interface Compatibility**: Module interfaces are properly defined
3. **Data Flow**: Input/output data handling is correct
4. **Control Logic**: State machines and control signals function properly
5. **Integration Readiness**: Module can be integrated into larger system

### ⚠️ What This Simulation Does NOT Validate

1. **Hardware Timing**: Actual MLP72 timing characteristics
2. **Resource Utilization**: Real MLP72 block usage
3. **Power Consumption**: Actual hardware power requirements
4. **Placement Constraints**: MLP72 placement and routing
5. **Performance**: Real hardware performance characteristics

## Verification Status

### Simulation Results (Behavioral)
- [PASS] All 4 test cases complete successfully
- [PASS] Correct arithmetic results (mantissa=32, exponent=0, etc.)
- [PASS] Special case handling (zero exponents)
- [PASS] Signed arithmetic (negative mantissas)
- [PASS] Real data processing (hex file data)

### Hardware Validation Required
- [PENDING] Synthesis with actual MLP72 primitives
- [PENDING] Timing analysis with real hardware constraints
- [PENDING] Resource utilization verification
- [PENDING] Place-and-route validation
- [PENDING] Hardware performance measurement

## Recommendations

### Immediate Actions
1. **Proceed with Integration**: Behavioral simulation validates functional correctness
2. **Plan Synthesis Testing**: Schedule synthesis run to verify hardware implementation
3. **Timing Analysis**: Check if 400MHz operation is feasible with real primitives

### Next Steps for Hardware Validation
1. **Synthesis Run**: Use actual MLP72 primitives in synthesis
2. **Timing Closure**: Verify timing constraints with real hardware
3. **Resource Mapping**: Confirm MLP72 placement and utilization
4. **Hardware Testing**: Validate on actual FPGA hardware

## Conclusion

**Status**: **BEHAVIORAL SIMULATION COMPLETE** - Functional validation successful

The GFP8 group dot simulation successfully validates the **functional correctness** of the design using behavioral models of the ACX_MLP72 primitives. While this confirms the arithmetic and logic are correct, **hardware validation with actual primitives** is still required for:

- Timing verification
- Resource utilization
- Performance measurement
- Hardware integration

**Next Phase**: Proceed to synthesis and hardware validation with actual MLP72 primitives.

---

**Generated by**: Claude Code (claude.ai/code)  
**Analysis Date**: Tue Oct 14 21:54:50 PDT 2025  
**Verification Method**: Simulation log analysis, file source verification, model origin tracing
